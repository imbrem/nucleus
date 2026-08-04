//! Native numeric-loopback server for the signed kernel-service byte protocol.
//!
//! The server owns one [`LocalKernelService`] on its dedicated thread. HTTP is only a strict,
//! bounded byte boundary: authenticated service failures remain recipient-signed HTTP 200
//! results, while malformed framing, unauthorized channel creation, and invalid signed exchanges
//! are unsigned HTTP errors.

use std::collections::{HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;
use std::io;
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::mpsc::{self, Receiver, Sender, TryRecvError};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

use covalence_kernel_service::{
    KernelService,
    wire::{ChannelGrant, ChannelNonce, PublicKeyIdentity, SignedInvocation},
};

use super::LocalKernelService;
use super::http_transport::{
    BootstrapToken, HttpTransportError, KernelHttpRequest, LoopbackHttpEndpoint,
    read_server_request, write_server_boundary_error, write_server_success,
};

const DEFAULT_IO_TIMEOUT: Duration = Duration::from_secs(10);
const DEFAULT_IDLE_TTL: Duration = Duration::from_mins(5);
const ACCEPT_POLL_INTERVAL: Duration = Duration::from_millis(10);
const DEFAULT_MAX_CHANNELS: usize = 64;
const DEFAULT_MAX_CHANNELS_PER_CALLER: usize = 4;

/// Explicit authorization and resource policy for one native loopback kernel.
#[derive(Clone)]
pub struct NativeKernelServerConfig {
    bind_address: SocketAddr,
    allowed_callers: HashSet<PublicKeyIdentity>,
    bootstrap_token: Option<BootstrapToken>,
    io_timeout: Duration,
    idle_ttl: Duration,
    max_channels: usize,
    max_channels_per_caller: usize,
}

impl fmt::Debug for NativeKernelServerConfig {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("NativeKernelServerConfig")
            .field("bind_address", &self.bind_address)
            .field("allowed_callers", &self.allowed_callers)
            .field("has_bootstrap_token", &self.bootstrap_token.is_some())
            .field("io_timeout", &self.io_timeout)
            .field("idle_ttl", &self.idle_ttl)
            .field("max_channels", &self.max_channels)
            .field("max_channels_per_caller", &self.max_channels_per_caller)
            .finish()
    }
}

impl NativeKernelServerConfig {
    /// Creates a server policy with an explicit static caller allow-list.
    ///
    /// An empty set is accepted only after adding a one-time bootstrap token.
    #[must_use]
    pub fn new(
        bind_address: SocketAddr,
        allowed_callers: impl IntoIterator<Item = PublicKeyIdentity>,
    ) -> Self {
        Self {
            bind_address,
            allowed_callers: allowed_callers.into_iter().collect(),
            bootstrap_token: None,
            io_timeout: DEFAULT_IO_TIMEOUT,
            idle_ttl: DEFAULT_IDLE_TTL,
            max_channels: DEFAULT_MAX_CHANNELS,
            max_channels_per_caller: DEFAULT_MAX_CHANNELS_PER_CALLER,
        }
    }

    /// Adds a one-time capability which authorizes its first caller key for future grants.
    #[must_use]
    pub fn with_bootstrap_token(mut self, token: BootstrapToken) -> Self {
        self.bootstrap_token = Some(token);
        self
    }

    /// Overrides the accepted-connection I/O timeout.
    #[must_use]
    pub const fn with_io_timeout(mut self, timeout: Duration) -> Self {
        self.io_timeout = timeout;
        self
    }

    /// Overrides the channel idle lifetime. Expiry closes every SQL handle owned by the channel.
    #[must_use]
    pub const fn with_idle_ttl(mut self, ttl: Duration) -> Self {
        self.idle_ttl = ttl;
        self
    }

    /// Overrides global and per-caller live-channel caps.
    #[must_use]
    pub const fn with_channel_limits(mut self, global: usize, per_caller: usize) -> Self {
        self.max_channels = global;
        self.max_channels_per_caller = per_caller;
        self
    }
}

/// Running dedicated-thread loopback kernel.
pub struct NativeKernelServerHandle {
    address: SocketAddr,
    public_key: PublicKeyIdentity,
    shutdown: Sender<()>,
    thread: Option<JoinHandle<Result<(), NativeKernelServerError>>>,
}

impl NativeKernelServerHandle {
    /// Bound numeric loopback address (including the selected port when configured with port 0).
    #[must_use]
    pub const fn address(&self) -> SocketAddr {
        self.address
    }

    /// Out-of-band key which clients must pin before accepting a channel grant.
    #[must_use]
    pub const fn public_key(&self) -> PublicKeyIdentity {
        self.public_key
    }

    /// Constructs a transport client pinned to this server.
    ///
    /// # Errors
    ///
    /// Returns an error only if the stored listener address violates endpoint invariants.
    pub fn endpoint(
        &self,
        connect_timeout: Duration,
        io_timeout: Duration,
    ) -> Result<LoopbackHttpEndpoint, HttpTransportError> {
        LoopbackHttpEndpoint::new(self.address, self.public_key, connect_timeout, io_timeout)
    }

    /// Requests shutdown and joins the service thread.
    ///
    /// # Errors
    ///
    /// Returns a server-loop failure or reports a panicked service thread.
    pub fn shutdown(mut self) -> Result<(), NativeKernelServerError> {
        let _ = self.shutdown.send(());
        self.join()
    }

    fn join(&mut self) -> Result<(), NativeKernelServerError> {
        let Some(thread) = self.thread.take() else {
            return Ok(());
        };
        thread
            .join()
            .map_err(|_| NativeKernelServerError::ThreadPanicked)?
    }
}

impl Drop for NativeKernelServerHandle {
    fn drop(&mut self) {
        if self.thread.is_some() {
            let _ = self.shutdown.send(());
            let _ = self.join();
        }
    }
}

/// Starts one independently keyed kernel service on a dedicated native thread.
///
/// # Errors
///
/// Rejects non-loopback binding, missing authorization, zero limits/timeouts, listener failures,
/// or failure to read the service identity.
pub fn spawn_native_kernel_server(
    config: NativeKernelServerConfig,
) -> Result<NativeKernelServerHandle, NativeKernelServerError> {
    validate_config(&config)?;
    let listener = TcpListener::bind(config.bind_address).map_err(NativeKernelServerError::Io)?;
    let address = listener.local_addr().map_err(NativeKernelServerError::Io)?;
    listener
        .set_nonblocking(true)
        .map_err(NativeKernelServerError::Io)?;

    let service = LocalKernelService::new(covalence_nucleus::Kernel::ephemeral());
    let public_key = service
        .identity()
        .map_err(|_| NativeKernelServerError::Identity)?
        .public_key;
    let (shutdown, shutdown_rx) = mpsc::channel();
    let thread = thread::Builder::new()
        .name("covalence-loopback-kernel".to_owned())
        .spawn(move || run_server(&listener, service, config, &shutdown_rx))
        .map_err(NativeKernelServerError::Io)?;

    Ok(NativeKernelServerHandle {
        address,
        public_key,
        shutdown,
        thread: Some(thread),
    })
}

/// Generates a fresh high-entropy one-time enrollment capability.
#[must_use]
pub fn random_bootstrap_token() -> BootstrapToken {
    covalence_lib_rand::random()
}

fn validate_config(config: &NativeKernelServerConfig) -> Result<(), NativeKernelServerError> {
    if !config.bind_address.ip().is_loopback() {
        return Err(NativeKernelServerError::NonLoopbackAddress(
            config.bind_address,
        ));
    }
    if config.allowed_callers.is_empty() && config.bootstrap_token.is_none() {
        return Err(NativeKernelServerError::MissingAuthorization);
    }
    if config.io_timeout.is_zero() || config.idle_ttl.is_zero() {
        return Err(NativeKernelServerError::ZeroTimeout);
    }
    if config.max_channels == 0
        || config.max_channels_per_caller == 0
        || config.max_channels_per_caller > config.max_channels
    {
        return Err(NativeKernelServerError::InvalidChannelLimits);
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct LiveChannel {
    caller: PublicKeyIdentity,
    channel: ChannelNonce,
    last_used: Instant,
}

fn run_server(
    listener: &TcpListener,
    mut service: LocalKernelService,
    mut config: NativeKernelServerConfig,
    shutdown: &Receiver<()>,
) -> Result<(), NativeKernelServerError> {
    let address = listener.local_addr().map_err(NativeKernelServerError::Io)?;
    let mut channels = HashMap::<(PublicKeyIdentity, ChannelNonce), LiveChannel>::new();
    loop {
        match shutdown.try_recv() {
            Ok(()) | Err(TryRecvError::Disconnected) => break,
            Err(TryRecvError::Empty) => {}
        }
        expire_channels(&mut service, &mut channels, config.idle_ttl);
        match listener.accept() {
            Ok((mut stream, peer)) => {
                if !peer.ip().is_loopback() {
                    let _ = write_server_boundary_error(
                        &mut stream,
                        403,
                        "Forbidden",
                        "loopback peers only",
                    );
                    continue;
                }
                serve_connection(
                    &mut stream,
                    address,
                    &mut service,
                    &mut config,
                    &mut channels,
                );
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                thread::sleep(ACCEPT_POLL_INTERVAL);
            }
            Err(error) => return Err(NativeKernelServerError::Io(error)),
        }
    }
    for channel in channels.into_values() {
        service.revoke_sql_channel(channel.caller, channel.channel);
    }
    Ok(())
}

fn serve_connection(
    stream: &mut TcpStream,
    address: SocketAddr,
    service: &mut LocalKernelService,
    config: &mut NativeKernelServerConfig,
    channels: &mut HashMap<(PublicKeyIdentity, ChannelNonce), LiveChannel>,
) {
    let Ok(request) = read_server_request(stream, address, config.io_timeout) else {
        let _ =
            write_server_boundary_error(stream, 400, "Bad Request", "invalid kernel HTTP request");
        return;
    };
    match request {
        KernelHttpRequest::Channel {
            caller,
            bootstrap_token,
        } => serve_channel(stream, service, config, channels, caller, bootstrap_token),
        KernelHttpRequest::Invocation(bytes) => serve_invocation(stream, service, channels, &bytes),
    }
}

fn serve_channel(
    stream: &mut TcpStream,
    service: &mut LocalKernelService,
    config: &mut NativeKernelServerConfig,
    channels: &mut HashMap<(PublicKeyIdentity, ChannelNonce), LiveChannel>,
    caller: PublicKeyIdentity,
    presented_token: Option<BootstrapToken>,
) {
    if !authorize_caller(config, caller, presented_token) {
        let _ = write_server_boundary_error(stream, 403, "Forbidden", "caller is not authorized");
        return;
    }
    let caller_channels = channels
        .values()
        .filter(|channel| channel.caller == caller)
        .count();
    if channels.len() >= config.max_channels || caller_channels >= config.max_channels_per_caller {
        let _ = write_server_boundary_error(
            stream,
            429,
            "Too Many Requests",
            "signed channel limit reached",
        );
        return;
    }
    let Ok(grant) = service.issue_sql_channel(caller) else {
        let _ = write_server_boundary_error(
            stream,
            500,
            "Internal Server Error",
            "could not issue signed channel",
        );
        return;
    };
    record_channel(channels, &grant);
    if write_server_success(stream, &grant.encode()).is_err() {
        channels.remove(&(caller, grant.channel()));
        service.revoke_sql_channel(caller, grant.channel());
    }
}

fn serve_invocation(
    stream: &mut TcpStream,
    service: &mut LocalKernelService,
    channels: &mut HashMap<(PublicKeyIdentity, ChannelNonce), LiveChannel>,
    bytes: &[u8],
) {
    let Ok(invocation) = SignedInvocation::decode(bytes) else {
        let _ =
            write_server_boundary_error(stream, 400, "Bad Request", "invalid signed invocation");
        return;
    };
    let key = (invocation.caller(), invocation.channel());
    if !channels.contains_key(&key) {
        let _ = write_server_boundary_error(
            stream,
            403,
            "Forbidden",
            "unknown or expired signed channel",
        );
        return;
    }
    match service.exchange_sql(bytes) {
        Ok(result) => {
            if let Some(channel) = channels.get_mut(&key) {
                channel.last_used = Instant::now();
            }
            let _ = write_server_success(stream, &result);
        }
        Err(_error) => {
            channels.remove(&key);
            service.revoke_sql_channel(key.0, key.1);
            let _ = write_server_boundary_error(
                stream,
                400,
                "Bad Request",
                "signed invocation was rejected",
            );
        }
    }
}

fn authorize_caller(
    config: &mut NativeKernelServerConfig,
    caller: PublicKeyIdentity,
    presented: Option<BootstrapToken>,
) -> bool {
    if config.allowed_callers.contains(&caller) {
        return true;
    }
    let (Some(expected), Some(presented)) = (config.bootstrap_token, presented) else {
        return false;
    };
    if !tokens_equal(&expected, &presented) {
        return false;
    }
    config.bootstrap_token = None;
    config.allowed_callers.insert(caller);
    true
}

fn tokens_equal(left: &BootstrapToken, right: &BootstrapToken) -> bool {
    left.iter()
        .zip(right)
        .fold(0_u8, |difference, (left, right)| {
            difference | (left ^ right)
        })
        == 0
}

fn record_channel(
    channels: &mut HashMap<(PublicKeyIdentity, ChannelNonce), LiveChannel>,
    grant: &ChannelGrant,
) {
    let channel = LiveChannel {
        caller: grant.caller(),
        channel: grant.channel(),
        last_used: Instant::now(),
    };
    channels.insert((channel.caller, channel.channel), channel);
}

fn expire_channels(
    service: &mut LocalKernelService,
    channels: &mut HashMap<(PublicKeyIdentity, ChannelNonce), LiveChannel>,
    idle_ttl: Duration,
) {
    let now = Instant::now();
    let expired = channels
        .values()
        .filter(|channel| now.duration_since(channel.last_used) >= idle_ttl)
        .map(|channel| (channel.caller, channel.channel))
        .collect::<Vec<_>>();
    for key in expired {
        channels.remove(&key);
        service.revoke_sql_channel(key.0, key.1);
    }
}

/// Startup or service-loop failure for a native loopback kernel.
#[derive(Debug)]
pub enum NativeKernelServerError {
    /// Listener address was not numeric loopback.
    NonLoopbackAddress(SocketAddr),
    /// Neither a caller allow-list nor a one-time bootstrap capability was configured.
    MissingAuthorization,
    /// An I/O or idle timeout was zero.
    ZeroTimeout,
    /// Channel limits were zero or internally inconsistent.
    InvalidChannelLimits,
    /// Kernel service identity could not be read.
    Identity,
    /// Listener or thread setup, or the listener loop, failed.
    Io(io::Error),
    /// The dedicated service thread panicked.
    ThreadPanicked,
}

impl fmt::Display for NativeKernelServerError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonLoopbackAddress(address) => write!(formatter, "non-loopback bind {address}"),
            Self::MissingAuthorization => formatter
                .write_str("native kernel requires an allowed caller or one-time bootstrap token"),
            Self::ZeroTimeout => formatter.write_str("native kernel timeouts must be nonzero"),
            Self::InvalidChannelLimits => formatter.write_str("invalid signed channel limits"),
            Self::Identity => formatter.write_str("could not read native kernel identity"),
            Self::Io(error) => write!(formatter, "native kernel I/O failed: {error}"),
            Self::ThreadPanicked => formatter.write_str("native kernel service thread panicked"),
        }
    }
}

impl StdError for NativeKernelServerError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{KernelId, SignedKernelClient};
    use covalence_kernel_service::rpc::{ServiceRequest, ServiceResponse};

    #[test]
    fn rejects_implicit_allow_any() {
        let config = NativeKernelServerConfig::new("127.0.0.1:0".parse().unwrap(), []);
        assert!(matches!(
            spawn_native_kernel_server(config),
            Err(NativeKernelServerError::MissingAuthorization)
        ));
    }

    #[test]
    fn bootstrap_then_signed_identity_round_trip() {
        let mut client = SignedKernelClient::ephemeral();
        let caller = client.caller_public_key();
        let token = [0x5a; 32];
        let server = match spawn_native_kernel_server(
            NativeKernelServerConfig::new("127.0.0.1:0".parse().unwrap(), [])
                .with_bootstrap_token(token)
                .with_io_timeout(Duration::from_secs(1))
                .with_idle_ttl(Duration::from_secs(30))
                .with_channel_limits(4, 2),
        ) {
            Ok(server) => server,
            Err(NativeKernelServerError::Io(error))
                if error.kind() == io::ErrorKind::PermissionDenied =>
            {
                return;
            }
            Err(error) => panic!("could not start loopback kernel: {error}"),
        };
        assert!(server.address().ip().is_loopback());
        let endpoint = server
            .endpoint(Duration::from_secs(1), Duration::from_secs(1))
            .unwrap()
            .with_bootstrap_token(token);
        let grant = endpoint.request_channel(caller).unwrap();
        // The token is consumed by the first request, but the admitted caller can renew a route
        // even when a simple client keeps sending the now-consumed enrollment header.
        assert!(endpoint.request_channel(caller).is_ok());
        client
            .accept_grant(KernelId::local(), server.public_key(), &grant)
            .unwrap();

        let pending = client
            .prepare(KernelId::local(), &ServiceRequest::Identity)
            .unwrap();
        let result = endpoint.invoke(&pending.encode()).unwrap();
        let response = client.accept_result(pending, &result).unwrap();
        assert!(matches!(
            response,
            ServiceResponse::Identity(Ok(identity)) if identity.public_key == server.public_key()
        ));
        server.shutdown().unwrap();
    }
}
