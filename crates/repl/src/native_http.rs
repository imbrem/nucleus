//! Minimal native HTTP carrier for signed kernel-service messages.
//!
//! HTTP is only physical framing here. Authentication, ordering, connection
//! capabilities, and shutdown all remain properties of [`SignedKernelService`].

use std::fmt;
use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream, ToSocketAddrs};
use std::time::Duration;

use crate::{
    MAX_SIGNED_MESSAGE_BYTES, PreparedHolProofComponent, ServiceIdentity, ServiceOperation,
    ServiceResult, SessionInitiator, SignedKernelService, SignedMessageRequest,
    SignedMessageResponse, SignedServiceCommand, SignedServiceSession, decode_signed_request,
    decode_signed_response, encode_signed_request, encode_signed_response,
};

/// The only application endpoint exposed by the native HTTP carrier.
pub const SIGNED_KERNEL_HTTP_PATH: &str = "/v0/signed-message";

/// Maximum accepted sockets over one native HTTP server lifetime.
///
/// Every socket consumes the budget before parsing, including malformed and
/// preflight requests. This bounds remotely retained session/connection state
/// until the semantic service grows its own compaction and per-session caps.
pub const MAX_NATIVE_HTTP_REQUESTS: usize = 4_096;

/// Lifetime socket budget for an endpoint which executes an allowlisted proof component.
///
/// Signed replies retain the last artifact for exact retry. Keeping this demo
/// endpoint deliberately short-lived bounds both execution and retained state
/// even though any requester can establish a PKI session.
pub const MAX_NATIVE_HOL_COMPONENT_REQUESTS: usize = 16;

/// Maximum artifact retained in a component endpoint's cached signed reply.
pub const MAX_NATIVE_HOL_COMPONENT_ARTIFACT_BYTES: usize = 1024 * 1024;

const MAX_HTTP_HEADER_BYTES: usize = 16 * 1024;
const IO_TIMEOUT: Duration = Duration::from_secs(10);

/// A single-threaded native HTTP carrier around one signed kernel service.
pub struct NativeHttpKernelServer {
    listener: TcpListener,
    service: SignedKernelService,
    cors_origin: String,
    remaining_requests: usize,
}

impl NativeHttpKernelServer {
    /// Binds a fresh ephemeral-key service to `address`.
    ///
    /// `cors_origin` must be one exact HTTP(S) origin and is emitted verbatim.
    /// Wildcards are rejected: CORS is not an authorization mechanism, but the
    /// browser-facing demo must be narrow.
    ///
    /// # Errors
    ///
    /// Returns an error when the address cannot be bound, the CORS value can
    /// inject a header, or the ephemeral signed service cannot be created.
    pub fn bind(
        address: impl ToSocketAddrs,
        cors_origin: impl Into<String>,
    ) -> Result<Self, NativeHttpError> {
        Self::bind_with_request_limit(address, cors_origin, MAX_NATIVE_HTTP_REQUESTS)
    }

    /// Binds a short-lived service for one locally prepared proof component.
    ///
    /// The component was already size-checked, validated, and compiled. Remote
    /// commands carry only its digest; they cannot upload bytes or trigger
    /// compilation. Every invocation uses a fresh fuel- and memory-bounded
    /// store and the existing checked replay/signing path.
    ///
    /// # Errors
    ///
    /// Returns an error when the address cannot be bound, the CORS value can
    /// inject a header, or the ephemeral signed service cannot be created.
    pub fn bind_hol_proof_component(
        address: impl ToSocketAddrs,
        cors_origin: impl Into<String>,
        component: PreparedHolProofComponent,
    ) -> Result<Self, NativeHttpError> {
        let digest = component.digest();
        let mut service = SignedKernelService::new()
            .map_err(|error| NativeHttpError::Service(error.to_string()))?;
        service
            .allow_hol_proof_component(digest, move |kernel| {
                let artifact = component
                    .run(kernel)
                    .map_err(|_| "allowlisted HOL proof component failed")?;
                if artifact.image().len() > MAX_NATIVE_HOL_COMPONENT_ARTIFACT_BYTES {
                    return Err("allowlisted HOL proof component artifact is too large");
                }
                Ok(artifact)
            })
            .map_err(|error| NativeHttpError::Service(error.to_string()))?;
        Self::bind_service_with_request_limit(
            address,
            cors_origin,
            MAX_NATIVE_HOL_COMPONENT_REQUESTS,
            service,
        )
    }

    fn bind_with_request_limit(
        address: impl ToSocketAddrs,
        cors_origin: impl Into<String>,
        request_limit: usize,
    ) -> Result<Self, NativeHttpError> {
        let service = SignedKernelService::new()
            .map_err(|error| NativeHttpError::Service(error.to_string()))?;
        Self::bind_service_with_request_limit(address, cors_origin, request_limit, service)
    }

    fn bind_service_with_request_limit(
        address: impl ToSocketAddrs,
        cors_origin: impl Into<String>,
        request_limit: usize,
        service: SignedKernelService,
    ) -> Result<Self, NativeHttpError> {
        let cors_origin = cors_origin.into();
        if !is_exact_http_origin(&cors_origin) {
            return Err(NativeHttpError::Protocol("invalid CORS origin"));
        }
        if request_limit == 0 {
            return Err(NativeHttpError::Protocol(
                "HTTP request limit must be positive",
            ));
        }
        Ok(Self {
            listener: TcpListener::bind(address)?,
            service,
            cors_origin,
            remaining_requests: request_limit,
        })
    }

    /// Returns the bound address (including an OS-selected port).
    ///
    /// # Errors
    ///
    /// Returns an operating-system socket error if the address is unavailable.
    pub fn local_addr(&self) -> io::Result<SocketAddr> {
        self.listener.local_addr()
    }

    /// Returns the endpoint identity which clients must pin out of band.
    #[must_use]
    pub const fn identity(&self) -> ServiceIdentity {
        self.service.description().identity()
    }

    /// Serves connections until an authenticated signed shutdown is dispatched.
    ///
    /// Malformed requests receive a bounded unsigned HTTP error and cannot
    /// affect service state. Every accepted socket consumes the fixed lifetime
    /// budget, whether or not parsing succeeds. This server never retries, but
    /// a client's HTTP stack may transparently retransmit replayable requests.
    ///
    /// # Errors
    ///
    /// Returns an error if accepting a connection, writing a response, or
    /// signing an authenticated service response fails.
    pub fn serve(mut self) -> Result<(), NativeHttpError> {
        loop {
            if self.remaining_requests == 0 {
                return Err(NativeHttpError::ResourceLimit);
            }
            let (mut stream, _) = self.listener.accept()?;
            self.remaining_requests -= 1;
            stream.set_read_timeout(Some(IO_TIMEOUT))?;
            stream.set_write_timeout(Some(IO_TIMEOUT))?;
            match self.serve_stream(&mut stream) {
                Ok(shutdown) => {
                    if shutdown {
                        return Ok(());
                    }
                }
                Err(error) => {
                    let _ = write_error(&mut stream, error.status(), &self.cors_origin);
                }
            }
        }
    }

    fn serve_stream(&mut self, stream: &mut TcpStream) -> Result<bool, NativeHttpError> {
        let request = read_http_request(stream)?;
        if request.method == "OPTIONS" {
            write_options(stream, &self.cors_origin)?;
            return Ok(false);
        }
        if request.method != "POST" {
            return Err(NativeHttpError::Method);
        }

        let message = decode_signed_request(&request.body)
            .map_err(|error| NativeHttpError::Message(error.to_string()))?;
        let (response, shutdown) = match message {
            SignedMessageRequest::Describe => (
                SignedMessageResponse::Description(self.service.description().clone()),
                false,
            ),
            SignedMessageRequest::OpenSession(request) => {
                let accepted = self
                    .service
                    .open_session(&request)
                    .map_err(|error| NativeHttpError::Service(error.to_string()))?;
                (SignedMessageResponse::SessionAccepted(accepted), false)
            }
            SignedMessageRequest::Execute(command) => {
                let reply = self
                    .service
                    .execute(&command)
                    .map_err(|error| NativeHttpError::Service(error.to_string()))?;
                let shutdown = reply.is_goodbye();
                (SignedMessageResponse::Reply(reply), shutdown)
            }
        };
        let body = encode_signed_response(&response)
            .map_err(|error| NativeHttpError::Message(error.to_string()))?;
        write_response(stream, "200 OK", &body, &self.cors_origin)?;
        Ok(shutdown)
    }
}

/// Minimal native client for the same signed HTTP service used by browser Fetch.
///
/// HTTP is not authority. The pinned endpoint identity and the complete signed
/// session capability live only in this process-local object.
pub struct NativeHttpKernelClient {
    address: SocketAddr,
    identity: ServiceIdentity,
    session: SignedServiceSession,
    pending: Option<SignedServiceCommand>,
}

impl NativeHttpKernelClient {
    /// Pins an endpoint description and establishes a requester-signed session.
    ///
    /// The exact public key must arrive independently of this HTTP connection.
    /// An ambiguous `OpenSession` response is terminal because that handshake has
    /// no cached-reply recovery.
    ///
    /// # Errors
    ///
    /// Returns a definite error before `OpenSession` is emitted, or an
    /// outcome-unknown error after it may have reached the endpoint.
    pub fn connect(
        address: SocketAddr,
        expected_public_key: [u8; 32],
    ) -> Result<Self, NativeHttpClientError> {
        let expected = ServiceIdentity::new(
            covalence_nucleus::ed25519_key_id(&expected_public_key),
            expected_public_key,
        )
        .map_err(|error| NativeHttpClientError::Definite(error.to_string()))?;
        let description = exchange_message(address, &SignedMessageRequest::Describe)
            .map_err(NativeHttpClientError::Definite)?;
        let SignedMessageResponse::Description(description) = description else {
            return Err(NativeHttpClientError::Definite(
                "expected signed endpoint description".to_owned(),
            ));
        };
        let initiator = SessionInitiator::begin(expected, &description)
            .map_err(|error| NativeHttpClientError::Definite(error.to_string()))?;
        let accepted = exchange_message(
            address,
            &SignedMessageRequest::OpenSession(initiator.request().clone()),
        )
        .map_err(NativeHttpClientError::OutcomeUnknown)?;
        let SignedMessageResponse::SessionAccepted(accepted) = accepted else {
            return Err(NativeHttpClientError::OutcomeUnknown(
                "expected signed session acceptance".to_owned(),
            ));
        };
        let session = initiator
            .accept(&accepted)
            .map_err(|error| NativeHttpClientError::OutcomeUnknown(error.to_string()))?;
        Ok(Self {
            address,
            identity: expected,
            session,
            pending: None,
        })
    }

    /// Returns the independently pinned endpoint identity.
    #[must_use]
    pub const fn identity(&self) -> ServiceIdentity {
        self.identity
    }

    /// Signs, sends, authenticates, and accepts one service operation.
    ///
    /// If transport or reply acceptance fails, the exact signed command is
    /// retained for an explicit [`Self::retry_pending`] decision.
    ///
    /// # Errors
    ///
    /// Returns an outcome-unknown error after a signed command may have been
    /// dispatched, or a definite local error before any request was emitted.
    pub fn execute(
        &mut self,
        operation: ServiceOperation,
    ) -> Result<ServiceResult, NativeHttpClientError> {
        if self.pending.is_some() {
            return Err(NativeHttpClientError::Definite(
                "a signed command is already pending".to_owned(),
            ));
        }
        let command = self
            .session
            .command(operation)
            .map_err(|error| NativeHttpClientError::Definite(error.to_string()))?;
        self.pending = Some(command);
        self.retry_pending()
    }

    /// Re-emits only the exact pending signed command.
    ///
    /// # Errors
    ///
    /// Returns a definite error when no command is pending, or an
    /// outcome-unknown error if transport/reply authentication fails again.
    pub fn retry_pending(&mut self) -> Result<ServiceResult, NativeHttpClientError> {
        let command = self.pending.as_ref().ok_or_else(|| {
            NativeHttpClientError::Definite("no signed command is pending".to_owned())
        })?;
        let response = exchange_message(
            self.address,
            &SignedMessageRequest::Execute(command.clone()),
        )
        .map_err(NativeHttpClientError::OutcomeUnknown)?;
        let SignedMessageResponse::Reply(reply) = response else {
            return Err(NativeHttpClientError::OutcomeUnknown(
                "expected signed service reply".to_owned(),
            ));
        };
        let result = self
            .session
            .accept_reply(command, reply)
            .map_err(|error| NativeHttpClientError::OutcomeUnknown(error.to_string()))?;
        self.pending = None;
        Ok(result)
    }

    /// Reports whether an exact signed command is retained for explicit retry.
    #[must_use]
    pub const fn has_pending_command(&self) -> bool {
        self.pending.is_some()
    }
}

/// Failure observed by the native signed HTTP client.
#[derive(Debug)]
pub enum NativeHttpClientError {
    /// No stateful request was emitted, so the endpoint outcome is known.
    Definite(String),
    /// A handshake/command may have been dispatched but was not accepted.
    OutcomeUnknown(String),
}

impl NativeHttpClientError {
    /// Returns whether remote state may have advanced.
    #[must_use]
    pub const fn outcome_unknown(&self) -> bool {
        matches!(self, Self::OutcomeUnknown(_))
    }
}

impl fmt::Display for NativeHttpClientError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definite(message) => write!(formatter, "native HTTP client error: {message}"),
            Self::OutcomeUnknown(message) => {
                write!(formatter, "native HTTP client outcome unknown: {message}")
            }
        }
    }
}

impl std::error::Error for NativeHttpClientError {}

fn exchange_message(
    address: SocketAddr,
    request: &SignedMessageRequest,
) -> Result<SignedMessageResponse, String> {
    let body = encode_signed_request(request).map_err(|error| error.to_string())?;
    let body = post_message(address, &body)?;
    decode_signed_response(&body).map_err(|error| error.to_string())
}

fn post_message(address: SocketAddr, body: &[u8]) -> Result<Vec<u8>, String> {
    let mut stream = TcpStream::connect_timeout(&address, IO_TIMEOUT)
        .map_err(|error| format!("connect failed: {error}"))?;
    stream
        .set_read_timeout(Some(IO_TIMEOUT))
        .and_then(|()| stream.set_write_timeout(Some(IO_TIMEOUT)))
        .map_err(|error| format!("could not set socket deadline: {error}"))?;
    write!(
        stream,
        "POST {SIGNED_KERNEL_HTTP_PATH} HTTP/1.1\r\nHost: {address}\r\nContent-Type: application/octet-stream\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        body.len()
    )
    .and_then(|()| stream.write_all(body))
    .and_then(|()| stream.flush())
    .map_err(|error| format!("request write failed: {error}"))?;

    let mut header = Vec::with_capacity(1024);
    let mut byte = [0_u8; 1];
    while !header.ends_with(b"\r\n\r\n") {
        if header.len() == MAX_HTTP_HEADER_BYTES {
            return Err("response header is too large".to_owned());
        }
        match stream.read(&mut byte) {
            Ok(0) => return Err("response ended before its header".to_owned()),
            Ok(_) => header.push(byte[0]),
            Err(error) => return Err(format!("response read failed: {error}")),
        }
    }
    let header =
        std::str::from_utf8(&header).map_err(|_| "response header is not UTF-8".to_owned())?;
    let mut lines = header[..header.len() - 4].split("\r\n");
    if lines.next() != Some("HTTP/1.1 200 OK") {
        return Err("endpoint returned a non-success HTTP status".to_owned());
    }
    let mut content_length = None;
    let mut content_type = None;
    for line in lines {
        let (name, value) = line
            .split_once(':')
            .ok_or_else(|| "malformed response header".to_owned())?;
        let value = value.trim();
        if name.eq_ignore_ascii_case("content-length") {
            if content_length.is_some() {
                return Err("duplicate response Content-Length".to_owned());
            }
            let length = value
                .parse::<usize>()
                .map_err(|_| "invalid response Content-Length".to_owned())?;
            if length > MAX_SIGNED_MESSAGE_BYTES {
                return Err("response exceeds signed-message bound".to_owned());
            }
            content_length = Some(length);
        } else if name.eq_ignore_ascii_case("content-type") {
            if content_type.replace(value).is_some() {
                return Err("duplicate response Content-Type".to_owned());
            }
        } else if name.eq_ignore_ascii_case("transfer-encoding") {
            return Err("response Transfer-Encoding is unsupported".to_owned());
        }
    }
    if content_type != Some("application/octet-stream") {
        return Err("response Content-Type is not application/octet-stream".to_owned());
    }
    let length = content_length.ok_or_else(|| "response Content-Length is missing".to_owned())?;
    let mut body = vec![0_u8; length];
    stream
        .read_exact(&mut body)
        .map_err(|error| format!("response body is incomplete: {error}"))?;
    let mut trailing = [0_u8; 1];
    if stream
        .read(&mut trailing)
        .map_err(|error| format!("could not check response boundary: {error}"))?
        != 0
    {
        return Err("response has bytes after Content-Length".to_owned());
    }
    Ok(body)
}

fn is_exact_http_origin(origin: &str) -> bool {
    let Some(authority) = origin
        .strip_prefix("http://")
        .or_else(|| origin.strip_prefix("https://"))
    else {
        return false;
    };
    if authority.is_empty()
        || !authority.is_ascii()
        || authority
            .bytes()
            .any(|byte| byte.is_ascii_control() || byte.is_ascii_whitespace())
        || authority.contains(['/', '?', '#', '@', '\\'])
    {
        return false;
    }

    if let Some(ipv6) = authority.strip_prefix('[') {
        let Some((host, suffix)) = ipv6.split_once(']') else {
            return false;
        };
        return host.parse::<std::net::Ipv6Addr>().is_ok() && valid_origin_port(suffix);
    }

    let (host, suffix) = authority
        .rsplit_once(':')
        .map_or((authority, ""), |(host, _port)| {
            (host, &authority[host.len()..])
        });
    !host.is_empty()
        && host
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-'))
        && valid_origin_port(suffix)
}

fn valid_origin_port(suffix: &str) -> bool {
    suffix.is_empty()
        || suffix
            .strip_prefix(':')
            .is_some_and(|port| !port.is_empty() && port.parse::<u16>().is_ok())
}

#[derive(Debug)]
struct HttpRequest {
    method: String,
    body: Vec<u8>,
}

fn read_http_request(stream: &mut TcpStream) -> Result<HttpRequest, NativeHttpError> {
    let mut header = Vec::with_capacity(1024);
    let mut byte = [0_u8; 1];
    while !header.ends_with(b"\r\n\r\n") {
        if header.len() == MAX_HTTP_HEADER_BYTES {
            return Err(NativeHttpError::HeaderTooLarge);
        }
        let count = stream.read(&mut byte)?;
        if count == 0 {
            return Err(NativeHttpError::Truncated);
        }
        header.push(byte[0]);
    }

    let header = std::str::from_utf8(&header)
        .map_err(|_| NativeHttpError::Protocol("HTTP header is not UTF-8"))?;
    let mut lines = header[..header.len() - 4].split("\r\n");
    let request_line = lines
        .next()
        .ok_or(NativeHttpError::Protocol("missing request line"))?;
    let mut words = request_line.split(' ');
    let method = words
        .next()
        .ok_or(NativeHttpError::Protocol("missing HTTP method"))?;
    let path = words
        .next()
        .ok_or(NativeHttpError::Protocol("missing HTTP path"))?;
    let version = words
        .next()
        .ok_or(NativeHttpError::Protocol("missing HTTP version"))?;
    if words.next().is_some() || version != "HTTP/1.1" {
        return Err(NativeHttpError::Protocol("invalid HTTP request line"));
    }
    if path != SIGNED_KERNEL_HTTP_PATH {
        return Err(NativeHttpError::NotFound);
    }

    let mut content_length = None;
    let mut content_type = None;
    for line in lines {
        let (name, value) = line
            .split_once(':')
            .ok_or(NativeHttpError::Protocol("malformed HTTP header"))?;
        let value = value.trim();
        if name.eq_ignore_ascii_case("content-length") {
            if content_length.is_some() {
                return Err(NativeHttpError::Protocol("duplicate Content-Length"));
            }
            let length = value
                .parse::<usize>()
                .map_err(|_| NativeHttpError::Protocol("invalid Content-Length"))?;
            if length > MAX_SIGNED_MESSAGE_BYTES {
                return Err(NativeHttpError::BodyTooLarge);
            }
            content_length = Some(length);
        } else if name.eq_ignore_ascii_case("content-type") {
            if content_type.replace(value).is_some() {
                return Err(NativeHttpError::Protocol("duplicate Content-Type"));
            }
        } else if name.eq_ignore_ascii_case("transfer-encoding") {
            return Err(NativeHttpError::Protocol(
                "Transfer-Encoding is not supported",
            ));
        }
    }

    if method == "OPTIONS" {
        if content_length.unwrap_or(0) != 0 {
            return Err(NativeHttpError::Protocol("OPTIONS body is not allowed"));
        }
        return Ok(HttpRequest {
            method: method.to_owned(),
            body: Vec::new(),
        });
    }
    if content_type != Some("application/octet-stream") {
        return Err(NativeHttpError::Protocol(
            "Content-Type must be application/octet-stream",
        ));
    }
    let length = content_length.ok_or(NativeHttpError::LengthRequired)?;
    let mut body = vec![0_u8; length];
    stream
        .read_exact(&mut body)
        .map_err(|error| match error.kind() {
            io::ErrorKind::UnexpectedEof => NativeHttpError::Truncated,
            _ => NativeHttpError::Io(error),
        })?;
    Ok(HttpRequest {
        method: method.to_owned(),
        body,
    })
}

fn write_options(stream: &mut TcpStream, cors_origin: &str) -> io::Result<()> {
    write_response(stream, "204 No Content", &[], cors_origin)
}

fn write_error(stream: &mut TcpStream, status: &str, cors_origin: &str) -> io::Result<()> {
    write_response(stream, status, &[], cors_origin)
}

fn write_response(
    stream: &mut TcpStream,
    status: &str,
    body: &[u8],
    cors_origin: &str,
) -> io::Result<()> {
    write!(
        stream,
        "HTTP/1.1 {status}\r\nContent-Length: {}\r\nContent-Type: application/octet-stream\r\nAccess-Control-Allow-Origin: {cors_origin}\r\nAccess-Control-Allow-Methods: POST, OPTIONS\r\nAccess-Control-Allow-Headers: Content-Type\r\nVary: Origin\r\nConnection: close\r\n\r\n",
        body.len()
    )?;
    stream.write_all(body)?;
    stream.flush()
}

/// Native HTTP carrier error.
#[derive(Debug)]
pub enum NativeHttpError {
    /// Socket or stream failure.
    Io(io::Error),
    /// Header exceeded the fixed pre-allocation bound.
    HeaderTooLarge,
    /// Declared body exceeded the signed-message bound.
    BodyTooLarge,
    /// Request ended before its declared body length.
    Truncated,
    /// POST omitted its mandatory body length.
    LengthRequired,
    /// The exact endpoint did not match.
    NotFound,
    /// The endpoint was addressed with a method other than POST/OPTIONS.
    Method,
    /// HTTP syntax or policy violation.
    Protocol(&'static str),
    /// Signed-message codec rejection.
    Message(String),
    /// Signed service failure outside an authenticated rejection reply.
    Service(String),
    /// The finite accepted-socket lifetime budget was exhausted.
    ResourceLimit,
}

impl NativeHttpError {
    const fn status(&self) -> &'static str {
        match self {
            Self::HeaderTooLarge => "431 Request Header Fields Too Large",
            Self::BodyTooLarge => "413 Content Too Large",
            Self::LengthRequired => "411 Length Required",
            Self::NotFound => "404 Not Found",
            Self::Method => "405 Method Not Allowed",
            Self::Io(_) | Self::Truncated | Self::Protocol(_) | Self::Message(_) => {
                "400 Bad Request"
            }
            Self::Service(_) => "422 Unprocessable Content",
            Self::ResourceLimit => "503 Service Unavailable",
        }
    }
}

impl fmt::Display for NativeHttpError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "native HTTP I/O error: {error}"),
            Self::HeaderTooLarge => formatter.write_str("HTTP header is too large"),
            Self::BodyTooLarge => formatter.write_str("HTTP body is too large"),
            Self::Truncated => formatter.write_str("truncated HTTP request"),
            Self::LengthRequired => formatter.write_str("HTTP Content-Length is required"),
            Self::NotFound => formatter.write_str("unknown HTTP endpoint"),
            Self::Method => formatter.write_str("HTTP method is not allowed"),
            Self::Protocol(message) => write!(formatter, "HTTP protocol error: {message}"),
            Self::Message(message) => write!(formatter, "signed-message error: {message}"),
            Self::Service(message) => write!(formatter, "signed-service error: {message}"),
            Self::ResourceLimit => formatter.write_str("native HTTP request budget exhausted"),
        }
    }
}

impl std::error::Error for NativeHttpError {}

impl From<io::Error> for NativeHttpError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

#[cfg(test)]
mod tests {
    use std::io::{Read as _, Write as _};
    use std::net::{Shutdown, SocketAddr, TcpStream};
    use std::thread::{self, JoinHandle};

    use super::*;
    use crate::{
        ServiceOperation, ServiceResult, SessionInitiator, SignedMessageRequest,
        SignedMessageResponse, decode_signed_response, encode_signed_request,
    };

    fn spawn_server() -> (SocketAddr, JoinHandle<Result<(), NativeHttpError>>) {
        let server = NativeHttpKernelServer::bind(
            (std::net::Ipv4Addr::LOCALHOST, 0),
            "https://repl.example",
        )
        .unwrap();
        let address = server.local_addr().unwrap();
        let handle = thread::spawn(move || server.serve());
        (address, handle)
    }

    fn raw_request(address: SocketAddr, request: &[u8]) -> (u16, Vec<u8>, String) {
        let mut stream = TcpStream::connect(address).unwrap();
        stream.write_all(request).unwrap();
        stream.shutdown(Shutdown::Write).unwrap();
        let mut response = Vec::new();
        stream.read_to_end(&mut response).unwrap();
        let split = response
            .windows(4)
            .position(|window| window == b"\r\n\r\n")
            .unwrap();
        let header = String::from_utf8(response[..split].to_vec()).unwrap();
        let status = header
            .lines()
            .next()
            .unwrap()
            .split_whitespace()
            .nth(1)
            .unwrap()
            .parse()
            .unwrap();
        (status, response[split + 4..].to_vec(), header)
    }

    fn post(address: SocketAddr, body: &[u8]) -> (u16, Vec<u8>, String) {
        let request = format!(
            "POST {SIGNED_KERNEL_HTTP_PATH} HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/octet-stream\r\nContent-Length: {}\r\n\r\n",
            body.len()
        );
        let mut bytes = request.into_bytes();
        bytes.extend_from_slice(body);
        raw_request(address, &bytes)
    }

    fn exchange(address: SocketAddr, request: &SignedMessageRequest) -> SignedMessageResponse {
        let body = encode_signed_request(request).unwrap();
        let (status, body, header) = post(address, &body);
        assert_eq!(status, 200, "{header}");
        decode_signed_response(&body).unwrap()
    }

    fn open_session(address: SocketAddr) -> (crate::SignedServiceSession, crate::ServiceIdentity) {
        let SignedMessageResponse::Description(description) =
            exchange(address, &SignedMessageRequest::Describe)
        else {
            panic!("expected description")
        };
        let identity = description.identity();
        let initiator = SessionInitiator::begin(identity, &description).unwrap();
        let SignedMessageResponse::SessionAccepted(accepted) = exchange(
            address,
            &SignedMessageRequest::OpenSession(initiator.request().clone()),
        ) else {
            panic!("expected session acceptance")
        };
        (initiator.accept(&accepted).unwrap(), identity)
    }

    fn shutdown(
        address: SocketAddr,
        mut session: crate::SignedServiceSession,
        handle: JoinHandle<Result<(), NativeHttpError>>,
    ) {
        let command = session.command(ServiceOperation::Shutdown).unwrap();
        let SignedMessageResponse::Reply(reply) =
            exchange(address, &SignedMessageRequest::Execute(command.clone()))
        else {
            panic!("expected signed reply")
        };
        assert!(matches!(
            session.accept_reply(&command, reply).unwrap(),
            ServiceResult::Goodbye
        ));
        handle.join().unwrap().unwrap();
    }

    #[test]
    fn native_client_pins_and_drives_the_same_signed_service() {
        let (address, handle) = spawn_server();
        let description = exchange(address, &SignedMessageRequest::Describe);
        let SignedMessageResponse::Description(description) = description else {
            panic!("expected description")
        };
        let mut client =
            NativeHttpKernelClient::connect(address, description.identity().public_key()).unwrap();
        assert_eq!(client.identity(), description.identity());
        let ServiceResult::Opened(connection) = client.execute(ServiceOperation::OpenHol).unwrap()
        else {
            panic!("expected opened HOL connection")
        };
        let ServiceResult::Produced(produced) = client
            .execute(ServiceOperation::ProduceSignedHol(connection))
            .unwrap()
        else {
            panic!("expected signed HOL artifact")
        };
        assert_eq!(produced.statement(), "(lambda x:bool. x) true = true");
        assert!(matches!(
            client
                .execute(ServiceOperation::CloseHol(connection))
                .unwrap(),
            ServiceResult::Closed
        ));
        assert!(matches!(
            client.execute(ServiceOperation::Shutdown).unwrap(),
            ServiceResult::Goodbye
        ));
        assert!(!client.has_pending_command());
        handle.join().unwrap().unwrap();
    }

    #[test]
    fn native_client_rejects_the_http_description_against_the_out_of_band_key() {
        let (address, handle) = spawn_server();
        let Err(error) = NativeHttpKernelClient::connect(address, [0x55; 32]) else {
            panic!("attacker key unexpectedly pinned")
        };
        assert!(!error.outcome_unknown());

        let (session, _) = open_session(address);
        shutdown(address, session, handle);
    }

    #[test]
    fn native_client_retries_only_the_exact_pending_signed_command() {
        let (upstream, server_handle) = spawn_server();
        let SignedMessageResponse::Description(description) =
            exchange(upstream, &SignedMessageRequest::Describe)
        else {
            panic!("expected description")
        };
        let proxy = TcpListener::bind((std::net::Ipv4Addr::LOCALHOST, 0)).unwrap();
        let proxy_address = proxy.local_addr().unwrap();
        let proxy_handle = thread::spawn(move || {
            let mut bodies = Vec::new();
            for count in 1..=6 {
                let (mut client, _) = proxy.accept().unwrap();
                let request = read_http_request(&mut client).unwrap();
                bodies.push(request.body.clone());
                let (status, body, _) = post(upstream, &request.body);
                assert_eq!(status, 200);
                if count != 3 {
                    write_response(&mut client, "200 OK", &body, "https://repl.example").unwrap();
                }
            }
            bodies
        });

        let mut client =
            NativeHttpKernelClient::connect(proxy_address, description.identity().public_key())
                .unwrap();
        let Err(error) = client.execute(ServiceOperation::OpenHol) else {
            panic!("dropped reply unexpectedly succeeded")
        };
        assert!(error.outcome_unknown());
        assert!(client.has_pending_command());
        let ServiceResult::Opened(connection) = client.retry_pending().unwrap() else {
            panic!("expected cached OpenHol reply")
        };
        assert!(!client.has_pending_command());
        assert!(matches!(
            client
                .execute(ServiceOperation::CloseHol(connection))
                .unwrap(),
            ServiceResult::Closed
        ));
        assert!(matches!(
            client.execute(ServiceOperation::Shutdown).unwrap(),
            ServiceResult::Goodbye
        ));
        let bodies = proxy_handle.join().unwrap();
        assert_eq!(bodies[2], bodies[3]);
        server_handle.join().unwrap().unwrap();
    }

    #[test]
    fn serves_strict_cors_and_stops_only_after_signed_shutdown() {
        let (address, handle) = spawn_server();
        let options = format!(
            "OPTIONS {SIGNED_KERNEL_HTTP_PATH} HTTP/1.1\r\nHost: localhost\r\nContent-Length: 0\r\n\r\n"
        );
        let (status, body, header) = raw_request(address, options.as_bytes());
        assert_eq!(status, 204);
        assert!(body.is_empty());
        assert!(header.contains("Access-Control-Allow-Origin: https://repl.example\r\n"));
        assert!(header.contains("Access-Control-Allow-Methods: POST, OPTIONS\r\n"));

        let (session, _) = open_session(address);
        let wrong_path = b"POST /shutdown HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/octet-stream\r\nContent-Length: 0\r\n\r\n";
        assert_eq!(raw_request(address, wrong_path).0, 404);
        shutdown(address, session, handle);
    }

    #[test]
    fn accepts_only_exact_http_origins() {
        assert!(is_exact_http_origin("http://127.0.0.1:8000"));
        assert!(is_exact_http_origin("https://repl.example"));
        assert!(is_exact_http_origin("http://[::1]:8000"));
        for invalid in [
            "",
            "*",
            "null",
            "ftp://repl.example",
            "https://repl.example/",
            "https://repl.example/path",
            "https://repl.example?query",
            "https://repl.example#fragment",
            "https://repl.example\r\nInjected: value",
            "https://repl.example evil",
            "https://user@repl.example",
            "https://repl.example:not-a-port",
            "https://repl.example:65536",
            "http://::1:8000",
        ] {
            assert!(!is_exact_http_origin(invalid), "accepted {invalid:?}");
        }
    }

    #[test]
    fn finite_socket_budget_counts_malformed_and_preflight_requests() {
        let server = NativeHttpKernelServer::bind_with_request_limit(
            (std::net::Ipv4Addr::LOCALHOST, 0),
            "https://repl.example",
            2,
        )
        .unwrap();
        let address = server.local_addr().unwrap();
        let handle = thread::spawn(move || server.serve());

        let malformed = b"POST /wrong HTTP/1.1\r\nHost: localhost\r\nContent-Length: 0\r\n\r\n";
        assert_eq!(raw_request(address, malformed).0, 404);
        let preflight = format!(
            "OPTIONS {SIGNED_KERNEL_HTTP_PATH} HTTP/1.1\r\nHost: localhost\r\nContent-Length: 0\r\n\r\n"
        );
        assert_eq!(raw_request(address, preflight.as_bytes()).0, 204);

        assert!(matches!(
            handle.join().unwrap(),
            Err(NativeHttpError::ResourceLimit)
        ));
    }

    #[test]
    fn rejects_oversized_and_truncated_bodies_before_dispatch() {
        let (address, handle) = spawn_server();
        let oversized = format!(
            "POST {SIGNED_KERNEL_HTTP_PATH} HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/octet-stream\r\nContent-Length: {}\r\n\r\n",
            MAX_SIGNED_MESSAGE_BYTES + 1
        );
        assert_eq!(raw_request(address, oversized.as_bytes()).0, 413);

        let truncated = format!(
            "POST {SIGNED_KERNEL_HTTP_PATH} HTTP/1.1\r\nHost: localhost\r\nContent-Type: application/octet-stream\r\nContent-Length: 10\r\n\r\nx"
        );
        assert_eq!(raw_request(address, truncated.as_bytes()).0, 400);

        let (session, _) = open_session(address);
        shutdown(address, session, handle);
    }

    #[test]
    fn tampered_command_gets_signed_rejection_without_advancing_session() {
        let (address, handle) = spawn_server();
        let (mut session, _) = open_session(address);
        let command = session.command(ServiceOperation::OpenHol).unwrap();
        let mut body =
            encode_signed_request(&SignedMessageRequest::Execute(command.clone())).unwrap();
        *body.last_mut().unwrap() ^= 1;
        let (status, body, _) = post(address, &body);
        assert_eq!(status, 200);
        let SignedMessageResponse::Reply(reply) = decode_signed_response(&body).unwrap() else {
            panic!("expected signed rejection")
        };
        assert!(matches!(
            session.accept_reply(&command, reply).unwrap(),
            ServiceResult::Rejected(_)
        ));

        let command = session.command(ServiceOperation::Shutdown).unwrap();
        let SignedMessageResponse::Reply(reply) =
            exchange(address, &SignedMessageRequest::Execute(command.clone()))
        else {
            panic!("expected signed shutdown reply")
        };
        assert!(matches!(
            session.accept_reply(&command, reply).unwrap(),
            ServiceResult::Goodbye
        ));
        handle.join().unwrap().unwrap();
    }

    #[test]
    fn endpoint_key_mismatch_is_rejected_by_the_client_pin() {
        let (address, handle) = spawn_server();
        let SignedMessageResponse::Description(description) =
            exchange(address, &SignedMessageRequest::Describe)
        else {
            panic!("expected description")
        };
        let attacker = SignedKernelService::new().unwrap();
        assert!(SessionInitiator::begin(attacker.description().identity(), &description).is_err());

        let (session, _) = open_session(address);
        shutdown(address, session, handle);
    }
}
