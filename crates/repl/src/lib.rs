//! Transport-neutral REPL orchestration.
//!
//! A [`Repl`] is not a Nucleus connection protocol. It maintains an ordinary,
//! inspectable `SQLite` directory in a raw Neutron connection and associates its
//! rows with runtime connection handles owned by the current process.

use std::collections::{HashMap, HashSet};
use std::error::Error as StdError;
use std::fmt;
use std::sync::Arc;
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
use std::{net::SocketAddr, time::Duration};

use covalence_kernel_service::{
    ImageBytes, KernelIdentity, KernelService, ServiceError, SqlConnectionId, SqlDiagnostic,
    SqlOutcome, SqlRunError, SqlStatement, SqlValue, operation_schema,
    rpc::{RpcCodecError, ServiceRequest, ServiceResponse},
    wire::{
        ChannelGrant, ChannelNonce, InvocationChannel, MessageSigningError, PublicKeyIdentity,
        SignedInvocation, SignedResult, StatementSigner, WireError,
    },
};
use covalence_lib_crypto::ed25519::VerifyingKey;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
mod http_transport;
mod metadata_spec;
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
mod native_http;
mod schema_spec;
mod signed_client;

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
pub use http_transport::{
    BootstrapToken, CHANNEL_PATH, HttpTransportError, INVOCATION_PATH, KernelHttpRequest,
    LoopbackHttpEndpoint, read_server_request, write_server_boundary_error, write_server_success,
};
pub use metadata_spec::MetadataSpecError;
use metadata_spec::{
    encode_metadata_values_json, parse_metadata_read_json, parse_metadata_write_json,
};
#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
pub use native_http::{
    NativeKernelServerConfig, NativeKernelServerError, NativeKernelServerHandle,
    random_bootstrap_token, spawn_native_kernel_server,
};
pub use schema_spec::{
    HolMetadataColumnSpec, HolMetadataIndexSpec, HolMetadataSchemaSpec, HolMetadataStorageSpec,
    HolMetadataTableSpec, HolSchemaSpecError, compile_hol_schema_json,
};
pub use signed_client::{
    ChannelCoordinates, PendingInvocation, SignedClientError, SignedKernelClient,
};

pub use covalence_lib_hash::O256;
pub use covalence_neutron::ImageError;
pub use covalence_nucleus::sql::{Outcome, QueryResult, Statement, Value};
pub use covalence_nucleus::{
    AllowAll, AuthenticatedHolImageValidationError, AuthenticatedSnapshotClaim,
    AuthenticatedValidatedHolImage, Connection, ContextError, ContextId, ContextImplication,
    ExportError, ExportId, ExportSort, ExportView, Hol, HolDatabaseRef, HolExportError,
    HolOpenError, HolSchema, HolSchemaDescriptor, HolSchemaDescriptorError, ImportError, ImportId,
    ImportedExport, ImportedReaderError, ImportedTermView, Kernel, Kind, KindError, KindId,
    KindView, MatchedTrustedHolImage, MetadataError, MetadataSchemaError, MetadataTable,
    MetadataTarget, MetadataType, MetadataValue, NamespaceError, NamespaceExport, NamespaceId,
    NamespaceView, ProofError, ProofSession, SignedSnapshotAttestation, SignedSnapshotEnvelope,
    SnapshotAuthenticationError, SnapshotTrustError, Sql, TermError, TermId, TermView, Theorem,
    TrustedImportError, TrustedImportId, TrustedImportImageError, TypeError, TypeId, TypeView,
    ValidatedHolImage,
};

const SCHEMA: &str = "
PRAGMA foreign_keys = ON;
CREATE TABLE repl_kernel (
    kernel_id INTEGER PRIMARY KEY,
    transport TEXT NOT NULL,
    endpoint TEXT,
    public_key BLOB NOT NULL CHECK (length(public_key) = 32)
) STRICT;
CREATE TABLE repl_connection (
    connection_id INTEGER PRIMARY KEY,
    kernel_id INTEGER NOT NULL REFERENCES repl_kernel,
    protocol TEXT NOT NULL,
    remote_connection_id TEXT
) STRICT;
CREATE TABLE repl_image (
    kernel_id INTEGER NOT NULL REFERENCES repl_kernel,
    image_hash BLOB NOT NULL CHECK (length(image_hash) = 32),
    byte_length INTEGER NOT NULL CHECK (byte_length >= 0),
    PRIMARY KEY (kernel_id, image_hash)
) STRICT, WITHOUT ROWID;
CREATE TABLE repl_hol_image (
    kernel_id INTEGER NOT NULL,
    schema_hash BLOB NOT NULL CHECK (length(schema_hash) = 32),
    image_hash BLOB NOT NULL CHECK (length(image_hash) = 32),
    descriptor BLOB NOT NULL,
    PRIMARY KEY (kernel_id, schema_hash, image_hash),
    FOREIGN KEY (kernel_id, image_hash) REFERENCES repl_image(kernel_id, image_hash)
) STRICT, WITHOUT ROWID;
CREATE TABLE repl_state (
    singleton INTEGER PRIMARY KEY CHECK (singleton = 0),
    active_connection_id INTEGER REFERENCES repl_connection
) STRICT;
INSERT INTO repl_state(singleton) VALUES (0);
";

#[derive(Clone, Copy)]
struct ImageCacheLimits {
    image_bytes: usize,
    images: usize,
    total_bytes: usize,
}

const IMAGE_CACHE_LIMITS: ImageCacheLimits = ImageCacheLimits {
    image_bytes: 64 << 20,
    images: 16,
    total_bytes: 256 << 20,
};

/// Process-local identifier for a managed connection.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConnectionId(i64);

impl ConnectionId {
    /// Creates an ID from the browser ABI's unsigned representation.
    #[must_use]
    pub const fn from_u32(id: u32) -> Self {
        Self(id as i64)
    }

    /// Returns the integer stored in the REPL state database.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

impl fmt::Display for ConnectionId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// Process-local identifier for one kernel known to the REPL controller.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct KernelId(i64);

impl KernelId {
    /// Returns the initial local kernel ID.
    #[must_use]
    pub const fn local() -> Self {
        Self(0)
    }

    /// Creates an ID from the browser ABI's unsigned representation.
    #[must_use]
    pub const fn from_u32(id: u32) -> Self {
        Self(id as i64)
    }

    /// Returns the integer stored in the REPL state database.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

impl fmt::Display for KernelId {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// Inspectable transport and identity metadata for one kernel directory entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct KernelView {
    /// Transport selected by the controller.
    pub transport: String,
    /// Optional transport endpoint.
    pub endpoint: Option<String>,
    /// Exact observed Ed25519 public key.
    pub public_key: [u8; 32],
}

/// A connection directory backed by its own raw `SQLite` database.
pub struct Repl<C> {
    state: covalence_neutron::Connection,
    connections: HashMap<ConnectionId, ManagedConnection<C>>,
    next_kernel_id: i64,
    next_connection_id: i64,
}

struct ManagedConnection<C> {
    kernel: KernelId,
    connection: C,
}

impl<C> Repl<C> {
    /// Opens an empty, in-memory REPL state database.
    ///
    /// # Errors
    ///
    /// Returns an error if the raw Neutron connection or state schema cannot
    /// be opened.
    pub fn new(local_public_key: &[u8]) -> Result<Self, ReplError> {
        let state = covalence_neutron::Connection::open_in_memory()?;
        let transaction = state.sqlite().unchecked_transaction()?;
        transaction.execute_batch(SCHEMA)?;
        transaction.execute(
            "INSERT INTO repl_kernel(kernel_id, transport, public_key) VALUES (0, 'local', ?1)",
            [local_public_key],
        )?;
        transaction.commit()?;
        Ok(Self {
            state,
            connections: HashMap::new(),
            next_kernel_id: 1,
            next_connection_id: 1,
        })
    }

    /// Returns the raw state connection for inspection and debugging.
    #[must_use]
    pub const fn state(&self) -> &covalence_neutron::Connection {
        &self.state
    }

    /// Adds one kernel identity to the inspectable controller directory.
    ///
    /// This records routing metadata only. It does not trust the key or grant any protocol
    /// authority.
    ///
    /// # Errors
    ///
    /// Returns an error if the state database rejects the row.
    pub fn insert_kernel(
        &mut self,
        transport: &str,
        endpoint: Option<&str>,
        public_key: &[u8; 32],
    ) -> Result<KernelId, ReplError> {
        let id = KernelId(self.next_kernel_id);
        let next = self
            .next_kernel_id
            .checked_add(1)
            .ok_or(ReplError::IdentifierExhausted("kernel"))?;
        self.state.sqlite().execute(
            "INSERT INTO repl_kernel(kernel_id, transport, endpoint, public_key)
             VALUES (?1, ?2, ?3, ?4)",
            sqlite::params![id.0, transport, endpoint, public_key.as_slice()],
        )?;
        self.next_kernel_id = next;
        Ok(id)
    }

    /// Reads one kernel directory entry.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown kernel, malformed stored key, or state database failure.
    pub fn kernel(&self, id: KernelId) -> Result<KernelView, ReplError> {
        let row = self
            .state
            .sqlite()
            .query_row(
                "SELECT transport, endpoint, public_key FROM repl_kernel WHERE kernel_id = ?1",
                [id.0],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, Option<String>>(1)?,
                        row.get::<_, Vec<u8>>(2)?,
                    ))
                },
            )
            .optional()?
            .ok_or(ReplError::UnknownKernel(id))?;
        let public_key = row.2.try_into().map_err(|_| ReplError::CorruptKernel(id))?;
        Ok(KernelView {
            transport: row.0,
            endpoint: row.1,
            public_key,
        })
    }

    /// Adds a runtime handle and records its protocol in the state database.
    ///
    /// # Errors
    ///
    /// Returns an error if the directory cannot be updated.
    pub fn insert(&mut self, protocol: &str, connection: C) -> Result<ConnectionId, ReplError> {
        self.insert_on(KernelId::local(), protocol, None, connection)
    }

    /// Adds one runtime handle owned by an explicit kernel directory entry.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown kernel or failed directory update.
    pub fn insert_on(
        &mut self,
        kernel: KernelId,
        protocol: &str,
        remote_connection_id: Option<&str>,
        connection: C,
    ) -> Result<ConnectionId, ReplError> {
        self.kernel(kernel)?;
        let id = ConnectionId(self.next_connection_id);
        if self.connections.contains_key(&id) {
            return Err(ReplError::RuntimeIdentifierCollision("connection", id.0));
        }
        let next = self
            .next_connection_id
            .checked_add(1)
            .ok_or(ReplError::IdentifierExhausted("connection"))?;
        let transaction = self.state.sqlite().unchecked_transaction()?;
        transaction.execute(
            "INSERT INTO repl_connection(connection_id, kernel_id, protocol, remote_connection_id)
             VALUES (?1, ?2, ?3, ?4)",
            sqlite::params![id.0, kernel.0, protocol, remote_connection_id],
        )?;
        transaction.execute(
            "UPDATE repl_state
             SET active_connection_id = COALESCE(active_connection_id, ?1)
             WHERE singleton = 0",
            [id.0],
        )?;
        transaction.commit()?;
        self.next_connection_id = next;
        self.connections
            .insert(id, ManagedConnection { kernel, connection });
        Ok(id)
    }

    /// Returns the kernel which owns one managed connection.
    ///
    /// # Errors
    ///
    /// The runtime association is authoritative; the raw `SQLite` directory is only an inspectable
    /// mirror and cannot redirect a live handle to another kernel.
    ///
    /// Returns an error for an unknown runtime connection.
    pub fn connection_kernel(&self, id: ConnectionId) -> Result<KernelId, ReplError> {
        self.connections
            .get(&id)
            .map(|managed| managed.kernel)
            .ok_or(ReplError::UnknownConnection(id))
    }

    /// Returns the active connection ID, if any.
    ///
    /// # Errors
    ///
    /// Returns an error if the state database cannot be read.
    pub fn active(&self) -> Result<Option<ConnectionId>, ReplError> {
        self.state
            .sqlite()
            .query_row(
                "SELECT active_connection_id FROM repl_state WHERE singleton = 0",
                (),
                |row| row.get::<_, Option<i64>>(0),
            )
            .map(|id| id.map(ConnectionId))
            .map_err(ReplError::from)
    }

    /// Selects an existing connection.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or failed state update.
    pub fn select(&mut self, id: ConnectionId) -> Result<(), ReplError> {
        self.require(id)?;
        self.state.sqlite().execute(
            "UPDATE repl_state SET active_connection_id = ?1 WHERE singleton = 0",
            [id.0],
        )?;
        Ok(())
    }

    /// Returns a mutable runtime handle.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown or closed connection.
    pub fn get_mut(&mut self, id: ConnectionId) -> Result<&mut C, ReplError> {
        self.connections
            .get_mut(&id)
            .map(|managed| &mut managed.connection)
            .ok_or(ReplError::UnknownConnection(id))
    }

    /// Returns the active mutable runtime handle.
    ///
    /// # Errors
    ///
    /// Returns an error if no connection is selected or state inspection fails.
    pub fn active_mut(&mut self) -> Result<&mut C, ReplError> {
        let id = self.active()?.ok_or(ReplError::NoActiveConnection)?;
        self.get_mut(id)
    }

    /// Closes and returns a runtime handle.
    ///
    /// If it was active, the lowest remaining ID becomes active.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or failed state update.
    pub fn remove(&mut self, id: ConnectionId) -> Result<C, ReplError> {
        self.require(id)?;
        let transaction = self.state.sqlite().unchecked_transaction()?;
        transaction.execute(
            "UPDATE repl_state
             SET active_connection_id = (
                 SELECT min(connection_id) FROM repl_connection WHERE connection_id <> ?1
             )
             WHERE singleton = 0 AND active_connection_id = ?1",
            [id.0],
        )?;
        transaction.execute(
            "DELETE FROM repl_connection WHERE connection_id = ?1",
            [id.0],
        )?;
        transaction.commit()?;
        self.connections
            .remove(&id)
            .map(|managed| managed.connection)
            .ok_or(ReplError::UnknownConnection(id))
    }

    fn require(&self, id: ConnectionId) -> Result<(), ReplError> {
        if self.connections.contains_key(&id) {
            Ok(())
        } else {
            Err(ReplError::UnknownConnection(id))
        }
    }
}

/// One process-local connection managed by the shared terminal/browser core.
pub enum LocalConnection {
    /// Route to an unrestricted raw SQL session owned by the connection's kernel service.
    Sql(SqlConnectionId),
    /// The current minimal HOL-omega protocol under an explicit demo policy.
    Hol(Connection<Hol<AllowAll>>),
}

impl LocalConnection {
    const fn protocol(&self) -> &'static str {
        match self {
            Self::Sql(_) => "nucleus/sql",
            Self::Hol(_) => "nucleus/hol-common-v2",
        }
    }
}

/// A local kernel and heterogeneous connection directory shared by all UIs.
pub struct LocalRepl {
    kernels: HashMap<KernelId, LocalKernelService>,
    remote_kernels: HashMap<KernelId, RemoteKernelRoute>,
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    remote_http: HashMap<KernelId, LoopbackHttpEndpoint>,
    signed_client: SignedKernelClient,
    directory: Repl<LocalConnection>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RemoteKernelRoute {
    transport: String,
    endpoint: Option<String>,
    public_key: PublicKeyIdentity,
}

/// One linear signed request whose exact bytes may cross an asynchronous transport boundary.
///
/// The controller signing key and replay state remain inside [`LocalRepl`]. Transport adapters
/// must consume this value through result acceptance or abandonment and must never retry its bytes
/// after an ambiguous failure.
pub struct PendingKernelRequest {
    pending: PendingInvocation,
    coordinates: ChannelCoordinates,
}

impl PendingKernelRequest {
    /// Kernel route which must receive this request.
    #[must_use]
    pub const fn kernel(&self) -> KernelId {
        self.pending.kernel()
    }

    /// Exact canonical signed bytes to carry without interpretation.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        self.pending.encode()
    }
}

/// One high-level SQL/image operation whose signed bytes may cross an asynchronous transport.
///
/// This is deliberately narrower than [`ServiceRequest`]: callers name REPL connections and
/// kernels, while Rust resolves authoritative service handles and retains every local commit or
/// compensation step.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReplOperation {
    /// Open and select one raw in-memory SQL connection on a kernel.
    OpenSql { kernel: KernelId },
    /// Close one managed raw SQL connection.
    CloseSql { connection: ConnectionId },
    /// Execute one complete SQL statement.
    RunSql {
        connection: ConnectionId,
        sql: String,
    },
    /// Admit exact complete database bytes under an expected operational address.
    PutImage {
        kernel: KernelId,
        expected: O256,
        bytes: Vec<u8>,
    },
    /// Test operational residency on one kernel.
    HasImage { kernel: KernelId, image: O256 },
    /// Attach one resident immutable image to a raw SQL connection.
    AttachImage {
        connection: ConnectionId,
        image: O256,
        schema: String,
    },
    /// Serialize the writable `main` database of a raw SQL connection.
    SerializeMain { connection: ConnectionId },
}

/// Typed completion of one [`ReplOperation`].
#[derive(Debug)]
pub enum ReplOperationOutput {
    /// Newly opened and selected REPL connection.
    Opened(ConnectionId),
    /// A connection was closed.
    Closed,
    /// Result of executing one SQL statement.
    Sql(Outcome),
    /// Exact image address admitted to the kernel and mirrored in REPL state.
    Image(O256),
    /// Whether the exact image is resident.
    ImageResident(bool),
    /// An immutable image was attached.
    Attached,
    /// Exact serialized `main` database bytes.
    Serialized(Vec<u8>),
}

/// Next Rust-owned step after accepting a transported operation result.
pub enum ReplOperationProgress {
    /// The operation reached its final typed result.
    Complete(Result<ReplOperationOutput, LocalReplError>),
    /// The result was not an acceptable response to this exact signed operation. The route and
    /// every SQL handle associated with it have been invalidated.
    Invalidated(LocalReplError),
    /// A local commit failed after the remote operation succeeded, so these exact signed bytes
    /// must be transported once to compensate before the original error is returned.
    Dispatch(Box<PendingReplOperation>),
}

/// One linear high-level operation with Rust-owned finalization state.
///
/// Transport adapters can inspect only its destination and canonical signed bytes. They must
/// consume it with [`LocalRepl::accept_operation_result`] or
/// [`LocalRepl::abandon_operation`], and must dispatch any follow-up returned by the former.
pub struct PendingReplOperation {
    request: PendingKernelRequest,
    completion: ReplOperationCompletion,
}

impl PendingReplOperation {
    /// Kernel route which must receive this operation step.
    #[must_use]
    pub const fn kernel(&self) -> KernelId {
        self.request.kernel()
    }

    /// Exact canonical signed bytes to transport without interpretation or retry.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        self.request.encode()
    }
}

enum ReplOperationCompletion {
    OpenSql {
        kernel: KernelId,
    },
    CloseSql {
        connection: ConnectionId,
    },
    RunSql,
    PutImage {
        kernel: KernelId,
        expected: O256,
        byte_length: usize,
    },
    HasImage,
    AttachImage,
    SerializeMain,
    CompensateOpen {
        original: Box<LocalReplError>,
    },
}

/// One in-process kernel endpoint with service-local SQL handles and immutable image residency.
///
/// Its maps are authoritative runtime state. Rows in a [`LocalRepl`]'s raw state database are
/// inspectable mirrors and never grant a handle, image, or identity authority.
pub struct LocalKernelService {
    kernel: Kernel,
    sql_connections: HashMap<SqlConnectionId, Connection<Sql>>,
    next_sql_connection_id: u64,
    images: HashMap<O256, covalence_neutron::ImmutableImage>,
    hol_images: HashMap<HolDatabaseRef, Vec<u8>>,
    resident_image_bytes: usize,
    sql_channels: HashMap<(PublicKeyIdentity, ChannelNonce), SqlServerChannel>,
}

struct SqlServerChannel {
    replay: InvocationChannel,
    caller: VerifyingKey,
    connections: HashSet<SqlConnectionId>,
}

struct NucleusStatementSigner<'a>(&'a covalence_nucleus::Ed25519Signer);

impl StatementSigner for NucleusStatementSigner<'_> {
    type Error = NucleusStatementSignError;

    fn public_key(&self) -> PublicKeyIdentity {
        *self.0.verifying_key().as_bytes()
    }

    fn sign_statement(&self, statement: O256) -> Result<[u8; 64], Self::Error> {
        use covalence_nucleus::Signer as _;

        self.0
            .sign(self.0.key_id(), statement)
            .map_err(NucleusStatementSignError::Sign)?
            .as_ref()
            .try_into()
            .map_err(|_| NucleusStatementSignError::InvalidLength)
    }
}

impl LocalKernelService {
    fn new(kernel: Kernel) -> Self {
        Self {
            kernel,
            sql_connections: HashMap::new(),
            next_sql_connection_id: 1,
            images: HashMap::new(),
            hol_images: HashMap::new(),
            resident_image_bytes: 0,
            sql_channels: HashMap::new(),
        }
    }

    /// Issues and records a recipient-signed SQL invocation channel for `caller`.
    ///
    /// # Errors
    ///
    /// Rejects a malformed Ed25519 caller identity or a signing failure.
    pub fn issue_sql_channel(
        &mut self,
        caller: PublicKeyIdentity,
    ) -> Result<ChannelGrant, LocalSignedExchangeError> {
        let caller_key = VerifyingKey::from_bytes(&caller)
            .map_err(|_| LocalSignedExchangeError::InvalidCallerKey)?;
        let recipient = *self.kernel.verifying_key().as_bytes();
        let channel = loop {
            let candidate = ChannelNonce::new(covalence_lib_rand::random());
            if !self.sql_channels.contains_key(&(caller, candidate)) {
                break candidate;
            }
        };
        let initial_sequence = 0;
        let grant = ChannelGrant::issue(
            &NucleusStatementSigner(self.kernel.signer()),
            caller,
            channel,
            initial_sequence,
        )
        .map_err(LocalSignedExchangeError::signing)?;
        self.sql_channels.insert(
            (caller, channel),
            SqlServerChannel {
                replay: InvocationChannel::new(caller, recipient, channel, initial_sequence),
                caller: caller_key,
                connections: HashSet::new(),
            },
        );
        Ok(grant)
    }

    /// Revokes one recipient-owned channel and closes all of its remaining SQL handles.
    pub fn revoke_sql_channel(&mut self, caller: PublicKeyIdentity, channel: ChannelNonce) {
        if let Some(channel) = self.sql_channels.remove(&(caller, channel)) {
            for connection in channel.connections {
                let _ = KernelService::close_sql(self, connection);
            }
        }
    }

    /// Authenticates, executes, and signs one canonical SQL service invocation.
    ///
    /// Malformed, unauthenticated, replayed, wrong-schema, and wrong-value-ID invocations fail at
    /// the exchange boundary and produce no signed service result. Once authenticated, portable
    /// service failures such as an unknown channel-owned handle are encoded and signed as results.
    ///
    /// # Errors
    ///
    /// Returns a transport-boundary error without treating it as a service result.
    pub fn exchange_sql(
        &mut self,
        invocation_bytes: &[u8],
    ) -> Result<Vec<u8>, LocalSignedExchangeError> {
        let invocation =
            SignedInvocation::decode(invocation_bytes).map_err(LocalSignedExchangeError::Wire)?;
        let channel_key = (invocation.caller(), invocation.channel());
        let channel = self
            .sql_channels
            .get_mut(&channel_key)
            .ok_or(LocalSignedExchangeError::UnknownChannel)?;
        channel
            .replay
            .verify(&invocation, &channel.caller)
            .map_err(LocalSignedExchangeError::Wire)?;
        let request = ServiceRequest::decode(invocation.payload())
            .map_err(LocalSignedExchangeError::Codec)?;
        if invocation.schema() != operation_schema(request.operation()) {
            return Err(LocalSignedExchangeError::SchemaMismatch);
        }
        if invocation.input_id() != request.value_id() {
            return Err(LocalSignedExchangeError::ValueIdMismatch);
        }

        let response = self.execute_service_request(channel_key, request)?;
        let payload = response.encode();
        let opened = match &response {
            ServiceResponse::Open(Ok(connection)) => Some(*connection),
            _ => None,
        };
        let signed = SignedResult::sign(
            &invocation,
            &NucleusStatementSigner(self.kernel.signer()),
            response.value_id(),
            payload,
        );
        match signed {
            Ok(result) => Ok(result.encode()),
            Err(error) => {
                if let Some(connection) = opened {
                    self.sql_channels
                        .get_mut(&channel_key)
                        .ok_or(LocalSignedExchangeError::UnknownChannel)?
                        .connections
                        .remove(&connection);
                    let _ = KernelService::close_sql(self, connection);
                }
                Err(LocalSignedExchangeError::signing(error))
            }
        }
    }

    fn execute_service_request(
        &mut self,
        channel_key: (PublicKeyIdentity, ChannelNonce),
        request: ServiceRequest,
    ) -> Result<ServiceResponse, LocalSignedExchangeError> {
        Ok(match request {
            ServiceRequest::Identity => ServiceResponse::Identity(KernelService::identity(self)),
            ServiceRequest::HasImage { image } => {
                ServiceResponse::HasImage(KernelService::has_image(self, image))
            }
            ServiceRequest::ListImages => {
                ServiceResponse::ListImages(KernelService::list_images(self))
            }
            ServiceRequest::PutImage { bytes } => {
                ServiceResponse::PutImage(KernelService::put_image(self, bytes))
            }
            ServiceRequest::Open => {
                let result = KernelService::open_sql(self);
                if let Ok(connection) = result {
                    self.sql_channels
                        .get_mut(&channel_key)
                        .ok_or(LocalSignedExchangeError::UnknownChannel)?
                        .connections
                        .insert(connection);
                }
                ServiceResponse::Open(result)
            }
            ServiceRequest::Run {
                connection,
                statement,
            } => {
                let owns = self
                    .sql_channels
                    .get(&channel_key)
                    .ok_or(LocalSignedExchangeError::UnknownChannel)?
                    .connections
                    .contains(&connection);
                let result = if owns {
                    KernelService::run_sql(self, connection, statement)
                } else {
                    Err(SqlRunError::Service(ServiceError::NotFound))
                };
                ServiceResponse::Run(result)
            }
            ServiceRequest::Attach {
                connection,
                image,
                schema,
            } => {
                let owns = self
                    .sql_channels
                    .get(&channel_key)
                    .ok_or(LocalSignedExchangeError::UnknownChannel)?
                    .connections
                    .contains(&connection);
                let result = if owns {
                    KernelService::attach_image(self, connection, image, &schema)
                } else {
                    Err(ServiceError::NotFound)
                };
                ServiceResponse::Attach(result)
            }
            ServiceRequest::Close { connection } => {
                let owns = self
                    .sql_channels
                    .get(&channel_key)
                    .ok_or(LocalSignedExchangeError::UnknownChannel)?
                    .connections
                    .contains(&connection);
                let result = if owns {
                    KernelService::close_sql(self, connection)
                } else {
                    Err(ServiceError::NotFound)
                };
                if result.is_ok() {
                    self.sql_channels
                        .get_mut(&channel_key)
                        .ok_or(LocalSignedExchangeError::UnknownChannel)?
                        .connections
                        .remove(&connection);
                }
                ServiceResponse::Close(result)
            }
            ServiceRequest::Serialize { connection } => {
                let owns = self
                    .sql_channels
                    .get(&channel_key)
                    .ok_or(LocalSignedExchangeError::UnknownChannel)?
                    .connections
                    .contains(&connection);
                let result = if owns {
                    KernelService::serialize_sql_main(self, connection)
                } else {
                    Err(ServiceError::NotFound)
                };
                ServiceResponse::Serialize(result)
            }
        })
    }

    fn sql_mut(
        &mut self,
        connection: SqlConnectionId,
    ) -> Result<&mut Connection<Sql>, ServiceError> {
        self.sql_connections
            .get_mut(&connection)
            .ok_or(ServiceError::NotFound)
    }

    fn image(&self, image: O256) -> Result<covalence_neutron::ImmutableImage, ReplImageError> {
        self.images
            .get(&image)
            .cloned()
            .ok_or(ReplImageError::Missing { image })
    }

    fn put_verified_image(&mut self, expected: O256, bytes: &[u8]) -> Result<bool, ReplImageError> {
        let actual = O256::from_bytes(bytes);
        if actual != expected {
            return Err(ReplImageError::AddressMismatch { expected, actual });
        }
        if let Some(existing) = self.images.get(&expected) {
            return if existing.bytes() == bytes {
                Ok(false)
            } else {
                Err(ReplImageError::HashCollision { image: expected })
            };
        }
        let new_total = check_image_cache_capacity(
            self.images.len(),
            self.resident_image_bytes,
            bytes.len(),
            IMAGE_CACHE_LIMITS,
        )?;
        let mounted = covalence_neutron::ImmutableImage::register(Arc::from(bytes))
            .map_err(ReplImageError::Register)?;
        self.images.insert(expected, mounted);
        self.resident_image_bytes = new_total;
        Ok(true)
    }

    fn record_hol_descriptor(
        &mut self,
        database: HolDatabaseRef,
        descriptor: Vec<u8>,
    ) -> Result<bool, ReplImageError> {
        if let Some(existing) = self.hol_images.get(&database) {
            return if existing == &descriptor {
                Ok(false)
            } else {
                Err(ReplImageError::ConflictingHolDescriptor { database })
            };
        }
        self.hol_images.insert(database, descriptor);
        Ok(true)
    }

    /// Serializes one service-local writable SQL connection's `main` database.
    ///
    /// # Errors
    ///
    /// Returns a service error for an unknown handle or oversized result, or the original Neutron
    /// image error when `SQLite` serialization fails.
    pub fn serialize_sql(
        &mut self,
        connection: SqlConnectionId,
    ) -> Result<ImageBytes, LocalKernelServiceError> {
        let bytes = self
            .sql_mut(connection)?
            .serialize_main()
            .map_err(LocalKernelServiceError::Image)?;
        ImageBytes::new(bytes.to_vec()).map_err(LocalKernelServiceError::Service)
    }
}

impl KernelService for LocalKernelService {
    fn identity(&self) -> Result<KernelIdentity, ServiceError> {
        Ok(KernelIdentity::complete(
            *self.kernel.verifying_key().as_bytes(),
        ))
    }

    fn has_image(&self, image: O256) -> Result<bool, ServiceError> {
        Ok(self.images.contains_key(&image))
    }

    fn list_images(&self) -> Result<Vec<O256>, ServiceError> {
        let mut images = self.images.keys().copied().collect::<Vec<_>>();
        images.sort_unstable();
        images.truncate(covalence_kernel_service::MAX_LISTED_IMAGES);
        Ok(images)
    }

    fn put_image(&mut self, bytes: ImageBytes) -> Result<O256, ServiceError> {
        let image = O256::from_bytes(bytes.as_slice());
        self.put_verified_image(image, bytes.as_slice())
            .map(|_| image)
            .map_err(|error| service_image_error(&error))
    }

    fn open_sql(&mut self) -> Result<SqlConnectionId, ServiceError> {
        let id = SqlConnectionId::from_u64(self.next_sql_connection_id);
        let next = self
            .next_sql_connection_id
            .checked_add(1)
            .ok_or(ServiceError::ResourceLimit)?;
        let connection = self.kernel.open_sql().map_err(|_| ServiceError::Internal)?;
        if self.sql_connections.insert(id, connection).is_some() {
            return Err(ServiceError::Internal);
        }
        self.next_sql_connection_id = next;
        Ok(id)
    }

    fn run_sql(
        &mut self,
        connection: SqlConnectionId,
        statement: SqlStatement,
    ) -> Result<SqlOutcome, SqlRunError> {
        let outcome = self
            .sql_mut(connection)
            .map_err(SqlRunError::Service)?
            .run(statement.as_str(), &[])
            .map_err(|error| sql_run_error(&error))?;
        match outcome {
            Outcome::Changed(count) => Ok(SqlOutcome::changed(
                u64::try_from(count).map_err(|_| ServiceError::ResourceLimit)?,
            )),
            Outcome::Rows(QueryResult { columns, rows }) => Ok(SqlOutcome::rows(
                columns,
                rows.into_iter()
                    .map(|row| row.into_iter().map(service_sql_value).collect())
                    .collect(),
            )?),
        }
    }

    fn attach_image(
        &mut self,
        connection: SqlConnectionId,
        image: O256,
        schema: &str,
    ) -> Result<(), ServiceError> {
        let image = self
            .images
            .get(&image)
            .cloned()
            .ok_or(ServiceError::NotFound)?;
        self.sql_mut(connection)?
            .attach_immutable(&image, schema)
            .map_err(|_| ServiceError::InvalidRequest)
    }

    fn close_sql(&mut self, connection: SqlConnectionId) -> Result<(), ServiceError> {
        self.sql_connections
            .remove(&connection)
            .map(drop)
            .ok_or(ServiceError::NotFound)
    }

    fn serialize_sql_main(
        &mut self,
        connection: SqlConnectionId,
    ) -> Result<ImageBytes, ServiceError> {
        self.serialize_sql(connection).map_err(|error| match error {
            LocalKernelServiceError::Service(error) => error,
            LocalKernelServiceError::Image(_) => ServiceError::Internal,
        })
    }
}

fn sql_run_error(error: &sqlite::Error) -> SqlRunError {
    let extended_code = error.sqlite_error().map_or(0, |code| code.extended_code);
    SqlRunError::Sqlite(SqlDiagnostic::new(
        extended_code & 0xff,
        extended_code,
        error.to_string(),
    ))
}

fn service_sql_value(value: Value) -> SqlValue {
    match value {
        Value::Null => SqlValue::Null,
        Value::Integer(value) => SqlValue::Integer(value),
        Value::Real(value) => SqlValue::Real(value),
        Value::Text(value) => SqlValue::Text(value),
        Value::Blob(value) => SqlValue::Blob(value),
    }
}

fn service_outcome(outcome: SqlOutcome) -> Result<Outcome, ServiceError> {
    Ok(match outcome.into_kind() {
        covalence_kernel_service::SqlOutcomeKind::Changed(count) => {
            Outcome::Changed(usize::try_from(count).map_err(|_| ServiceError::ResourceLimit)?)
        }
        covalence_kernel_service::SqlOutcomeKind::Rows { columns, rows } => {
            Outcome::Rows(QueryResult {
                columns,
                rows: rows
                    .into_iter()
                    .map(|row| {
                        row.into_iter()
                            .map(|value| match value {
                                SqlValue::Null => Value::Null,
                                SqlValue::Integer(value) => Value::Integer(value),
                                SqlValue::Real(value) => Value::Real(value),
                                SqlValue::Text(value) => Value::Text(value),
                                SqlValue::Blob(value) => Value::Blob(value),
                            })
                            .collect()
                    })
                    .collect(),
            })
        }
    })
}

fn service_image_error(error: &ReplImageError) -> ServiceError {
    match error {
        ReplImageError::ImageTooLarge { .. }
        | ReplImageError::ImageCountLimit { .. }
        | ReplImageError::TotalBytesLimit { .. } => ServiceError::ResourceLimit,
        ReplImageError::AddressMismatch { .. } | ReplImageError::HashCollision { .. } => {
            ServiceError::InvalidRequest
        }
        _ => ServiceError::Internal,
    }
}

/// Failure from a local service extension which is not part of the portable typed contract.
#[derive(Debug)]
pub enum LocalKernelServiceError {
    /// Portable service failure.
    Service(ServiceError),
    /// `SQLite` image serialization failed.
    Image(ImageError),
}

/// Failure of the Nucleus-backed statement-signing adapter.
#[derive(Debug)]
pub enum NucleusStatementSignError {
    /// Nucleus refused or failed the signing operation.
    Sign(covalence_nucleus::SignError),
    /// A signing backend returned bytes which were not an Ed25519 signature.
    InvalidLength,
}

impl fmt::Display for NucleusStatementSignError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sign(error) => error.fmt(formatter),
            Self::InvalidLength => formatter.write_str("signer returned a non-Ed25519 signature"),
        }
    }
}

impl StdError for NucleusStatementSignError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Sign(error) => Some(error),
            Self::InvalidLength => None,
        }
    }
}

/// Rejected signed in-process SQL exchange.
#[derive(Debug)]
pub enum LocalSignedExchangeError {
    /// Signed frame syntax, authentication, context, or replay failure.
    Wire(WireError),
    /// Canonical typed payload failure.
    Codec(RpcCodecError),
    /// Caller bytes did not encode an Ed25519 verification key.
    InvalidCallerKey,
    /// No recipient-issued channel matched the authenticated frame context.
    UnknownChannel,
    /// The signed semantic schema did not match the payload operation.
    SchemaMismatch,
    /// The signed value ID did not name the exact canonical payload.
    ValueIdMismatch,
    /// A verified result carried the wrong operation variant or output value identity.
    ResponseMismatch,
    /// The kernel signing capability failed.
    Signing(NucleusStatementSignError),
}

impl LocalSignedExchangeError {
    fn signing(error: MessageSigningError<NucleusStatementSignError>) -> Self {
        match error {
            MessageSigningError::Wire(error) => Self::Wire(error),
            MessageSigningError::Signer(error) => Self::Signing(error),
        }
    }
}

impl fmt::Display for LocalSignedExchangeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(error) => error.fmt(formatter),
            Self::Codec(error) => write!(formatter, "invalid canonical SQL payload: {error:?}"),
            Self::InvalidCallerKey => formatter.write_str("invalid caller Ed25519 public key"),
            Self::UnknownChannel => formatter.write_str("unknown signed SQL channel"),
            Self::SchemaMismatch => formatter.write_str("signed SQL operation schema mismatch"),
            Self::ValueIdMismatch => formatter.write_str("signed SQL value identity mismatch"),
            Self::ResponseMismatch => formatter.write_str("signed SQL response mismatch"),
            Self::Signing(error) => error.fmt(formatter),
        }
    }
}

impl StdError for LocalSignedExchangeError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Wire(error) => Some(error),
            Self::Signing(error) => Some(error),
            Self::Codec(_)
            | Self::InvalidCallerKey
            | Self::UnknownChannel
            | Self::SchemaMismatch
            | Self::ValueIdMismatch
            | Self::ResponseMismatch => None,
        }
    }
}

impl fmt::Display for LocalKernelServiceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Service(error) => error.fmt(formatter),
            Self::Image(error) => error.fmt(formatter),
        }
    }
}

impl StdError for LocalKernelServiceError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Service(error) => Some(error),
            Self::Image(error) => Some(error),
        }
    }
}

impl From<ServiceError> for LocalKernelServiceError {
    fn from(error: ServiceError) -> Self {
        Self::Service(error)
    }
}

/// Transport-neutral owned signed HOL snapshot returned by the shared REPL.
pub struct LocalSignedHolSnapshot {
    bytes: Vec<u8>,
    descriptor: Vec<u8>,
    schema: covalence_lib_hash::O256,
    image: covalence_lib_hash::O256,
    signer: covalence_lib_hash::O256,
    public_key: [u8; 32],
    signature: Vec<u8>,
}

/// Result of explicitly trusting and persisting one hash-first HOL import attestation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LocalTrustedHolImport {
    import: ImportId,
    trusted_import: TrustedImportId,
    database: HolDatabaseRef,
    signer: O256,
}

/// Owned structural result copied out of one scoped immutable imported-image reader.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LocalImportedHolExport {
    /// Destination connection whose trust and namespace rows authorized the read.
    pub connection: ConnectionId,
    /// Exact persistent trust assumption used for the bytes.
    pub trusted_import: TrustedImportId,
    /// Exact inert import-directory row named by the namespace alias.
    pub import: ImportId,
    /// Destination-local imported namespace alias.
    pub namespace: NamespaceId,
    /// Requested source namespace export coordinate.
    pub export: ExportId,
    /// Structural source value, carrying only inert source-database IDs.
    pub value: LocalImportedHolValue,
}

/// Structural source value copied out of an imported image.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalImportedHolValue {
    /// Imported kind coordinate.
    Kind(i64),
    /// Imported type coordinate.
    Type(i64),
    /// Imported term coordinate and its checked structural row.
    Term {
        /// Source-database term ID.
        id: i64,
        /// Source-database structural term representation.
        term: LocalImportedHolTerm,
    },
    /// Imported context coordinate.
    Context(i64),
}

/// Owned structural imported term. All IDs remain coordinates in the source image.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalImportedHolTerm {
    /// Boolean literal.
    Bool(bool),
    /// Typed free symbol.
    Free { symbol: u64, ty: i64 },
    /// Typed de Bruijn occurrence.
    Bound { index: u64, ty: i64 },
    /// Typed application.
    Application {
        function: i64,
        argument: i64,
        ty: i64,
    },
    /// Typed lambda.
    Lambda {
        parameter_type: i64,
        body: i64,
        ty: i64,
    },
    /// Same-typed equality.
    Equality { left: i64, right: i64, ty: i64 },
}

fn record_resident_image(
    state: &covalence_neutron::Connection,
    kernel: KernelId,
    image: O256,
    byte_length: usize,
) -> Result<(), LocalReplError> {
    let byte_length = i64::try_from(byte_length).map_err(|_| ReplImageError::ImageTooLarge {
        length: byte_length,
        maximum: IMAGE_CACHE_LIMITS.image_bytes,
    })?;
    state
        .sqlite()
        .execute(
            "INSERT INTO repl_image(kernel_id, image_hash, byte_length) VALUES (?1, ?2, ?3)
             ON CONFLICT(kernel_id, image_hash)
             DO UPDATE SET byte_length = excluded.byte_length",
            sqlite::params![kernel.get(), image.as_ref(), byte_length],
        )
        .map_err(ReplError::from)?;
    Ok(())
}

fn check_image_cache_capacity(
    count: usize,
    total_bytes: usize,
    image_bytes: usize,
    limits: ImageCacheLimits,
) -> Result<usize, ReplImageError> {
    if image_bytes > limits.image_bytes {
        return Err(ReplImageError::ImageTooLarge {
            length: image_bytes,
            maximum: limits.image_bytes,
        });
    }
    if count >= limits.images {
        return Err(ReplImageError::ImageCountLimit {
            maximum: limits.images,
        });
    }
    total_bytes
        .checked_add(image_bytes)
        .filter(|total| *total <= limits.total_bytes)
        .ok_or(ReplImageError::TotalBytesLimit {
            maximum: limits.total_bytes,
        })
}

fn record_resident_hol_descriptor(
    state: &covalence_neutron::Connection,
    kernel: KernelId,
    database: HolDatabaseRef,
    descriptor: &[u8],
) -> Result<(), LocalReplError> {
    state
        .sqlite()
        .execute(
            "INSERT INTO repl_hol_image(kernel_id, schema_hash, image_hash, descriptor)
             VALUES (?1, ?2, ?3, ?4)
             ON CONFLICT(kernel_id, schema_hash, image_hash)
             DO UPDATE SET descriptor = excluded.descriptor",
            sqlite::params![
                kernel.get(),
                database.schema().as_ref(),
                database.image().as_ref(),
                descriptor
            ],
        )
        .map_err(ReplError::from)?;
    Ok(())
}

fn copy_imported_term(term: ImportedTermView<'_>) -> LocalImportedHolTerm {
    match term {
        ImportedTermView::Bool(value) => LocalImportedHolTerm::Bool(value),
        ImportedTermView::Free { symbol, ty } => LocalImportedHolTerm::Free {
            symbol,
            ty: ty.get(),
        },
        ImportedTermView::Bound { index, ty } => LocalImportedHolTerm::Bound {
            index,
            ty: ty.get(),
        },
        ImportedTermView::Application {
            function,
            argument,
            ty,
        } => LocalImportedHolTerm::Application {
            function: function.get(),
            argument: argument.get(),
            ty: ty.get(),
        },
        ImportedTermView::Lambda {
            parameter_type,
            body,
            ty,
        } => LocalImportedHolTerm::Lambda {
            parameter_type: parameter_type.get(),
            body: body.get(),
            ty: ty.get(),
        },
        ImportedTermView::Equality { left, right, ty } => LocalImportedHolTerm::Equality {
            left: left.get(),
            right: right.get(),
            ty: ty.get(),
        },
    }
}

fn read_matched_hol_export(
    id: ConnectionId,
    trusted_import: TrustedImportId,
    matched: MatchedTrustedHolImage<'_, AllowAll>,
    mounted: &covalence_neutron::ImmutableImage,
    namespace: NamespaceId,
    export: ExportId,
) -> Result<Option<LocalImportedHolExport>, LocalReplError> {
    let import = matched.import();
    let result = matched.with_mounted_reader(
        namespace,
        mounted,
        |mut reader| -> Result<Option<LocalImportedHolExport>, ImportedReaderError> {
            let Some(value) = reader.namespace_export(export.get())? else {
                return Ok(None);
            };
            let value = match value {
                ImportedExport::Kind(source_id) => LocalImportedHolValue::Kind(source_id.get()),
                ImportedExport::Type(source_id) => LocalImportedHolValue::Type(source_id.get()),
                ImportedExport::Context(source_id) => {
                    LocalImportedHolValue::Context(source_id.get())
                }
                ImportedExport::Term(source_id) => LocalImportedHolValue::Term {
                    id: source_id.get(),
                    term: copy_imported_term(reader.term(source_id)?),
                },
            };
            Ok(Some(LocalImportedHolExport {
                connection: id,
                trusted_import,
                import,
                namespace,
                export,
                value,
            }))
        },
    )?;
    Ok(result?)
}

impl LocalTrustedHolImport {
    /// Returns the inert registered import ID.
    #[must_use]
    pub const fn import(&self) -> ImportId {
        self.import
    }

    /// Returns the persistent accepted-assumption ID.
    #[must_use]
    pub const fn trusted_import(&self) -> TrustedImportId {
        self.trusted_import
    }

    /// Returns the exact schema/image coordinates.
    #[must_use]
    pub const fn database(&self) -> HolDatabaseRef {
        self.database
    }

    /// Returns the authenticated signer identity.
    #[must_use]
    pub const fn signer(&self) -> O256 {
        self.signer
    }
}

impl LocalSignedHolSnapshot {
    /// Returns the exact signed `SQLite` image bytes.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the canonical checked metadata schema descriptor.
    #[must_use]
    pub fn descriptor(&self) -> &[u8] {
        &self.descriptor
    }

    /// Returns the interpretation-qualified HOL schema identity.
    #[must_use]
    pub const fn schema(&self) -> covalence_lib_hash::O256 {
        self.schema
    }

    /// Returns the exact image hash.
    #[must_use]
    pub const fn image(&self) -> covalence_lib_hash::O256 {
        self.image
    }

    /// Returns the content-derived signing-key identity.
    #[must_use]
    pub const fn signer(&self) -> covalence_lib_hash::O256 {
        self.signer
    }

    /// Returns the kernel's public verification key.
    #[must_use]
    pub const fn public_key(&self) -> &[u8; 32] {
        &self.public_key
    }

    /// Returns the schema-qualified snapshot signature.
    #[must_use]
    pub fn signature(&self) -> &[u8] {
        &self.signature
    }
}

impl LocalRepl {
    /// Creates a REPL with one fresh ephemeral kernel identity.
    ///
    /// # Errors
    ///
    /// Returns an error if its raw `SQLite` state database cannot open.
    pub fn new() -> Result<Self, LocalReplError> {
        let kernel = Kernel::ephemeral();
        let directory = Repl::new(kernel.verifying_key().as_bytes())?;
        let kernels = HashMap::from([(KernelId::local(), LocalKernelService::new(kernel))]);
        Ok(Self {
            kernels,
            remote_kernels: HashMap::new(),
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            remote_http: HashMap::new(),
            signed_client: SignedKernelClient::ephemeral(),
            directory,
        })
    }

    /// Creates and records another independently keyed in-process kernel.
    ///
    /// # Errors
    ///
    /// Returns an error if the inspectable directory cannot record its public identity.
    pub fn create_local_kernel(&mut self) -> Result<KernelId, LocalReplError> {
        let kernel = Kernel::ephemeral();
        let id = self
            .directory
            .insert_kernel("local", None, kernel.verifying_key().as_bytes())?;
        self.kernels.insert(id, LocalKernelService::new(kernel));
        Ok(id)
    }

    /// Connects a numeric loopback HTTP kernel using an out-of-band recipient-key pin.
    ///
    /// Registration eagerly requests and verifies a recipient-signed channel grant. The kernel is
    /// not added to the inspectable directory unless the endpoint proves possession of the pinned
    /// key. Requests are never retried by this client.
    ///
    /// # Errors
    ///
    /// Returns an error for a non-loopback endpoint, invalid key, transport failure, invalid grant,
    /// or failed directory update.
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    pub fn connect_native_http(
        &mut self,
        address: SocketAddr,
        pinned_recipient: PublicKeyIdentity,
        bootstrap_token: Option<BootstrapToken>,
    ) -> Result<KernelId, LocalReplError> {
        const CONNECT_TIMEOUT: Duration = Duration::from_secs(5);
        const IO_TIMEOUT: Duration = Duration::from_secs(30);

        let endpoint =
            LoopbackHttpEndpoint::new(address, pinned_recipient, CONNECT_TIMEOUT, IO_TIMEOUT)?;
        let enrollment_endpoint =
            bootstrap_token.map_or(endpoint, |token| endpoint.with_bootstrap_token(token));
        let grant = enrollment_endpoint.request_channel(self.signed_client.caller_public_key())?;
        let id = self.accept_remote_kernel(
            "native-http",
            Some(&address.to_string()),
            pinned_recipient,
            &grant,
        )?;
        let replaced = self.remote_http.insert(id, endpoint);
        debug_assert!(replaced.is_none());
        Ok(id)
    }

    /// Returns the ephemeral controller key which a remote kernel must bind into its grant.
    #[must_use]
    pub fn remote_caller_public_key(&self) -> PublicKeyIdentity {
        self.signed_client.caller_public_key()
    }

    /// Verifies and records one transport-neutral remote-kernel channel.
    ///
    /// The inspectable `SQLite` directory row is inserted only after the recipient-signed grant is
    /// authenticated against `pinned_recipient`. The transport and endpoint are descriptive route
    /// metadata and confer no authority.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed or mismatched grant, invalid recipient key, or failed
    /// directory update.
    pub fn accept_remote_kernel(
        &mut self,
        transport: &str,
        endpoint: Option<&str>,
        pinned_recipient: PublicKeyIdentity,
        grant: &[u8],
    ) -> Result<KernelId, LocalReplError> {
        // `insert_kernel` allocates this exact next ID. Installing the verified route first makes
        // a failed directory transaction locally atomic; the remote may retain only an unused,
        // bounded channel grant.
        let candidate = KernelId(self.directory.next_kernel_id);
        self.signed_client
            .accept_grant(candidate, pinned_recipient, grant)?;
        let id = match self
            .directory
            .insert_kernel(transport, endpoint, &pinned_recipient)
        {
            Ok(id) => id,
            Err(error) => {
                let _ = self.signed_client.remove_route(candidate);
                return Err(error.into());
            }
        };
        debug_assert_eq!(id, candidate);
        let replaced = self.remote_kernels.insert(
            id,
            RemoteKernelRoute {
                transport: transport.to_owned(),
                endpoint: endpoint.map(str::to_owned),
                public_key: pinned_recipient,
            },
        );
        debug_assert!(replaced.is_none());
        Ok(id)
    }

    /// Reads one kernel's transport and public identity metadata.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown live local kernel.
    pub fn kernel(&self, id: KernelId) -> Result<KernelView, LocalReplError> {
        if let Some(service) = self.kernels.get(&id) {
            return Ok(KernelView {
                transport: "local".to_owned(),
                endpoint: None,
                public_key: service
                    .identity()
                    .map_err(LocalReplError::Service)?
                    .public_key,
            });
        }
        if let Some(route) = self.remote_kernels.get(&id) {
            return Ok(KernelView {
                transport: route.transport.clone(),
                endpoint: route.endpoint.clone(),
                public_key: route.public_key,
            });
        }
        Err(ReplError::UnknownKernel(id).into())
    }

    /// Lists live local kernels using their authoritative runtime identities.
    #[must_use]
    pub fn kernels(&self) -> Vec<(KernelId, KernelView)> {
        let mut kernels = self
            .kernels
            .iter()
            .filter_map(|(id, service)| {
                let identity = service.identity().ok()?;
                (
                    *id,
                    KernelView {
                        transport: "local".to_owned(),
                        endpoint: None,
                        public_key: identity.public_key,
                    },
                )
                    .into()
            })
            .collect::<Vec<_>>();
        kernels.extend(self.remote_kernels.iter().map(|(id, route)| {
            (
                *id,
                KernelView {
                    transport: route.transport.clone(),
                    endpoint: route.endpoint.clone(),
                    public_key: route.public_key,
                },
            )
        }));
        kernels.sort_unstable_by_key(|(id, _)| *id);
        kernels
    }

    /// Stores one uninterpreted complete database image in the initial kernel's resident cache.
    ///
    /// The returned content address is an operational lookup key only. This does not validate a
    /// `SQLite` schema, authenticate a signer, or grant any protocol authority. Matching bytes reuse
    /// one fixed immutable VFS across connections owned by the initial kernel.
    ///
    /// # Errors
    ///
    /// Returns an error for an address collision, an image too large to record, VFS registration,
    /// or REPL state database failure.
    pub fn put_image(&mut self, bytes: &[u8]) -> Result<O256, LocalReplError> {
        self.put_image_on(KernelId::local(), bytes)
    }

    /// Stores one complete immutable image in an explicit kernel's bounded resident cache.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown kernel, a residency bound, VFS registration, or debug-state
    /// mirror failure.
    pub fn put_image_on(&mut self, kernel: KernelId, bytes: &[u8]) -> Result<O256, LocalReplError> {
        let image = O256::from_bytes(bytes);
        self.put_verified_image_on(kernel, image, bytes)?;
        Ok(image)
    }

    /// Authenticates and validates one complete signed HOL snapshot before admitting it as a
    /// reusable resident `(schema, image)`.
    ///
    /// Admission is operational state local to the initial kernel, not logical trust. No HOL
    /// connection is consulted or modified. Later reads must use one destination connection's
    /// independently persisted trusted-import row.
    ///
    /// # Errors
    ///
    /// Returns an error for cache limits, authentication, malformed/noncanonical descriptors,
    /// detached HOL validation, conflicting resident evidence, VFS registration, or state writes.
    #[allow(clippy::too_many_arguments)]
    pub fn put_signed_hol_snapshot_with_descriptor(
        &mut self,
        bytes: &[u8],
        descriptor: &[u8],
        schema: O256,
        image: O256,
        signer: O256,
        public_key: [u8; 32],
        signature: &[u8],
    ) -> Result<O256, LocalReplError> {
        self.put_signed_hol_snapshot_with_descriptor_on(
            KernelId::local(),
            bytes,
            descriptor,
            schema,
            image,
            signer,
            public_key,
            signature,
        )
    }

    /// Authenticates, validates, and admits a signed HOL snapshot to one kernel's residency.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown kernel, invalid authentication or schema evidence,
    /// detached validation failure, a residency bound, or debug-state mirror failure.
    #[allow(clippy::too_many_arguments)]
    pub fn put_signed_hol_snapshot_with_descriptor_on(
        &mut self,
        kernel: KernelId,
        bytes: &[u8],
        descriptor: &[u8],
        schema: O256,
        image: O256,
        signer: O256,
        public_key: [u8; 32],
        signature: &[u8],
    ) -> Result<O256, LocalReplError> {
        self.require_local_hol_kernel(kernel)?;
        let service = self
            .kernels
            .get(&kernel)
            .ok_or(ReplError::UnknownKernel(kernel))?;
        if let Some(existing) = service.images.get(&image) {
            if existing.bytes() != bytes {
                return Err(ReplImageError::HashCollision { image }.into());
            }
        } else {
            check_image_cache_capacity(
                service.images.len(),
                service.resident_image_bytes,
                bytes.len(),
                IMAGE_CACHE_LIMITS,
            )?;
        }
        let authenticated =
            SignedSnapshotEnvelope::new(bytes, schema, image, signer, public_key, signature)
                .authenticate()?;
        let descriptor = HolSchemaDescriptor::decode(descriptor)?;
        let validated =
            AuthenticatedValidatedHolImage::validate_with_descriptor(authenticated, &descriptor)?;
        let database = HolDatabaseRef::new(schema, image);
        let canonical = descriptor.encode().to_vec();
        if let Some(existing) = service.hol_images.get(&database) {
            if existing == &canonical {
                return Ok(image);
            }
            return Err(ReplImageError::ConflictingHolDescriptor { database }.into());
        }
        self.put_verified_image_on(kernel, image, validated.image().bytes())?;
        self.kernels
            .get_mut(&kernel)
            .ok_or(ReplError::UnknownKernel(kernel))?
            .record_hol_descriptor(database, canonical.clone())?;
        record_resident_hol_descriptor(self.directory.state(), kernel, database, &canonical)?;
        Ok(image)
    }

    /// Stores one complete database image after checking its expected operational address.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes do not match `expected`, collide with a resident entry, are
    /// too large to record, or cannot be registered/persisted.
    pub fn put_verified_image(
        &mut self,
        expected: O256,
        bytes: &[u8],
    ) -> Result<(), LocalReplError> {
        self.put_verified_image_on(KernelId::local(), expected, bytes)
    }

    /// Stores one image on a selected kernel after checking its operational address.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown kernel, address mismatch, residency bound, VFS
    /// registration, or debug-state mirror failure.
    pub fn put_verified_image_on(
        &mut self,
        kernel: KernelId,
        expected: O256,
        bytes: &[u8],
    ) -> Result<(), LocalReplError> {
        let image_bytes = ImageBytes::new(bytes.to_vec()).map_err(LocalReplError::Service)?;
        let actual = match self
            .signed_sql_request(kernel, &ServiceRequest::PutImage { bytes: image_bytes })?
        {
            ServiceResponse::PutImage(result) => result.map_err(LocalReplError::Service)?,
            _ => return Err(LocalSignedExchangeError::ResponseMismatch.into()),
        };
        if actual != expected {
            return Err(ReplImageError::AddressMismatch { expected, actual }.into());
        }
        record_resident_image(self.directory.state(), kernel, expected, bytes.len())
    }

    /// Reports whether a complete image is resident on the initial kernel.
    #[must_use]
    pub fn has_image(&mut self, image: O256) -> bool {
        self.has_image_on(KernelId::local(), image).unwrap_or(false)
    }

    /// Reports operational residency on one exact kernel.
    ///
    /// # Errors
    ///
    /// Returns an error when `kernel` does not identify a live local service.
    pub fn has_image_on(&mut self, kernel: KernelId, image: O256) -> Result<bool, LocalReplError> {
        match self.signed_sql_request(kernel, &ServiceRequest::HasImage { image })? {
            ServiceResponse::HasImage(result) => result.map_err(LocalReplError::Service),
            _ => Err(LocalSignedExchangeError::ResponseMismatch.into()),
        }
    }

    /// Returns the number of deduplicated resident immutable images.
    #[must_use]
    pub fn resident_image_count(&self) -> usize {
        self.kernels
            .get(&KernelId::local())
            .map_or(0, |service| service.images.len())
    }

    /// Returns the total exact byte length of deduplicated resident images.
    #[must_use]
    pub fn resident_image_bytes(&self) -> usize {
        self.kernels
            .get(&KernelId::local())
            .map_or(0, |service| service.resident_image_bytes)
    }

    /// Returns the inspectable raw REPL state database.
    #[must_use]
    pub const fn state(&self) -> &covalence_neutron::Connection {
        self.directory.state()
    }

    /// Returns the selected connection ID, if any.
    ///
    /// # Errors
    ///
    /// Returns an error if the state database cannot be read.
    pub fn active(&self) -> Result<Option<ConnectionId>, LocalReplError> {
        self.directory.active().map_err(Into::into)
    }

    /// Selects an existing heterogeneous connection.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or state update failure.
    pub fn select(&mut self, id: ConnectionId) -> Result<(), LocalReplError> {
        self.directory.select(id).map_err(Into::into)
    }

    fn ensure_sql_client_channel(&mut self, recipient: KernelId) -> Result<(), LocalReplError> {
        if self.signed_client.grant(recipient).is_some() {
            return Ok(());
        }
        let caller_key = self.signed_client.caller_public_key();
        if let Some(service) = self.kernels.get_mut(&recipient) {
            let grant = service.issue_sql_channel(caller_key)?;
            let recipient_key = *service.kernel.verifying_key().as_bytes();
            if let Err(error) =
                self.signed_client
                    .accept_grant(recipient, recipient_key, &grant.encode())
            {
                service.revoke_sql_channel(caller_key, grant.channel());
                return Err(error.into());
            }
            return Ok(());
        }
        #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
        if let Some(endpoint) = self.remote_http.get(&recipient).copied() {
            let grant = endpoint.request_channel(caller_key)?;
            self.signed_client
                .accept_grant(recipient, endpoint.pinned_recipient(), &grant)?;
            return Ok(());
        }
        Err(ReplError::UnknownKernel(recipient).into())
    }

    /// Signs one request for an already established kernel route without performing I/O.
    ///
    /// At most one request may be pending per kernel. The returned linear token retains no secret
    /// key material and must be consumed by [`Self::accept_kernel_result`] or
    /// [`Self::abandon_kernel_request`].
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown/unestablished route, an existing pending request, sequence
    /// exhaustion, frame bounds, or signing failure.
    pub fn prepare_kernel_request(
        &mut self,
        kernel: KernelId,
        request: &ServiceRequest,
    ) -> Result<PendingKernelRequest, LocalReplError> {
        let pending = self.signed_client.prepare(kernel, request)?;
        let coordinates = pending.channel_coordinates();
        Ok(PendingKernelRequest {
            pending,
            coordinates,
        })
    }

    /// Verifies one exact result and advances its signed route without performing I/O.
    ///
    /// Any malformed, unauthenticated, mismatched, or stale result poisons the route and
    /// invalidates all SQL handles associated with it.
    ///
    /// # Errors
    ///
    /// Returns the precise signed-client verification or response-codec failure.
    #[allow(clippy::needless_pass_by_value)]
    pub fn accept_kernel_result(
        &mut self,
        request: PendingKernelRequest,
        result: &[u8],
    ) -> Result<ServiceResponse, LocalReplError> {
        let kernel = request.pending.kernel();
        match self.signed_client.accept_result(request.pending, result) {
            Ok(response) => Ok(response),
            Err(error) => {
                self.revoke_sql_client_channel(kernel, request.coordinates);
                Err(error.into())
            }
        }
    }

    /// Abandons an ambiguously transported request, poisons its route, and invalidates its SQL
    /// handles. The invocation bytes must not be retried.
    #[allow(clippy::needless_pass_by_value)]
    pub fn abandon_kernel_request(&mut self, request: PendingKernelRequest) {
        let kernel = request.pending.kernel();
        let _ = self.signed_client.abandon_pending(request.pending);
        self.revoke_sql_client_channel(kernel, request.coordinates);
    }

    /// Resolves and signs one high-level SQL/image operation without performing transport I/O.
    ///
    /// The returned token retains all state needed to validate the response, commit local REPL
    /// state, and (for an opened remote handle whose local directory insert fails) construct a
    /// signed close compensation. A browser or other asynchronous adapter therefore handles only
    /// opaque bytes and [`ReplOperationProgress`].
    ///
    /// # Errors
    ///
    /// Returns an error before dispatch for an unknown/wrong-protocol connection, invalid bounded
    /// request value, unavailable route, or signed-client state failure.
    pub fn prepare_operation(
        &mut self,
        operation: ReplOperation,
    ) -> Result<PendingReplOperation, LocalReplError> {
        let (kernel, request, completion) = match operation {
            ReplOperation::OpenSql { kernel } => (
                kernel,
                ServiceRequest::Open,
                ReplOperationCompletion::OpenSql { kernel },
            ),
            ReplOperation::CloseSql { connection } => {
                let (kernel, service_connection) = self.sql_operation_target(connection)?;
                (
                    kernel,
                    ServiceRequest::Close {
                        connection: service_connection,
                    },
                    ReplOperationCompletion::CloseSql { connection },
                )
            }
            ReplOperation::RunSql { connection, sql } => {
                let (kernel, service_connection) = self.sql_operation_target(connection)?;
                let statement = SqlStatement::new(sql).map_err(LocalReplError::Service)?;
                (
                    kernel,
                    ServiceRequest::Run {
                        connection: service_connection,
                        statement,
                    },
                    ReplOperationCompletion::RunSql,
                )
            }
            ReplOperation::PutImage {
                kernel,
                expected,
                bytes,
            } => {
                let byte_length = bytes.len();
                let bytes = ImageBytes::new(bytes).map_err(LocalReplError::Service)?;
                (
                    kernel,
                    ServiceRequest::PutImage { bytes },
                    ReplOperationCompletion::PutImage {
                        kernel,
                        expected,
                        byte_length,
                    },
                )
            }
            ReplOperation::HasImage { kernel, image } => (
                kernel,
                ServiceRequest::HasImage { image },
                ReplOperationCompletion::HasImage,
            ),
            ReplOperation::AttachImage {
                connection,
                image,
                schema,
            } => {
                let (kernel, service_connection) = self.sql_operation_target(connection)?;
                (
                    kernel,
                    ServiceRequest::Attach {
                        connection: service_connection,
                        image,
                        schema,
                    },
                    ReplOperationCompletion::AttachImage,
                )
            }
            ReplOperation::SerializeMain { connection } => {
                let (kernel, service_connection) = self.sql_operation_target(connection)?;
                (
                    kernel,
                    ServiceRequest::Serialize {
                        connection: service_connection,
                    },
                    ReplOperationCompletion::SerializeMain,
                )
            }
        };
        self.ensure_sql_client_channel(kernel)?;
        let request = self.prepare_kernel_request(kernel, &request)?;
        Ok(PendingReplOperation {
            request,
            completion,
        })
    }

    /// Verifies one transported operation result and performs its exact Rust-owned finalization.
    ///
    /// A [`ReplOperationProgress::Dispatch`] is the signed close compensation for a service handle
    /// which opened successfully but could not be recorded locally. Its bytes must be dispatched
    /// exactly once just like the original operation.
    #[must_use]
    pub fn accept_operation_result(
        &mut self,
        operation: PendingReplOperation,
        result: &[u8],
    ) -> ReplOperationProgress {
        let PendingReplOperation {
            request,
            completion,
        } = operation;
        let kernel = request.pending.kernel();
        let coordinates = request.coordinates;
        let response = self.accept_kernel_result(request, result);
        if let ReplOperationCompletion::CompensateOpen { original } = completion {
            // The synchronous API deliberately ignores every close-compensation result while the
            // signed layer still verifies it and poisons the route on invalid evidence.
            return if response.is_ok() {
                ReplOperationProgress::Complete(Err(*original))
            } else {
                ReplOperationProgress::Invalidated(*original)
            };
        }
        let response = match response {
            Ok(response) => response,
            Err(error) => return ReplOperationProgress::Invalidated(error),
        };
        self.finalize_operation(&completion, response, kernel, coordinates)
    }

    /// Abandons an ambiguously transported operation and invalidates its route and SQL handles.
    ///
    /// The invocation bytes must not be retried. If the abandoned step was only a close
    /// compensation, the returned error is the original local commit failure which the
    /// compensation was trying to clean up; otherwise transport failure remains the caller's
    /// primary error and this returns `None`.
    #[must_use]
    pub fn abandon_operation(&mut self, operation: PendingReplOperation) -> Option<LocalReplError> {
        let PendingReplOperation {
            request,
            completion,
        } = operation;
        self.abandon_kernel_request(request);
        match completion {
            ReplOperationCompletion::CompensateOpen { original } => Some(*original),
            _ => None,
        }
    }

    fn sql_operation_target(
        &mut self,
        id: ConnectionId,
    ) -> Result<(KernelId, SqlConnectionId), LocalReplError> {
        let kernel = self.directory.connection_kernel(id)?;
        let connection = match self.directory.get_mut(id)? {
            LocalConnection::Sql(connection) => *connection,
            other @ LocalConnection::Hol(_) => {
                return Err(LocalReplError::WrongProtocol {
                    id,
                    expected: "nucleus/sql",
                    actual: other.protocol(),
                });
            }
        };
        Ok((kernel, connection))
    }

    fn finalize_operation(
        &mut self,
        completion: &ReplOperationCompletion,
        response: ServiceResponse,
        route_kernel: KernelId,
        coordinates: ChannelCoordinates,
    ) -> ReplOperationProgress {
        let result = match completion {
            ReplOperationCompletion::OpenSql { kernel } => {
                return self.finalize_open_operation(*kernel, coordinates, &response);
            }
            ReplOperationCompletion::CloseSql { connection } => match response {
                ServiceResponse::Close(result) => match result {
                    Ok(()) => self
                        .directory
                        .remove(*connection)
                        .map(|_| ReplOperationOutput::Closed)
                        .map_err(Into::into),
                    Err(error) => Err(LocalReplError::Service(error)),
                },
                _ => return self.response_mismatch_progress(route_kernel, coordinates),
            },
            ReplOperationCompletion::RunSql => match response {
                ServiceResponse::Run(result) => result
                    .and_then(|outcome| service_outcome(outcome).map_err(SqlRunError::Service))
                    .map(ReplOperationOutput::Sql)
                    .map_err(LocalReplError::SqlRun),
                _ => return self.response_mismatch_progress(route_kernel, coordinates),
            },
            ReplOperationCompletion::PutImage {
                kernel,
                expected,
                byte_length,
            } => match response {
                ServiceResponse::PutImage(result) => match result {
                    Ok(actual) if actual == *expected => record_resident_image(
                        self.directory.state(),
                        *kernel,
                        *expected,
                        *byte_length,
                    )
                    .map(|()| ReplOperationOutput::Image(*expected)),
                    Ok(actual) => Err(ReplImageError::AddressMismatch {
                        expected: *expected,
                        actual,
                    }
                    .into()),
                    Err(error) => Err(LocalReplError::Service(error)),
                },
                _ => return self.response_mismatch_progress(route_kernel, coordinates),
            },
            ReplOperationCompletion::HasImage => match response {
                ServiceResponse::HasImage(result) => result
                    .map(ReplOperationOutput::ImageResident)
                    .map_err(LocalReplError::Service),
                _ => return self.response_mismatch_progress(route_kernel, coordinates),
            },
            ReplOperationCompletion::AttachImage => match response {
                ServiceResponse::Attach(result) => result
                    .map(|()| ReplOperationOutput::Attached)
                    .map_err(LocalReplError::Service),
                _ => return self.response_mismatch_progress(route_kernel, coordinates),
            },
            ReplOperationCompletion::SerializeMain => match response {
                ServiceResponse::Serialize(result) => result
                    .map(ImageBytes::into_vec)
                    .map(ReplOperationOutput::Serialized)
                    .map_err(LocalReplError::Service),
                _ => return self.response_mismatch_progress(route_kernel, coordinates),
            },
            ReplOperationCompletion::CompensateOpen { .. } => {
                unreachable!("close compensation handled before response dispatch")
            }
        };
        ReplOperationProgress::Complete(result)
    }

    fn response_mismatch_progress(
        &mut self,
        kernel: KernelId,
        coordinates: ChannelCoordinates,
    ) -> ReplOperationProgress {
        let _ = self.signed_client.remove_route(kernel);
        self.revoke_sql_client_channel(kernel, coordinates);
        ReplOperationProgress::Invalidated(LocalSignedExchangeError::ResponseMismatch.into())
    }

    fn finalize_open_operation(
        &mut self,
        kernel: KernelId,
        coordinates: ChannelCoordinates,
        response: &ServiceResponse,
    ) -> ReplOperationProgress {
        let service_connection = match response {
            ServiceResponse::Open(result) => match result {
                Ok(connection) => *connection,
                Err(error) => {
                    return ReplOperationProgress::Complete(Err(LocalReplError::Service(*error)));
                }
            },
            _ => return self.response_mismatch_progress(kernel, coordinates),
        };
        let inserted = self.directory.insert_on(
            kernel,
            "nucleus/sql",
            Some(&service_connection.get().to_string()),
            LocalConnection::Sql(service_connection),
        );
        let id = match inserted {
            Ok(id) => id,
            Err(error) => {
                let original = Box::new(LocalReplError::Directory(error));
                let close = ServiceRequest::Close {
                    connection: service_connection,
                };
                let Ok(request) = self.prepare_kernel_request(kernel, &close) else {
                    return ReplOperationProgress::Complete(Err(*original));
                };
                return ReplOperationProgress::Dispatch(Box::new(PendingReplOperation {
                    request,
                    completion: ReplOperationCompletion::CompensateOpen { original },
                }));
            }
        };
        let result = if let Err(error) = self.directory.select(id) {
            Err(error.into())
        } else {
            Ok(ReplOperationOutput::Opened(id))
        };
        ReplOperationProgress::Complete(result)
    }

    fn signed_sql_request(
        &mut self,
        recipient: KernelId,
        request: &ServiceRequest,
    ) -> Result<ServiceResponse, LocalReplError> {
        self.ensure_sql_client_channel(recipient)?;
        let pending = self.prepare_kernel_request(recipient, request)?;
        let invocation = pending.encode();
        let exchange = if let Some(service) = self.kernels.get_mut(&recipient) {
            service
                .exchange_sql(&invocation)
                .map_err(LocalReplError::from)
        } else {
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            {
                self.remote_http
                    .get(&recipient)
                    .copied()
                    .ok_or(ReplError::UnknownKernel(recipient).into())
                    .and_then(|endpoint| endpoint.invoke(&invocation).map_err(Into::into))
            }
            #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
            {
                Err(ReplError::UnknownKernel(recipient).into())
            }
        };
        let result_bytes = match exchange {
            Ok(bytes) => bytes,
            Err(error) => {
                self.abandon_kernel_request(pending);
                return Err(error);
            }
        };
        self.accept_kernel_result(pending, &result_bytes)
    }

    fn revoke_sql_client_channel(&mut self, recipient: KernelId, coordinates: ChannelCoordinates) {
        if let Some(service) = self.kernels.get_mut(&recipient) {
            service.revoke_sql_channel(coordinates.caller, coordinates.channel);
        }
        let stale = self
            .directory
            .connections
            .iter()
            .filter_map(|(id, managed)| {
                (managed.kernel == recipient
                    && matches!(managed.connection, LocalConnection::Sql(_)))
                .then_some(*id)
            })
            .collect::<Vec<_>>();
        for id in stale {
            if self.directory.remove(id).is_err() {
                self.directory.connections.remove(&id);
            }
        }
    }

    fn require_local_hol_kernel(&self, kernel: KernelId) -> Result<(), LocalReplError> {
        if self.kernels.contains_key(&kernel) {
            return Ok(());
        }
        if self.remote_kernels.contains_key(&kernel) {
            return Err(LocalReplError::RemoteProtocolUnsupported {
                kernel,
                protocol: "nucleus/hol-common-v2",
            });
        }
        Err(ReplError::UnknownKernel(kernel).into())
    }

    /// Opens and selects a raw in-memory SQL session.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection or directory row cannot be created.
    pub fn open_sql(&mut self) -> Result<ConnectionId, LocalReplError> {
        self.open_sql_on(KernelId::local())
    }

    /// Opens and selects a raw in-memory SQL session on one local kernel.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown/nonlocal kernel or failed connection/directory creation.
    pub fn open_sql_on(&mut self, kernel: KernelId) -> Result<ConnectionId, LocalReplError> {
        let service_connection = match self.signed_sql_request(kernel, &ServiceRequest::Open)? {
            ServiceResponse::Open(result) => result.map_err(LocalReplError::Service)?,
            _ => return Err(LocalSignedExchangeError::ResponseMismatch.into()),
        };
        let inserted = self.directory.insert_on(
            kernel,
            "nucleus/sql",
            Some(&service_connection.get().to_string()),
            LocalConnection::Sql(service_connection),
        );
        let id = match inserted {
            Ok(id) => id,
            Err(error) => {
                let _ = self.signed_sql_request(
                    kernel,
                    &ServiceRequest::Close {
                        connection: service_connection,
                    },
                );
                return Err(error.into());
            }
        };
        self.directory.select(id)?;
        Ok(id)
    }

    /// Opens and selects a minimal HOL-omega connection.
    ///
    /// The demo explicitly chooses [`AllowAll`]; it does not weaken the HOL
    /// connection API or expose its underlying `SQLite` handle.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection/schema or directory row cannot open.
    pub fn open_hol(&mut self) -> Result<ConnectionId, LocalReplError> {
        self.open_hol_on(KernelId::local())
    }

    /// Opens and selects a minimal HOL-omega connection on one local kernel.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown/nonlocal kernel or failed connection/schema/directory
    /// creation.
    pub fn open_hol_on(&mut self, kernel: KernelId) -> Result<ConnectionId, LocalReplError> {
        self.require_local_hol_kernel(kernel)?;
        let connection = self
            .kernels
            .get(&kernel)
            .ok_or(ReplError::UnknownKernel(kernel))?
            .kernel
            .open_hol(AllowAll)
            .map_err(LocalReplError::HolOpen)?;
        let id = self.directory.insert_on(
            kernel,
            "nucleus/hol-common-v2",
            None,
            LocalConnection::Hol(connection),
        )?;
        self.directory.select(id)?;
        Ok(id)
    }

    /// Opens and selects a HOL-omega connection with one checked portable metadata schema.
    ///
    /// # Errors
    ///
    /// Returns an error if the descriptor is malformed/noncanonical or the connection/schema or
    /// directory row cannot open.
    pub fn open_hol_with_descriptor(
        &mut self,
        descriptor: &[u8],
    ) -> Result<ConnectionId, LocalReplError> {
        self.open_hol_with_descriptor_on(KernelId::local(), descriptor)
    }

    /// Opens and selects a HOL-omega connection with one checked metadata schema on a local
    /// kernel.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown/nonlocal kernel, malformed descriptor, or failed
    /// connection/schema/directory creation.
    pub fn open_hol_with_descriptor_on(
        &mut self,
        kernel: KernelId,
        descriptor: &[u8],
    ) -> Result<ConnectionId, LocalReplError> {
        self.require_local_hol_kernel(kernel)?;
        let descriptor = HolSchemaDescriptor::decode(descriptor)?;
        let connection =
            Connection::open_hol_in_memory_with_schema(AllowAll, descriptor.into_schema())
                .map_err(LocalReplError::HolOpen)?;
        let id = self.directory.insert_on(
            kernel,
            "nucleus/hol-common-v2",
            None,
            LocalConnection::Hol(connection),
        )?;
        self.directory.select(id)?;
        Ok(id)
    }

    /// Opens and selects a HOL-omega connection from a strict declarative JSON metadata schema.
    ///
    /// # Errors
    ///
    /// Returns an error if JSON parsing, checked schema construction, descriptor construction, or
    /// connection opening fails.
    pub fn open_hol_with_schema_json(
        &mut self,
        json: &str,
    ) -> Result<ConnectionId, LocalReplError> {
        let descriptor = compile_hol_schema_json(json)?;
        self.open_hol_with_descriptor(descriptor.encode())
    }

    /// Opens and selects a HOL-omega connection from declarative metadata JSON on a local kernel.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid JSON/schema declarations, an unknown kernel, or failed
    /// connection creation.
    pub fn open_hol_with_schema_json_on(
        &mut self,
        kernel: KernelId,
        json: &str,
    ) -> Result<ConnectionId, LocalReplError> {
        let descriptor = compile_hol_schema_json(json)?;
        self.open_hol_with_descriptor_on(kernel, descriptor.encode())
    }

    /// Closes any managed connection.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or state update failure.
    pub fn close(&mut self, id: ConnectionId) -> Result<(), LocalReplError> {
        let kernel = self.directory.connection_kernel(id)?;
        let service_connection = match self.directory.get_mut(id)? {
            LocalConnection::Sql(connection) => Some(*connection),
            LocalConnection::Hol(_) => None,
        };
        if let Some(service_connection) = service_connection {
            match self.signed_sql_request(
                kernel,
                &ServiceRequest::Close {
                    connection: service_connection,
                },
            )? {
                ServiceResponse::Close(result) => {
                    result.map_err(LocalReplError::Service)?;
                }
                _ => return Err(LocalSignedExchangeError::ResponseMismatch.into()),
            }
        }
        self.directory.remove(id)?;
        Ok(())
    }

    /// Executes one statement through the connection's authoritative kernel route.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown connection or kernel, a protocol mismatch, or the original
    /// local `SQLite` diagnostic.
    pub fn run_sql(&mut self, id: ConnectionId, sql: &str) -> Result<Outcome, LocalReplError> {
        let kernel = self.directory.connection_kernel(id)?;
        let service_connection = match self.directory.get_mut(id)? {
            LocalConnection::Sql(connection) => *connection,
            other @ LocalConnection::Hol(_) => {
                return Err(LocalReplError::WrongProtocol {
                    id,
                    expected: "nucleus/sql",
                    actual: other.protocol(),
                });
            }
        };
        let statement = SqlStatement::new(sql.to_owned()).map_err(LocalReplError::Service)?;
        match self.signed_sql_request(
            kernel,
            &ServiceRequest::Run {
                connection: service_connection,
                statement,
            },
        )? {
            ServiceResponse::Run(result) => result
                .and_then(|outcome| service_outcome(outcome).map_err(SqlRunError::Service))
                .map_err(LocalReplError::SqlRun),
            _ => Err(LocalSignedExchangeError::ResponseMismatch.into()),
        }
    }

    /// Admits an image to the exact kernel which owns `id`.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown connection/kernel, residency failure, or debug-state mirror
    /// failure.
    pub fn put_image_for_connection(
        &mut self,
        id: ConnectionId,
        bytes: &[u8],
    ) -> Result<O256, LocalReplError> {
        let kernel = self.directory.connection_kernel(id)?;
        self.put_image_on(kernel, bytes)
    }

    /// Attaches a resident image through the exact kernel-local SQL handle.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown connection/kernel/image, protocol mismatch, invalid schema,
    /// attachment failure, or actual VFS-pointer mismatch.
    pub fn attach_image(
        &mut self,
        id: ConnectionId,
        image: O256,
        schema: &str,
    ) -> Result<(), LocalReplError> {
        let kernel = self.directory.connection_kernel(id)?;
        let service_connection = match self.directory.get_mut(id)? {
            LocalConnection::Sql(connection) => *connection,
            other @ LocalConnection::Hol(_) => {
                return Err(LocalReplError::WrongProtocol {
                    id,
                    expected: "nucleus/sql",
                    actual: other.protocol(),
                });
            }
        };
        match self.signed_sql_request(
            kernel,
            &ServiceRequest::Attach {
                connection: service_connection,
                image,
                schema: schema.to_owned(),
            },
        )? {
            ServiceResponse::Attach(result) => result.map_err(LocalReplError::Service),
            _ => Err(LocalSignedExchangeError::ResponseMismatch.into()),
        }
    }

    /// Serializes the writable `main` database through its kernel-local SQL handle.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown connection/kernel, protocol mismatch, serialization failure,
    /// or a result exceeding the service image bound.
    pub fn serialize_main(&mut self, id: ConnectionId) -> Result<Vec<u8>, LocalReplError> {
        let kernel = self.directory.connection_kernel(id)?;
        let service_connection = match self.directory.get_mut(id)? {
            LocalConnection::Sql(connection) => *connection,
            other @ LocalConnection::Hol(_) => {
                return Err(LocalReplError::WrongProtocol {
                    id,
                    expected: "nucleus/sql",
                    actual: other.protocol(),
                });
            }
        };
        match self.signed_sql_request(
            kernel,
            &ServiceRequest::Serialize {
                connection: service_connection,
            },
        )? {
            ServiceResponse::Serialize(result) => result
                .map(ImageBytes::into_vec)
                .map_err(LocalReplError::Service),
            _ => Err(LocalSignedExchangeError::ResponseMismatch.into()),
        }
    }

    /// Returns a mutable HOL session, rejecting SQL connection IDs.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or protocol mismatch.
    pub fn hol_mut(
        &mut self,
        id: ConnectionId,
    ) -> Result<&mut Connection<Hol<AllowAll>>, LocalReplError> {
        let connection = self.directory.get_mut(id)?;
        match connection {
            LocalConnection::Hol(connection) => Ok(connection),
            other @ LocalConnection::Sql(_) => Err(LocalReplError::WrongProtocol {
                id,
                expected: "nucleus/hol-common-v2",
                actual: other.protocol(),
            }),
        }
    }

    /// Reads user-declared metadata from one existing HOL structural row.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol, denied read, unknown target or column,
    /// or failed database access.
    pub fn hol_metadata(
        &mut self,
        id: ConnectionId,
        target: MetadataTarget,
        columns: &[&str],
    ) -> Result<Vec<MetadataValue>, LocalReplError> {
        self.hol_mut(id)?
            .metadata(target, columns)
            .map_err(Into::into)
    }

    /// Replaces user-declared metadata on one existing HOL structural row.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol, denied write, unknown target or column,
    /// invalid value, repeated column, or failed database access.
    pub fn set_hol_metadata(
        &mut self,
        id: ConnectionId,
        target: MetadataTarget,
        metadata: &[(&str, MetadataValue)],
    ) -> Result<(), LocalReplError> {
        self.hol_mut(id)?
            .set_metadata(target, metadata)
            .map_err(Into::into)
    }

    /// Reads HOL metadata through the strict transport-neutral JSON request format.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed/bounded JSON or any rejected metadata read.
    pub fn hol_metadata_json(
        &mut self,
        id: ConnectionId,
        json: &str,
    ) -> Result<String, LocalReplError> {
        let request = parse_metadata_read_json(json)?;
        let columns = request
            .columns
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let values = self.hol_metadata(id, request.target, &columns)?;
        encode_metadata_values_json(values).map_err(Into::into)
    }

    /// Writes HOL metadata through the strict transport-neutral JSON request format.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed/bounded JSON or any rejected metadata write.
    pub fn set_hol_metadata_json(
        &mut self,
        id: ConnectionId,
        json: &str,
    ) -> Result<(), LocalReplError> {
        let request = parse_metadata_write_json(json)?;
        let metadata = request
            .metadata
            .iter()
            .map(|(column, value)| (column.as_str(), value.clone()))
            .collect::<Vec<_>>();
        self.set_hol_metadata(id, request.target, &metadata)
    }

    /// Defines a local hierarchical namespace in one HOL connection.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol or rejected namespace definition.
    pub fn create_hol_namespace(
        &mut self,
        id: ConnectionId,
        parent: Option<NamespaceId>,
        name: Option<&str>,
    ) -> Result<NamespaceId, LocalReplError> {
        self.hol_mut(id)?
            .create_namespace(parent, name)
            .map_err(Into::into)
    }

    /// Reads a local HOL namespace.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol or rejected namespace read.
    pub fn hol_namespace(
        &mut self,
        id: ConnectionId,
        namespace: NamespaceId,
    ) -> Result<NamespaceView, LocalReplError> {
        self.hol_mut(id)?.namespace(namespace).map_err(Into::into)
    }

    /// Binds one local HOL value to a namespace-wide export ID.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong protocol, invalid local value, or conflicting export.
    pub fn bind_hol_export(
        &mut self,
        id: ConnectionId,
        namespace: NamespaceId,
        export: ExportId,
        value: NamespaceExport,
        name: Option<&str>,
    ) -> Result<(), LocalReplError> {
        self.hol_mut(id)?
            .export_value(namespace, export, value, name)
            .map_err(Into::into)
    }

    /// Reads one local namespace export.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong protocol or rejected export read.
    pub fn hol_export(
        &mut self,
        id: ConnectionId,
        namespace: NamespaceId,
        export: ExportId,
    ) -> Result<Option<ExportView>, LocalReplError> {
        self.hol_mut(id)?
            .resolve_export(namespace, export)
            .map_err(Into::into)
    }

    /// Resolves one namespace-local export name.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong protocol or rejected export read.
    pub fn resolve_hol_export_name(
        &mut self,
        id: ConnectionId,
        namespace: NamespaceId,
        name: &str,
    ) -> Result<Option<(ExportId, ExportView)>, LocalReplError> {
        self.hol_mut(id)?
            .resolve_export_name(namespace, name)
            .map_err(Into::into)
    }

    /// Serializes and signs one complete local HOL connection.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong protocol, denied export, serialization, validation, or
    /// signing failure.
    pub fn export_hol_snapshot(
        &mut self,
        id: ConnectionId,
    ) -> Result<LocalSignedHolSnapshot, LocalReplError> {
        let Self {
            kernels, directory, ..
        } = self;
        let kernel_id = directory.connection_kernel(id)?;
        let kernel = kernels
            .get(&kernel_id)
            .ok_or(ReplError::UnknownKernel(kernel_id))?;
        let managed = directory.get_mut(id)?;
        let connection = match managed {
            LocalConnection::Hol(connection) => connection,
            other @ LocalConnection::Sql(_) => {
                return Err(LocalReplError::WrongProtocol {
                    id,
                    expected: "nucleus/hol-common-v2",
                    actual: other.protocol(),
                });
            }
        };
        let snapshot = kernel.kernel.export_hol(connection)?;
        let attestation = snapshot.attestation();
        Ok(LocalSignedHolSnapshot {
            bytes: snapshot.image().bytes().to_vec(),
            descriptor: snapshot.descriptor().encode().to_vec(),
            schema: attestation.schema(),
            image: attestation.image(),
            signer: attestation.signer(),
            public_key: *attestation.public_key(),
            signature: attestation.signature().to_vec(),
        })
    }

    /// Authenticates one hash-first snapshot claim without changing connection state.
    ///
    /// This checks that the signer identity matches the public key and that the signature covers
    /// the exact schema/image coordinates. It does not trust the signer, accept the claim,
    /// register an import, fetch bytes, or inspect a database.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed or invalid authentication evidence.
    pub fn authenticate_hol_snapshot_claim(
        schema: O256,
        image: O256,
        signer: O256,
        public_key: [u8; 32],
        signature: &[u8],
    ) -> Result<AuthenticatedSnapshotClaim, SnapshotAuthenticationError> {
        SignedSnapshotAttestation::new(schema, image, signer, public_key, signature).authenticate()
    }

    /// Explicitly trusts one authenticated signer for snapshot claims on this connection.
    ///
    /// This connection-local policy change does not accept even the claim supplied here. It does
    /// not register an import, persist an import assumption, fetch bytes, or inspect a database.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol or rejected/conflicting signer trust.
    pub fn trust_hol_snapshot_signer(
        &mut self,
        id: ConnectionId,
        claim: &AuthenticatedSnapshotClaim,
    ) -> Result<(), LocalReplError> {
        self.hol_mut(id)?.trust_snapshot_signer(claim)?;
        Ok(())
    }

    /// Reports whether this connection explicitly trusts the authenticated claim's signer.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol or rejected/conflicting trust read.
    pub fn hol_snapshot_signer_is_trusted(
        &mut self,
        id: ConnectionId,
        claim: &AuthenticatedSnapshotClaim,
    ) -> Result<bool, LocalReplError> {
        Ok(self.hol_mut(id)?.snapshot_signer_is_trusted(claim)?)
    }

    /// Reports whether this exact authenticated schema/image/signer/signature claim was accepted.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol or rejected/conflicting acceptance read.
    pub fn hol_snapshot_claim_is_accepted(
        &mut self,
        id: ConnectionId,
        claim: &AuthenticatedSnapshotClaim,
    ) -> Result<bool, LocalReplError> {
        Ok(self
            .hol_mut(id)?
            .authenticated_snapshot_is_accepted(claim)?)
    }

    /// Accepts and persists one exact hash-first import claim from an already trusted signer.
    ///
    /// The claim is accepted before its schema/image coordinates are registered, so an untrusted
    /// signer fails without creating persistent import state. Nucleus currently exposes exact
    /// acceptance, inert import registration, and persistent assumption recording as separate
    /// transactions. A later failure may therefore leave only the exact connection-local claim
    /// acceptance or an inert import-directory row; this method never broadens signer trust.
    ///
    /// This operation never fetches, parses, validates, or attaches the named database.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol, an untrusted signer, rejected exact-claim
    /// acceptance/import operations, or failed persistence.
    pub fn accept_hol_import(
        &mut self,
        id: ConnectionId,
        claim: &AuthenticatedSnapshotClaim,
    ) -> Result<LocalTrustedHolImport, LocalReplError> {
        let connection = self.hol_mut(id)?;
        connection.accept_authenticated_snapshot(claim)?;
        let database = HolDatabaseRef::new(claim.schema(), claim.image());
        let import = connection.register_import(database)?;
        let trusted_import = connection.accept_trusted_import(import, claim)?;
        Ok(LocalTrustedHolImport {
            import,
            trusted_import,
            database,
            signer: claim.signer(),
        })
    }

    /// Compatibility convenience that authenticates, trusts, accepts, and persists one claim.
    ///
    /// New callers should use [`Self::authenticate_hol_snapshot_claim`],
    /// [`Self::trust_hol_snapshot_signer`], and [`Self::accept_hol_import`] so the signer trust
    /// decision is visible at the call site. This method performs no cryptography itself and never
    /// fetches, parses, validates, or attaches the named database.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong connection protocol, malformed/invalid authentication
    /// evidence, rejected trust/import operations, or failed persistence.
    pub fn trust_hol_import(
        &mut self,
        id: ConnectionId,
        schema: O256,
        image: O256,
        signer: O256,
        public_key: [u8; 32],
        signature: &[u8],
    ) -> Result<LocalTrustedHolImport, LocalReplError> {
        let claim =
            Self::authenticate_hol_snapshot_claim(schema, image, signer, public_key, signature)?;
        self.trust_hol_snapshot_signer(id, &claim)?;
        self.accept_hol_import(id, &claim)
    }

    /// Reads one persistent trusted-import assumption through the shared connection directory.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong protocol or rejected/unknown trusted-import read.
    pub fn hol_trusted_import(
        &mut self,
        id: ConnectionId,
        trusted_import: TrustedImportId,
    ) -> Result<LocalTrustedHolImport, LocalReplError> {
        let connection = self.hol_mut(id)?;
        let view = connection.trusted_import(trusted_import)?;
        let database = connection.import_reference(view.import)?.database;
        Ok(LocalTrustedHolImport {
            import: view.import,
            trusted_import,
            database,
            signer: view.signer,
        })
    }

    /// Defines a destination-local alias for one complete namespace in an unfetched import.
    ///
    /// # Errors
    ///
    /// Returns an error for a wrong protocol, rejected operation, invalid source coordinates, or
    /// failed persistence.
    pub fn create_hol_imported_namespace(
        &mut self,
        id: ConnectionId,
        parent: Option<NamespaceId>,
        name: Option<&str>,
        import: ImportId,
        source_namespace: i64,
    ) -> Result<NamespaceId, LocalReplError> {
        self.hol_mut(id)?
            .create_imported_namespace(parent, name, import, source_namespace)
            .map_err(Into::into)
    }

    /// Authenticates and validates complete zero-metadata HOL bytes, matches one exact persistent
    /// trust record, and reads a structural namespace export through a scoped immutable reader.
    ///
    /// The returned integers are inert coordinates in the imported database. This operation does
    /// not import values into the local node table or grant authority to imported judgements.
    /// Successful connection-local trust matching admits the exact bytes and descriptor to the
    /// bounded shared resident cache, so later independently authorized connections can reuse the
    /// immutable mount without receiving the bytes again.
    ///
    /// # Errors
    ///
    /// Returns an error if authentication, detached validation, namespace provenance, exact trust
    /// matching, immutable VFS verification, or structural reading fails.
    #[allow(clippy::too_many_arguments)]
    pub fn inspect_trusted_hol_export(
        &mut self,
        id: ConnectionId,
        trusted_import: TrustedImportId,
        bytes: &[u8],
        schema: O256,
        image: O256,
        signer: O256,
        public_key: [u8; 32],
        signature: &[u8],
        namespace: NamespaceId,
        export: ExportId,
    ) -> Result<Option<LocalImportedHolExport>, LocalReplError> {
        let descriptor = HolSchemaDescriptor::from_schema(&HolSchema::new())?;
        self.inspect_trusted_hol_export_with_descriptor(
            id,
            trusted_import,
            bytes,
            descriptor.encode(),
            schema,
            image,
            signer,
            public_key,
            signature,
            namespace,
            export,
        )
    }

    /// Authenticates and validates complete bytes against their supplied portable metadata schema,
    /// then reads one exact trusted namespace export through a scoped immutable reader.
    ///
    /// # Errors
    ///
    /// Returns an error if authentication, descriptor decoding, exact detached validation,
    /// persistent trust matching, immutable VFS verification, or structural reading fails.
    #[allow(clippy::too_many_arguments)]
    pub fn inspect_trusted_hol_export_with_descriptor(
        &mut self,
        id: ConnectionId,
        trusted_import: TrustedImportId,
        bytes: &[u8],
        descriptor: &[u8],
        schema: O256,
        image: O256,
        signer: O256,
        public_key: [u8; 32],
        signature: &[u8],
        namespace: NamespaceId,
        export: ExportId,
    ) -> Result<Option<LocalImportedHolExport>, LocalReplError> {
        let authenticated =
            SignedSnapshotEnvelope::new(bytes, schema, image, signer, public_key, signature)
                .authenticate()?;
        let descriptor = HolSchemaDescriptor::decode(descriptor)?;
        let validated =
            AuthenticatedValidatedHolImage::validate_with_descriptor(authenticated, &descriptor)?;
        let canonical_descriptor = descriptor.encode().to_vec();
        let database = HolDatabaseRef::new(schema, image);
        let kernel_id = self.directory.connection_kernel(id)?;
        {
            let connection = match self.directory.get_mut(id)? {
                LocalConnection::Hol(connection) => connection,
                other @ LocalConnection::Sql(_) => {
                    return Err(LocalReplError::WrongProtocol {
                        id,
                        expected: "nucleus/hol-common-v2",
                        actual: other.protocol(),
                    });
                }
            };
            let _ = connection.match_trusted_import_image(trusted_import, validated)?;
        }

        // Admission happens only after connection-local trust matching, and uses the same signed
        // image operation as every SQL-facing transport. Rematch afterwards to reconstruct the
        // scoped logical capability without letting operational residency imply trust.
        self.put_verified_image_on(kernel_id, image, bytes)?;
        let service = self
            .kernels
            .get_mut(&kernel_id)
            .ok_or(ReplError::UnknownKernel(kernel_id))?;
        service.record_hol_descriptor(database, canonical_descriptor.clone())?;
        record_resident_hol_descriptor(
            self.directory.state(),
            kernel_id,
            database,
            &canonical_descriptor,
        )?;
        let mounted = service.image(image)?;
        let authenticated =
            SignedSnapshotEnvelope::new(bytes, schema, image, signer, public_key, signature)
                .authenticate()?;
        let descriptor = HolSchemaDescriptor::decode(descriptor.encode())?;
        let validated =
            AuthenticatedValidatedHolImage::validate_with_descriptor(authenticated, &descriptor)?;
        let matched = match self.directory.get_mut(id)? {
            LocalConnection::Hol(connection) => {
                connection.match_trusted_import_image(trusted_import, validated)?
            }
            LocalConnection::Sql(_) => unreachable!("protocol checked before image admission"),
        };
        read_matched_hol_export(id, trusted_import, matched, &mounted, namespace, export)
    }

    /// Authenticates and validates one already-resident signed HOL snapshot, then reads an exact
    /// trusted namespace export without receiving its bytes, descriptor, or attestation again.
    ///
    /// Residency is only an operational cache fact. The destination connection's persistent
    /// trusted-import row supplies the exact schema, signer, key, and signature; it is checked
    /// before cache lookup and full detached validation. Namespace provenance and actual VFS
    /// identity are then checked by the scoped structural reader.
    ///
    /// # Errors
    ///
    /// Returns an error if the destination does not independently trust the requested image, its
    /// validated resident interpretation is absent, revalidation fails, or immutable reading fails.
    pub fn inspect_resident_trusted_hol_export(
        &mut self,
        id: ConnectionId,
        trusted_import: TrustedImportId,
        image: O256,
        namespace: NamespaceId,
        export: ExportId,
    ) -> Result<Option<LocalImportedHolExport>, LocalReplError> {
        let kernel_id = self.directory.connection_kernel(id)?;
        let (trusted, database) = {
            let connection = self.hol_mut(id)?;
            let trusted = connection.trusted_import(trusted_import)?;
            let database = connection.import_reference(trusted.import)?.database;
            (trusted, database)
        };
        if database.image() != image {
            return Err(ReplImageError::TrustedImageMismatch {
                expected: database.image(),
                actual: image,
            }
            .into());
        }
        SignedSnapshotAttestation::new(
            database.schema(),
            image,
            trusted.signer,
            trusted.public_key,
            &trusted.signature,
        )
        .authenticate()?;
        let service = self
            .kernels
            .get(&kernel_id)
            .ok_or(ReplError::UnknownKernel(kernel_id))?;
        let descriptor = service
            .hol_images
            .get(&database)
            .cloned()
            .ok_or(ReplImageError::MissingHolImage { database })?;
        let mounted = service.image(image)?;
        let authenticated = SignedSnapshotEnvelope::new(
            mounted.bytes(),
            database.schema(),
            image,
            trusted.signer,
            trusted.public_key,
            &trusted.signature,
        )
        .authenticate()?;
        let descriptor = HolSchemaDescriptor::decode(&descriptor)?;
        let validated =
            AuthenticatedValidatedHolImage::validate_with_descriptor(authenticated, &descriptor)?;
        let matched = self
            .hol_mut(id)?
            .match_trusted_import_image(trusted_import, validated)?;
        read_matched_hol_export(id, trusted_import, matched, &mounted, namespace, export)
    }

    /// Introduces one exact implication from persisted witness keys.
    ///
    /// This shared orchestration performs no search: every supplied term must
    /// identify an exact judgement under `antecedent`.
    ///
    /// # Errors
    ///
    /// Returns an error for a protocol mismatch, absent witness judgement, or
    /// rejected trusted rule.
    pub fn prove_context_implication(
        &mut self,
        id: ConnectionId,
        antecedent: ContextId,
        consequent: ContextId,
        witness_terms: &[TermId],
    ) -> Result<(), LocalProofError> {
        self.hol_mut(id)?.with_proof_session(|mut proof| {
            let mut witnesses = Vec::with_capacity(witness_terms.len());
            for term in witness_terms {
                let theorem = proof.load_theorem(antecedent, *term)?.ok_or(
                    LocalProofError::MissingTheorem {
                        context: antecedent,
                        conclusion: *term,
                    },
                )?;
                witnesses.push(theorem);
            }
            let implication =
                proof.prove_context_implication(antecedent, consequent, &witnesses)?;
            proof.persist_context_implication(&implication)?;
            Ok(())
        })
    }

    /// Weakens an exact persisted theorem along an exact persisted edge.
    ///
    /// # Errors
    ///
    /// Returns an error for missing exact inputs, a protocol mismatch, or a
    /// rejected trusted rule.
    pub fn weaken(
        &mut self,
        id: ConnectionId,
        antecedent: ContextId,
        consequent: ContextId,
        conclusion: TermId,
    ) -> Result<TermId, LocalProofError> {
        self.hol_mut(id)?.with_proof_session(|mut proof| {
            let implication = proof
                .load_context_implication(antecedent, consequent)?
                .ok_or(LocalProofError::MissingImplication {
                    antecedent,
                    consequent,
                })?;
            let theorem = proof.load_theorem(consequent, conclusion)?.ok_or(
                LocalProofError::MissingTheorem {
                    context: consequent,
                    conclusion,
                },
            )?;
            let theorem = proof.weaken(&implication, &theorem)?;
            let conclusion = theorem.conclusion();
            proof.persist_theorem(&theorem)?;
            Ok(conclusion)
        })
    }

    /// Applies `EqMp` to two exact persisted theorem keys and persists the result.
    ///
    /// # Errors
    ///
    /// Returns an error for missing exact premises, a protocol mismatch, a
    /// rejected inference, or denied persistence.
    pub fn equality_modus_ponens(
        &mut self,
        id: ConnectionId,
        context: ContextId,
        equality: TermId,
        premise: TermId,
    ) -> Result<TermId, LocalProofError> {
        self.hol_mut(id)?.with_proof_session(|mut proof| {
            let equality =
                proof
                    .load_theorem(context, equality)?
                    .ok_or(LocalProofError::MissingTheorem {
                        context,
                        conclusion: equality,
                    })?;
            let premise =
                proof
                    .load_theorem(context, premise)?
                    .ok_or(LocalProofError::MissingTheorem {
                        context,
                        conclusion: premise,
                    })?;
            let theorem = proof.equality_modus_ponens(&equality, &premise)?;
            let conclusion = theorem.conclusion();
            proof.persist_theorem(&theorem)?;
            Ok(conclusion)
        })
    }
}

/// Failure while reconstructing proof capabilities for a REPL request.
#[derive(Debug)]
pub enum LocalProofError {
    /// The managed connection could not be selected as HOL.
    Repl(LocalReplError),
    /// Nucleus rejected a proof operation.
    Proof(ProofError),
    /// An exact persisted theorem key is absent.
    MissingTheorem {
        context: ContextId,
        conclusion: TermId,
    },
    /// An exact persisted implication edge is absent.
    MissingImplication {
        antecedent: ContextId,
        consequent: ContextId,
    },
}

impl fmt::Display for LocalProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Repl(error) => error.fmt(formatter),
            Self::Proof(error) => error.fmt(formatter),
            Self::MissingTheorem {
                context,
                conclusion,
            } => write!(
                formatter,
                "judgement {} |- {} is not persisted",
                context.get(),
                conclusion.get()
            ),
            Self::MissingImplication {
                antecedent,
                consequent,
            } => write!(
                formatter,
                "context implication {} => {} is not persisted",
                antecedent.get(),
                consequent.get()
            ),
        }
    }
}

impl StdError for LocalProofError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Repl(error) => Some(error),
            Self::Proof(error) => Some(error),
            Self::MissingTheorem { .. } | Self::MissingImplication { .. } => None,
        }
    }
}

impl From<LocalReplError> for LocalProofError {
    fn from(error: LocalReplError) -> Self {
        Self::Repl(error)
    }
}

impl From<ProofError> for LocalProofError {
    fn from(error: ProofError) -> Self {
        Self::Proof(error)
    }
}

/// Failure to cache one uninterpreted immutable database image in the REPL.
#[derive(Debug)]
pub enum ReplImageError {
    /// Supplied bytes did not have the expected operational address.
    AddressMismatch { expected: O256, actual: O256 },
    /// Different resident bytes claimed the same operational address.
    HashCollision { image: O256 },
    /// The requested complete image is not resident.
    Missing { image: O256 },
    /// No validated resident HOL interpretation exists for these coordinates.
    MissingHolImage { database: HolDatabaseRef },
    /// The same schema/image coordinates were associated with different canonical descriptors.
    ConflictingHolDescriptor { database: HolDatabaseRef },
    /// The requested resident image differs from the connection's trusted import.
    TrustedImageMismatch { expected: O256, actual: O256 },
    /// One image exceeds the fixed resident byte limit.
    ImageTooLarge { length: usize, maximum: usize },
    /// The fixed number of distinct resident images has been reached.
    ImageCountLimit { maximum: usize },
    /// Adding the image would exceed the fixed total resident byte limit.
    TotalBytesLimit { maximum: usize },
    /// The fixed immutable VFS could not be registered.
    Register(covalence_neutron::ImmutableImageError),
}

impl fmt::Display for ReplImageError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AddressMismatch { expected, actual } => {
                write!(
                    formatter,
                    "database image has address {actual}, expected {expected}"
                )
            }
            Self::HashCollision { image } => {
                write!(
                    formatter,
                    "different resident bytes share image address {image}"
                )
            }
            Self::Missing { image } => write!(formatter, "database image {image} is not resident"),
            Self::MissingHolImage { database } => write!(
                formatter,
                "HOL database ({}, {}) is not resident",
                database.schema(),
                database.image()
            ),
            Self::ConflictingHolDescriptor { database } => write!(
                formatter,
                "HOL database ({}, {}) has conflicting resident descriptors",
                database.schema(),
                database.image()
            ),
            Self::TrustedImageMismatch { expected, actual } => write!(
                formatter,
                "requested resident image {actual} differs from trusted image {expected}"
            ),
            Self::ImageTooLarge { length, maximum } => write!(
                formatter,
                "database image contains {length} bytes; resident limit is {maximum}"
            ),
            Self::ImageCountLimit { maximum } => {
                write!(formatter, "resident image count limit {maximum} reached")
            }
            Self::TotalBytesLimit { maximum } => write!(
                formatter,
                "resident images would exceed total byte limit {maximum}"
            ),
            Self::Register(error) => error.fmt(formatter),
        }
    }
}

impl StdError for ReplImageError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Register(error) => Some(error),
            _ => None,
        }
    }
}

/// Failure in the shared local-kernel REPL layer.
#[derive(Debug)]
pub enum LocalReplError {
    /// The connection directory failed.
    Directory(ReplError),
    /// A raw SQL connection could not open.
    SqlOpen(covalence_neutron::ConnectionError),
    /// A local raw SQL operation failed with its original diagnostic.
    Sql(sqlite::Error),
    /// A portable kernel-service operation failed.
    Service(ServiceError),
    /// A raw SQL service operation failed with a portable or `SQLite` diagnostic.
    SqlRun(SqlRunError),
    /// A local kernel service extension failed.
    KernelService(LocalKernelServiceError),
    /// A signed inter-kernel exchange failed before producing a verified service result.
    SignedExchange(LocalSignedExchangeError),
    /// The transport-neutral signed caller rejected a grant, request, or result.
    SignedClient(SignedClientError),
    /// Native loopback HTTP framing or I/O failed.
    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    HttpTransport(HttpTransportError),
    /// A known remote kernel does not yet expose the requested protocol over its transport.
    RemoteProtocolUnsupported {
        /// Exact known remote kernel.
        kernel: KernelId,
        /// Requested protocol identifier.
        protocol: &'static str,
    },
    /// A HOL connection or its schema could not open.
    HolOpen(HolOpenError),
    /// A portable HOL metadata schema descriptor was invalid.
    HolSchemaDescriptor(HolSchemaDescriptorError),
    /// A declarative REPL HOL metadata schema was invalid.
    HolSchemaSpec(HolSchemaSpecError),
    /// A transport-neutral HOL metadata value request was invalid.
    MetadataSpec(MetadataSpecError),
    /// A HOL metadata read or write failed.
    Metadata(MetadataError),
    /// One kernel's immutable image residency failed.
    Image(ReplImageError),
    /// A namespace operation failed.
    Namespace(NamespaceError),
    /// A namespace export operation failed.
    Export(ExportError),
    /// Signed HOL snapshot export failed.
    HolExport(HolExportError),
    /// Hash-first snapshot authentication failed.
    SnapshotAuthentication(SnapshotAuthenticationError),
    /// Connection-local snapshot trust failed.
    SnapshotTrust(SnapshotTrustError),
    /// Import-directory operation failed.
    Import(ImportError),
    /// Persistent trusted-import operation failed.
    TrustedImport(TrustedImportError),
    /// Authenticated bytes failed detached default HOL validation.
    HolImageValidation(AuthenticatedHolImageValidationError),
    /// Validated bytes did not match the exact persistent trusted import.
    TrustedImportImage(TrustedImportImageError),
    /// The scoped immutable imported-image reader failed.
    ImportedReader(ImportedReaderError),
    /// A command was sent to a connection of another protocol.
    WrongProtocol {
        /// Requested connection.
        id: ConnectionId,
        /// Protocol required by the operation.
        expected: &'static str,
        /// Protocol actually owned by the connection.
        actual: &'static str,
    },
}

impl fmt::Display for LocalReplError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Directory(error) => error.fmt(formatter),
            Self::SqlOpen(error) => write!(formatter, "could not open SQL connection: {error}"),
            Self::Sql(error) => error.fmt(formatter),
            Self::Service(error) => error.fmt(formatter),
            Self::SqlRun(error) => error.fmt(formatter),
            Self::KernelService(error) => error.fmt(formatter),
            Self::SignedExchange(error) => error.fmt(formatter),
            Self::SignedClient(error) => error.fmt(formatter),
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            Self::HttpTransport(error) => error.fmt(formatter),
            Self::RemoteProtocolUnsupported { kernel, protocol } => write!(
                formatter,
                "remote kernel {kernel} does not expose {protocol} over its configured transport"
            ),
            Self::HolOpen(error) => error.fmt(formatter),
            Self::HolSchemaDescriptor(error) => error.fmt(formatter),
            Self::HolSchemaSpec(error) => error.fmt(formatter),
            Self::MetadataSpec(error) => error.fmt(formatter),
            Self::Metadata(error) => error.fmt(formatter),
            Self::Image(error) => error.fmt(formatter),
            Self::Namespace(error) => error.fmt(formatter),
            Self::Export(error) => error.fmt(formatter),
            Self::HolExport(error) => error.fmt(formatter),
            Self::SnapshotAuthentication(error) => error.fmt(formatter),
            Self::SnapshotTrust(error) => error.fmt(formatter),
            Self::Import(error) => error.fmt(formatter),
            Self::TrustedImport(error) => error.fmt(formatter),
            Self::HolImageValidation(error) => error.fmt(formatter),
            Self::TrustedImportImage(error) => error.fmt(formatter),
            Self::ImportedReader(error) => error.fmt(formatter),
            Self::WrongProtocol {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "connection {id} uses {actual}; operation requires {expected}"
            ),
        }
    }
}

impl StdError for LocalReplError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Directory(error) => Some(error),
            Self::SqlOpen(error) => Some(error),
            Self::Sql(error) => Some(error),
            Self::Service(error) => Some(error),
            Self::SqlRun(error) => Some(error),
            Self::KernelService(error) => Some(error),
            Self::SignedExchange(error) => Some(error),
            Self::SignedClient(error) => Some(error),
            #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
            Self::HttpTransport(error) => Some(error),
            Self::HolOpen(error) => Some(error),
            Self::HolSchemaDescriptor(error) => Some(error),
            Self::HolSchemaSpec(error) => Some(error),
            Self::MetadataSpec(error) => Some(error),
            Self::Metadata(error) => Some(error),
            Self::Image(error) => Some(error),
            Self::Namespace(error) => Some(error),
            Self::Export(error) => Some(error),
            Self::HolExport(error) => Some(error),
            Self::SnapshotAuthentication(error) => Some(error),
            Self::SnapshotTrust(error) => Some(error),
            Self::Import(error) => Some(error),
            Self::TrustedImport(error) => Some(error),
            Self::HolImageValidation(error) => Some(error),
            Self::TrustedImportImage(error) => Some(error),
            Self::ImportedReader(error) => Some(error),
            Self::WrongProtocol { .. } | Self::RemoteProtocolUnsupported { .. } => None,
        }
    }
}

impl From<ReplError> for LocalReplError {
    fn from(error: ReplError) -> Self {
        Self::Directory(error)
    }
}

impl From<LocalSignedExchangeError> for LocalReplError {
    fn from(error: LocalSignedExchangeError) -> Self {
        Self::SignedExchange(error)
    }
}

impl From<SignedClientError> for LocalReplError {
    fn from(error: SignedClientError) -> Self {
        Self::SignedClient(error)
    }
}

#[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
impl From<HttpTransportError> for LocalReplError {
    fn from(error: HttpTransportError) -> Self {
        Self::HttpTransport(error)
    }
}

impl From<HolSchemaDescriptorError> for LocalReplError {
    fn from(error: HolSchemaDescriptorError) -> Self {
        Self::HolSchemaDescriptor(error)
    }
}

impl From<HolSchemaSpecError> for LocalReplError {
    fn from(error: HolSchemaSpecError) -> Self {
        Self::HolSchemaSpec(error)
    }
}

impl From<MetadataSpecError> for LocalReplError {
    fn from(error: MetadataSpecError) -> Self {
        Self::MetadataSpec(error)
    }
}

impl From<MetadataError> for LocalReplError {
    fn from(error: MetadataError) -> Self {
        Self::Metadata(error)
    }
}

impl From<ReplImageError> for LocalReplError {
    fn from(error: ReplImageError) -> Self {
        Self::Image(error)
    }
}

impl From<covalence_neutron::ImmutableImageError> for LocalReplError {
    fn from(error: covalence_neutron::ImmutableImageError) -> Self {
        Self::Image(ReplImageError::Register(error))
    }
}

impl From<NamespaceError> for LocalReplError {
    fn from(error: NamespaceError) -> Self {
        Self::Namespace(error)
    }
}

impl From<ExportError> for LocalReplError {
    fn from(error: ExportError) -> Self {
        Self::Export(error)
    }
}

impl From<HolExportError> for LocalReplError {
    fn from(error: HolExportError) -> Self {
        Self::HolExport(error)
    }
}

impl From<SnapshotAuthenticationError> for LocalReplError {
    fn from(error: SnapshotAuthenticationError) -> Self {
        Self::SnapshotAuthentication(error)
    }
}

impl From<SnapshotTrustError> for LocalReplError {
    fn from(error: SnapshotTrustError) -> Self {
        Self::SnapshotTrust(error)
    }
}

impl From<ImportError> for LocalReplError {
    fn from(error: ImportError) -> Self {
        Self::Import(error)
    }
}

impl From<TrustedImportError> for LocalReplError {
    fn from(error: TrustedImportError) -> Self {
        Self::TrustedImport(error)
    }
}

impl From<AuthenticatedHolImageValidationError> for LocalReplError {
    fn from(error: AuthenticatedHolImageValidationError) -> Self {
        Self::HolImageValidation(error)
    }
}

impl From<TrustedImportImageError> for LocalReplError {
    fn from(error: TrustedImportImageError) -> Self {
        Self::TrustedImportImage(error)
    }
}

impl From<ImportedReaderError> for LocalReplError {
    fn from(error: ImportedReaderError) -> Self {
        Self::ImportedReader(error)
    }
}

/// Failure to operate the REPL directory.
#[derive(Debug)]
pub enum ReplError {
    /// The raw state connection could not be opened.
    Open(covalence_neutron::ConnectionError),
    /// The state database rejected an operation.
    State(sqlite::Error),
    /// A requested kernel directory entry does not exist.
    UnknownKernel(KernelId),
    /// A stored kernel directory entry is malformed.
    CorruptKernel(KernelId),
    /// A requested runtime connection does not exist.
    UnknownConnection(ConnectionId),
    /// A process-local identifier counter was exhausted.
    IdentifierExhausted(&'static str),
    /// Runtime state unexpectedly already owns a freshly allocated identifier.
    RuntimeIdentifierCollision(&'static str, i64),
    /// No runtime connection is currently selected.
    NoActiveConnection,
}

impl fmt::Display for ReplError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Open(error) => write!(formatter, "could not open REPL state: {error}"),
            Self::State(error) => write!(formatter, "could not access REPL state: {error}"),
            Self::UnknownKernel(id) => write!(formatter, "unknown kernel {id}"),
            Self::CorruptKernel(id) => write!(formatter, "kernel {id} is corrupt"),
            Self::UnknownConnection(id) => write!(formatter, "unknown connection {id}"),
            Self::IdentifierExhausted(kind) => {
                write!(formatter, "REPL exhausted process-local {kind} identifiers")
            }
            Self::RuntimeIdentifierCollision(kind, id) => {
                write!(
                    formatter,
                    "runtime {kind} identifier {id} is already in use"
                )
            }
            Self::NoActiveConnection => formatter.write_str("no active connection"),
        }
    }
}

impl StdError for ReplError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Open(error) => Some(error),
            Self::State(error) => Some(error),
            Self::UnknownKernel(_)
            | Self::CorruptKernel(_)
            | Self::UnknownConnection(_)
            | Self::IdentifierExhausted(_)
            | Self::RuntimeIdentifierCollision(_, _)
            | Self::NoActiveConnection => None,
        }
    }
}

impl From<covalence_neutron::ConnectionError> for ReplError {
    fn from(error: covalence_neutron::ConnectionError) -> Self {
        Self::Open(error)
    }
}

impl From<sqlite::Error> for ReplError {
    fn from(error: sqlite::Error) -> Self {
        Self::State(error)
    }
}

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
mod web;

#[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
pub use web::{
    WebExport, WebImportedHolExport, WebKernel, WebKind, WebNamespace, WebOutcome,
    WebSignedHolSnapshot, WebTerm, WebTrustedHolImport, WebType,
};

/// Returns the cross-target `SQLite` smoke-test value.
#[must_use]
#[cfg_attr(
    all(target_arch = "wasm32", target_os = "unknown"),
    wasm_bindgen::prelude::wasm_bindgen
)]
pub fn smoke() -> u32 {
    covalence_nucleus::smoke()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn records_lifecycle_and_selection_in_sqlite() {
        let mut repl = Repl::new(&[7; 32]).unwrap();
        let first = repl.insert("one", String::from("first")).unwrap();
        let second = repl.insert("two", String::from("second")).unwrap();
        assert_eq!(repl.active().unwrap(), Some(first));

        repl.select(second).unwrap();
        assert_eq!(repl.active().unwrap(), Some(second));
        assert_eq!(repl.active_mut().unwrap(), "second");
        assert_eq!(repl.remove(second).unwrap(), "second");
        assert_eq!(repl.active().unwrap(), Some(first));

        let rows = repl
            .state()
            .sqlite()
            .query_row("SELECT count(*) FROM repl_connection", (), |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(rows, 1);
        let public_key = repl
            .state()
            .sqlite()
            .query_row(
                "SELECT public_key FROM repl_kernel WHERE kernel_id = 0",
                (),
                |row| row.get::<_, Vec<u8>>(0),
            )
            .unwrap();
        assert_eq!(public_key, vec![7; 32]);
    }

    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    #[test]
    fn remote_http_directory_and_hol_rejection_are_local_and_atomic() {
        let mut repl = LocalRepl::new().unwrap();
        let remote_kernel = Kernel::ephemeral();
        let public_key = *remote_kernel.verifying_key().as_bytes();
        let address: SocketAddr = "127.0.0.1:9".parse().unwrap();
        let endpoint = LoopbackHttpEndpoint::new(
            address,
            public_key,
            Duration::from_secs(1),
            Duration::from_secs(1),
        )
        .unwrap();
        let id = repl
            .directory
            .insert_kernel("native-http", Some(&address.to_string()), &public_key)
            .unwrap();
        assert!(
            repl.remote_kernels
                .insert(
                    id,
                    RemoteKernelRoute {
                        transport: "native-http".to_owned(),
                        endpoint: Some(address.to_string()),
                        public_key,
                    },
                )
                .is_none()
        );
        assert!(repl.remote_http.insert(id, endpoint).is_none());

        assert_eq!(
            repl.kernel(id).unwrap(),
            KernelView {
                transport: "native-http".to_owned(),
                endpoint: Some(address.to_string()),
                public_key,
            }
        );
        assert!(repl.kernels().iter().any(|(kernel, _)| *kernel == id));
        assert!(matches!(
            repl.open_hol_on(id),
            Err(LocalReplError::RemoteProtocolUnsupported {
                kernel,
                protocol: "nucleus/hol-common-v2"
            }) if kernel == id
        ));
        assert!(matches!(
            repl.open_hol_with_descriptor_on(id, b"not examined"),
            Err(LocalReplError::RemoteProtocolUnsupported { kernel, .. }) if kernel == id
        ));
        assert_eq!(repl.active().unwrap(), None);
        assert!(repl.directory.connections.is_empty());

        let before = repl.kernels().len();
        let non_loopback: SocketAddr = "192.0.2.1:8000".parse().unwrap();
        assert!(matches!(
            repl.connect_native_http(non_loopback, public_key, None),
            Err(LocalReplError::HttpTransport(
                HttpTransportError::NonLoopbackAddress(address)
            )) if address == non_loopback
        ));
        assert_eq!(repl.kernels().len(), before);
    }

    #[test]
    fn split_remote_rpc_keeps_linear_signed_state_in_rust() {
        let mut repl = LocalRepl::new().unwrap();
        let mut remote = LocalKernelService::new(Kernel::ephemeral());
        let caller = repl.remote_caller_public_key();
        let grant = remote.issue_sql_channel(caller).unwrap();
        let recipient = remote.identity().unwrap().public_key;
        let kernel = repl
            .accept_remote_kernel("test-bytes", Some("opaque"), recipient, &grant.encode())
            .unwrap();
        assert_eq!(
            repl.kernel(kernel).unwrap(),
            KernelView {
                transport: "test-bytes".to_owned(),
                endpoint: Some("opaque".to_owned()),
                public_key: recipient,
            }
        );

        let pending = repl
            .prepare_kernel_request(kernel, &ServiceRequest::Identity)
            .unwrap();
        let result = remote.exchange_sql(&pending.encode()).unwrap();
        assert!(matches!(
            repl.accept_kernel_result(pending, &result).unwrap(),
            ServiceResponse::Identity(Ok(identity)) if identity.public_key == recipient
        ));

        let abandoned = repl
            .prepare_kernel_request(kernel, &ServiceRequest::Identity)
            .unwrap();
        repl.abandon_kernel_request(abandoned);
        assert!(matches!(
            repl.prepare_kernel_request(kernel, &ServiceRequest::Identity),
            Err(LocalReplError::SignedClient(
                SignedClientError::UnknownRoute(route)
            )) if route == kernel
        ));
    }

    #[test]
    fn split_repl_operations_keep_typed_finalization_in_rust() {
        fn exchange(
            repl: &mut LocalRepl,
            remote: &mut LocalKernelService,
            operation: PendingReplOperation,
        ) -> ReplOperationProgress {
            let result = remote.exchange_sql(&operation.encode()).unwrap();
            repl.accept_operation_result(operation, &result)
        }

        let mut repl = LocalRepl::new().unwrap();
        let mut remote = LocalKernelService::new(Kernel::ephemeral());
        let caller = repl.remote_caller_public_key();
        let grant = remote.issue_sql_channel(caller).unwrap();
        let recipient = remote.identity().unwrap().public_key;
        let kernel = repl
            .accept_remote_kernel("test-bytes", Some("opaque"), recipient, &grant.encode())
            .unwrap();

        let open = repl
            .prepare_operation(ReplOperation::OpenSql { kernel })
            .unwrap();
        let ReplOperationProgress::Complete(Ok(ReplOperationOutput::Opened(connection))) =
            exchange(&mut repl, &mut remote, open)
        else {
            panic!("open did not reach its typed completion");
        };
        assert_eq!(repl.active().unwrap(), Some(connection));

        let rejected = repl
            .prepare_operation(ReplOperation::RunSql {
                connection,
                sql: "SELECT * FROM missing_table".to_owned(),
            })
            .unwrap();
        assert!(matches!(
            exchange(&mut repl, &mut remote, rejected),
            ReplOperationProgress::Complete(Err(LocalReplError::SqlRun(_)))
        ));

        let run = repl
            .prepare_operation(ReplOperation::RunSql {
                connection,
                sql: "SELECT 42 AS answer".to_owned(),
            })
            .unwrap();
        assert!(matches!(
            exchange(&mut repl, &mut remote, run),
            ReplOperationProgress::Complete(Ok(ReplOperationOutput::Sql(Outcome::Rows(
                QueryResult { columns, rows }
            )))) if columns == ["answer"] && rows == [vec![Value::Integer(42)]]
        ));

        let serialize = repl
            .prepare_operation(ReplOperation::SerializeMain { connection })
            .unwrap();
        let ReplOperationProgress::Complete(Ok(ReplOperationOutput::Serialized(bytes))) =
            exchange(&mut repl, &mut remote, serialize)
        else {
            panic!("serialize did not reach its typed completion");
        };
        let image = O256::from_bytes(&bytes);
        let put = repl
            .prepare_operation(ReplOperation::PutImage {
                kernel,
                expected: image,
                bytes,
            })
            .unwrap();
        assert!(matches!(
            exchange(&mut repl, &mut remote, put),
            ReplOperationProgress::Complete(Ok(ReplOperationOutput::Image(actual)))
                if actual == image
        ));
        let resident = repl
            .prepare_operation(ReplOperation::HasImage { kernel, image })
            .unwrap();
        assert!(matches!(
            exchange(&mut repl, &mut remote, resident),
            ReplOperationProgress::Complete(Ok(ReplOperationOutput::ImageResident(true)))
        ));

        let close = repl
            .prepare_operation(ReplOperation::CloseSql { connection })
            .unwrap();
        assert!(matches!(
            exchange(&mut repl, &mut remote, close),
            ReplOperationProgress::Complete(Ok(ReplOperationOutput::Closed))
        ));
        assert!(matches!(
            repl.prepare_operation(ReplOperation::SerializeMain { connection }),
            Err(LocalReplError::Directory(ReplError::UnknownConnection(id))) if id == connection
        ));
    }

    #[test]
    fn split_repl_operation_distinguishes_invalid_signed_evidence() {
        let mut repl = LocalRepl::new().unwrap();
        let mut remote = LocalKernelService::new(Kernel::ephemeral());
        let caller = repl.remote_caller_public_key();
        let grant = remote.issue_sql_channel(caller).unwrap();
        let recipient = remote.identity().unwrap().public_key;
        let kernel = repl
            .accept_remote_kernel("test-bytes", Some("opaque"), recipient, &grant.encode())
            .unwrap();
        let open = repl
            .prepare_operation(ReplOperation::OpenSql { kernel })
            .unwrap();
        let result = remote.exchange_sql(&open.encode()).unwrap();
        let ReplOperationProgress::Complete(Ok(ReplOperationOutput::Opened(connection))) =
            repl.accept_operation_result(open, &result)
        else {
            panic!("open did not reach its typed completion");
        };

        let run = repl
            .prepare_operation(ReplOperation::RunSql {
                connection,
                sql: "SELECT 1".to_owned(),
            })
            .unwrap();
        assert!(matches!(
            repl.accept_operation_result(run, b"not a signed result"),
            ReplOperationProgress::Invalidated(LocalReplError::SignedClient(_))
        ));
        assert!(matches!(
            repl.prepare_operation(ReplOperation::RunSql {
                connection,
                sql: "SELECT 2".to_owned(),
            }),
            Err(LocalReplError::Directory(ReplError::UnknownConnection(id))) if id == connection
        ));
    }

    #[test]
    fn split_open_dispatches_close_compensation_after_directory_failure() {
        let mut repl = LocalRepl::new().unwrap();
        let mut remote = LocalKernelService::new(Kernel::ephemeral());
        let caller = repl.remote_caller_public_key();
        let grant = remote.issue_sql_channel(caller).unwrap();
        let recipient = remote.identity().unwrap().public_key;
        let kernel = repl
            .accept_remote_kernel("test-bytes", Some("opaque"), recipient, &grant.encode())
            .unwrap();
        let open = repl
            .prepare_operation(ReplOperation::OpenSql { kernel })
            .unwrap();
        let open_result = remote.exchange_sql(&open.encode()).unwrap();
        assert_eq!(remote.sql_connections.len(), 1);

        repl.state()
            .sqlite()
            .execute_batch("DROP TABLE repl_connection")
            .unwrap();
        let ReplOperationProgress::Dispatch(compensation) =
            repl.accept_operation_result(open, &open_result)
        else {
            panic!("failed local open commit did not request compensation");
        };
        let close_result = remote.exchange_sql(&compensation.encode()).unwrap();
        assert!(matches!(
            repl.accept_operation_result(*compensation, &close_result),
            ReplOperationProgress::Complete(Err(LocalReplError::Directory(_)))
        ));
        assert!(remote.sql_connections.is_empty());
    }

    #[test]
    fn rejected_remote_grant_leaves_no_directory_or_route() {
        let mut repl = LocalRepl::new().unwrap();
        let before = repl.kernels();
        let recipient = *Kernel::ephemeral().verifying_key().as_bytes();
        assert!(
            repl.accept_remote_kernel("fetch", Some("https://example.invalid"), recipient, b"bad")
                .is_err()
        );
        assert_eq!(repl.kernels(), before);
        assert!(repl.remote_kernels.is_empty());
    }

    #[cfg(not(all(target_arch = "wasm32", target_os = "unknown")))]
    #[test]
    fn native_http_kernel_runs_the_shared_sql_and_image_workflow() {
        let bootstrap = [0x5a; 32];
        let server = spawn_native_kernel_server(
            NativeKernelServerConfig::new("127.0.0.1:0".parse().unwrap(), [])
                .with_bootstrap_token(bootstrap),
        )
        .unwrap();
        let address = server.address();
        let public_key = server.public_key();

        let mut repl = LocalRepl::new().unwrap();
        let remote = repl
            .connect_native_http(address, public_key, Some(bootstrap))
            .unwrap();
        assert_eq!(repl.kernel(remote).unwrap().public_key, public_key);

        let source = repl.open_sql_on(remote).unwrap();
        repl.run_sql(source, "CREATE TABLE payload(value INTEGER) STRICT")
            .unwrap();
        repl.run_sql(source, "INSERT INTO payload VALUES (42)")
            .unwrap();
        assert_eq!(
            repl.run_sql(source, "SELECT value FROM payload").unwrap(),
            Outcome::Rows(QueryResult {
                columns: vec!["value".to_owned()],
                rows: vec![vec![Value::Integer(42)]],
            })
        );

        let snapshot = repl.serialize_main(source).unwrap();
        let image = repl.put_image_for_connection(source, &snapshot).unwrap();
        assert!(repl.has_image_on(remote, image).unwrap());
        let reader = repl.open_sql_on(remote).unwrap();
        repl.attach_image(reader, image, "snapshot").unwrap();
        assert_eq!(
            repl.run_sql(reader, "SELECT value FROM snapshot.payload")
                .unwrap(),
            Outcome::Rows(QueryResult {
                columns: vec!["value".to_owned()],
                rows: vec![vec![Value::Integer(42)]],
            })
        );

        repl.close(reader).unwrap();
        repl.close(source).unwrap();
        drop(repl);
        server.shutdown().unwrap();
    }

    #[test]
    fn shared_image_cache_is_uninterpreted_deduplicated_and_inspectable() {
        let mut repl = LocalRepl::new().unwrap();
        let bytes = b"untrusted bytes need not be SQLite";
        let image = repl.put_image(bytes).unwrap();
        assert!(repl.has_image(image));
        assert_eq!(repl.resident_image_count(), 1);
        assert_eq!(repl.put_image(bytes).unwrap(), image);
        assert_eq!(repl.resident_image_count(), 1);
        assert!(matches!(
            repl.put_verified_image(O256::from_bytes(b"different"), bytes),
            Err(LocalReplError::Image(
                ReplImageError::AddressMismatch { .. }
            ))
        ));
        let recorded = repl
            .state()
            .sqlite()
            .query_row(
                "SELECT byte_length FROM repl_image WHERE image_hash = ?1",
                [image.as_ref()],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(recorded, i64::try_from(bytes.len()).unwrap());
    }

    #[test]
    fn shared_image_cache_capacity_checks_exact_boundaries() {
        let limits = ImageCacheLimits {
            image_bytes: 10,
            images: 2,
            total_bytes: 15,
        };
        assert_eq!(check_image_cache_capacity(0, 0, 10, limits).unwrap(), 10);
        assert!(matches!(
            check_image_cache_capacity(0, 0, 11, limits),
            Err(ReplImageError::ImageTooLarge { .. })
        ));
        assert!(matches!(
            check_image_cache_capacity(2, 0, 1, limits),
            Err(ReplImageError::ImageCountLimit { .. })
        ));
        assert_eq!(check_image_cache_capacity(1, 5, 10, limits).unwrap(), 15);
        assert!(matches!(
            check_image_cache_capacity(1, 6, 10, limits),
            Err(ReplImageError::TotalBytesLimit { .. })
        ));
    }

    #[test]
    fn local_kernel_directory_manages_sql_and_hol_without_crossing_protocols() {
        let mut repl = LocalRepl::new().unwrap();
        let sql = repl.open_sql().unwrap();
        let hol = repl.open_hol().unwrap();

        repl.run_sql(sql, "SELECT 1").unwrap();
        let star = repl.hol_mut(hol).unwrap().insert_kind(&Kind::Star).unwrap();
        assert_eq!(star.get(), 1);
        assert!(matches!(
            repl.run_sql(hol, "SELECT 1"),
            Err(LocalReplError::WrongProtocol {
                expected: "nucleus/sql",
                actual: "nucleus/hol-common-v2",
                ..
            })
        ));
        assert!(matches!(
            repl.hol_mut(sql),
            Err(LocalReplError::WrongProtocol {
                expected: "nucleus/hol-common-v2",
                actual: "nucleus/sql",
                ..
            })
        ));
        let protocols = repl
            .state()
            .sqlite()
            .prepare("SELECT protocol FROM repl_connection ORDER BY connection_id")
            .unwrap()
            .query_map([], |row| row.get::<_, String>(0))
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(protocols, ["nucleus/sql", "nucleus/hol-common-v2"]);
    }

    #[test]
    fn local_kernel_service_runs_select_42_through_an_opaque_handle() {
        let mut service = LocalKernelService::new(Kernel::ephemeral());
        let connection = service.open_sql().unwrap();
        let outcome = KernelService::run_sql(
            &mut service,
            connection,
            SqlStatement::new("SELECT 42 AS answer".to_owned()).unwrap(),
        )
        .unwrap();
        assert!(matches!(
            outcome.kind(),
            covalence_kernel_service::SqlOutcomeKind::Rows { columns, rows }
                if columns == &["answer"] && rows == &[vec![SqlValue::Integer(42)]]
        ));
    }

    fn signed_sql_call(
        caller: &LocalKernelService,
        recipient: &mut LocalKernelService,
        grant: &ChannelGrant,
        sequence: u64,
        request: &ServiceRequest,
    ) -> (SignedInvocation, ServiceResponse) {
        let payload = request.encode();
        let invocation = SignedInvocation::sign(
            operation_schema(request.operation()),
            &NucleusStatementSigner(caller.kernel.signer()),
            grant.recipient(),
            grant.channel(),
            sequence,
            request.value_id(),
            payload,
        )
        .unwrap();
        let result =
            SignedResult::decode(&recipient.exchange_sql(&invocation.encode()).unwrap()).unwrap();
        result
            .verify(&invocation, &recipient.kernel.verifying_key())
            .unwrap();
        let response = ServiceResponse::decode(result.payload()).unwrap();
        assert_eq!(result.output_id(), response.value_id());
        assert_eq!(response.operation(), request.operation());
        (invocation, response)
    }

    #[test]
    fn signed_channels_run_sql_reject_replay_and_scope_handles() {
        let caller = LocalKernelService::new(Kernel::ephemeral());
        let mut recipient = LocalKernelService::new(Kernel::ephemeral());
        let caller_key = *caller.kernel.verifying_key().as_bytes();
        let grant = recipient.issue_sql_channel(caller_key).unwrap();
        grant
            .verify(caller_key, &recipient.kernel.verifying_key())
            .unwrap();

        let (open_invocation, open_response) =
            signed_sql_call(&caller, &mut recipient, &grant, 0, &ServiceRequest::Open);
        let ServiceResponse::Open(Ok(connection)) = open_response else {
            panic!("signed open did not return a connection")
        };
        assert!(matches!(
            recipient.exchange_sql(&open_invocation.encode()),
            Err(LocalSignedExchangeError::Wire(
                WireError::UnexpectedSequence {
                    expected: 1,
                    actual: 0
                }
            ))
        ));

        let statement = SqlStatement::new("SELECT 42 AS answer".to_owned()).unwrap();
        let run = ServiceRequest::Run {
            connection,
            statement: statement.clone(),
        };
        let valid_run = SignedInvocation::sign(
            operation_schema(run.operation()),
            &NucleusStatementSigner(caller.kernel.signer()),
            grant.recipient(),
            grant.channel(),
            1,
            run.value_id(),
            run.encode(),
        )
        .unwrap();
        let mut tampered = valid_run.encode();
        *tampered.last_mut().unwrap() ^= 1;
        assert!(matches!(
            recipient.exchange_sql(&tampered),
            Err(LocalSignedExchangeError::Wire(WireError::InvalidSignature))
        ));
        let result =
            SignedResult::decode(&recipient.exchange_sql(&valid_run.encode()).unwrap()).unwrap();
        result
            .verify(&valid_run, &recipient.kernel.verifying_key())
            .unwrap();
        assert!(matches!(
            ServiceResponse::decode(result.payload()).unwrap(),
            ServiceResponse::Run(Ok(ref outcome))
                if matches!(
                    outcome.kind(),
                    covalence_kernel_service::SqlOutcomeKind::Rows { columns, rows }
                        if columns == &["answer"] && rows == &[vec![SqlValue::Integer(42)]]
                )
        ));

        let second_grant = recipient.issue_sql_channel(caller_key).unwrap();
        let (_, cross_channel) = signed_sql_call(
            &caller,
            &mut recipient,
            &second_grant,
            0,
            &ServiceRequest::Run {
                connection,
                statement,
            },
        );
        assert_eq!(
            cross_channel,
            ServiceResponse::Run(Err(SqlRunError::Service(ServiceError::NotFound)))
        );

        let (_, closed) = signed_sql_call(
            &caller,
            &mut recipient,
            &grant,
            2,
            &ServiceRequest::Close { connection },
        );
        assert_eq!(closed, ServiceResponse::Close(Ok(())));

        let revoked_grant = recipient.issue_sql_channel(caller_key).unwrap();
        let (_, opened) = signed_sql_call(
            &caller,
            &mut recipient,
            &revoked_grant,
            0,
            &ServiceRequest::Open,
        );
        let ServiceResponse::Open(Ok(revoked_connection)) = opened else {
            panic!("signed open did not return a revocable connection")
        };
        assert!(recipient.sql_connections.contains_key(&revoked_connection));
        recipient.revoke_sql_channel(caller_key, revoked_grant.channel());
        assert!(!recipient.sql_connections.contains_key(&revoked_connection));
    }

    #[test]
    fn authenticated_malformed_request_consumes_sequence_until_channel_revocation() {
        let caller = LocalKernelService::new(Kernel::ephemeral());
        let mut recipient = LocalKernelService::new(Kernel::ephemeral());
        let caller_key = *caller.kernel.verifying_key().as_bytes();
        let grant = recipient.issue_sql_channel(caller_key).unwrap();
        let malformed = SignedInvocation::sign(
            operation_schema(covalence_kernel_service::Operation::OpenSql),
            &NucleusStatementSigner(caller.kernel.signer()),
            grant.recipient(),
            grant.channel(),
            0,
            O256::from_bytes(b"malformed"),
            b"malformed".to_vec(),
        )
        .unwrap();
        assert!(matches!(
            recipient.exchange_sql(&malformed.encode()),
            Err(LocalSignedExchangeError::Codec(_))
        ));

        let valid = ServiceRequest::Open;
        let replayed_sequence = SignedInvocation::sign(
            operation_schema(valid.operation()),
            &NucleusStatementSigner(caller.kernel.signer()),
            grant.recipient(),
            grant.channel(),
            0,
            valid.value_id(),
            valid.encode(),
        )
        .unwrap();
        assert!(matches!(
            recipient.exchange_sql(&replayed_sequence.encode()),
            Err(LocalSignedExchangeError::Wire(
                WireError::UnexpectedSequence {
                    expected: 1,
                    actual: 0
                }
            ))
        ));
        recipient.revoke_sql_channel(caller_key, grant.channel());
        assert!(
            !recipient
                .sql_channels
                .contains_key(&(caller_key, grant.channel()))
        );
    }

    #[test]
    fn sql_handles_are_service_local_and_runtime_routing_resists_directory_tampering() {
        let mut repl = LocalRepl::new().unwrap();
        let other_kernel = repl.create_local_kernel().unwrap();
        let first = repl.open_sql().unwrap();
        let second = repl.open_sql_on(other_kernel).unwrap();
        assert!(repl.signed_client.grant(KernelId::local()).is_some());
        assert!(repl.signed_client.grant(other_kernel).is_some());
        assert_ne!(
            repl.signed_client.caller_public_key(),
            repl.kernel(KernelId::local()).unwrap().public_key
        );
        assert_ne!(
            repl.signed_client.caller_public_key(),
            repl.kernel(other_kernel).unwrap().public_key
        );
        let remote_handles = repl
            .state()
            .sqlite()
            .prepare("SELECT remote_connection_id FROM repl_connection ORDER BY connection_id")
            .unwrap()
            .query_map([], |row| row.get::<_, String>(0))
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(remote_handles, ["1", "1"]);

        repl.run_sql(first, "CREATE TABLE only_first(value INTEGER) STRICT")
            .unwrap();
        repl.state()
            .sqlite()
            .execute(
                "UPDATE repl_connection SET kernel_id = ?1 WHERE connection_id = ?2",
                sqlite::params![other_kernel.get(), first.get()],
            )
            .unwrap();
        assert_eq!(
            repl.run_sql(
                first,
                "SELECT count(*) FROM sqlite_schema WHERE name = 'only_first'",
            )
            .unwrap(),
            Outcome::Rows(QueryResult {
                columns: vec!["count(*)".to_owned()],
                rows: vec![vec![Value::Integer(1)]],
            })
        );
        assert_eq!(
            repl.run_sql(
                second,
                "SELECT count(*) FROM sqlite_schema WHERE name = 'only_first'",
            )
            .unwrap(),
            Outcome::Rows(QueryResult {
                columns: vec!["count(*)".to_owned()],
                rows: vec![vec![Value::Integer(0)]],
            })
        );
    }

    #[test]
    fn immutable_images_are_shared_within_one_kernel_but_not_across_kernels() {
        let mut repl = LocalRepl::new().unwrap();
        let local = KernelId::local();
        let other = repl.create_local_kernel().unwrap();
        let source = repl.open_sql_on(local).unwrap();
        repl.run_sql(source, "CREATE TABLE payload(value INTEGER) STRICT")
            .unwrap();
        repl.run_sql(source, "INSERT INTO payload VALUES (42)")
            .unwrap();
        let bytes = repl.serialize_main(source).unwrap();
        let image = repl.put_image_for_connection(source, &bytes).unwrap();
        assert!(repl.has_image_on(local, image).unwrap());
        assert!(!repl.has_image_on(other, image).unwrap());

        let first_reader = repl.open_sql_on(local).unwrap();
        let second_reader = repl.open_sql_on(local).unwrap();
        repl.attach_image(first_reader, image, "snapshot").unwrap();
        repl.attach_image(second_reader, image, "snapshot").unwrap();
        for reader in [first_reader, second_reader] {
            assert_eq!(
                repl.run_sql(reader, "SELECT value FROM snapshot.payload")
                    .unwrap(),
                Outcome::Rows(QueryResult {
                    columns: vec!["value".to_owned()],
                    rows: vec![vec![Value::Integer(42)]],
                })
            );
        }

        let other_reader = repl.open_sql_on(other).unwrap();
        assert!(matches!(
            repl.attach_image(other_reader, image, "snapshot"),
            Err(LocalReplError::Service(ServiceError::NotFound))
        ));
        assert_eq!(repl.put_image_on(other, &bytes).unwrap(), image);
        assert!(repl.has_image_on(other, image).unwrap());
        repl.attach_image(other_reader, image, "snapshot").unwrap();
        assert_eq!(
            repl.run_sql(other_reader, "SELECT value FROM snapshot.payload")
                .unwrap(),
            Outcome::Rows(QueryResult {
                columns: vec!["value".to_owned()],
                rows: vec![vec![Value::Integer(42)]],
            })
        );
        let mirrored_kernel_rows = repl
            .state()
            .sqlite()
            .query_row(
                "SELECT count(*) FROM repl_image WHERE image_hash = ?1",
                [image.as_ref()],
                |row| row.get::<_, i64>(0),
            )
            .unwrap();
        assert_eq!(mirrored_kernel_rows, 2);
    }

    #[test]
    fn one_repl_routes_connections_to_independently_keyed_local_kernels() {
        let mut repl = LocalRepl::new().unwrap();
        let first_kernel = KernelId::local();
        let second_kernel = repl.create_local_kernel().unwrap();
        let first_identity = repl.kernel(first_kernel).unwrap();
        let second_identity = repl.kernel(second_kernel).unwrap();
        assert_eq!(first_identity.transport, "local");
        assert_eq!(second_identity.transport, "local");
        assert_ne!(first_identity.public_key, second_identity.public_key);
        repl.state()
            .sqlite()
            .execute(
                "UPDATE repl_kernel SET public_key = zeroblob(32) WHERE kernel_id = ?1",
                [second_kernel.get()],
            )
            .unwrap();
        assert_eq!(
            repl.kernel(second_kernel).unwrap().public_key,
            second_identity.public_key
        );

        let first_sql = repl.open_sql_on(first_kernel).unwrap();
        repl.run_sql(first_sql, "CREATE TABLE only_first(value INTEGER) STRICT")
            .unwrap();
        let second_sql = repl.open_sql_on(second_kernel).unwrap();
        assert_eq!(
            repl.run_sql(
                second_sql,
                "SELECT count(*) FROM sqlite_schema WHERE name = 'only_first'",
            )
            .unwrap(),
            Outcome::Rows(QueryResult {
                columns: vec!["count(*)".to_owned()],
                rows: vec![vec![Value::Integer(0)]],
            })
        );

        let first_hol = repl.open_hol_on(first_kernel).unwrap();
        let mut metadata_schema = HolSchema::new();
        metadata_schema
            .add_column("origin", MetadataType::Text)
            .unwrap();
        metadata_schema
            .add_index("by_origin", ["origin"], false)
            .unwrap();
        let descriptor = HolSchemaDescriptor::from_schema(&metadata_schema).unwrap();
        let second_hol = repl
            .open_hol_with_descriptor_on(second_kernel, descriptor.encode())
            .unwrap();
        repl.hol_mut(second_hol)
            .unwrap()
            .insert_kind_with_metadata(
                &Kind::Star,
                &[("origin", MetadataValue::Text("second".to_owned()))],
            )
            .unwrap();
        repl.state()
            .sqlite()
            .execute(
                "UPDATE repl_connection SET kernel_id = ?1 WHERE connection_id = ?2",
                sqlite::params![second_kernel.get(), first_hol.get()],
            )
            .unwrap();
        let first_snapshot = repl.export_hol_snapshot(first_hol).unwrap();
        let second_snapshot = repl.export_hol_snapshot(second_hol).unwrap();
        assert_eq!(first_snapshot.public_key(), &first_identity.public_key);
        assert_eq!(second_snapshot.public_key(), &second_identity.public_key);
        assert_ne!(first_snapshot.signer(), second_snapshot.signer());
        assert_eq!(second_snapshot.descriptor(), descriptor.encode());
        assert_eq!(
            repl.directory.connection_kernel(first_sql).unwrap(),
            first_kernel
        );
        assert_eq!(
            repl.directory.connection_kernel(first_hol).unwrap(),
            first_kernel
        );
        assert_eq!(
            repl.directory.connection_kernel(second_sql).unwrap(),
            second_kernel
        );
    }

    #[test]
    fn mutable_directory_rows_cannot_reuse_live_runtime_identifiers() {
        let mut repl = LocalRepl::new().unwrap();
        let second_kernel = repl.create_local_kernel().unwrap();
        let second_identity = repl.kernel(second_kernel).unwrap();
        repl.state()
            .sqlite()
            .execute(
                "DELETE FROM repl_kernel WHERE kernel_id = ?1",
                [second_kernel.get()],
            )
            .unwrap();
        let third_kernel = repl.create_local_kernel().unwrap();
        assert_eq!(second_kernel.get(), 1);
        assert_eq!(third_kernel.get(), 2);
        assert_eq!(
            repl.kernel(second_kernel).unwrap().public_key,
            second_identity.public_key
        );

        let first_connection = repl.open_sql().unwrap();
        repl.state()
            .sqlite()
            .execute("UPDATE repl_state SET active_connection_id = NULL", ())
            .unwrap();
        repl.state()
            .sqlite()
            .execute(
                "DELETE FROM repl_connection WHERE connection_id = ?1",
                [first_connection.get()],
            )
            .unwrap();
        let second_connection = repl.open_sql().unwrap();
        assert_eq!(first_connection.get(), 1);
        assert_eq!(second_connection.get(), 2);
        assert_eq!(
            repl.directory.connection_kernel(first_connection).unwrap(),
            KernelId::local()
        );
        repl.run_sql(first_connection, "SELECT 1").unwrap();
    }

    #[test]
    fn shared_namespace_and_signed_snapshot_surface_is_transport_neutral() {
        let mut repl = LocalRepl::new().unwrap();
        let hol = repl.open_hol().unwrap();
        let namespace = repl
            .create_hol_namespace(hol, Some(NamespaceId::root()), Some("demo"))
            .unwrap();
        let star = repl.hol_mut(hol).unwrap().insert_kind(&Kind::Star).unwrap();
        repl.bind_hol_export(
            hol,
            namespace,
            ExportId::from_i64(7),
            NamespaceExport::Kind(star),
            Some("star"),
        )
        .unwrap();
        let snapshot = repl.export_hol_snapshot(hol).unwrap();
        assert_eq!(
            snapshot.image(),
            covalence_lib_hash::O256::from_bytes(snapshot.bytes())
        );
        assert_eq!(
            snapshot.signer(),
            covalence_nucleus::ed25519_key_id(snapshot.public_key())
        );
        assert_eq!(snapshot.signature().len(), 64);
        let validated = covalence_nucleus::ValidatedHolImage::validate(snapshot.bytes()).unwrap();
        assert_eq!(validated.schema(), snapshot.schema());
        assert_eq!(validated.counts().namespaces, 2);
        assert_eq!(validated.counts().namespace_exports, 1);

        let sql = repl.open_sql().unwrap();
        assert!(matches!(
            repl.export_hol_snapshot(sql),
            Err(LocalReplError::WrongProtocol { .. })
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn shared_repl_transports_and_checks_custom_metadata_schemas() {
        let mut schema = HolSchema::new();
        schema
            .add_column("source label", MetadataType::Text)
            .unwrap();
        schema
            .add_index("by source", ["source label"], false)
            .unwrap();
        let descriptor = HolSchemaDescriptor::from_schema(&schema).unwrap();
        let mut repl = LocalRepl::new().unwrap();
        let source_identity = repl.kernel(KernelId::local()).unwrap();
        let target_kernel = repl.create_local_kernel().unwrap();
        let target_identity = repl.kernel(target_kernel).unwrap();
        let source = repl.open_hol_with_descriptor(descriptor.encode()).unwrap();
        let target = repl.open_hol_on(target_kernel).unwrap();
        let star = repl
            .hol_mut(source)
            .unwrap()
            .insert_kind_with_metadata(
                &Kind::Star,
                &[("source label", MetadataValue::Text("demo".to_owned()))],
            )
            .unwrap();
        let source_namespace = repl
            .create_hol_namespace(source, None, Some("custom"))
            .unwrap();
        repl.bind_hol_export(
            source,
            source_namespace,
            ExportId::from_i64(9),
            NamespaceExport::Kind(star),
            Some("star"),
        )
        .unwrap();
        let snapshot = repl.export_hol_snapshot(source).unwrap();
        assert_eq!(snapshot.public_key(), &source_identity.public_key);
        assert_eq!(snapshot.descriptor(), descriptor.encode());
        assert_eq!(
            HolSchemaDescriptor::decode(snapshot.descriptor())
                .unwrap()
                .schema_id(),
            snapshot.schema()
        );

        let trusted = repl
            .trust_hol_import(
                target,
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
            )
            .unwrap();
        let imported_namespace = repl
            .create_hol_imported_namespace(
                target,
                None,
                Some("custom"),
                trusted.import(),
                source_namespace.get(),
            )
            .unwrap();
        assert_eq!(
            repl.inspect_trusted_hol_export_with_descriptor(
                target,
                trusted.trusted_import(),
                snapshot.bytes(),
                snapshot.descriptor(),
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
                imported_namespace,
                ExportId::from_i64(9),
            )
            .unwrap(),
            Some(LocalImportedHolExport {
                connection: target,
                trusted_import: trusted.trusted_import(),
                import: trusted.import(),
                namespace: imported_namespace,
                export: ExportId::from_i64(9),
                value: LocalImportedHolValue::Kind(star.get()),
            })
        );

        let empty = HolSchemaDescriptor::from_schema(&HolSchema::new()).unwrap();
        assert!(matches!(
            repl.inspect_trusted_hol_export_with_descriptor(
                target,
                trusted.trusted_import(),
                snapshot.bytes(),
                empty.encode(),
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
                imported_namespace,
                ExportId::from_i64(9),
            ),
            Err(LocalReplError::HolImageValidation(
                AuthenticatedHolImageValidationError::SchemaMismatch { .. }
            ))
        ));
        assert!(matches!(
            repl.inspect_trusted_hol_export_with_descriptor(
                target,
                trusted.trusted_import(),
                snapshot.bytes(),
                b"malformed",
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
                imported_namespace,
                ExportId::from_i64(9),
            ),
            Err(LocalReplError::HolSchemaDescriptor(_))
        ));
        let mut bad_signature = snapshot.signature().to_vec();
        bad_signature[0] ^= 1;
        assert!(matches!(
            repl.inspect_trusted_hol_export_with_descriptor(
                target,
                trusted.trusted_import(),
                snapshot.bytes(),
                b"malformed",
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                &bad_signature,
                imported_namespace,
                ExportId::from_i64(9),
            ),
            Err(LocalReplError::SnapshotAuthentication(_))
        ));
        let target_snapshot = repl.export_hol_snapshot(target).unwrap();
        assert_eq!(
            repl.hol_trusted_import(target, trusted.trusted_import())
                .unwrap(),
            trusted
        );
        assert_eq!(target_snapshot.public_key(), &target_identity.public_key);
        assert_ne!(target_snapshot.signer(), snapshot.signer());
        let target_image = ValidatedHolImage::validate(target_snapshot.bytes()).unwrap();
        assert_eq!(target_image.counts().untrusted_trusted_import_rows, 1);
    }

    #[test]
    fn shared_json_metadata_api_preserves_typed_values_on_any_local_kernel() {
        let schema = r#"{
            "version": 1,
            "columns": [
                {"table":"node","name":"source label","storage":"text"},
                {"table":"node","name":"priority","storage":"integer"},
                {"table":"node","name":"ratio","storage":"real"},
                {"table":"node","name":"payload","storage":"blob"}
            ],
            "indexes": [
                {"table":"node","name":"by source","columns":["source label"]}
            ]
        }"#;
        let mut repl = LocalRepl::new().unwrap();
        let kernel = repl.create_local_kernel().unwrap();
        let hol = repl.open_hol_with_schema_json_on(kernel, schema).unwrap();
        let star = repl.hol_mut(hol).unwrap().insert_kind(&Kind::Star).unwrap();
        let set = format!(
            r#"{{"target":{{"kind":"node","id":{}}},"assignments":[
                {{"column":"source label","value":{{"kind":"text","value":"demo value"}}}},
                {{"column":"priority","value":{{"kind":"integer","value":"9223372036854775807"}}}},
                {{"column":"ratio","value":{{"kind":"real","value":"1.5"}}}},
                {{"column":"payload","value":{{"kind":"blob","hex":"00ff80"}}}}
            ]}}"#,
            star.get()
        );
        repl.set_hol_metadata_json(hol, &set).unwrap();
        let get = format!(
            r#"{{"target":{{"kind":"node","id":{}}},"columns":["payload","priority","source label","ratio"]}}"#,
            star.get()
        );
        assert_eq!(
            repl.hol_metadata_json(hol, &get).unwrap(),
            r#"[{"kind":"blob","hex":"00ff80"},{"kind":"integer","value":"9223372036854775807"},{"kind":"text","value":"demo value"},{"kind":"real","value":"1.5"}]"#
        );
        let clear = format!(
            r#"{{"target":{{"kind":"node","id":{}}},"assignments":[{{"column":"payload","value":{{"kind":"null"}}}}]}}"#,
            star.get()
        );
        repl.set_hol_metadata_json(hol, &clear).unwrap();
        assert_eq!(
            repl.hol_metadata_json(hol, &get).unwrap(),
            r#"[{"kind":"null"},{"kind":"integer","value":"9223372036854775807"},{"kind":"text","value":"demo value"},{"kind":"real","value":"1.5"}]"#
        );
    }

    #[test]
    fn resident_hol_admission_is_operational_and_schema_qualified() {
        let mut repl = LocalRepl::new().unwrap();
        let source = repl.open_hol().unwrap();
        let target = repl.open_hol().unwrap();
        let star = repl
            .hol_mut(source)
            .unwrap()
            .insert_kind(&Kind::Star)
            .unwrap();
        repl.bind_hol_export(
            source,
            NamespaceId::root(),
            ExportId::from_i64(5),
            NamespaceExport::Kind(star),
            Some("star"),
        )
        .unwrap();
        let snapshot = repl.export_hol_snapshot(source).unwrap();
        let trusted = repl
            .trust_hol_import(
                target,
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
            )
            .unwrap();
        let namespace = repl
            .create_hol_imported_namespace(target, None, Some("resident"), trusted.import(), 0)
            .unwrap();
        assert!(matches!(
            repl.inspect_resident_trusted_hol_export(
                target,
                trusted.trusted_import(),
                snapshot.image(),
                namespace,
                ExportId::from_i64(5),
            ),
            Err(LocalReplError::Image(
                ReplImageError::MissingHolImage { .. }
            ))
        ));
        assert_eq!(
            repl.put_signed_hol_snapshot_with_descriptor(
                snapshot.bytes(),
                snapshot.descriptor(),
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
            )
            .unwrap(),
            snapshot.image()
        );
        assert_eq!(
            repl.inspect_resident_trusted_hol_export(
                target,
                trusted.trusted_import(),
                snapshot.image(),
                namespace,
                ExportId::from_i64(5),
            )
            .unwrap()
            .unwrap()
            .value,
            LocalImportedHolValue::Kind(star.get())
        );
        assert_eq!(repl.resident_image_count(), 1);
        let rows = repl
            .state()
            .sqlite()
            .query_row("SELECT count(*) FROM repl_hol_image", (), |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(rows, 1);
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn shared_repl_trusts_one_hash_first_snapshot_across_connections() {
        let mut repl = LocalRepl::new().unwrap();
        let source = repl.open_hol().unwrap();
        let target = repl.open_hol().unwrap();
        let observer = repl.open_hol().unwrap();
        let truth = repl
            .hol_mut(source)
            .unwrap()
            .insert_bool_term(true)
            .unwrap();
        let namespace = repl
            .create_hol_namespace(source, None, Some("downloaded"))
            .unwrap();
        repl.bind_hol_export(
            source,
            namespace,
            ExportId::from_i64(7),
            NamespaceExport::Term(truth),
            Some("truth"),
        )
        .unwrap();
        let snapshot = repl.export_hol_snapshot(source).unwrap();
        repl.close(source).unwrap();

        let trusted = repl
            .trust_hol_import(
                target,
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
            )
            .unwrap();
        assert_eq!(trusted.database().schema(), snapshot.schema());
        assert_eq!(trusted.database().image(), snapshot.image());
        assert_eq!(trusted.signer(), snapshot.signer());
        assert!(matches!(
            repl.inspect_trusted_hol_export(
                target,
                trusted.trusted_import(),
                snapshot.bytes(),
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
                NamespaceId::root(),
                ExportId::from_i64(7),
            ),
            Err(LocalReplError::ImportedReader(ImportedReaderError::Import(
                ImportError::LocalNamespace(_)
            )))
        ));
        let imported_namespace = repl
            .create_hol_imported_namespace(
                target,
                None,
                Some("downloaded"),
                trusted.import(),
                namespace.get(),
            )
            .unwrap();
        let before_inspection = repl.export_hol_snapshot(target).unwrap();
        assert_eq!(
            repl.inspect_trusted_hol_export_with_descriptor(
                target,
                trusted.trusted_import(),
                snapshot.bytes(),
                snapshot.descriptor(),
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
                imported_namespace,
                ExportId::from_i64(7),
            )
            .unwrap(),
            Some(LocalImportedHolExport {
                connection: target,
                trusted_import: trusted.trusted_import(),
                import: trusted.import(),
                namespace: imported_namespace,
                export: ExportId::from_i64(7),
                value: LocalImportedHolValue::Term {
                    id: truth.get(),
                    term: LocalImportedHolTerm::Bool(true),
                },
            })
        );
        let after_inspection = repl.export_hol_snapshot(target).unwrap();
        assert_eq!(before_inspection.bytes(), after_inspection.bytes());
        assert_eq!(
            repl.hol_trusted_import(target, trusted.trusted_import())
                .unwrap(),
            trusted
        );
        assert!(matches!(
            repl.hol_trusted_import(observer, trusted.trusted_import()),
            Err(LocalReplError::TrustedImport(
                TrustedImportError::UnknownTrustedImport(_)
            ))
        ));
        assert!(matches!(
            repl.inspect_resident_trusted_hol_export(
                observer,
                trusted.trusted_import(),
                snapshot.image(),
                imported_namespace,
                ExportId::from_i64(7),
            ),
            Err(LocalReplError::TrustedImport(
                TrustedImportError::UnknownTrustedImport(_)
            ))
        ));
        assert_eq!(repl.resident_image_count(), 1);

        let exported_target = repl.export_hol_snapshot(target).unwrap();
        let validated =
            covalence_nucleus::ValidatedHolImage::validate(exported_target.bytes()).unwrap();
        assert_eq!(validated.counts().import_references, 1);
        assert_eq!(validated.counts().untrusted_trusted_import_rows, 1);

        let observer_trusted = repl
            .trust_hol_import(
                observer,
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
            )
            .unwrap();
        let observer_namespace = repl
            .create_hol_imported_namespace(
                observer,
                None,
                Some("downloaded"),
                observer_trusted.import(),
                namespace.get(),
            )
            .unwrap();
        repl.close(target).unwrap();
        assert_eq!(
            repl.inspect_resident_trusted_hol_export(
                observer,
                observer_trusted.trusted_import(),
                snapshot.image(),
                observer_namespace,
                ExportId::from_i64(7),
            )
            .unwrap()
            .unwrap()
            .connection,
            observer
        );
        assert_eq!(repl.resident_image_count(), 1);
    }

    #[test]
    fn shared_repl_rejects_tampered_attestations_before_import_state() {
        let mut repl = LocalRepl::new().unwrap();
        let source = repl.open_hol().unwrap();
        let target = repl.open_hol().unwrap();
        let snapshot = repl.export_hol_snapshot(source).unwrap();
        let mut signature = snapshot.signature().to_vec();
        signature[0] ^= 1;

        assert!(matches!(
            repl.trust_hol_import(
                target,
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                &signature,
            ),
            Err(LocalReplError::SnapshotAuthentication(_))
        ));
        let exported_target = repl.export_hol_snapshot(target).unwrap();
        let validated =
            covalence_nucleus::ValidatedHolImage::validate(exported_target.bytes()).unwrap();
        assert_eq!(validated.counts().import_references, 0);
        assert_eq!(validated.counts().untrusted_trusted_import_rows, 0);
    }

    #[test]
    fn shared_repl_makes_snapshot_signer_trust_and_exact_import_acceptance_explicit() {
        let mut repl = LocalRepl::new().unwrap();
        let source = repl.open_hol().unwrap();
        let target = repl.open_hol().unwrap();
        let snapshot = repl.export_hol_snapshot(source).unwrap();
        let claim = LocalRepl::authenticate_hol_snapshot_claim(
            snapshot.schema(),
            snapshot.image(),
            snapshot.signer(),
            *snapshot.public_key(),
            snapshot.signature(),
        )
        .unwrap();

        assert!(!repl.hol_snapshot_signer_is_trusted(target, &claim).unwrap());
        assert!(!repl.hol_snapshot_claim_is_accepted(target, &claim).unwrap());
        assert!(matches!(
            repl.accept_hol_import(target, &claim),
            Err(LocalReplError::SnapshotTrust(
                SnapshotTrustError::UntrustedSigner(_)
            ))
        ));
        assert!(!repl.hol_snapshot_signer_is_trusted(target, &claim).unwrap());
        assert!(!repl.hol_snapshot_claim_is_accepted(target, &claim).unwrap());
        let before_trust = repl.export_hol_snapshot(target).unwrap();
        let validated = ValidatedHolImage::validate(before_trust.bytes()).unwrap();
        assert_eq!(validated.counts().import_references, 0);
        assert_eq!(validated.counts().untrusted_trusted_import_rows, 0);

        repl.trust_hol_snapshot_signer(target, &claim).unwrap();
        assert!(repl.hol_snapshot_signer_is_trusted(target, &claim).unwrap());
        assert!(!repl.hol_snapshot_claim_is_accepted(target, &claim).unwrap());

        let trusted = repl.accept_hol_import(target, &claim).unwrap();
        assert!(repl.hol_snapshot_claim_is_accepted(target, &claim).unwrap());
        assert_eq!(trusted.database().schema(), snapshot.schema());
        assert_eq!(trusted.database().image(), snapshot.image());
        assert_eq!(trusted.signer(), snapshot.signer());
        let persisted = repl
            .hol_mut(target)
            .unwrap()
            .trusted_import(trusted.trusted_import())
            .unwrap();
        assert_eq!(persisted.import, trusted.import());
        assert_eq!(persisted.signer, snapshot.signer());
        assert_eq!(&persisted.public_key, snapshot.public_key());
        assert_eq!(persisted.signature, snapshot.signature());

        let after_acceptance = repl.export_hol_snapshot(target).unwrap();
        let validated = ValidatedHolImage::validate(after_acceptance.bytes()).unwrap();
        assert_eq!(validated.counts().import_references, 1);
        assert_eq!(validated.counts().untrusted_trusted_import_rows, 1);
    }

    #[test]
    fn valid_but_untrusted_image_is_not_admitted_to_the_shared_cache() {
        let mut repl = LocalRepl::new().unwrap();
        let source = repl.open_hol().unwrap();
        let observer = repl.open_hol().unwrap();
        let snapshot = repl.export_hol_snapshot(source).unwrap();

        assert!(matches!(
            repl.inspect_trusted_hol_export_with_descriptor(
                observer,
                TrustedImportId::from_i64(0),
                snapshot.bytes(),
                snapshot.descriptor(),
                snapshot.schema(),
                snapshot.image(),
                snapshot.signer(),
                *snapshot.public_key(),
                snapshot.signature(),
                NamespaceId::root(),
                ExportId::from_i64(0),
            ),
            Err(LocalReplError::TrustedImportImage(
                TrustedImportImageError::Unknown(_)
            ))
        ));
        assert_eq!(repl.resident_image_count(), 0);
        assert_eq!(repl.resident_image_bytes(), 0);
    }

    #[test]
    fn shared_repl_reconstructs_exact_weakening_capabilities() {
        let mut repl = LocalRepl::new().unwrap();
        let id = repl.open_hol().unwrap();
        let bool_type = repl.hol_mut(id).unwrap().insert_bool_type().unwrap();
        let p = repl
            .hol_mut(id)
            .unwrap()
            .insert_free_term(20, bool_type)
            .unwrap();
        let q = repl
            .hol_mut(id)
            .unwrap()
            .insert_free_term(21, bool_type)
            .unwrap();
        let consequent = repl.hol_mut(id).unwrap().define_context([p]).unwrap();
        let antecedent = repl.hol_mut(id).unwrap().define_context([p, q]).unwrap();
        let equality = repl
            .hol_mut(id)
            .unwrap()
            .with_proof_session(|mut proof| {
                let witness = proof.prove_hypothesis(antecedent, p)?;
                let equality = proof.prove_reflexivity(consequent, p)?;
                proof.persist_theorem(&witness)?;
                proof.persist_theorem(&equality)?;
                Ok::<_, ProofError>((witness.conclusion(), equality.conclusion()))
            })
            .unwrap();
        assert!(
            !repl
                .hol_mut(id)
                .unwrap()
                .proved_judgement(antecedent, equality.1)
                .unwrap()
        );

        repl.prove_context_implication(id, antecedent, consequent, &[equality.0])
            .unwrap();
        assert_eq!(
            repl.weaken(id, antecedent, consequent, equality.1).unwrap(),
            equality.1
        );
        assert_eq!(
            repl.equality_modus_ponens(id, antecedent, equality.1, p)
                .unwrap(),
            p
        );
        assert!(
            repl.hol_mut(id)
                .unwrap()
                .proved_judgement(antecedent, equality.1)
                .unwrap()
        );
    }
}
