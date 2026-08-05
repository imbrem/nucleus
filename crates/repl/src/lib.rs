//! Transport-neutral REPL orchestration.
//!
//! A [`Repl`] is not a Nucleus connection protocol. It maintains an ordinary,
//! inspectable `SQLite` directory in a raw Neutron connection and associates its
//! rows with runtime connection handles owned by the current process.

use std::collections::HashMap;
use std::error::Error as StdError;
use std::fmt;
use std::str::FromStr;
use std::sync::Arc;

use covalence_lib_sqlite as sqlite;

pub mod hol_recipes;

#[cfg(not(target_arch = "wasm32"))]
mod hol_guest;
#[cfg(not(target_arch = "wasm32"))]
pub use covalence_proton::WasmtimeComponentLimits;
#[cfg(not(target_arch = "wasm32"))]
pub use hol_guest::{
    HolGuestError, ManagedHolGuestError, ManagedHolGuestResult, retain_signed_hol_guest_artifact,
    run_hol_proof_component, run_managed_hol_proof_component,
};

pub use covalence_nucleus::sql::{
    ImageError, MAX_IMAGE_BYTES, Outcome, QueryResult, Statement, Value,
};
pub use covalence_nucleus::{AllowAll, Connection, ContextId, Hol, Kernel, Sql, TermId};
use covalence_nucleus::{
    AuthenticatedValidatedHolImage, ExportId, HolDatabaseRef, ImportedExport, ImportedTermView,
    NamespaceExport, ProofError, SignedSnapshotEnvelope, TermError, TypeError,
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
CREATE TABLE repl_state (
    singleton INTEGER PRIMARY KEY CHECK (singleton = 0),
    active_connection_id INTEGER REFERENCES repl_connection
) STRICT;
INSERT INTO repl_state(singleton) VALUES (0);
";

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

/// A connection directory backed by its own raw `SQLite` database.
pub struct Repl<C> {
    state: covalence_neutron::Connection,
    connections: HashMap<ConnectionId, C>,
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
        })
    }

    /// Returns the raw state connection for inspection and debugging.
    #[must_use]
    pub const fn state(&self) -> &covalence_neutron::Connection {
        &self.state
    }

    /// Adds a runtime handle and records its protocol in the state database.
    ///
    /// # Errors
    ///
    /// Returns an error if the directory cannot be updated.
    pub fn insert(&mut self, protocol: &str, connection: C) -> Result<ConnectionId, ReplError> {
        let transaction = self.state.sqlite().unchecked_transaction()?;
        transaction.execute(
            "INSERT INTO repl_connection(kernel_id, protocol) VALUES (0, ?1)",
            [protocol],
        )?;
        let id = ConnectionId(transaction.last_insert_rowid());
        transaction.execute(
            "UPDATE repl_state
             SET active_connection_id = COALESCE(active_connection_id, ?1)
             WHERE singleton = 0",
            [id.0],
        )?;
        transaction.commit()?;
        self.connections.insert(id, connection);
        Ok(id)
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
            .ok_or(ReplError::UnknownConnection(id))
    }

    /// Runs one row-returning SQL statement against the REPL state database.
    ///
    /// The directory is ordinary `SQLite` and carries no logical trust, so
    /// front ends may expose this directly for debugging. The statement runs
    /// under `PRAGMA query_only`, so inspection cannot mutate the directory.
    ///
    /// # Errors
    ///
    /// Returns an error if the statement is invalid, returns no columns, or
    /// fails while executing.
    pub fn inspect_state(&self, sql: &str) -> Result<QueryResult, ReplError> {
        let connection = self.state.sqlite();
        connection.pragma_update(None, "query_only", true)?;
        let result = Self::query_state(connection, sql);
        connection.pragma_update(None, "query_only", false)?;
        result
    }

    fn query_state(connection: &sqlite::Connection, sql: &str) -> Result<QueryResult, ReplError> {
        let mut statement = connection.prepare(sql)?;
        let columns: Vec<String> = statement
            .column_names()
            .into_iter()
            .map(str::to_owned)
            .collect();
        if columns.is_empty() {
            return Err(ReplError::StateQueryReturnsNoRows);
        }
        let mut query = statement.query(())?;
        let mut rows = Vec::new();
        while let Some(row) = query.next()? {
            let mut values = Vec::with_capacity(columns.len());
            for index in 0..columns.len() {
                values.push(Value::from(row.get::<_, sqlite::types::Value>(index)?));
            }
            rows.push(values);
        }
        Ok(QueryResult { columns, rows })
    }

    fn require(&self, id: ConnectionId) -> Result<(), ReplError> {
        if self.connections.contains_key(&id) {
            Ok(())
        } else {
            Err(ReplError::UnknownConnection(id))
        }
    }
}

/// A process-local connection managed by the terminal or browser adapter.
///
/// This sum belongs above Nucleus's protocol boundary. It lets one REPL
/// directory select heterogeneous connections without making `Repl` itself a
/// protocol or weakening either connection's type.
pub enum LocalConnection {
    /// An unrestricted raw `SQLite` connection.
    Sql(Connection<Sql>),
    /// A rank-zero HOL connection using the demo's permissive policy.
    Hol(Connection<Hol<AllowAll>>),
}

impl LocalConnection {
    /// Returns the stable protocol name recorded in the REPL state database.
    #[must_use]
    pub const fn protocol(&self) -> &'static str {
        match self {
            Self::Sql(_) => "nucleus/sql",
            Self::Hol(_) => "nucleus/hol",
        }
    }

    /// Borrows this connection as SQL.
    ///
    /// # Errors
    ///
    /// Returns an error when the selected connection is HOL.
    pub const fn sql_mut(&mut self) -> Result<&mut Connection<Sql>, ConnectionKindError> {
        match self {
            Self::Sql(connection) => Ok(connection),
            Self::Hol(_) => Err(ConnectionKindError::ExpectedSql),
        }
    }

    /// Borrows this connection as HOL.
    ///
    /// # Errors
    ///
    /// Returns an error when the selected connection is SQL.
    pub const fn hol_mut(&mut self) -> Result<&mut Connection<Hol<AllowAll>>, ConnectionKindError> {
        match self {
            Self::Hol(connection) => Ok(connection),
            Self::Sql(_) => Err(ConnectionKindError::ExpectedHol),
        }
    }
}

/// A selected local connection has the wrong protocol for an operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConnectionKindError {
    /// A SQL operation selected a HOL connection.
    ExpectedSql,
    /// A HOL operation selected a SQL connection.
    ExpectedHol,
}

impl fmt::Display for ConnectionKindError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExpectedSql => formatter.write_str("selected connection is not SQL"),
            Self::ExpectedHol => formatter.write_str("selected connection is not HOL"),
        }
    }
}

impl StdError for ConnectionKindError {}

/// Completed stages of the signed HOL round trip.
///
/// The list is stable presentation data for terminal and browser adapters. It
/// is not a proof trace: each stage reports a boundary crossed by the shared
/// orchestration code, while the database persists only canonical kernel
/// state.
pub const SIGNED_HOL_PHASES: &[&str] = &[
    "proof-persisted",
    "namespace-exported",
    "snapshot-signed",
    "signature-authenticated",
    "image-detached-validated",
    "signer-trusted",
    "snapshot-accepted",
    "namespace-imported",
    "theorem-read",
];

/// Exact producer artifact transported between independent HOL connections.
///
/// This is an above-TCB demo carrier, not a stabilized wire format. The
/// receiver treats every field as untrusted and establishes authentication,
/// structural validity, and connection-local trust independently.
#[derive(Clone)]
pub struct SignedHolArtifact {
    namespace_id: i64,
    image: Vec<u8>,
    schema: covalence_lib_hash::O256,
    image_hash: covalence_lib_hash::O256,
    signer: covalence_lib_hash::O256,
    public_key: Vec<u8>,
    signature: Vec<u8>,
}

/// Producer-local presentation paired with an independently transportable artifact.
pub struct ProducedSignedHol {
    proof: HolRecipeResult,
    artifact: SignedHolArtifact,
}

/// Receiver-local coordinates established from one [`SignedHolArtifact`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ReceivedHolSnapshot {
    import: i64,
    namespace: i64,
    context: i64,
    conclusion: i64,
}

/// Result shared by the terminal and browser signed-snapshot demonstrations.
pub struct SignedHolRoundTripResult {
    produced: ProducedSignedHol,
    received: ReceivedHolSnapshot,
}

impl SignedHolArtifact {
    /// Reconstructs untrusted transport fields without authenticating them.
    ///
    /// This parses hash coordinates and checks fixed-width fields only.
    /// [`receive_signed_hol_artifact`] performs every semantic check.
    ///
    /// # Errors
    ///
    /// Returns an error for a negative namespace, malformed hash, or wrong
    /// public-key/signature width.
    pub fn from_untrusted_parts(
        namespace_id: i64,
        image: Vec<u8>,
        schema: &str,
        image_hash: &str,
        signer: &str,
        public_key: Vec<u8>,
        signature: Vec<u8>,
    ) -> Result<Self, SignedHolArtifactError> {
        if namespace_id < 0 {
            return Err(SignedHolArtifactError("namespace ID must be non-negative"));
        }
        if public_key.len() != 32 {
            return Err(SignedHolArtifactError("public key must be 32 bytes"));
        }
        if signature.len() != 64 {
            return Err(SignedHolArtifactError("signature must be 64 bytes"));
        }
        Ok(Self {
            namespace_id,
            image,
            schema: covalence_lib_hash::O256::from_hex(schema)
                .map_err(|_| SignedHolArtifactError("schema must be an O256 hex string"))?,
            image_hash: covalence_lib_hash::O256::from_hex(image_hash)
                .map_err(|_| SignedHolArtifactError("image must be an O256 hex string"))?,
            signer: covalence_lib_hash::O256::from_hex(signer)
                .map_err(|_| SignedHolArtifactError("signer must be an O256 hex string"))?,
            public_key,
            signature,
        })
    }

    /// Returns the source namespace exported by this demonstration.
    #[must_use]
    pub const fn namespace_id(&self) -> i64 {
        self.namespace_id
    }

    /// Returns the exact signed `SQLite` bytes.
    #[must_use]
    pub fn image(&self) -> &[u8] {
        &self.image
    }

    /// Returns the signed HOL schema coordinate.
    #[must_use]
    pub const fn schema(&self) -> covalence_lib_hash::O256 {
        self.schema
    }

    /// Returns the claimed exact image coordinate.
    #[must_use]
    pub const fn image_hash(&self) -> covalence_lib_hash::O256 {
        self.image_hash
    }

    /// Returns the claimed signer identity.
    #[must_use]
    pub const fn signer(&self) -> covalence_lib_hash::O256 {
        self.signer
    }

    /// Returns the claimed Ed25519 public key.
    #[must_use]
    pub fn public_key(&self) -> &[u8] {
        &self.public_key
    }

    /// Returns the claimed schema-qualified snapshot signature.
    #[must_use]
    pub fn signature(&self) -> &[u8] {
        &self.signature
    }

    /// Renders a deliberately demo-local text sidecar for downloading artifacts.
    ///
    /// This is presentation output rather than a stable inter-kernel codec.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        format!(
            "format=covalence-repl-signed-snapshot-demo-v0\nnamespace={}\nschema={}\nimage={}\nsigner={}\npublic_key={}\nsignature={}\n",
            self.namespace_id,
            self.schema,
            self.image_hash,
            self.signer,
            hex(&self.public_key),
            hex(&self.signature),
        )
    }
}

/// Malformed above-TCB signed-HOL transport fields.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SignedHolArtifactError(&'static str);

impl fmt::Display for SignedHolArtifactError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.0)
    }
}

impl StdError for SignedHolArtifactError {}

impl ProducedSignedHol {
    /// Returns the producer-local persisted proof presentation.
    #[must_use]
    pub const fn proof(&self) -> &HolRecipeResult {
        &self.proof
    }

    /// Returns the independently transportable signed artifact.
    #[must_use]
    pub const fn artifact(&self) -> &SignedHolArtifact {
        &self.artifact
    }

    /// Separates producer-local presentation from transport ownership.
    #[must_use]
    pub fn into_parts(self) -> (HolRecipeResult, SignedHolArtifact) {
        (self.proof, self.artifact)
    }
}

impl ReceivedHolSnapshot {
    /// Returns the receiver's inert import-directory ID.
    #[must_use]
    pub const fn import_id(self) -> i64 {
        self.import
    }

    /// Returns the receiver's imported namespace alias ID.
    #[must_use]
    pub const fn namespace_id(self) -> i64 {
        self.namespace
    }

    /// Returns the imported empty-context source coordinate.
    #[must_use]
    pub const fn context_id(self) -> i64 {
        self.context
    }

    /// Returns the imported conclusion source coordinate.
    #[must_use]
    pub const fn conclusion_id(self) -> i64 {
        self.conclusion
    }
}

impl SignedHolRoundTripResult {
    /// Combines completed producer and receiver halves for presentation.
    #[must_use]
    pub const fn from_parts(produced: ProducedSignedHol, received: ReceivedHolSnapshot) -> Self {
        Self { produced, received }
    }

    /// Returns `signed-hol-round-trip`, the shared frontend discriminant.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "signed-hol-round-trip"
    }

    /// Returns each successfully completed trust-boundary stage in order.
    #[must_use]
    pub const fn phases(&self) -> &'static [&'static str] {
        SIGNED_HOL_PHASES
    }

    /// Returns the local proof result persisted before serialization.
    #[must_use]
    pub const fn proof(&self) -> &HolRecipeResult {
        self.produced.proof()
    }

    /// Returns the source database's exported namespace ID.
    #[must_use]
    pub const fn namespace_id(&self) -> i64 {
        self.produced.artifact().namespace_id()
    }

    /// Returns the exact signed `SQLite` database image.
    #[must_use]
    pub fn image(&self) -> &[u8] {
        self.produced.artifact().image()
    }

    /// Returns the signed interpretation-qualified HOL schema hash.
    #[must_use]
    pub const fn schema(&self) -> covalence_lib_hash::O256 {
        self.produced.artifact().schema()
    }

    /// Returns the hash of the exact exported database bytes.
    #[must_use]
    pub const fn image_hash(&self) -> covalence_lib_hash::O256 {
        self.produced.artifact().image_hash()
    }

    /// Returns the producer key identity.
    #[must_use]
    pub const fn signer(&self) -> covalence_lib_hash::O256 {
        self.produced.artifact().signer()
    }

    /// Returns the producer's Ed25519 public key.
    #[must_use]
    pub fn public_key(&self) -> &[u8] {
        self.produced.artifact().public_key()
    }

    /// Returns the signature over the schema-qualified image statement.
    #[must_use]
    pub fn signature(&self) -> &[u8] {
        self.produced.artifact().signature()
    }

    /// Returns the receiver's inert import-directory ID.
    #[must_use]
    pub const fn import_id(&self) -> i64 {
        self.received.import_id()
    }

    /// Returns the receiver's imported namespace alias ID.
    #[must_use]
    pub const fn imported_namespace_id(&self) -> i64 {
        self.received.namespace_id()
    }

    /// Returns the source coordinate of the imported empty context.
    #[must_use]
    pub const fn imported_context_id(&self) -> i64 {
        self.received.context_id()
    }

    /// Returns the source coordinate of the imported beta conclusion.
    #[must_use]
    pub const fn imported_conclusion_id(&self) -> i64 {
        self.received.conclusion_id()
    }

    /// Renders a deliberately demo-local text sidecar for downloading artifacts.
    ///
    /// This is presentation output rather than a stable inter-kernel codec.
    #[must_use]
    pub fn attestation_text(&self) -> String {
        self.produced.artifact().attestation_text()
    }
}

fn hex(bytes: &[u8]) -> String {
    use fmt::Write as _;

    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(encoded, "{byte:02x}").expect("writing to a String cannot fail");
    }
    encoded
}

/// Failure of one explicitly named signed-snapshot demonstration phase.
#[derive(Debug)]
pub struct SignedHolRoundTripError {
    phase: &'static str,
    message: String,
}

impl SignedHolRoundTripError {
    fn at<E: fmt::Display>(phase: &'static str, error: E) -> Self {
        Self {
            phase,
            message: error.to_string(),
        }
    }

    fn invalid(phase: &'static str, message: &'static str) -> Self {
        Self {
            phase,
            message: message.to_owned(),
        }
    }

    /// Returns the stage which rejected the operation.
    #[must_use]
    pub const fn phase(&self) -> &'static str {
        self.phase
    }
}

impl fmt::Display for SignedHolRoundTripError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.phase, self.message)
    }
}

impl StdError for SignedHolRoundTripError {}

/// Proves and persists beta, exports a namespace, and signs the exact database.
///
/// # Errors
///
/// Returns the name and message of the first rejected producer stage.
pub fn produce_signed_hol_artifact(
    producer: &Kernel,
    source: &mut Connection<Hol<AllowAll>>,
) -> Result<ProducedSignedHol, SignedHolRoundTripError> {
    let proof = HolRecipe::Beta(true)
        .execute(source)
        .map_err(|error| SignedHolRoundTripError::at("proof-persisted", error))?;

    let namespace = source
        .create_namespace(None, Some("beta-demo"))
        .map_err(|error| SignedHolRoundTripError::at("namespace-exported", error))?;
    source
        .export_value(
            namespace,
            ExportId::from_i64(0),
            NamespaceExport::Context(ContextId::empty()),
            Some("empty-context"),
        )
        .map_err(|error| SignedHolRoundTripError::at("namespace-exported", error))?;
    source
        .export_value(
            namespace,
            ExportId::from_i64(1),
            NamespaceExport::Term(covalence_nucleus::TermId::from_i64(proof.conclusion_id())),
            Some("beta-conclusion"),
        )
        .map_err(|error| SignedHolRoundTripError::at("namespace-exported", error))?;

    let signed_snapshot = producer
        .export_hol(source)
        .map_err(|error| SignedHolRoundTripError::at("snapshot-signed", error))?;
    let attestation = signed_snapshot.attestation();
    let image = signed_snapshot.image().bytes().to_vec();
    let schema = attestation.schema();
    let image_hash = attestation.image();
    let signer_id = attestation.signer();
    let public_key = *attestation.public_key();
    let signature = attestation.signature().to_vec();

    Ok(ProducedSignedHol {
        proof,
        artifact: SignedHolArtifact {
            namespace_id: namespace.get(),
            image,
            schema,
            image_hash,
            signer: signer_id,
            public_key: public_key.to_vec(),
            signature,
        },
    })
}

/// Authenticates, validates, trusts, imports, and reads one transported artifact.
///
/// The caller supplies the receiver connection explicitly, so it remains in
/// the REPL and its connection-local trust and persistent import state can be
/// inspected after this operation. Imported theorem authority remains scoped
/// to the immutable reader and is never promoted to a local LCF theorem.
///
/// # Errors
///
/// Returns the name and message of the first rejected receiver stage.
pub fn receive_signed_hol_artifact(
    target: &mut Connection<Hol<AllowAll>>,
    artifact: &SignedHolArtifact,
) -> Result<ReceivedHolSnapshot, SignedHolRoundTripError> {
    let validated = authenticate_and_validate_artifact(artifact)?;
    let claim = validated.claim();
    target
        .trust_snapshot_signer(claim)
        .map_err(|error| SignedHolRoundTripError::at("signer-trusted", error))?;
    target
        .accept_authenticated_snapshot(claim)
        .map_err(|error| SignedHolRoundTripError::at("snapshot-accepted", error))?;
    let import = target
        .register_import(HolDatabaseRef::new(claim.schema(), claim.image()))
        .map_err(|error| SignedHolRoundTripError::at("namespace-imported", error))?;
    let trusted = target
        .accept_trusted_import(import, claim)
        .map_err(|error| SignedHolRoundTripError::at("namespace-imported", error))?;
    let namespace = target
        .create_imported_namespace(
            None,
            Some("received-beta-demo"),
            import,
            artifact.namespace_id,
        )
        .map_err(|error| SignedHolRoundTripError::at("namespace-imported", error))?;

    let mounted = covalence_neutron::ImmutableImage::register(Arc::from(artifact.image.as_slice()))
        .map_err(|error| SignedHolRoundTripError::at("theorem-read", error))?;
    let (context_id, conclusion_id) = target
        .match_trusted_import_image(trusted, validated)
        .map_err(|error| SignedHolRoundTripError::at("theorem-read", error))?
        .with_mounted_reader(namespace, &mounted, read_imported_beta)
        .map_err(|error| SignedHolRoundTripError::at("theorem-read", error))??;

    Ok(ReceivedHolSnapshot {
        import: import.get(),
        namespace: namespace.get(),
        context: context_id,
        conclusion: conclusion_id,
    })
}

fn authenticate_and_validate_artifact(
    artifact: &SignedHolArtifact,
) -> Result<AuthenticatedValidatedHolImage, SignedHolRoundTripError> {
    let public_key: [u8; 32] = artifact.public_key.as_slice().try_into().map_err(|_| {
        SignedHolRoundTripError::invalid("signature-authenticated", "public key is not 32 bytes")
    })?;
    let authenticated = SignedSnapshotEnvelope::new(
        &artifact.image,
        artifact.schema,
        artifact.image_hash,
        artifact.signer,
        public_key,
        &artifact.signature,
    )
    .authenticate()
    .map_err(|error| SignedHolRoundTripError::at("signature-authenticated", error))?;
    AuthenticatedValidatedHolImage::validate_default(authenticated)
        .map_err(|error| SignedHolRoundTripError::at("image-detached-validated", error))
}

fn read_imported_beta(
    mut reader: covalence_nucleus::ImportedHolReader<'_, '_, AllowAll>,
) -> Result<(i64, i64), SignedHolRoundTripError> {
    let Some(context_export) = reader
        .namespace_export(0)
        .map_err(|error| SignedHolRoundTripError::at("theorem-read", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "theorem-read",
            "missing context export",
        ));
    };
    let ImportedExport::Context(context) = context_export else {
        return Err(SignedHolRoundTripError::invalid(
            "theorem-read",
            "export 0 is not a context",
        ));
    };
    let Some(conclusion_export) = reader
        .namespace_export(1)
        .map_err(|error| SignedHolRoundTripError::at("theorem-read", error))?
    else {
        return Err(SignedHolRoundTripError::invalid(
            "theorem-read",
            "missing term export",
        ));
    };
    let ImportedExport::Term(conclusion) = conclusion_export else {
        return Err(SignedHolRoundTripError::invalid(
            "theorem-read",
            "export 1 is not a term",
        ));
    };
    if reader
        .theorem(context, conclusion)
        .map_err(|error| SignedHolRoundTripError::at("theorem-read", error))?
        .is_none()
    {
        return Err(SignedHolRoundTripError::invalid(
            "theorem-read",
            "persisted beta theorem is absent",
        ));
    }
    if !matches!(
        reader
            .term(conclusion)
            .map_err(|error| SignedHolRoundTripError::at("theorem-read", error))?,
        ImportedTermView::Equality { .. }
    ) {
        return Err(SignedHolRoundTripError::invalid(
            "theorem-read",
            "imported conclusion is not an equality",
        ));
    }
    Ok((context.get(), conclusion.get()))
}

/// Runs the split producer and receiver operations as one convenience demo.
///
/// # Errors
///
/// Returns the name and message of the first rejected boundary stage.
pub fn run_signed_hol_round_trip(
    producer_kernel: &Kernel,
    source: &mut Connection<Hol<AllowAll>>,
    target: &mut Connection<Hol<AllowAll>>,
) -> Result<SignedHolRoundTripResult, SignedHolRoundTripError> {
    let output = produce_signed_hol_artifact(producer_kernel, source)?;
    let received = receive_signed_hol_artifact(target, output.artifact())?;
    Ok(SignedHolRoundTripResult::from_parts(output, received))
}

/// Runs the signed HOL demonstration while retaining both connections in one REPL directory.
///
/// The returned receiver ID names live caller-owned state. In particular, the receiver's
/// connection-local signer trust and snapshot acceptance remain available after this function
/// returns; no private kernel or receiver is created and dropped behind the caller's back.
///
/// # Errors
///
/// Returns the explicitly named phase which rejected source lookup, receiver creation, proof,
/// authentication, validation, trust, import, or the scoped theorem read. The adapter attempts to
/// remove a newly inserted receiver when admission fails.
pub fn run_managed_signed_hol_round_trip(
    producer_kernel: &Kernel,
    directory: &mut Repl<LocalConnection>,
    source: ConnectionId,
) -> Result<(SignedHolRoundTripResult, ConnectionId), SignedHolRoundTripError> {
    let produced = produce_signed_hol_artifact(
        producer_kernel,
        directory
            .get_mut(source)
            .map_err(|error| SignedHolRoundTripError::at("source-selected", error))?
            .hol_mut()
            .map_err(|error| SignedHolRoundTripError::at("source-selected", error))?,
    )?;
    let target_connection = LocalConnection::Hol(
        producer_kernel
            .open_hol(AllowAll)
            .map_err(|error| SignedHolRoundTripError::at("receiver-opened", error))?,
    );
    let receiver_id = directory
        .insert(target_connection.protocol(), target_connection)
        .map_err(|error| SignedHolRoundTripError::at("receiver-opened", error))?;
    let admission = receive_signed_hol_artifact(
        directory
            .get_mut(receiver_id)
            .map_err(|error| SignedHolRoundTripError::at("receiver-opened", error))?
            .hol_mut()
            .map_err(|error| SignedHolRoundTripError::at("receiver-opened", error))?,
        produced.artifact(),
    );
    match admission {
        Ok(admitted) => Ok((
            SignedHolRoundTripResult::from_parts(produced, admitted),
            receiver_id,
        )),
        Err(error) => {
            let _ = directory.remove(receiver_id);
            Err(error)
        }
    }
}

/// A deliberately tiny, transport-neutral HOL demo recipe.
///
/// Recipe interpretation is an untrusted convenience layer. Soundness comes
/// from the branded Nucleus operations called by [`HolRecipe::execute`], not
/// from parsing or from this enum.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HolRecipe {
    /// Prove primitive truth in the empty context.
    Truth,
    /// Prove reflexivity of one Boolean literal.
    Reflexivity(bool),
    /// Prove closed beta reduction of Boolean identity at one literal.
    Beta(bool),
}

impl HolRecipe {
    /// Runs the recipe and persists its syntax and resulting judgement.
    ///
    /// Proof steps remain ephemeral capabilities. The persisted judgement is
    /// canonical kernel state; recording a recipe or trace is left to an
    /// optional metadata database above this adapter.
    ///
    /// # Errors
    ///
    /// Returns an error if Nucleus rejects a syntax constructor or proof rule.
    pub fn execute<P: covalence_nucleus::Policy>(
        self,
        connection: &mut Connection<Hol<P>>,
    ) -> Result<HolRecipeResult, HolRecipeError> {
        let context = ContextId::empty();
        let (recipe, statement, conclusion) = match self {
            Self::Truth => {
                let conclusion = connection.with_proof_session(|mut proof| {
                    let theorem = proof.prove_truth(context)?;
                    let conclusion = theorem.conclusion();
                    proof.persist_theorem(&theorem)?;
                    Ok::<_, ProofError>(conclusion)
                })?;
                ("truth", "true", conclusion)
            }
            Self::Reflexivity(value) => {
                let literal = connection.insert_bool_term(value)?;
                let conclusion = connection.with_proof_session(|mut proof| {
                    let theorem = hol_recipes::reflexivity(&mut proof, context, literal)?;
                    let conclusion = theorem.conclusion();
                    proof.persist_theorem(&theorem)?;
                    Ok::<_, ProofError>(conclusion)
                })?;
                (
                    "reflexivity",
                    if value {
                        "true = true"
                    } else {
                        "false = false"
                    },
                    conclusion,
                )
            }
            Self::Beta(value) => {
                let bool_type = connection.insert_bool_type()?;
                let variable = connection.insert_bound_term(0, bool_type)?;
                let identity = connection.insert_lambda(bool_type, variable)?;
                let literal = connection.insert_bool_term(value)?;
                let conclusion = connection.with_proof_session(|mut proof| {
                    let theorem = hol_recipes::beta(&mut proof, context, identity, literal)?;
                    let conclusion = theorem.conclusion();
                    proof.persist_theorem(&theorem)?;
                    Ok::<_, ProofError>(conclusion)
                })?;
                (
                    "beta",
                    if value {
                        "(lambda x:bool. x) true = true"
                    } else {
                        "(lambda x:bool. x) false = false"
                    },
                    conclusion,
                )
            }
        };
        Ok(HolRecipeResult {
            recipe,
            context_id: context.get(),
            conclusion_id: conclusion.get(),
            statement,
        })
    }
}

impl FromStr for HolRecipe {
    type Err = HolRecipeError;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        let mut words = source.split_whitespace();
        let recipe = match (words.next(), words.next(), words.next()) {
            (Some("truth"), None, None) => Self::Truth,
            (Some("reflexivity" | "refl"), Some(value), None) => {
                Self::Reflexivity(parse_bool(value)?)
            }
            (Some("beta"), Some(value), None) => Self::Beta(parse_bool(value)?),
            _ => return Err(HolRecipeError::InvalidRecipe),
        };
        Ok(recipe)
    }
}

fn parse_bool(value: &str) -> Result<bool, HolRecipeError> {
    match value {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => Err(HolRecipeError::InvalidBoolean),
    }
}

/// Common result returned by native and browser recipe adapters.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HolRecipeResult {
    recipe: &'static str,
    context_id: i64,
    conclusion_id: i64,
    statement: &'static str,
}

impl HolRecipeResult {
    /// Returns `hol-theorem`, the discriminant shared by every frontend.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        "hol-theorem"
    }

    /// Returns the recipe constructor name.
    #[must_use]
    pub const fn recipe(&self) -> &'static str {
        self.recipe
    }

    /// Returns the database-local context ID.
    #[must_use]
    pub const fn context_id(&self) -> i64 {
        self.context_id
    }

    /// Returns the database-local conclusion term ID.
    #[must_use]
    pub const fn conclusion_id(&self) -> i64 {
        self.conclusion_id
    }

    /// Returns a human-readable statement fixed by the recipe.
    #[must_use]
    pub const fn statement(&self) -> &'static str {
        self.statement
    }
}

/// Failure to parse or execute a demo recipe.
#[derive(Debug)]
pub enum HolRecipeError {
    /// The recipe does not match the deliberately small grammar.
    InvalidRecipe,
    /// A recipe Boolean must be exactly `true` or `false`.
    InvalidBoolean,
    /// A type constructor was rejected by Nucleus.
    Type(TypeError),
    /// A term constructor was rejected by Nucleus.
    Term(TermError),
    /// A branded proof operation was rejected by Nucleus.
    Proof(ProofError),
}

impl fmt::Display for HolRecipeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRecipe => {
                formatter.write_str("expected `truth`, `reflexivity BOOL`, or `beta BOOL`")
            }
            Self::InvalidBoolean => formatter.write_str("BOOL must be `true` or `false`"),
            Self::Type(error) => error.fmt(formatter),
            Self::Term(error) => error.fmt(formatter),
            Self::Proof(error) => error.fmt(formatter),
        }
    }
}

impl StdError for HolRecipeError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Type(error) => Some(error),
            Self::Term(error) => Some(error),
            Self::Proof(error) => Some(error),
            Self::InvalidRecipe | Self::InvalidBoolean => None,
        }
    }
}

impl From<TypeError> for HolRecipeError {
    fn from(error: TypeError) -> Self {
        Self::Type(error)
    }
}

impl From<TermError> for HolRecipeError {
    fn from(error: TermError) -> Self {
        Self::Term(error)
    }
}

impl From<ProofError> for HolRecipeError {
    fn from(error: ProofError) -> Self {
        Self::Proof(error)
    }
}

/// Failure to operate the REPL directory.
#[derive(Debug)]
pub enum ReplError {
    /// The raw state connection could not be opened.
    Open(covalence_neutron::ConnectionError),
    /// The state database rejected an operation.
    State(sqlite::Error),
    /// A requested runtime connection does not exist.
    UnknownConnection(ConnectionId),
    /// A state inspection statement returned no columns.
    StateQueryReturnsNoRows,
    /// No runtime connection is currently selected.
    NoActiveConnection,
}

impl fmt::Display for ReplError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Open(error) => write!(formatter, "could not open REPL state: {error}"),
            Self::State(error) => write!(formatter, "could not access REPL state: {error}"),
            Self::UnknownConnection(id) => write!(formatter, "unknown connection {id}"),
            Self::StateQueryReturnsNoRows => {
                formatter.write_str("state inspection statements must return rows")
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
            Self::UnknownConnection(_)
            | Self::NoActiveConnection
            | Self::StateQueryReturnsNoRows => None,
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
pub use web::{WebHolOutcome, WebKernel, WebOutcome, WebSignedHolOutcome};

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
    fn orchestrates_two_simultaneous_sql_connections() {
        let kernel = Kernel::ephemeral();
        let mut repl = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let first = repl
            .insert("nucleus/sql", kernel.open_sql().unwrap())
            .unwrap();
        let second = repl
            .insert("nucleus/sql", kernel.open_sql().unwrap())
            .unwrap();

        repl.get_mut(first)
            .unwrap()
            .run("CREATE TABLE only_here(x INTEGER)", &[])
            .unwrap();
        let isolated = repl
            .get_mut(second)
            .unwrap()
            .run(
                "SELECT count(*) FROM sqlite_schema WHERE name = 'only_here'",
                &[],
            )
            .unwrap();
        assert!(matches!(
            isolated,
            Outcome::Rows(result) if result.rows == [[Value::Integer(0)]]
        ));
        let present = repl
            .get_mut(first)
            .unwrap()
            .run(
                "SELECT count(*) FROM sqlite_schema WHERE name = 'only_here'",
                &[],
            )
            .unwrap();
        assert!(matches!(
            present,
            Outcome::Rows(result) if result.rows == [[Value::Integer(1)]]
        ));
    }

    #[test]
    fn inspects_state_read_only() {
        let mut repl = Repl::new(&[9; 32]).unwrap();
        let _ = repl.insert("nucleus/sql", ()).unwrap();

        let result = repl
            .inspect_state("SELECT connection_id, protocol FROM repl_connection")
            .unwrap();
        assert_eq!(result.columns, ["connection_id", "protocol"]);
        assert_eq!(
            result.rows,
            [[Value::Integer(1), Value::Text("nucleus/sql".to_owned())]]
        );

        // Inspection cannot mutate the directory, and ordinary directory
        // updates still work afterwards.
        assert!(repl.inspect_state("DELETE FROM repl_connection").is_err());
        assert!(
            repl.inspect_state("INSERT INTO repl_connection(kernel_id, protocol) VALUES (0, 'x') RETURNING connection_id")
                .is_err()
        );
        assert_eq!(
            repl.inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(1)]]
        );
        let _ = repl.insert("nucleus/sql", ()).unwrap();
        assert_eq!(
            repl.inspect_state("SELECT count(*) FROM repl_connection")
                .unwrap()
                .rows,
            [[Value::Integer(2)]]
        );
    }

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

    #[test]
    fn manages_independent_sql_and_hol_connections() {
        let kernel = Kernel::ephemeral();
        let mut repl = Repl::new(kernel.verifying_key().as_bytes()).unwrap();
        let sql = LocalConnection::Sql(kernel.open_sql().unwrap());
        let hol = LocalConnection::Hol(kernel.open_hol(AllowAll).unwrap());
        let sql_id = repl.insert(sql.protocol(), sql).unwrap();
        let hol_id = repl.insert(hol.protocol(), hol).unwrap();

        repl.get_mut(sql_id)
            .unwrap()
            .sql_mut()
            .unwrap()
            .execute_batch("CREATE TABLE only_sql(value INTEGER)")
            .unwrap();
        let result = HolRecipe::Beta(true)
            .execute(repl.get_mut(hol_id).unwrap().hol_mut().unwrap())
            .unwrap();

        assert_eq!(result.kind(), "hol-theorem");
        assert_eq!(result.recipe(), "beta");
        assert_eq!(result.context_id(), 0);
        assert_eq!(result.statement(), "(lambda x:bool. x) true = true");
        assert!(result.conclusion_id() > 0);
        assert!(matches!(
            repl.get_mut(sql_id).unwrap().hol_mut(),
            Err(ConnectionKindError::ExpectedHol)
        ));
        assert!(matches!(
            repl.get_mut(hol_id).unwrap().sql_mut(),
            Err(ConnectionKindError::ExpectedSql)
        ));

        let protocols = repl
            .state()
            .sqlite()
            .prepare("SELECT protocol FROM repl_connection ORDER BY connection_id")
            .unwrap()
            .query_map((), |row| row.get::<_, String>(0))
            .unwrap()
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(protocols, ["nucleus/sql", "nucleus/hol"]);
    }

    #[test]
    fn recipe_parser_is_intentionally_small() {
        assert_eq!("truth".parse::<HolRecipe>().unwrap(), HolRecipe::Truth);
        assert_eq!(
            "refl false".parse::<HolRecipe>().unwrap(),
            HolRecipe::Reflexivity(false)
        );
        assert_eq!(
            "beta true".parse::<HolRecipe>().unwrap(),
            HolRecipe::Beta(true)
        );
        assert!(matches!(
            "beta maybe".parse::<HolRecipe>(),
            Err(HolRecipeError::InvalidBoolean)
        ));
        assert!(matches!(
            "anything".parse::<HolRecipe>(),
            Err(HolRecipeError::InvalidRecipe)
        ));
    }

    #[test]
    fn signed_round_trip_crosses_every_explicit_boundary() {
        let producer = Kernel::ephemeral();
        let mut source = producer.open_hol(AllowAll).unwrap();
        let receiver = Kernel::ephemeral();
        let mut target = receiver.open_hol(AllowAll).unwrap();

        let result = run_signed_hol_round_trip(&producer, &mut source, &mut target).unwrap();

        assert_eq!(result.kind(), "signed-hol-round-trip");
        assert_eq!(result.phases(), SIGNED_HOL_PHASES);
        assert_eq!(result.proof().recipe(), "beta");
        assert_eq!(result.proof().context_id(), 0);
        assert_eq!(result.proof().statement(), "(lambda x:bool. x) true = true");
        assert_eq!(result.public_key().len(), 32);
        assert_eq!(result.signature().len(), 64);
        assert!(!result.image().is_empty());
        assert!(
            result
                .attestation_text()
                .contains(&format!("namespace={}", result.namespace_id()))
        );
        assert_eq!(result.imported_context_id(), 0);
        assert_eq!(
            result.imported_conclusion_id(),
            result.proof().conclusion_id()
        );
    }

    #[test]
    fn managed_receiver_remains_authoritative_after_the_helper_returns() {
        let producer = Kernel::ephemeral();
        let mut directory = Repl::new(producer.verifying_key().as_bytes()).unwrap();
        let source = LocalConnection::Hol(producer.open_hol(AllowAll).unwrap());
        let source = directory.insert(source.protocol(), source).unwrap();

        let (result, receiver) =
            run_managed_signed_hol_round_trip(&producer, &mut directory, source).unwrap();

        // Re-establish portable evidence independently after the managed helper
        // has returned. Returned integer coordinates are not used as authority.
        let artifact = result.produced.artifact();
        let validated = authenticate_and_validate_artifact(artifact).unwrap();
        let target = directory.get_mut(receiver).unwrap().hol_mut().unwrap();
        let import = target
            .register_import(HolDatabaseRef::new(
                validated.claim().schema(),
                validated.claim().image(),
            ))
            .unwrap();
        assert_eq!(import.get(), result.import_id());
        let trusted = target
            .accept_trusted_import(import, validated.claim())
            .unwrap();
        assert_eq!(target.trusted_import(trusted).unwrap().import, import);
        let namespace = covalence_nucleus::NamespaceId::from_i64(result.imported_namespace_id());
        assert!(matches!(
            target.namespace_source(namespace).unwrap(),
            covalence_nucleus::NamespaceSource::Imported {
                import: actual,
                source_namespace
            } if actual == import && source_namespace == result.namespace_id()
        ));

        // Match the persisted accepted-import row to the freshly authenticated
        // bytes, mount through the verified immutable VFS, and read the theorem
        // again. This capability is created now, not smuggled out of the helper.
        let mounted =
            covalence_neutron::ImmutableImage::register(Arc::from(artifact.image())).unwrap();
        let reread = target
            .match_trusted_import_image(trusted, validated)
            .unwrap()
            .with_mounted_reader(namespace, &mounted, read_imported_beta)
            .unwrap()
            .unwrap();
        assert_eq!(reread.0, result.imported_context_id());
        assert_eq!(reread.1, result.imported_conclusion_id());
        assert_eq!(directory.connections.len(), 2);
    }

    #[test]
    fn receiver_rejects_tampered_transport_before_trust_or_import() {
        let producer = Kernel::ephemeral();
        let mut source = producer.open_hol(AllowAll).unwrap();
        let output = produce_signed_hol_artifact(&producer, &mut source).unwrap();
        let artifact = output.artifact();

        let reconstructed = SignedHolArtifact::from_untrusted_parts(
            artifact.namespace_id(),
            artifact.image().to_vec(),
            &artifact.schema().to_string(),
            &artifact.image_hash().to_string(),
            &artifact.signer().to_string(),
            artifact.public_key().to_vec(),
            artifact.signature().to_vec(),
        )
        .unwrap();
        let mut target = Kernel::ephemeral().open_hol(AllowAll).unwrap();
        receive_signed_hol_artifact(&mut target, &reconstructed).unwrap();

        let mut bytes = artifact.image().to_vec();
        bytes[0] ^= 1;
        let wrong_bytes = SignedHolArtifact::from_untrusted_parts(
            artifact.namespace_id(),
            bytes,
            &artifact.schema().to_string(),
            &artifact.image_hash().to_string(),
            &artifact.signer().to_string(),
            artifact.public_key().to_vec(),
            artifact.signature().to_vec(),
        )
        .unwrap();
        let mut target = Kernel::ephemeral().open_hol(AllowAll).unwrap();
        assert_eq!(
            receive_signed_hol_artifact(&mut target, &wrong_bytes)
                .unwrap_err()
                .phase(),
            "signature-authenticated"
        );

        let wrong_schema = SignedHolArtifact::from_untrusted_parts(
            artifact.namespace_id(),
            artifact.image().to_vec(),
            &covalence_lib_hash::O256::from_bytes(b"wrong schema").to_string(),
            &artifact.image_hash().to_string(),
            &artifact.signer().to_string(),
            artifact.public_key().to_vec(),
            artifact.signature().to_vec(),
        )
        .unwrap();
        let mut target = Kernel::ephemeral().open_hol(AllowAll).unwrap();
        assert_eq!(
            receive_signed_hol_artifact(&mut target, &wrong_schema)
                .unwrap_err()
                .phase(),
            "signature-authenticated"
        );

        let mut signature = artifact.signature().to_vec();
        signature[0] ^= 1;
        let wrong_signature = SignedHolArtifact::from_untrusted_parts(
            artifact.namespace_id(),
            artifact.image().to_vec(),
            &artifact.schema().to_string(),
            &artifact.image_hash().to_string(),
            &artifact.signer().to_string(),
            artifact.public_key().to_vec(),
            signature,
        )
        .unwrap();
        let mut target = Kernel::ephemeral().open_hol(AllowAll).unwrap();
        assert_eq!(
            receive_signed_hol_artifact(&mut target, &wrong_signature)
                .unwrap_err()
                .phase(),
            "signature-authenticated"
        );
    }
}
