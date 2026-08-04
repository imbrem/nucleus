//! Transport-neutral REPL orchestration.
//!
//! A [`Repl`] is not a Nucleus connection protocol. It maintains an ordinary,
//! inspectable `SQLite` directory in a raw Neutron connection and associates its
//! rows with runtime connection handles owned by the current process.

use std::collections::HashMap;
use std::error::Error as StdError;
use std::fmt;

use covalence_lib_sqlite as sqlite;

pub use covalence_lib_hash::O256;
pub use covalence_nucleus::sql::{ImageError, Outcome, QueryResult, Statement, Value};
pub use covalence_nucleus::{
    AllowAll, AuthenticatedHolImageValidationError, AuthenticatedValidatedHolImage, Connection,
    ContextError, ContextId, ContextImplication, ExportError, ExportId, ExportSort, ExportView,
    Hol, HolDatabaseRef, HolExportError, HolOpenError, HolSchema, HolSchemaDescriptor,
    HolSchemaDescriptorError, ImportError, ImportId, ImportedExport, ImportedReaderError,
    ImportedTermView, Kernel, Kind, KindError, KindId, KindView, MetadataTable, MetadataTarget,
    MetadataType, MetadataValue, NamespaceError, NamespaceExport, NamespaceId, NamespaceView,
    ProofError, ProofSession, SignedSnapshotAttestation, SignedSnapshotEnvelope,
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
    /// An unrestricted raw SQL session.
    Sql(Connection<Sql>),
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
    kernel: Kernel,
    directory: Repl<LocalConnection>,
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
        Ok(Self { kernel, directory })
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

    /// Opens and selects a raw in-memory SQL session.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection or directory row cannot be created.
    pub fn open_sql(&mut self) -> Result<ConnectionId, LocalReplError> {
        let connection = self.kernel.open_sql().map_err(LocalReplError::SqlOpen)?;
        let id = self
            .directory
            .insert("nucleus/sql", LocalConnection::Sql(connection))?;
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
        let connection = self
            .kernel
            .open_hol(AllowAll)
            .map_err(LocalReplError::HolOpen)?;
        let id = self
            .directory
            .insert("nucleus/hol-common-v2", LocalConnection::Hol(connection))?;
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
        let descriptor = HolSchemaDescriptor::decode(descriptor)?;
        let connection =
            Connection::open_hol_in_memory_with_schema(AllowAll, descriptor.into_schema())
                .map_err(LocalReplError::HolOpen)?;
        let id = self
            .directory
            .insert("nucleus/hol-common-v2", LocalConnection::Hol(connection))?;
        self.directory.select(id)?;
        Ok(id)
    }

    /// Closes any managed connection.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or state update failure.
    pub fn close(&mut self, id: ConnectionId) -> Result<(), LocalReplError> {
        self.directory.remove(id).map(drop).map_err(Into::into)
    }

    /// Returns a mutable SQL session, rejecting HOL connection IDs.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown ID or protocol mismatch.
    pub fn sql_mut(&mut self, id: ConnectionId) -> Result<&mut Connection<Sql>, LocalReplError> {
        let connection = self.directory.get_mut(id)?;
        match connection {
            LocalConnection::Sql(connection) => Ok(connection),
            other @ LocalConnection::Hol(_) => Err(LocalReplError::WrongProtocol {
                id,
                expected: "nucleus/sql",
                actual: other.protocol(),
            }),
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
        let Self { kernel, directory } = self;
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
        let snapshot = kernel.export_hol(connection)?;
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

    /// Authenticates, explicitly trusts, and persists one hash-first import attestation.
    ///
    /// This is transport orchestration over Nucleus APIs. It performs no cryptography itself and
    /// never fetches, parses, or attaches the named database.
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
        let claim = SignedSnapshotAttestation::new(schema, image, signer, public_key, signature)
            .authenticate()?;
        let connection = self.hol_mut(id)?;
        connection.trust_snapshot_signer(&claim)?;
        connection.accept_authenticated_snapshot(&claim)?;
        let database = HolDatabaseRef::new(schema, image);
        let import = connection.register_import(database)?;
        let trusted_import = connection.accept_trusted_import(import, &claim)?;
        Ok(LocalTrustedHolImport {
            import,
            trusted_import,
            database,
            signer,
        })
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
    /// This first whole-image demo copies the received bytes and registers a process-lifetime
    /// immutable VFS for the one-shot read; repeated reads are not yet a cached mount API.
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
        let matched = self
            .hol_mut(id)?
            .match_trusted_import_image(trusted_import, validated)?;
        let import = matched.import();
        let result = matched.with_reader(
            namespace,
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

/// Failure in the shared local-kernel REPL layer.
#[derive(Debug)]
pub enum LocalReplError {
    /// The connection directory failed.
    Directory(ReplError),
    /// A raw SQL connection could not open.
    SqlOpen(covalence_neutron::ConnectionError),
    /// A HOL connection or its schema could not open.
    HolOpen(HolOpenError),
    /// A portable HOL metadata schema descriptor was invalid.
    HolSchemaDescriptor(HolSchemaDescriptorError),
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
            Self::HolOpen(error) => error.fmt(formatter),
            Self::HolSchemaDescriptor(error) => error.fmt(formatter),
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
            Self::HolOpen(error) => Some(error),
            Self::HolSchemaDescriptor(error) => Some(error),
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
            Self::WrongProtocol { .. } => None,
        }
    }
}

impl From<ReplError> for LocalReplError {
    fn from(error: ReplError) -> Self {
        Self::Directory(error)
    }
}

impl From<HolSchemaDescriptorError> for LocalReplError {
    fn from(error: HolSchemaDescriptorError) -> Self {
        Self::HolSchemaDescriptor(error)
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
    /// A requested runtime connection does not exist.
    UnknownConnection(ConnectionId),
    /// No runtime connection is currently selected.
    NoActiveConnection,
}

impl fmt::Display for ReplError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Open(error) => write!(formatter, "could not open REPL state: {error}"),
            Self::State(error) => write!(formatter, "could not access REPL state: {error}"),
            Self::UnknownConnection(id) => write!(formatter, "unknown connection {id}"),
            Self::NoActiveConnection => formatter.write_str("no active connection"),
        }
    }
}

impl StdError for ReplError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Open(error) => Some(error),
            Self::State(error) => Some(error),
            Self::UnknownConnection(_) | Self::NoActiveConnection => None,
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

    #[test]
    fn local_kernel_directory_manages_sql_and_hol_without_crossing_protocols() {
        let mut repl = LocalRepl::new().unwrap();
        let sql = repl.open_sql().unwrap();
        let hol = repl.open_hol().unwrap();

        repl.sql_mut(sql).unwrap().run("SELECT 1", &[]).unwrap();
        let star = repl.hol_mut(hol).unwrap().insert_kind(&Kind::Star).unwrap();
        assert_eq!(star.get(), 1);
        assert!(matches!(
            repl.sql_mut(hol),
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
        let source = repl.open_hol_with_descriptor(descriptor.encode()).unwrap();
        let target = repl.open_hol().unwrap();
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

        let exported_target = repl.export_hol_snapshot(target).unwrap();
        let validated =
            covalence_nucleus::ValidatedHolImage::validate(exported_target.bytes()).unwrap();
        assert_eq!(validated.counts().import_references, 1);
        assert_eq!(validated.counts().untrusted_trusted_import_rows, 1);
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
