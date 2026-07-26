use std::{any::type_name, collections::BTreeSet};

use covalence_lib_error::snafu;
use covalence_lib_hash::O256;
use covalence_lib_sqlite::{Connection, OptionalExtension, params};
use covalence_neutron::{
    BLAKE3_CAS_INTERPRETATION_V0, BLAKE3_CAS_METATABLE_V0, BOOTSTRAP_CATALOG, CatalogCandidate,
    MetatableKind, RUST_TYPES_INTERPRETATION_V0, RUST_TYPES_METATABLE_V0, ScanError,
    metatable_name, scan_metatables,
};
use snafu::Snafu;

/// One metatable accepted from the permanent bootstrap catalog.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Metatable {
    table_name: String,
    interpretation: String,
}

impl Metatable {
    /// Returns the physical metatable name.
    #[must_use]
    pub fn table_name(&self) -> &str {
        &self.table_name
    }

    /// Returns the interpretation selected by the bootstrap.
    #[must_use]
    pub fn interpretation(&self) -> &str {
        &self.interpretation
    }
}

/// Accepted connection-local metatable interpretations.
///
/// Acceptance requires exactly one bootstrap catalog with the permanent
/// [`covalence_neutron::BOOTSTRAP_CATALOG`] identity and physical ABI.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NeutronCatalog {
    metatables: Vec<Metatable>,
}

impl NeutronCatalog {
    /// Returns extension metatables registered by the bootstrap.
    #[must_use]
    pub fn metatables(&self) -> &[Metatable] {
        &self.metatables
    }

    fn accept(candidate: &CatalogCandidate, connection: &Connection) -> Result<Self, CatalogError> {
        let bootstrap = candidate
            .bootstrap()
            .ok_or(CatalogError::MissingBootstrapCatalog)?;
        let metatables = bootstrap
            .declarations()
            .iter()
            .map(|declaration| Metatable {
                table_name: declaration.table_name().to_owned(),
                interpretation: declaration.interpretation().to_owned(),
            })
            .collect::<Vec<_>>();
        let mut interpretations = BTreeSet::new();
        for metatable in &metatables {
            if !interpretations.insert(metatable.interpretation.as_str()) {
                return Err(CatalogError::DuplicateInterpretation {
                    interpretation: metatable.interpretation.clone(),
                });
            }
            if metatable.interpretation == RUST_TYPES_INTERPRETATION_V0 {
                validate_rust_types_metatable(connection, metatable)?;
            } else if metatable.interpretation == BLAKE3_CAS_INTERPRETATION_V0 {
                validate_blake3_cas_metatable(connection, metatable)?;
            }
        }
        Ok(Self { metatables })
    }

    fn by_interpretation(&self, interpretation: &str) -> Option<&Metatable> {
        self.metatables
            .iter()
            .find(|metatable| metatable.interpretation == interpretation)
    }
}

/// A request presented to an explicitly registered computational capability.
///
/// The request has no logical authority. Any returned bytes remain candidates
/// until Nucleus validates them against [`Self::hash`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BlobRequest {
    hash: O256,
}

impl BlobRequest {
    /// Returns the requested BLAKE3 content address.
    #[must_use]
    pub const fn hash(self) -> O256 {
        self.hash
    }
}

/// An object-safe, connection-scoped source of candidate bytes.
///
/// Resolver implementations may perform arbitrary effects authorized by their
/// embedding code. Persisted database state cannot construct a resolver or
/// grant it capabilities. Resolver output is never trusted directly.
pub trait BlobResolver {
    /// Attempts to produce bytes for `request`.
    ///
    /// `Ok(None)` means this resolver has no candidate. Returned bytes need
    /// not be correct: the trusted connection validates their content address.
    ///
    /// # Errors
    ///
    /// Returns an operational failure reported by the resolver.
    fn resolve(&mut self, request: BlobRequest) -> Result<Option<Vec<u8>>, ResolveError>;
}

/// An operational failure reported across the object-safe resolver boundary.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
#[snafu(display("{message}"))]
pub struct ResolveError {
    message: String,
}

impl ResolveError {
    /// Constructs an opaque resolver failure with a diagnostic message.
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

struct ResolverCapability {
    id: String,
    resolver: Box<dyn BlobResolver>,
}

/// Rejection while accepting structurally decoded metadata as a known API.
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum CatalogError {
    /// The required bootstrap catalog was absent.
    #[snafu(display("missing bootstrap catalog"))]
    MissingBootstrapCatalog,
    /// A known interpretation appeared at an unexpected physical table.
    #[snafu(display(
        "interpretation `{interpretation}` must use table `{expected}`, found `{actual}`"
    ))]
    WrongInterpretationTable {
        /// Interpretation selected by the bootstrap.
        interpretation: String,
        /// Required physical name.
        expected: String,
        /// Actual registered name.
        actual: String,
    },
    /// A recognized extension had the wrong permanent shape.
    #[snafu(display("invalid `{interpretation}` metatable schema: {reason}"))]
    InvalidExtensionSchema {
        /// Interpretation being validated.
        interpretation: String,
        /// Stable rejection detail.
        reason: String,
    },
    /// Two physical tables selected the same singleton interpretation.
    #[snafu(display("duplicate metatable interpretation `{interpretation}`"))]
    DuplicateInterpretation {
        /// Duplicated interpretation.
        interpretation: String,
    },
    /// `SQLite` failed during interpretation validation.
    #[snafu(display("could not validate metatable interpretation: {source}"))]
    ValidationSqlite {
        /// Underlying `SQLite` failure.
        source: covalence_lib_sqlite::Error,
    },
}

/// The only writable trusted `SQLite` owner in this initial slice.
///
/// The raw connection is intentionally private and has no public escape hatch.
/// Construction accepts exactly one bootstrap catalog in `main`; the MVP does
/// not yet support attached database namespaces.
pub struct TrustedDb {
    connection: Connection,
    catalog: NeutronCatalog,
    generation: u64,
    resolvers: Vec<ResolverCapability>,
}

impl TrustedDb {
    /// Creates a fresh trusted database containing an empty bootstrap catalog.
    ///
    /// At this point the database supports no extension metatable
    /// interpretations and exposes no typed relation capabilities.
    ///
    /// # Errors
    ///
    /// Fails atomically if `SQLite` setup, metatable scanning, or catalog
    /// acceptance fails.
    pub fn create_in_memory() -> Result<Self, TrustedDbError> {
        let mut connection = Connection::open_in_memory().map_err(TrustedDbError::sqlite)?;
        connection
            .execute_batch("PRAGMA foreign_keys = ON;")
            .map_err(TrustedDbError::sqlite)?;
        let transaction = connection.transaction().map_err(TrustedDbError::sqlite)?;
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        transaction
            .execute_batch(&format!(
                "CREATE TABLE \"{bootstrap}\" (
                    table_name TEXT PRIMARY KEY,
                    interpretation TEXT NOT NULL
                ) STRICT;"
            ))
            .map_err(TrustedDbError::sqlite)?;
        let candidate = scan_metatables(&transaction).map_err(TrustedDbError::scan)?;
        let catalog =
            NeutronCatalog::accept(&candidate, &transaction).map_err(TrustedDbError::catalog)?;
        transaction.commit().map_err(TrustedDbError::sqlite)?;
        Ok(Self {
            connection,
            catalog,
            generation: 0,
            resolvers: Vec::new(),
        })
    }

    /// Returns the accepted connection-local catalog.
    #[must_use]
    pub const fn catalog(&self) -> &NeutronCatalog {
        &self.catalog
    }

    /// Returns the schema generation.
    #[must_use]
    pub const fn generation(&self) -> u64 {
        self.generation
    }

    /// Installs the first extension metatable: Rust type names to integer IDs.
    ///
    /// The extension table and its bootstrap registration are created in one
    /// transaction, rescanned, and accepted before becoming visible.
    ///
    /// # Errors
    ///
    /// Returns a checked database, scan, or catalog error.
    pub fn install_rust_types(&mut self) -> Result<InstallOutcome, TrustedDbError> {
        if self
            .catalog
            .by_interpretation(RUST_TYPES_INTERPRETATION_V0)
            .is_some()
        {
            return Ok(InstallOutcome::AlreadyPresent);
        }

        let transaction = self
            .connection
            .transaction()
            .map_err(TrustedDbError::sqlite)?;
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        let rust_types = metatable_name(MetatableKind::new(RUST_TYPES_METATABLE_V0));
        transaction
            .execute_batch(&format!(
                "CREATE TABLE \"{rust_types}\" (
                    id INTEGER PRIMARY KEY,
                    rust_type TEXT NOT NULL UNIQUE
                ) STRICT;"
            ))
            .map_err(TrustedDbError::sqlite)?;
        transaction
            .execute(
                &format!(
                    "INSERT INTO \"{bootstrap}\" (table_name, interpretation) VALUES (?1, ?2)"
                ),
                params![rust_types, RUST_TYPES_INTERPRETATION_V0],
            )
            .map_err(TrustedDbError::sqlite)?;
        let candidate = scan_metatables(&transaction).map_err(TrustedDbError::scan)?;
        let catalog =
            NeutronCatalog::accept(&candidate, &transaction).map_err(TrustedDbError::catalog)?;
        transaction.commit().map_err(TrustedDbError::sqlite)?;
        self.catalog = catalog;
        self.generation += 1;
        Ok(InstallOutcome::Installed)
    }

    /// Resolves the installed Rust-type registry as a checked capability.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::MissingRustTypes`] before the extension has
    /// been installed.
    pub fn rust_types(&mut self) -> Result<RustTypes<'_>, TrustedDbError> {
        let metatable = self
            .catalog
            .by_interpretation(RUST_TYPES_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingRustTypes)?;
        Ok(RustTypes {
            connection: &mut self.connection,
            metatable,
        })
    }

    /// Installs a hardcoded indexed BLAKE3 content-addressed relation.
    ///
    /// `id` defines a connection-local identity, `hash` quotes the stable
    /// BLAKE3 digest, and nullable `data` distinguishes a known lazy reference
    /// from locally available bytes.
    ///
    /// # Errors
    ///
    /// Returns a checked database, scan, or catalog error.
    pub fn install_blake3_cas(&mut self) -> Result<InstallOutcome, TrustedDbError> {
        if self
            .catalog
            .by_interpretation(BLAKE3_CAS_INTERPRETATION_V0)
            .is_some()
        {
            return Ok(InstallOutcome::AlreadyPresent);
        }

        let transaction = self
            .connection
            .transaction()
            .map_err(TrustedDbError::sqlite)?;
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        let cas = metatable_name(MetatableKind::new(BLAKE3_CAS_METATABLE_V0));
        transaction
            .execute_batch(&format!(
                "CREATE TABLE \"{cas}\" (
                    id INTEGER PRIMARY KEY,
                    hash BLOB NOT NULL UNIQUE CHECK (length(hash) = 32),
                    data BLOB
                ) STRICT;"
            ))
            .map_err(TrustedDbError::sqlite)?;
        transaction
            .execute(
                &format!(
                    "INSERT INTO \"{bootstrap}\" (table_name, interpretation) VALUES (?1, ?2)"
                ),
                params![cas, BLAKE3_CAS_INTERPRETATION_V0],
            )
            .map_err(TrustedDbError::sqlite)?;
        let candidate = scan_metatables(&transaction).map_err(TrustedDbError::scan)?;
        let catalog =
            NeutronCatalog::accept(&candidate, &transaction).map_err(TrustedDbError::catalog)?;
        transaction.commit().map_err(TrustedDbError::sqlite)?;
        self.catalog = catalog;
        self.generation += 1;
        Ok(InstallOutcome::Installed)
    }

    /// Resolves the installed BLAKE3 CAS as a checked capability.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::MissingBlake3Cas`] before installation.
    pub fn blake3_cas(&mut self) -> Result<Blake3Cas<'_>, TrustedDbError> {
        let metatable = self
            .catalog
            .by_interpretation(BLAKE3_CAS_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingBlake3Cas)?;
        Ok(Blake3Cas {
            connection: &mut self.connection,
            metatable,
        })
    }

    /// Registers one explicitly supplied resolver capability.
    ///
    /// Resolvers are consulted in registration order after the local trusted
    /// CAS. A database row cannot register, replace, or reorder capabilities.
    ///
    /// # Errors
    ///
    /// Rejects an empty or duplicate connection-local resolver ID.
    pub fn register_blob_resolver(
        &mut self,
        id: impl Into<String>,
        resolver: impl BlobResolver + 'static,
    ) -> Result<(), TrustedDbError> {
        let id = id.into();
        if id.is_empty() {
            return Err(TrustedDbError::InvalidResolverId);
        }
        if self.resolvers.iter().any(|capability| capability.id == id) {
            return Err(TrustedDbError::DuplicateResolver { id });
        }
        self.resolvers.push(ResolverCapability {
            id,
            resolver: Box::new(resolver),
        });
        Ok(())
    }

    /// Loads one BLAKE3 object through the local CAS and registered resolvers.
    ///
    /// The local CAS is checked first. On a cache miss, resolvers are consulted
    /// in registration order. The first candidate whose digest matches is
    /// inserted through the trusted CAS transition and returned. If every
    /// resolver misses, the lazy reference remains pending.
    ///
    /// # Errors
    ///
    /// Returns a typed failure for a missing CAS, a resolver failure, a lying
    /// resolver, or a trusted database operation.
    pub fn load_blake3(&mut self, hash: O256) -> Result<CasLoad, TrustedDbError> {
        let (id, local) = {
            let mut cas = self.blake3_cas()?;
            let id = cas.declare(hash)?;
            (id, cas.entry(hash)?)
        };
        if let Some(entry) = local
            && entry.data.is_some()
        {
            return Ok(CasLoad::Resident(entry));
        }

        for index in 0..self.resolvers.len() {
            let candidate = {
                let capability = &mut self.resolvers[index];
                capability
                    .resolver
                    .resolve(BlobRequest { hash })
                    .map_err(|source| TrustedDbError::Resolver {
                        id: capability.id.clone(),
                        source,
                    })?
            };
            if let Some(data) = candidate {
                let id = {
                    let mut cas = self.blake3_cas()?;
                    cas.provide(hash, &data)?
                };
                return Ok(CasLoad::Resident(CasEntry {
                    id,
                    hash,
                    data: Some(data),
                }));
            }
        }
        Ok(CasLoad::Pending(id))
    }
}

/// Result of installing a singleton extension metatable.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum InstallOutcome {
    /// The extension and its bootstrap row were created.
    Installed,
    /// The accepted catalog already contained the extension.
    AlreadyPresent,
}

/// A connection-local integer identifying one Rust type name.
///
/// The ID and [`std::any::type_name`] text are execution metadata, not stable
/// substrate semantics or a portable Rust ABI.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RustTypeId(i64);

impl RustTypeId {
    /// Returns the stored `SQLite` integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// Checked access to the Rust-type registry extension.
pub struct RustTypes<'db> {
    connection: &'db mut Connection,
    metatable: Metatable,
}

/// A connection-local identity defined by the indexed CAS relation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CasId(i64);

impl CasId {
    /// Returns the stored `SQLite` integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One checked row read from the BLAKE3 CAS.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CasEntry {
    /// Connection-local identity.
    pub id: CasId,
    /// Stable content address.
    pub hash: O256,
    /// Locally available bytes, or `None` for a lazy reference.
    pub data: Option<Vec<u8>>,
}

/// Result of cache-first lookup over the local CAS and resolver capabilities.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CasLoad {
    /// Validated bytes are resident in the trusted local CAS.
    Resident(CasEntry),
    /// The address is known, but no registered capability produced bytes.
    Pending(CasId),
}

/// Checked access to the hardcoded indexed BLAKE3 CAS.
pub struct Blake3Cas<'db> {
    connection: &'db mut Connection,
    metatable: Metatable,
}

impl Blake3Cas<'_> {
    /// Declares a content address whose bytes may be fetched later.
    ///
    /// Repeated declarations return the same local identity.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be updated.
    pub fn declare(&mut self, hash: O256) -> Result<CasId, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .execute(
                &format!("INSERT OR IGNORE INTO {table} (hash) VALUES (?1)"),
                [hash.as_bytes().as_slice()],
            )
            .map_err(TrustedDbError::sqlite)?;
        self.id_for_hash(hash)
    }

    /// Stores bytes under their computed BLAKE3 digest.
    ///
    /// This also fills a previously declared lazy reference.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be updated.
    pub fn put(&mut self, data: &[u8]) -> Result<(CasId, O256), TrustedDbError> {
        let hash = O256::blake3(data);
        let id = self.provide(hash, data)?;
        Ok((id, hash))
    }

    /// Supplies bytes for an expected BLAKE3 digest.
    ///
    /// The digest is checked before trusted state is changed.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::ContentHashMismatch`] when the bytes do not
    /// match, or a typed database error if the relation cannot be updated.
    pub fn provide(&mut self, expected: O256, data: &[u8]) -> Result<CasId, TrustedDbError> {
        let actual = O256::blake3(data);
        if actual != expected {
            return Err(TrustedDbError::ContentHashMismatch { expected, actual });
        }
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .execute(
                &format!(
                    "INSERT INTO {table} (hash, data) VALUES (?1, ?2)
                     ON CONFLICT(hash) DO UPDATE SET data = excluded.data
                     WHERE {table}.data IS NULL"
                ),
                params![expected.as_bytes().as_slice(), data],
            )
            .map_err(TrustedDbError::sqlite)?;
        self.id_for_hash(expected)
    }

    /// Reads an entry by stable content address.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be read.
    pub fn entry(&self, hash: O256) -> Result<Option<CasEntry>, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .query_row(
                &format!("SELECT id, hash, data FROM {table} WHERE hash = ?1"),
                [hash.as_bytes().as_slice()],
                |row| {
                    let stored_hash = row.get::<_, Vec<u8>>(1)?;
                    Ok((CasId(row.get(0)?), stored_hash, row.get(2)?))
                },
            )
            .optional()
            .map_err(TrustedDbError::sqlite)?
            .map(|(id, stored_hash, data)| {
                let bytes: [u8; 32] = stored_hash
                    .try_into()
                    .map_err(|_| TrustedDbError::InvalidStoredHash { id })?;
                Ok(CasEntry {
                    id,
                    hash: O256::from_bytes(bytes),
                    data,
                })
            })
            .transpose()
    }

    fn id_for_hash(&self, hash: O256) -> Result<CasId, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .query_row(
                &format!("SELECT id FROM {table} WHERE hash = ?1"),
                [hash.as_bytes().as_slice()],
                |row| row.get::<_, i64>(0).map(CasId),
            )
            .map_err(TrustedDbError::sqlite)
    }
}

impl RustTypes<'_> {
    /// Registers `T`'s diagnostic Rust type name and returns its local ID.
    ///
    /// Repeated registration of the same name returns the same ID.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if insertion or lookup fails.
    pub fn register<T: ?Sized>(&mut self) -> Result<RustTypeId, TrustedDbError> {
        self.register_name(type_name::<T>())
    }

    /// Returns all registered IDs and diagnostic names in ID order.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the registry cannot be read.
    pub fn entries(&self) -> Result<Vec<(RustTypeId, String)>, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        let mut statement = self
            .connection
            .prepare(&format!("SELECT id, rust_type FROM {table} ORDER BY id"))
            .map_err(TrustedDbError::sqlite)?;
        statement
            .query_map((), |row| {
                Ok((RustTypeId(row.get(0)?), row.get::<_, String>(1)?))
            })
            .map_err(TrustedDbError::sqlite)?
            .collect::<Result<Vec<_>, _>>()
            .map_err(TrustedDbError::sqlite)
    }

    fn register_name(&mut self, name: &str) -> Result<RustTypeId, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .execute(
                &format!("INSERT OR IGNORE INTO {table} (rust_type) VALUES (?1)"),
                [name],
            )
            .map_err(TrustedDbError::sqlite)?;
        self.connection
            .query_row(
                &format!("SELECT id FROM {table} WHERE rust_type = ?1"),
                [name],
                |row| row.get::<_, i64>(0).map(RustTypeId),
            )
            .map_err(TrustedDbError::sqlite)
    }
}

/// Failure while constructing or using the exclusive trusted wrapper.
#[derive(Debug, Snafu)]
#[snafu(crate_root(snafu))]
pub enum TrustedDbError {
    /// `SQLite` failed within a checked operation.
    #[snafu(display("trusted SQLite operation failed: {source}"))]
    Sqlite {
        /// Underlying failure.
        source: covalence_lib_sqlite::Error,
    },
    /// Mechanical metatable scanning failed.
    #[snafu(display("could not scan metatables: {source}"))]
    Scan {
        /// Scanner failure.
        source: ScanError,
    },
    /// Structurally valid metadata was not accepted by compiled policy.
    #[snafu(display("could not accept Neutron catalog: {source}"))]
    Catalog {
        /// Acceptance failure.
        source: CatalogError,
    },
    /// The Rust-type extension has not been installed.
    #[snafu(display("the Rust-type metatable is not installed"))]
    MissingRustTypes,
    /// The BLAKE3 CAS extension has not been installed.
    #[snafu(display("the BLAKE3 CAS metatable is not installed"))]
    MissingBlake3Cas,
    /// Bytes supplied by an effect or caller did not match their address.
    #[snafu(display("content hash mismatch: expected {expected}, computed {actual}"))]
    ContentHashMismatch {
        /// Requested content address.
        expected: O256,
        /// Digest computed over the supplied bytes.
        actual: O256,
    },
    /// A trusted CAS row contained a malformed digest.
    #[snafu(display("CAS row {} contains a malformed hash", id.get()))]
    InvalidStoredHash {
        /// Connection-local row identity.
        id: CasId,
    },
    /// A resolver capability ID was empty.
    #[snafu(display("resolver capability ID must not be empty"))]
    InvalidResolverId,
    /// A resolver capability ID was already registered on this connection.
    #[snafu(display("resolver capability `{id}` is already registered"))]
    DuplicateResolver {
        /// Duplicate connection-local resolver ID.
        id: String,
    },
    /// An explicitly registered resolver failed operationally.
    #[snafu(display("resolver capability `{id}` failed: {source}"))]
    Resolver {
        /// Connection-local resolver ID.
        id: String,
        /// Resolver-provided diagnostic.
        source: ResolveError,
    },
}

impl TrustedDbError {
    fn sqlite(source: covalence_lib_sqlite::Error) -> Self {
        Self::Sqlite { source }
    }

    const fn scan(source: ScanError) -> Self {
        Self::Scan { source }
    }

    const fn catalog(source: CatalogError) -> Self {
        Self::Catalog { source }
    }
}

fn validate_rust_types_metatable(
    connection: &Connection,
    metatable: &Metatable,
) -> Result<(), CatalogError> {
    let expected = metatable_name(MetatableKind::new(RUST_TYPES_METATABLE_V0));
    if metatable.table_name != expected {
        return Err(CatalogError::WrongInterpretationTable {
            interpretation: metatable.interpretation.clone(),
            expected,
            actual: metatable.table_name.clone(),
        });
    }
    if !table_is_strict(connection, &metatable.table_name)? {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: metatable.interpretation.clone(),
            reason: String::from("table must be STRICT"),
        });
    }
    let columns = table_columns(connection, &metatable.table_name)?;
    let expected_columns = [
        ("id", "INTEGER", false, 1_u32),
        ("rust_type", "TEXT", true, 0),
    ];
    if columns.len() != expected_columns.len()
        || !columns.iter().zip(expected_columns).all(
            |((actual_name, actual_type, not_null, pk), expected)| {
                actual_name == expected.0
                    && actual_type == expected.1
                    && *not_null == expected.2
                    && *pk == expected.3
            },
        )
    {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: metatable.interpretation.clone(),
            reason: String::from("columns do not match the Rust-type registry contract"),
        });
    }
    Ok(())
}

fn validate_blake3_cas_metatable(
    connection: &Connection,
    metatable: &Metatable,
) -> Result<(), CatalogError> {
    let expected = metatable_name(MetatableKind::new(BLAKE3_CAS_METATABLE_V0));
    if metatable.table_name != expected {
        return Err(CatalogError::WrongInterpretationTable {
            interpretation: metatable.interpretation.clone(),
            expected,
            actual: metatable.table_name.clone(),
        });
    }
    if !table_is_strict(connection, &metatable.table_name)? {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: metatable.interpretation.clone(),
            reason: String::from("table must be STRICT"),
        });
    }
    let columns = table_columns(connection, &metatable.table_name)?;
    let expected_columns = [
        ("id", "INTEGER", false, 1_u32),
        ("hash", "BLOB", true, 0),
        ("data", "BLOB", false, 0),
    ];
    if columns.len() != expected_columns.len()
        || !columns.iter().zip(expected_columns).all(
            |((actual_name, actual_type, not_null, pk), expected)| {
                actual_name == expected.0
                    && actual_type == expected.1
                    && *not_null == expected.2
                    && *pk == expected.3
            },
        )
    {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: metatable.interpretation.clone(),
            reason: String::from("columns do not match the indexed BLAKE3 CAS contract"),
        });
    }
    Ok(())
}

type PhysicalColumn = (String, String, bool, u32);

fn table_columns(
    connection: &Connection,
    table: &str,
) -> Result<Vec<PhysicalColumn>, CatalogError> {
    let mut statement = connection
        .prepare(&format!(
            "PRAGMA main.table_info({})",
            quote_identifier(table)
        ))
        .map_err(|source| CatalogError::ValidationSqlite { source })?;
    statement
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, i64>(3)? != 0,
                row.get::<_, u32>(5)?,
            ))
        })
        .map_err(|source| CatalogError::ValidationSqlite { source })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|source| CatalogError::ValidationSqlite { source })
}

fn table_is_strict(connection: &Connection, table: &str) -> Result<bool, CatalogError> {
    connection
        .query_row(
            "SELECT strict FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
            [table],
            |row| row.get::<_, i64>(0),
        )
        .optional()
        .map(|strict| strict == Some(1))
        .map_err(|source| CatalogError::ValidationSqlite { source })
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::rc::Rc;

    use covalence_lib_hash::O256;

    use super::{
        BlobRequest, BlobResolver, CasEntry, CasLoad, InstallOutcome, ResolveError, TrustedDb,
        TrustedDbError,
    };

    struct FakeResolver {
        calls: Rc<Cell<usize>>,
        answer: Option<Vec<u8>>,
    }

    impl BlobResolver for FakeResolver {
        fn resolve(&mut self, _request: BlobRequest) -> Result<Option<Vec<u8>>, ResolveError> {
            self.calls.set(self.calls.get() + 1);
            Ok(self.answer.clone())
        }
    }

    struct FailingResolver;

    impl BlobResolver for FailingResolver {
        fn resolve(&mut self, _request: BlobRequest) -> Result<Option<Vec<u8>>, ResolveError> {
            Err(ResolveError::new("offline"))
        }
    }

    #[test]
    fn creation_accepts_an_empty_bootstrap() {
        let database = TrustedDb::create_in_memory().unwrap();
        assert_eq!(database.generation(), 0);
        assert!(database.catalog().metatables().is_empty());
    }

    #[test]
    fn no_typed_extension_exists_before_installation() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert!(matches!(
            database.rust_types(),
            Err(TrustedDbError::MissingRustTypes)
        ));
    }

    #[test]
    fn rust_type_registry_is_installed_through_the_bootstrap() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert_eq!(
            database.install_rust_types().unwrap(),
            InstallOutcome::Installed
        );
        assert_eq!(
            database.install_rust_types().unwrap(),
            InstallOutcome::AlreadyPresent
        );
        assert_eq!(database.generation(), 1);
        assert_eq!(database.catalog().metatables().len(), 1);

        let mut types = database.rust_types().unwrap();
        let bool_id = types.register::<bool>().unwrap();
        assert_eq!(types.register::<bool>().unwrap(), bool_id);
        let u64_id = types.register::<u64>().unwrap();
        assert_ne!(bool_id, u64_id);
        assert_eq!(
            types.entries().unwrap(),
            vec![
                (bool_id, String::from("bool")),
                (u64_id, String::from("u64"))
            ]
        );
    }

    #[test]
    fn blake3_cas_distinguishes_lazy_and_available_content() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert!(matches!(
            database.blake3_cas(),
            Err(TrustedDbError::MissingBlake3Cas)
        ));
        assert_eq!(
            database.install_blake3_cas().unwrap(),
            InstallOutcome::Installed
        );
        assert_eq!(
            database.install_blake3_cas().unwrap(),
            InstallOutcome::AlreadyPresent
        );

        let data = b"theorem";
        let hash = O256::blake3(data);
        let mut cas = database.blake3_cas().unwrap();
        let declared = cas.declare(hash).unwrap();
        assert_eq!(cas.entry(hash).unwrap().unwrap().data, None,);
        let stored = cas.provide(hash, data).unwrap();
        assert_eq!(stored, declared);
        assert_eq!(cas.entry(hash).unwrap().unwrap().data, Some(data.to_vec()),);
        assert_eq!(cas.put(data).unwrap(), (declared, hash));
    }

    #[test]
    fn blake3_cas_rejects_mismatched_content() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_blake3_cas().unwrap();
        let expected = O256::blake3(b"expected");
        let mut cas = database.blake3_cas().unwrap();
        assert!(matches!(
            cas.provide(expected, b"different"),
            Err(TrustedDbError::ContentHashMismatch { .. })
        ));
        assert_eq!(cas.entry(expected).unwrap(), None);
    }

    #[test]
    fn resolver_fills_the_cache_and_is_skipped_on_the_next_load() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_blake3_cas().unwrap();
        let data = b"resolved theorem".to_vec();
        let hash = O256::blake3(&data);
        let calls = Rc::new(Cell::new(0));
        database
            .register_blob_resolver(
                "fixture",
                FakeResolver {
                    calls: Rc::clone(&calls),
                    answer: Some(data.clone()),
                },
            )
            .unwrap();

        let CasLoad::Resident(first) = database.load_blake3(hash).unwrap() else {
            panic!("resolver should make the object resident");
        };
        assert_eq!(first.data, Some(data.clone()));
        assert_eq!(calls.get(), 1);

        let CasLoad::Resident(second) = database.load_blake3(hash).unwrap() else {
            panic!("cache should remain resident");
        };
        assert_eq!(second, first);
        assert_eq!(calls.get(), 1);
    }

    #[test]
    fn resolver_miss_leaves_a_pending_reference() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_blake3_cas().unwrap();
        database
            .register_blob_resolver(
                "miss",
                FakeResolver {
                    calls: Rc::new(Cell::new(0)),
                    answer: None,
                },
            )
            .unwrap();
        let hash = O256::blake3(b"absent");

        let CasLoad::Pending(id) = database.load_blake3(hash).unwrap() else {
            panic!("all resolvers missed");
        };
        assert_eq!(
            database.blake3_cas().unwrap().entry(hash).unwrap(),
            Some(CasEntry {
                id,
                hash,
                data: None,
            })
        );
    }

    #[test]
    fn lying_resolver_cannot_mutate_pending_trusted_data() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_blake3_cas().unwrap();
        database
            .register_blob_resolver(
                "liar",
                FakeResolver {
                    calls: Rc::new(Cell::new(0)),
                    answer: Some(b"wrong".to_vec()),
                },
            )
            .unwrap();
        let hash = O256::blake3(b"right");

        assert!(matches!(
            database.load_blake3(hash),
            Err(TrustedDbError::ContentHashMismatch { .. })
        ));
        assert_eq!(
            database
                .blake3_cas()
                .unwrap()
                .entry(hash)
                .unwrap()
                .unwrap()
                .data,
            None
        );
    }

    #[test]
    fn resolver_failures_remain_distinct_from_misses() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_blake3_cas().unwrap();
        database
            .register_blob_resolver("offline", FailingResolver)
            .unwrap();
        let hash = O256::blake3(b"right");

        assert!(matches!(
            database.load_blake3(hash),
            Err(TrustedDbError::Resolver { id, .. }) if id == "offline"
        ));
        assert_eq!(
            database
                .blake3_cas()
                .unwrap()
                .entry(hash)
                .unwrap()
                .unwrap()
                .data,
            None
        );
    }

    #[test]
    fn resolver_capability_ids_are_explicit_and_cannot_be_replaced() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert!(matches!(
            database.register_blob_resolver("", FailingResolver),
            Err(TrustedDbError::InvalidResolverId)
        ));
        database
            .register_blob_resolver("source", FailingResolver)
            .unwrap();
        assert!(matches!(
            database.register_blob_resolver("source", FailingResolver),
            Err(TrustedDbError::DuplicateResolver { id }) if id == "source"
        ));
    }
}
