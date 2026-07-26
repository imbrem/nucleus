use std::{any::type_name, collections::BTreeSet};

use covalence_lib_error::snafu;
use covalence_lib_hash::O256;
use covalence_lib_sqlite::{Connection, OptionalExtension, params};
use covalence_neutron::{
    BLAKE3_CAS_INTERPRETATION_V0, BLAKE3_CAS_METATABLE_V0, BOOTSTRAP_CATALOG,
    CAS_INSTANCES_INTERPRETATION_V0, CAS_INSTANCES_METATABLE_V0, CatalogCandidate,
    DIRECT_KV_INTERPRETATION_V0, DIRECT_KV_METATABLE_V0, HASH_ALGORITHMS_INTERPRETATION_V0,
    HASH_ALGORITHMS_METATABLE_V0, INDEXED_KV_INTERPRETATION_V0, INDEXED_KV_METATABLE_V0,
    MIXED_HASH_CAS_INTERPRETATION_V0, MIXED_HASH_CAS_METATABLE_V0, MetatableKind,
    RUST_TYPES_INTERPRETATION_V0, RUST_TYPES_METATABLE_V0, ScanError, metatable_name,
    scan_metatables,
};
use snafu::Snafu;

const TEMP_BLAKE3_CACHE: &str = "covalence_cache_blake3_v0";

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
            } else if metatable.interpretation == INDEXED_KV_INTERPRETATION_V0 {
                validate_indexed_kv_metatable(connection, metatable)?;
            } else if metatable.interpretation == DIRECT_KV_INTERPRETATION_V0 {
                validate_direct_kv_metatable(connection, metatable)?;
            } else if metatable.interpretation == HASH_ALGORITHMS_INTERPRETATION_V0 {
                validate_hash_algorithms_metatable(connection, metatable)?;
            } else if metatable.interpretation == MIXED_HASH_CAS_INTERPRETATION_V0 {
                validate_mixed_hash_cas_metatable(connection, metatable)?;
            } else if metatable.interpretation == CAS_INSTANCES_INTERPRETATION_V0 {
                validate_cas_instances_metatable(connection, metatable)?;
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
    blake3_temp_cache: bool,
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
            blake3_temp_cache: false,
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

    /// Installs the indexed and direct KV reference relations atomically.
    ///
    /// The indexed table has a local integer DEF identity in addition to its
    /// unique byte key. The direct table uses its byte key as the physical
    /// primary key and is stored `WITHOUT ROWID`. In both relations a present
    /// row with `value IS NULL` is distinct from an absent row.
    ///
    /// # Errors
    ///
    /// Returns a checked database, scan, or catalog error. A pre-existing
    /// partial family is rejected rather than silently repaired.
    pub fn install_kv_relations(&mut self) -> Result<InstallOutcome, TrustedDbError> {
        let indexed_present = self
            .catalog
            .by_interpretation(INDEXED_KV_INTERPRETATION_V0)
            .is_some();
        let direct_present = self
            .catalog
            .by_interpretation(DIRECT_KV_INTERPRETATION_V0)
            .is_some();
        match (indexed_present, direct_present) {
            (true, true) => return Ok(InstallOutcome::AlreadyPresent),
            (true, false) | (false, true) => return Err(TrustedDbError::PartialKvFamily),
            (false, false) => {}
        }

        let transaction = self
            .connection
            .transaction()
            .map_err(TrustedDbError::sqlite)?;
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        let indexed = metatable_name(MetatableKind::new(INDEXED_KV_METATABLE_V0));
        let direct = metatable_name(MetatableKind::new(DIRECT_KV_METATABLE_V0));
        transaction
            .execute_batch(&format!(
                "CREATE TABLE \"{indexed}\" (
                    id INTEGER PRIMARY KEY,
                    key BLOB NOT NULL UNIQUE,
                    value BLOB
                ) STRICT;
                CREATE TABLE \"{direct}\" (
                    key BLOB PRIMARY KEY,
                    value BLOB
                ) STRICT, WITHOUT ROWID;"
            ))
            .map_err(TrustedDbError::sqlite)?;
        transaction
            .execute(
                &format!(
                    "INSERT INTO \"{bootstrap}\" (table_name, interpretation)
                     VALUES (?1, ?2), (?3, ?4)"
                ),
                params![
                    indexed,
                    INDEXED_KV_INTERPRETATION_V0,
                    direct,
                    DIRECT_KV_INTERPRETATION_V0
                ],
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

    /// Resolves the installed indexed KV relation as a checked capability.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::MissingKvRelations`] before installation.
    pub fn indexed_kv(&mut self) -> Result<IndexedKv<'_>, TrustedDbError> {
        let metatable = self
            .catalog
            .by_interpretation(INDEXED_KV_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingKvRelations)?;
        Ok(IndexedKv {
            connection: &mut self.connection,
            metatable,
        })
    }

    /// Resolves the installed direct KV relation as a checked capability.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::MissingKvRelations`] before installation.
    pub fn direct_kv(&mut self) -> Result<DirectKv<'_>, TrustedDbError> {
        let metatable = self
            .catalog
            .by_interpretation(DIRECT_KV_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingKvRelations)?;
        Ok(DirectKv {
            connection: &mut self.connection,
            metatable,
        })
    }

    /// Installs a finite compiled hash-algorithm registry and mixed CAS.
    ///
    /// The two tables form one atomic family. The CAS stores an explicit USE
    /// of the algorithm DEF, so equal-width digests from different algorithms
    /// occupy disjoint address spaces.
    ///
    /// # Errors
    ///
    /// Returns a checked database, scan, or catalog error. A pre-existing
    /// partial family is rejected rather than silently repaired.
    pub fn install_hash_cas_relations(&mut self) -> Result<InstallOutcome, TrustedDbError> {
        let algorithms_present = self
            .catalog
            .by_interpretation(HASH_ALGORITHMS_INTERPRETATION_V0)
            .is_some();
        let cas_present = self
            .catalog
            .by_interpretation(MIXED_HASH_CAS_INTERPRETATION_V0)
            .is_some();
        match (algorithms_present, cas_present) {
            (true, true) => return Ok(InstallOutcome::AlreadyPresent),
            (true, false) | (false, true) => return Err(TrustedDbError::PartialHashCasFamily),
            (false, false) => {}
        }

        let transaction = self
            .connection
            .transaction()
            .map_err(TrustedDbError::sqlite)?;
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        let algorithms = metatable_name(MetatableKind::new(HASH_ALGORITHMS_METATABLE_V0));
        let cas = metatable_name(MetatableKind::new(MIXED_HASH_CAS_METATABLE_V0));
        transaction
            .execute_batch(&format!(
                "CREATE TABLE \"{algorithms}\" (
                    id INTEGER PRIMARY KEY,
                    stable_name TEXT NOT NULL UNIQUE
                ) STRICT;
                CREATE TABLE \"{cas}\" (
                    id INTEGER PRIMARY KEY,
                    algorithm_id INTEGER NOT NULL REFERENCES \"{algorithms}\"(id),
                    digest BLOB NOT NULL CHECK (length(digest) = 32),
                    data BLOB,
                    UNIQUE (algorithm_id, digest)
                ) STRICT;"
            ))
            .map_err(TrustedDbError::sqlite)?;
        for algorithm in HashAlgorithm::ALL {
            transaction
                .execute(
                    &format!("INSERT INTO \"{algorithms}\" (stable_name) VALUES (?1)"),
                    [algorithm.stable_name()],
                )
                .map_err(TrustedDbError::sqlite)?;
        }
        transaction
            .execute(
                &format!(
                    "INSERT INTO \"{bootstrap}\" (table_name, interpretation)
                     VALUES (?1, ?2), (?3, ?4)"
                ),
                params![
                    algorithms,
                    HASH_ALGORITHMS_INTERPRETATION_V0,
                    cas,
                    MIXED_HASH_CAS_INTERPRETATION_V0
                ],
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

    /// Resolves the finite hash-algorithm relation as a checked capability.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::MissingHashCasRelations`] before installation.
    pub fn hash_algorithms(&mut self) -> Result<HashAlgorithms<'_>, TrustedDbError> {
        let metatable = self
            .catalog
            .by_interpretation(HASH_ALGORITHMS_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingHashCasRelations)?;
        Ok(HashAlgorithms {
            connection: &mut self.connection,
            metatable,
        })
    }

    /// Resolves the mixed-algorithm CAS as a checked capability.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::MissingHashCasRelations`] before installation.
    pub fn mixed_hash_cas(&mut self) -> Result<MixedHashCas<'_>, TrustedDbError> {
        let algorithms = self
            .catalog
            .by_interpretation(HASH_ALGORITHMS_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingHashCasRelations)?;
        let cas = self
            .catalog
            .by_interpretation(MIXED_HASH_CAS_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingHashCasRelations)?;
        Ok(MixedHashCas {
            connection: &mut self.connection,
            algorithms,
            cas,
        })
    }

    /// Installs the singleton owner registry for ordinary CAS table instances.
    ///
    /// The finite hash-algorithm relation must already be installed. The root
    /// bootstrap owns this registry; each registry row uniquely owns and
    /// interprets one non-reserved ordinary table.
    ///
    /// # Errors
    ///
    /// Returns a typed error when the hash family is absent or when atomic
    /// installation, scanning, or catalog acceptance fails.
    pub fn install_cas_instance_registry(&mut self) -> Result<InstallOutcome, TrustedDbError> {
        if self
            .catalog
            .by_interpretation(CAS_INSTANCES_INTERPRETATION_V0)
            .is_some()
        {
            return Ok(InstallOutcome::AlreadyPresent);
        }
        let algorithms = self
            .catalog
            .by_interpretation(HASH_ALGORITHMS_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingHashCasRelations)?;
        let transaction = self
            .connection
            .transaction()
            .map_err(TrustedDbError::sqlite)?;
        let bootstrap = metatable_name(MetatableKind::new(BOOTSTRAP_CATALOG));
        let instances = metatable_name(MetatableKind::new(CAS_INSTANCES_METATABLE_V0));
        transaction
            .execute_batch(&format!(
                "CREATE TABLE \"{instances}\" (
                    id INTEGER PRIMARY KEY,
                    table_name TEXT NOT NULL UNIQUE,
                    algorithm_id INTEGER NOT NULL
                        REFERENCES \"{}\"(id)
                ) STRICT;",
                algorithms.table_name
            ))
            .map_err(TrustedDbError::sqlite)?;
        transaction
            .execute(
                &format!(
                    "INSERT INTO \"{bootstrap}\" (table_name, interpretation) VALUES (?1, ?2)"
                ),
                params![instances, CAS_INSTANCES_INTERPRETATION_V0],
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

    /// Creates one ordinary CAS table owned by the instance registry.
    ///
    /// `table_name` uses a deliberately narrow ASCII identifier policy for
    /// this probe. The physical table, owner row, rescan, and acceptance are
    /// one transaction.
    ///
    /// # Errors
    ///
    /// Rejects invalid names, absent registry/algorithm relations, an
    /// unowned pre-existing table, conflicting ownership parameters, or any
    /// checked database/catalog failure.
    pub fn create_cas_instance(
        &mut self,
        table_name: &str,
        algorithm: HashAlgorithm,
    ) -> Result<CreateCasInstanceOutcome, TrustedDbError> {
        validate_instance_table_name(table_name)?;
        let instances = self
            .catalog
            .by_interpretation(CAS_INSTANCES_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingCasInstanceRegistry)?;
        let algorithms = self
            .catalog
            .by_interpretation(HASH_ALGORITHMS_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingHashCasRelations)?;
        let instances_table = quote_identifier(&instances.table_name);
        let existing = read_cas_instance(
            &self.connection,
            &instances_table,
            &quote_identifier(&algorithms.table_name),
            table_name,
        )?;
        if let Some(existing) = existing {
            if existing.algorithm == algorithm {
                return Ok(CreateCasInstanceOutcome::AlreadyPresent(existing.id));
            }
            return Err(TrustedDbError::CasInstanceAlgorithmConflict {
                table_name: table_name.to_owned(),
                existing: existing.algorithm,
                requested: algorithm,
            });
        }
        if main_table_exists(&self.connection, table_name)? {
            return Err(TrustedDbError::UnownedTableExists {
                table_name: table_name.to_owned(),
            });
        }

        let transaction = self
            .connection
            .transaction()
            .map_err(TrustedDbError::sqlite)?;
        let algorithm_id = hash_algorithm_id(
            &transaction,
            &quote_identifier(&algorithms.table_name),
            algorithm,
        )?;
        let table = quote_identifier(table_name);
        transaction
            .execute_batch(&format!(
                "CREATE TABLE {table} (
                    id INTEGER PRIMARY KEY,
                    digest BLOB NOT NULL UNIQUE CHECK (length(digest) = 32),
                    data BLOB
                ) STRICT;"
            ))
            .map_err(TrustedDbError::sqlite)?;
        transaction
            .execute(
                &format!(
                    "INSERT INTO {instances_table} (table_name, algorithm_id) VALUES (?1, ?2)"
                ),
                params![table_name, algorithm_id.get()],
            )
            .map_err(TrustedDbError::sqlite)?;
        let id = CasInstanceId(transaction.last_insert_rowid());
        let candidate = scan_metatables(&transaction).map_err(TrustedDbError::scan)?;
        let catalog =
            NeutronCatalog::accept(&candidate, &transaction).map_err(TrustedDbError::catalog)?;
        transaction.commit().map_err(TrustedDbError::sqlite)?;
        self.catalog = catalog;
        self.generation += 1;
        Ok(CreateCasInstanceOutcome::Created(id))
    }

    /// Returns the accepted definitions owned by the CAS-instance registry.
    ///
    /// # Errors
    ///
    /// Returns a typed error before installation or when the checked registry
    /// cannot be read.
    pub fn cas_instances(&self) -> Result<Vec<CasInstanceDefinition>, TrustedDbError> {
        let instances = self
            .catalog
            .by_interpretation(CAS_INSTANCES_INTERPRETATION_V0)
            .ok_or(TrustedDbError::MissingCasInstanceRegistry)?;
        let algorithms = self
            .catalog
            .by_interpretation(HASH_ALGORITHMS_INTERPRETATION_V0)
            .ok_or(TrustedDbError::MissingHashCasRelations)?;
        read_cas_instances(
            &self.connection,
            &quote_identifier(&instances.table_name),
            &quote_identifier(&algorithms.table_name),
        )
    }

    /// Resolves one owned ordinary CAS table as a checked capability.
    ///
    /// # Errors
    ///
    /// Returns a typed error when the registry is absent or does not own
    /// `table_name`.
    pub fn cas_instance(&mut self, table_name: &str) -> Result<CasInstance<'_>, TrustedDbError> {
        validate_instance_table_name(table_name)?;
        let instances = self
            .catalog
            .by_interpretation(CAS_INSTANCES_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingCasInstanceRegistry)?;
        let algorithms = self
            .catalog
            .by_interpretation(HASH_ALGORITHMS_INTERPRETATION_V0)
            .cloned()
            .ok_or(TrustedDbError::MissingHashCasRelations)?;
        let definition = read_cas_instance(
            &self.connection,
            &quote_identifier(&instances.table_name),
            &quote_identifier(&algorithms.table_name),
            table_name,
        )?
        .ok_or_else(|| TrustedDbError::UnknownCasInstance {
            table_name: table_name.to_owned(),
        })?;
        Ok(CasInstance {
            connection: &mut self.connection,
            definition,
        })
    }

    /// Installs a checked connection-local BLAKE3 CAS in `SQLite`'s `temp` schema.
    ///
    /// This table is computational cache state, not a persisted relation
    /// interpretation. It therefore uses a non-metatable name and is not
    /// registered in the permanent bootstrap catalog.
    ///
    /// # Errors
    ///
    /// Fails atomically if the exact STRICT cache shape cannot be created and
    /// validated.
    pub fn install_blake3_temp_cache(&mut self) -> Result<InstallOutcome, TrustedDbError> {
        if self.blake3_temp_cache {
            return Ok(InstallOutcome::AlreadyPresent);
        }
        let transaction = self
            .connection
            .transaction()
            .map_err(TrustedDbError::sqlite)?;
        transaction
            .execute_batch(&format!(
                "CREATE TEMP TABLE \"{TEMP_BLAKE3_CACHE}\" (
                    id INTEGER PRIMARY KEY,
                    hash BLOB NOT NULL UNIQUE CHECK (length(hash) = 32),
                    data BLOB
                ) STRICT;"
            ))
            .map_err(TrustedDbError::sqlite)?;
        validate_temp_blake3_cache(&transaction)?;
        transaction.commit().map_err(TrustedDbError::sqlite)?;
        self.blake3_temp_cache = true;
        Ok(InstallOutcome::Installed)
    }

    /// Resolves the installed connection-local temp CAS.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::MissingBlake3TempCache`] before installation.
    pub fn blake3_temp_cache(&mut self) -> Result<TempBlake3Cas<'_>, TrustedDbError> {
        if !self.blake3_temp_cache {
            return Err(TrustedDbError::MissingBlake3TempCache);
        }
        Ok(TempBlake3Cas {
            connection: &mut self.connection,
        })
    }

    /// Loads BLAKE3 bytes through temp cache, main CAS, then resolvers.
    ///
    /// A validated main or resolver hit is copied only into the temp cache.
    /// Resolver output does not promote itself into the persisted main
    /// relation. All-source miss leaves an explicit pending temp-cache row.
    ///
    /// # Errors
    ///
    /// Returns a typed failure for missing cache/main capabilities, resolver
    /// failure, content mismatch, or a checked database operation.
    pub fn load_blake3_cached(&mut self, hash: O256) -> Result<TempCasLoad, TrustedDbError> {
        let (id, cached) = {
            let mut cache = self.blake3_temp_cache()?;
            let id = cache.declare(hash)?;
            (id, cache.entry(hash)?)
        };
        if let Some(entry) = cached
            && entry.data.is_some()
        {
            return Ok(TempCasLoad::Resident(entry));
        }

        let main = self.blake3_cas()?.entry(hash)?;
        if let Some(data) = main.and_then(|entry| entry.data) {
            let id = self.blake3_temp_cache()?.provide(hash, &data)?;
            return Ok(TempCasLoad::Resident(TempCasEntry {
                id,
                hash,
                data: Some(data),
            }));
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
                let id = self.blake3_temp_cache()?.provide(hash, &data)?;
                return Ok(TempCasLoad::Resident(TempCasEntry {
                    id,
                    hash,
                    data: Some(data),
                }));
            }
        }
        Ok(TempCasLoad::Pending(id))
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

/// Connection-local DEF identity assigned by the temp BLAKE3 cache.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TempCasId(i64);

impl TempCasId {
    /// Returns the stored `SQLite` integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One checked row from the connection-local temp BLAKE3 cache.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TempCasEntry {
    /// Temp-schema-local identity.
    pub id: TempCasId,
    /// Stable BLAKE3 address.
    pub hash: O256,
    /// Resident bytes, or `None` for a pending cache entry.
    pub data: Option<Vec<u8>>,
}

/// Result of fused lookup through temp cache, main CAS, and resolvers.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TempCasLoad {
    /// Validated bytes are resident in the temp cache.
    Resident(TempCasEntry),
    /// No source produced bytes; the temp address remains pending.
    Pending(TempCasId),
}

/// Checked access to the connection-local temp BLAKE3 CAS.
pub struct TempBlake3Cas<'db> {
    connection: &'db mut Connection,
}

impl TempBlake3Cas<'_> {
    /// Declares a pending temp-cache address.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the cache cannot be updated.
    pub fn declare(&mut self, hash: O256) -> Result<TempCasId, TrustedDbError> {
        let table = temp_blake3_cache_identifier();
        self.connection
            .execute(
                &format!("INSERT OR IGNORE INTO {table} (hash) VALUES (?1)"),
                [hash.as_bytes().as_slice()],
            )
            .map_err(TrustedDbError::sqlite)?;
        self.id_for_hash(hash)
    }

    /// Supplies validated bytes to the temp cache.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::ContentHashMismatch`] before mutation when
    /// the bytes do not match their BLAKE3 address.
    pub fn provide(&mut self, expected: O256, data: &[u8]) -> Result<TempCasId, TrustedDbError> {
        let actual = O256::blake3(data);
        if actual != expected {
            return Err(TrustedDbError::ContentHashMismatch { expected, actual });
        }
        let table = temp_blake3_cache_identifier();
        self.connection
            .execute(
                &format!(
                    "INSERT INTO {table} (hash, data) VALUES (?1, ?2)
                     ON CONFLICT(hash) DO UPDATE SET data = excluded.data
                     WHERE data IS NULL"
                ),
                params![expected.as_bytes().as_slice(), data],
            )
            .map_err(TrustedDbError::sqlite)?;
        self.id_for_hash(expected)
    }

    /// Reads a temp-cache entry by BLAKE3 address.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the cache cannot be read.
    pub fn entry(&self, hash: O256) -> Result<Option<TempCasEntry>, TrustedDbError> {
        let table = temp_blake3_cache_identifier();
        self.connection
            .query_row(
                &format!("SELECT id, hash, data FROM {table} WHERE hash = ?1"),
                [hash.as_bytes().as_slice()],
                |row| {
                    Ok((
                        TempCasId(row.get(0)?),
                        row.get::<_, Vec<u8>>(1)?,
                        row.get(2)?,
                    ))
                },
            )
            .optional()
            .map_err(TrustedDbError::sqlite)?
            .map(|(id, stored_hash, data)| {
                let bytes: [u8; 32] = stored_hash
                    .try_into()
                    .map_err(|_| TrustedDbError::InvalidTempStoredHash { id })?;
                Ok(TempCasEntry {
                    id,
                    hash: O256::from_bytes(bytes),
                    data,
                })
            })
            .transpose()
    }

    fn id_for_hash(&self, hash: O256) -> Result<TempCasId, TrustedDbError> {
        let table = temp_blake3_cache_identifier();
        self.connection
            .query_row(
                &format!("SELECT id FROM {table} WHERE hash = ?1"),
                [hash.as_bytes().as_slice()],
                |row| row.get::<_, i64>(0).map(TempCasId),
            )
            .map_err(TrustedDbError::sqlite)
    }
}

fn temp_blake3_cache_identifier() -> String {
    format!("\"temp\".{}", quote_identifier(TEMP_BLAKE3_CACHE))
}

/// Connection-local DEF identity assigned by the indexed KV relation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct IndexedKvId(i64);

impl IndexedKvId {
    /// Returns the stored `SQLite` integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One row from the indexed KV relation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IndexedKvEntry {
    /// Connection-local row identity.
    pub id: IndexedKvId,
    /// Unique quoted byte key.
    pub key: Vec<u8>,
    /// Explicit optional value; `None` means a present pending entry.
    pub value: Option<Vec<u8>>,
}

/// One row from the direct `WITHOUT ROWID` KV relation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DirectKvEntry {
    /// Primary quoted byte key.
    pub key: Vec<u8>,
    /// Explicit optional value; `None` means a present pending entry.
    pub value: Option<Vec<u8>>,
}

/// Checked access to a mutable indexed byte KV relation.
pub struct IndexedKv<'db> {
    connection: &'db mut Connection,
    metatable: Metatable,
}

impl IndexedKv<'_> {
    /// Inserts or replaces the value for `key`, preserving its local identity.
    ///
    /// Passing `None` creates or restores an explicit pending entry.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be updated.
    pub fn set(&mut self, key: &[u8], value: Option<&[u8]>) -> Result<IndexedKvId, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .execute(
                &format!(
                    "INSERT INTO {table} (key, value) VALUES (?1, ?2)
                     ON CONFLICT(key) DO UPDATE SET value = excluded.value"
                ),
                params![key, value],
            )
            .map_err(TrustedDbError::sqlite)?;
        self.connection
            .query_row(
                &format!("SELECT id FROM {table} WHERE key = ?1"),
                [key],
                |row| row.get::<_, i64>(0).map(IndexedKvId),
            )
            .map_err(TrustedDbError::sqlite)
    }

    /// Reads a row by quoted byte key.
    ///
    /// `Ok(None)` means no row. A returned entry whose value is `None` is a
    /// distinct present/pending row.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be read.
    pub fn entry(&self, key: &[u8]) -> Result<Option<IndexedKvEntry>, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .query_row(
                &format!("SELECT id, key, value FROM {table} WHERE key = ?1"),
                [key],
                |row| {
                    Ok(IndexedKvEntry {
                        id: IndexedKvId(row.get(0)?),
                        key: row.get(1)?,
                        value: row.get(2)?,
                    })
                },
            )
            .optional()
            .map_err(TrustedDbError::sqlite)
    }
}

/// Checked access to a mutable direct byte KV relation.
pub struct DirectKv<'db> {
    connection: &'db mut Connection,
    metatable: Metatable,
}

impl DirectKv<'_> {
    /// Inserts or replaces the value for `key`.
    ///
    /// Passing `None` creates or restores an explicit pending entry.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be updated.
    pub fn set(&mut self, key: &[u8], value: Option<&[u8]>) -> Result<(), TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .execute(
                &format!(
                    "INSERT INTO {table} (key, value) VALUES (?1, ?2)
                     ON CONFLICT(key) DO UPDATE SET value = excluded.value"
                ),
                params![key, value],
            )
            .map_err(TrustedDbError::sqlite)?;
        Ok(())
    }

    /// Reads a row by primary byte key.
    ///
    /// `Ok(None)` means no row. A returned entry whose value is `None` is a
    /// distinct present/pending row.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be read.
    pub fn entry(&self, key: &[u8]) -> Result<Option<DirectKvEntry>, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        self.connection
            .query_row(
                &format!("SELECT key, value FROM {table} WHERE key = ?1"),
                [key],
                |row| {
                    Ok(DirectKvEntry {
                        key: row.get(0)?,
                        value: row.get(1)?,
                    })
                },
            )
            .optional()
            .map_err(TrustedDbError::sqlite)
    }
}

/// One compiled 256-bit hash algorithm named by the finite registry.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum HashAlgorithm {
    /// BLAKE3 with its default 256-bit output.
    Blake3,
    /// SHA-256.
    Sha256,
}

impl HashAlgorithm {
    /// Every algorithm admitted by the v0 compiled interpretation.
    pub const ALL: [Self; 2] = [Self::Blake3, Self::Sha256];

    /// Returns the stable name stored in the algorithm relation.
    #[must_use]
    pub const fn stable_name(self) -> &'static str {
        match self {
            Self::Blake3 => "blake3",
            Self::Sha256 => "sha256",
        }
    }

    /// Computes this algorithm's 256-bit digest.
    #[must_use]
    pub fn digest(self, data: &[u8]) -> O256 {
        match self {
            Self::Blake3 => O256::blake3(data),
            Self::Sha256 => O256::sha256(data),
        }
    }

    fn from_stable_name(name: &str) -> Option<Self> {
        match name {
            "blake3" => Some(Self::Blake3),
            "sha256" => Some(Self::Sha256),
            _ => None,
        }
    }
}

/// Connection-local DEF identity for one compiled hash algorithm.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HashAlgorithmId(i64);

impl HashAlgorithmId {
    /// Returns the stored `SQLite` integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One row from the finite hash-algorithm relation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct HashAlgorithmEntry {
    /// Connection-local DEF identity.
    pub id: HashAlgorithmId,
    /// Compiled algorithm selected by the stable name.
    pub algorithm: HashAlgorithm,
}

/// A portable mixed-CAS address whose algorithm is explicit.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct HashAddress {
    /// Hash algorithm.
    pub algorithm: HashAlgorithm,
    /// Raw 256-bit digest under that algorithm.
    pub digest: O256,
}

/// Connection-local DEF identity assigned by the mixed CAS relation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MixedCasId(i64);

impl MixedCasId {
    /// Returns the stored `SQLite` integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One checked row from the mixed-algorithm CAS.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MixedCasEntry {
    /// Connection-local object identity.
    pub id: MixedCasId,
    /// Algorithm-qualified content address.
    pub address: HashAddress,
    /// Resident bytes, or `None` for a pending reference.
    pub data: Option<Vec<u8>>,
}

/// Checked access to the finite compiled hash-algorithm relation.
pub struct HashAlgorithms<'db> {
    connection: &'db mut Connection,
    metatable: Metatable,
}

impl HashAlgorithms<'_> {
    /// Returns compiled algorithms in connection-local ID order.
    ///
    /// # Errors
    ///
    /// Returns a typed error if the relation cannot be read or contains an
    /// algorithm outside the accepted finite interpretation.
    pub fn entries(&self) -> Result<Vec<HashAlgorithmEntry>, TrustedDbError> {
        let table = quote_identifier(&self.metatable.table_name);
        let mut statement = self
            .connection
            .prepare(&format!("SELECT id, stable_name FROM {table} ORDER BY id"))
            .map_err(TrustedDbError::sqlite)?;
        statement
            .query_map((), |row| {
                Ok((row.get::<_, i64>(0)?, row.get::<_, String>(1)?))
            })
            .map_err(TrustedDbError::sqlite)?
            .map(|row| {
                let (id, name) = row.map_err(TrustedDbError::sqlite)?;
                let algorithm = HashAlgorithm::from_stable_name(&name)
                    .ok_or(TrustedDbError::UnknownHashAlgorithm { name })?;
                Ok(HashAlgorithmEntry {
                    id: HashAlgorithmId(id),
                    algorithm,
                })
            })
            .collect()
    }
}

/// Checked access to the hardcoded mixed-algorithm CAS.
pub struct MixedHashCas<'db> {
    connection: &'db mut Connection,
    algorithms: Metatable,
    cas: Metatable,
}

impl MixedHashCas<'_> {
    /// Declares an algorithm-qualified address whose bytes may arrive later.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be updated.
    pub fn declare(&mut self, address: HashAddress) -> Result<MixedCasId, TrustedDbError> {
        let algorithms = quote_identifier(&self.algorithms.table_name);
        let cas = quote_identifier(&self.cas.table_name);
        let algorithm_id = hash_algorithm_id(self.connection, &algorithms, address.algorithm)?;
        self.connection
            .execute(
                &format!("INSERT OR IGNORE INTO {cas} (algorithm_id, digest) VALUES (?1, ?2)"),
                params![algorithm_id.get(), address.digest.as_bytes().as_slice()],
            )
            .map_err(TrustedDbError::sqlite)?;
        mixed_cas_id(self.connection, &cas, algorithm_id, address.digest)
    }

    /// Stores bytes under an address computed with `algorithm`.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be updated.
    pub fn put(
        &mut self,
        algorithm: HashAlgorithm,
        data: &[u8],
    ) -> Result<(MixedCasId, HashAddress), TrustedDbError> {
        let address = HashAddress {
            algorithm,
            digest: algorithm.digest(data),
        };
        let id = self.provide(address, data)?;
        Ok((id, address))
    }

    /// Supplies bytes for an expected algorithm-qualified address.
    ///
    /// # Errors
    ///
    /// Returns [`TrustedDbError::ContentHashMismatch`] before mutation when
    /// the selected algorithm computes a different digest.
    pub fn provide(
        &mut self,
        address: HashAddress,
        data: &[u8],
    ) -> Result<MixedCasId, TrustedDbError> {
        let actual = address.algorithm.digest(data);
        if actual != address.digest {
            return Err(TrustedDbError::ContentHashMismatch {
                expected: address.digest,
                actual,
            });
        }
        let algorithms = quote_identifier(&self.algorithms.table_name);
        let cas = quote_identifier(&self.cas.table_name);
        let algorithm_id = hash_algorithm_id(self.connection, &algorithms, address.algorithm)?;
        self.connection
            .execute(
                &format!(
                    "INSERT INTO {cas} (algorithm_id, digest, data) VALUES (?1, ?2, ?3)
                     ON CONFLICT(algorithm_id, digest) DO UPDATE SET data = excluded.data
                     WHERE {cas}.data IS NULL"
                ),
                params![
                    algorithm_id.get(),
                    address.digest.as_bytes().as_slice(),
                    data
                ],
            )
            .map_err(TrustedDbError::sqlite)?;
        mixed_cas_id(self.connection, &cas, algorithm_id, address.digest)
    }

    /// Reads one row by algorithm-qualified address.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the relation cannot be read.
    pub fn entry(&self, address: HashAddress) -> Result<Option<MixedCasEntry>, TrustedDbError> {
        let algorithms = quote_identifier(&self.algorithms.table_name);
        let cas = quote_identifier(&self.cas.table_name);
        let algorithm_id = hash_algorithm_id(self.connection, &algorithms, address.algorithm)?;
        self.connection
            .query_row(
                &format!(
                    "SELECT id, data FROM {cas}
                     WHERE algorithm_id = ?1 AND digest = ?2"
                ),
                params![algorithm_id.get(), address.digest.as_bytes().as_slice()],
                |row| Ok((MixedCasId(row.get(0)?), row.get(1)?)),
            )
            .optional()
            .map(|entry| entry.map(|(id, data)| MixedCasEntry { id, address, data }))
            .map_err(TrustedDbError::sqlite)
    }
}

/// Connection-local DEF identity for one owned CAS relation instance.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CasInstanceId(i64);

impl CasInstanceId {
    /// Returns the stored `SQLite` integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One accepted ownership/parameter row for an ordinary CAS table.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CasInstanceDefinition {
    /// Connection-local instance identity.
    pub id: CasInstanceId,
    /// Unquoted physical table locator in `main`.
    pub table_name: String,
    /// Compiled algorithm parameter applied to every row in the child table.
    pub algorithm: HashAlgorithm,
}

/// Result of requesting a uniquely named CAS instance.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CreateCasInstanceOutcome {
    /// A physical table and ownership row were created atomically.
    Created(CasInstanceId),
    /// The registry already owned an instance with the same algorithm.
    AlreadyPresent(CasInstanceId),
}

/// Connection-local object identity defined inside one CAS instance.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CasInstanceObjectId(i64);

impl CasInstanceObjectId {
    /// Returns the stored `SQLite` integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// One row read from an owned algorithm-parameterized CAS instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CasInstanceEntry {
    /// Identity local to the child table.
    pub id: CasInstanceObjectId,
    /// Algorithm-qualified portable address.
    pub address: HashAddress,
    /// Resident bytes, or `None` for a pending reference.
    pub data: Option<Vec<u8>>,
}

/// Checked access to one ordinary CAS table through its unique owner row.
pub struct CasInstance<'db> {
    connection: &'db mut Connection,
    definition: CasInstanceDefinition,
}

impl CasInstance<'_> {
    /// Returns this physical relation's accepted ownership/parameter row.
    #[must_use]
    pub const fn definition(&self) -> &CasInstanceDefinition {
        &self.definition
    }

    /// Declares an address under this instance's algorithm parameter.
    ///
    /// # Errors
    ///
    /// Rejects an address from another algorithm and returns a typed database
    /// error if the owned relation cannot be updated.
    pub fn declare(&mut self, address: HashAddress) -> Result<CasInstanceObjectId, TrustedDbError> {
        self.require_algorithm(address)?;
        let table = quote_identifier(&self.definition.table_name);
        self.connection
            .execute(
                &format!("INSERT OR IGNORE INTO {table} (digest) VALUES (?1)"),
                [address.digest.as_bytes().as_slice()],
            )
            .map_err(TrustedDbError::sqlite)?;
        self.id_for_digest(address.digest)
    }

    /// Stores bytes under this instance's fixed algorithm parameter.
    ///
    /// # Errors
    ///
    /// Returns a typed database error if the owned relation cannot be updated.
    pub fn put(
        &mut self,
        data: &[u8],
    ) -> Result<(CasInstanceObjectId, HashAddress), TrustedDbError> {
        let address = HashAddress {
            algorithm: self.definition.algorithm,
            digest: self.definition.algorithm.digest(data),
        };
        let id = self.provide(address, data)?;
        Ok((id, address))
    }

    /// Supplies bytes for an address under the fixed algorithm parameter.
    ///
    /// # Errors
    ///
    /// Rejects the wrong algorithm or digest before trusted mutation.
    pub fn provide(
        &mut self,
        address: HashAddress,
        data: &[u8],
    ) -> Result<CasInstanceObjectId, TrustedDbError> {
        self.require_algorithm(address)?;
        let actual = self.definition.algorithm.digest(data);
        if actual != address.digest {
            return Err(TrustedDbError::ContentHashMismatch {
                expected: address.digest,
                actual,
            });
        }
        let table = quote_identifier(&self.definition.table_name);
        self.connection
            .execute(
                &format!(
                    "INSERT INTO {table} (digest, data) VALUES (?1, ?2)
                     ON CONFLICT(digest) DO UPDATE SET data = excluded.data
                     WHERE data IS NULL"
                ),
                params![address.digest.as_bytes().as_slice(), data],
            )
            .map_err(TrustedDbError::sqlite)?;
        self.id_for_digest(address.digest)
    }

    /// Reads an address under the fixed algorithm parameter.
    ///
    /// # Errors
    ///
    /// Rejects an address from another algorithm or a database read failure.
    pub fn entry(&self, address: HashAddress) -> Result<Option<CasInstanceEntry>, TrustedDbError> {
        self.require_algorithm(address)?;
        let table = quote_identifier(&self.definition.table_name);
        self.connection
            .query_row(
                &format!("SELECT id, data FROM {table} WHERE digest = ?1"),
                [address.digest.as_bytes().as_slice()],
                |row| Ok((CasInstanceObjectId(row.get(0)?), row.get(1)?)),
            )
            .optional()
            .map(|entry| entry.map(|(id, data)| CasInstanceEntry { id, address, data }))
            .map_err(TrustedDbError::sqlite)
    }

    fn require_algorithm(&self, address: HashAddress) -> Result<(), TrustedDbError> {
        if address.algorithm == self.definition.algorithm {
            Ok(())
        } else {
            Err(TrustedDbError::CasInstanceAddressAlgorithm {
                table_name: self.definition.table_name.clone(),
                expected: self.definition.algorithm,
                actual: address.algorithm,
            })
        }
    }

    fn id_for_digest(&self, digest: O256) -> Result<CasInstanceObjectId, TrustedDbError> {
        let table = quote_identifier(&self.definition.table_name);
        self.connection
            .query_row(
                &format!("SELECT id FROM {table} WHERE digest = ?1"),
                [digest.as_bytes().as_slice()],
                |row| row.get::<_, i64>(0).map(CasInstanceObjectId),
            )
            .map_err(TrustedDbError::sqlite)
    }
}

fn read_cas_instance(
    connection: &Connection,
    instances: &str,
    algorithms: &str,
    table_name: &str,
) -> Result<Option<CasInstanceDefinition>, TrustedDbError> {
    connection
        .query_row(
            &format!(
                "SELECT i.id, i.table_name, a.stable_name
                 FROM {instances} AS i
                 JOIN {algorithms} AS a ON a.id = i.algorithm_id
                 WHERE i.table_name = ?1"
            ),
            [table_name],
            |row| {
                Ok((
                    CasInstanceId(row.get(0)?),
                    row.get::<_, String>(1)?,
                    row.get::<_, String>(2)?,
                ))
            },
        )
        .optional()
        .map_err(TrustedDbError::sqlite)?
        .map(|(id, table_name, name)| {
            let algorithm = HashAlgorithm::from_stable_name(&name)
                .ok_or(TrustedDbError::UnknownHashAlgorithm { name })?;
            Ok(CasInstanceDefinition {
                id,
                table_name,
                algorithm,
            })
        })
        .transpose()
}

fn read_cas_instances(
    connection: &Connection,
    instances: &str,
    algorithms: &str,
) -> Result<Vec<CasInstanceDefinition>, TrustedDbError> {
    let mut statement = connection
        .prepare(&format!(
            "SELECT i.id, i.table_name, a.stable_name
             FROM {instances} AS i
             JOIN {algorithms} AS a ON a.id = i.algorithm_id
             ORDER BY i.id"
        ))
        .map_err(TrustedDbError::sqlite)?;
    statement
        .query_map((), |row| {
            Ok((
                CasInstanceId(row.get(0)?),
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
            ))
        })
        .map_err(TrustedDbError::sqlite)?
        .map(|row| {
            let (id, table_name, name) = row.map_err(TrustedDbError::sqlite)?;
            let algorithm = HashAlgorithm::from_stable_name(&name)
                .ok_or(TrustedDbError::UnknownHashAlgorithm { name })?;
            Ok(CasInstanceDefinition {
                id,
                table_name,
                algorithm,
            })
        })
        .collect()
}

fn validate_instance_table_name(table_name: &str) -> Result<(), TrustedDbError> {
    if instance_table_name_is_valid(table_name) {
        Ok(())
    } else {
        Err(TrustedDbError::InvalidCasInstanceName {
            table_name: table_name.to_owned(),
        })
    }
}

fn instance_table_name_is_valid(table_name: &str) -> bool {
    let mut bytes = table_name.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    first.is_ascii_lowercase()
        && bytes.all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'_')
        && !table_name.starts_with("sqlite_")
        && !table_name.starts_with(covalence_neutron::META_PREFIX)
        && table_name != TEMP_BLAKE3_CACHE
}

fn main_table_exists(connection: &Connection, table_name: &str) -> Result<bool, TrustedDbError> {
    connection
        .query_row(
            "SELECT 1 FROM main.sqlite_schema WHERE type = 'table' AND name = ?1",
            [table_name],
            |_| Ok(()),
        )
        .optional()
        .map(|row| row.is_some())
        .map_err(TrustedDbError::sqlite)
}

fn hash_algorithm_id(
    connection: &Connection,
    algorithms: &str,
    algorithm: HashAlgorithm,
) -> Result<HashAlgorithmId, TrustedDbError> {
    connection
        .query_row(
            &format!("SELECT id FROM {algorithms} WHERE stable_name = ?1"),
            [algorithm.stable_name()],
            |row| row.get::<_, i64>(0).map(HashAlgorithmId),
        )
        .map_err(TrustedDbError::sqlite)
}

fn mixed_cas_id(
    connection: &Connection,
    cas: &str,
    algorithm: HashAlgorithmId,
    digest: O256,
) -> Result<MixedCasId, TrustedDbError> {
    connection
        .query_row(
            &format!(
                "SELECT id FROM {cas}
                 WHERE algorithm_id = ?1 AND digest = ?2"
            ),
            params![algorithm.get(), digest.as_bytes().as_slice()],
            |row| row.get::<_, i64>(0).map(MixedCasId),
        )
        .map_err(TrustedDbError::sqlite)
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
                     WHERE data IS NULL"
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
    /// Exactly one member of the atomic KV reference family was present.
    #[snafu(display("indexed and direct KV relations must be installed as one family"))]
    PartialKvFamily,
    /// The KV reference family has not been installed.
    #[snafu(display("the indexed/direct KV relation family is not installed"))]
    MissingKvRelations,
    /// Exactly one member of the hash-algorithm/CAS family was present.
    #[snafu(display("hash algorithms and mixed CAS must be installed as one family"))]
    PartialHashCasFamily,
    /// The hash-algorithm/CAS family has not been installed.
    #[snafu(display("the hash-algorithm/mixed-CAS relation family is not installed"))]
    MissingHashCasRelations,
    /// The accepted finite registry contained an unknown algorithm name.
    #[snafu(display("unknown compiled hash algorithm `{name}`"))]
    UnknownHashAlgorithm {
        /// Unrecognized stable name.
        name: String,
    },
    /// The connection-local temp BLAKE3 cache has not been installed.
    #[snafu(display("the connection-local temp BLAKE3 cache is not installed"))]
    MissingBlake3TempCache,
    /// A trusted temp-cache row contained a malformed digest.
    #[snafu(display("temp CAS row {} contains a malformed hash", id.get()))]
    InvalidTempStoredHash {
        /// Temp-schema-local row identity.
        id: TempCasId,
    },
    /// The connection-local cache did not match its compiled physical ABI.
    #[snafu(display("invalid temp BLAKE3 cache schema: {reason}"))]
    InvalidTempCacheSchema {
        /// Stable rejection detail.
        reason: String,
    },
    /// The owner registry has not been installed.
    #[snafu(display("the CAS-instance owner registry is not installed"))]
    MissingCasInstanceRegistry,
    /// A requested child name was outside the narrow v0 identifier policy.
    #[snafu(display("invalid CAS-instance table name `{table_name}`"))]
    InvalidCasInstanceName {
        /// Rejected physical name.
        table_name: String,
    },
    /// An ordinary physical table existed without an accepted owner row.
    #[snafu(display("ordinary table `{table_name}` already exists without CAS ownership"))]
    UnownedTableExists {
        /// Conflicting physical name.
        table_name: String,
    },
    /// One owner row was requested with a conflicting algorithm parameter.
    #[snafu(display(
        "CAS instance `{table_name}` already uses {existing:?}, requested {requested:?}"
    ))]
    CasInstanceAlgorithmConflict {
        /// Owned physical table.
        table_name: String,
        /// Accepted parameter.
        existing: HashAlgorithm,
        /// Conflicting requested parameter.
        requested: HashAlgorithm,
    },
    /// No accepted owner row named the requested ordinary table.
    #[snafu(display("unknown owned CAS instance `{table_name}`"))]
    UnknownCasInstance {
        /// Requested physical name.
        table_name: String,
    },
    /// An address used a different algorithm from its table parameter.
    #[snafu(display("CAS instance `{table_name}` requires {expected:?}, address used {actual:?}"))]
    CasInstanceAddressAlgorithm {
        /// Owned physical table.
        table_name: String,
        /// Instance algorithm parameter.
        expected: HashAlgorithm,
        /// Address algorithm.
        actual: HashAlgorithm,
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

fn validate_temp_blake3_cache(connection: &Connection) -> Result<(), TrustedDbError> {
    let strict = connection
        .query_row(
            "SELECT strict FROM pragma_table_list WHERE schema = 'temp' AND name = ?1",
            [TEMP_BLAKE3_CACHE],
            |row| row.get::<_, i64>(0),
        )
        .optional()
        .map_err(TrustedDbError::sqlite)?;
    if strict != Some(1) {
        return Err(TrustedDbError::InvalidTempCacheSchema {
            reason: String::from("cache must be a STRICT table in temp"),
        });
    }
    let mut statement = connection
        .prepare(&format!(
            "PRAGMA temp.table_info({})",
            quote_identifier(TEMP_BLAKE3_CACHE)
        ))
        .map_err(TrustedDbError::sqlite)?;
    let columns = statement
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, i64>(3)? != 0,
                row.get::<_, u32>(5)?,
            ))
        })
        .map_err(TrustedDbError::sqlite)?
        .collect::<Result<Vec<_>, _>>()
        .map_err(TrustedDbError::sqlite)?;
    let expected = [
        ("id", "INTEGER", false, 1_u32),
        ("hash", "BLOB", true, 0),
        ("data", "BLOB", false, 0),
    ];
    if columns.len() != expected.len()
        || !columns.iter().zip(expected).all(
            |((actual_name, actual_type, not_null, pk), expected)| {
                actual_name == expected.0
                    && actual_type == expected.1
                    && *not_null == expected.2
                    && *pk == expected.3
            },
        )
    {
        return Err(TrustedDbError::InvalidTempCacheSchema {
            reason: String::from("columns do not match the indexed BLAKE3 cache contract"),
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

fn validate_indexed_kv_metatable(
    connection: &Connection,
    metatable: &Metatable,
) -> Result<(), CatalogError> {
    validate_kv_metatable(
        connection,
        metatable,
        INDEXED_KV_METATABLE_V0,
        &[
            ("id", "INTEGER", false, 1_u32),
            ("key", "BLOB", true, 0),
            ("value", "BLOB", false, 0),
        ],
        false,
    )
}

fn validate_direct_kv_metatable(
    connection: &Connection,
    metatable: &Metatable,
) -> Result<(), CatalogError> {
    validate_kv_metatable(
        connection,
        metatable,
        DIRECT_KV_METATABLE_V0,
        &[("key", "BLOB", true, 1_u32), ("value", "BLOB", false, 0)],
        true,
    )
}

fn validate_hash_algorithms_metatable(
    connection: &Connection,
    metatable: &Metatable,
) -> Result<(), CatalogError> {
    let expected = metatable_name(MetatableKind::new(HASH_ALGORITHMS_METATABLE_V0));
    validate_fixed_table(
        connection,
        metatable,
        &expected,
        &[
            ("id", "INTEGER", false, 1_u32),
            ("stable_name", "TEXT", true, 0),
        ],
        "finite hash-algorithm relation",
    )
}

fn validate_mixed_hash_cas_metatable(
    connection: &Connection,
    metatable: &Metatable,
) -> Result<(), CatalogError> {
    let expected = metatable_name(MetatableKind::new(MIXED_HASH_CAS_METATABLE_V0));
    validate_fixed_table(
        connection,
        metatable,
        &expected,
        &[
            ("id", "INTEGER", false, 1_u32),
            ("algorithm_id", "INTEGER", true, 0),
            ("digest", "BLOB", true, 0),
            ("data", "BLOB", false, 0),
        ],
        "mixed hash CAS",
    )?;
    let algorithms = metatable_name(MetatableKind::new(HASH_ALGORITHMS_METATABLE_V0));
    let foreign_keys = table_foreign_keys(connection, &metatable.table_name)?;
    if foreign_keys != [(String::from("algorithm_id"), algorithms, String::from("id"))] {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: metatable.interpretation.clone(),
            reason: String::from("algorithm_id must reference the finite hash-algorithm relation"),
        });
    }
    Ok(())
}

fn validate_cas_instances_metatable(
    connection: &Connection,
    metatable: &Metatable,
) -> Result<(), CatalogError> {
    let expected = metatable_name(MetatableKind::new(CAS_INSTANCES_METATABLE_V0));
    validate_fixed_table(
        connection,
        metatable,
        &expected,
        &[
            ("id", "INTEGER", false, 1_u32),
            ("table_name", "TEXT", true, 0),
            ("algorithm_id", "INTEGER", true, 0),
        ],
        "CAS-instance owner registry",
    )?;
    let algorithms = metatable_name(MetatableKind::new(HASH_ALGORITHMS_METATABLE_V0));
    let foreign_keys = table_foreign_keys(connection, &metatable.table_name)?;
    if foreign_keys != [(String::from("algorithm_id"), algorithms, String::from("id"))] {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: metatable.interpretation.clone(),
            reason: String::from("algorithm_id must reference the finite hash-algorithm relation"),
        });
    }

    let mut statement = connection
        .prepare(&format!(
            "SELECT table_name FROM {} ORDER BY id",
            quote_identifier(&metatable.table_name)
        ))
        .map_err(|source| CatalogError::ValidationSqlite { source })?;
    let table_names = statement
        .query_map((), |row| row.get::<_, String>(0))
        .map_err(|source| CatalogError::ValidationSqlite { source })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|source| CatalogError::ValidationSqlite { source })?;
    for table_name in table_names {
        if !instance_table_name_is_valid(&table_name) {
            return Err(CatalogError::InvalidExtensionSchema {
                interpretation: metatable.interpretation.clone(),
                reason: format!("owned child has invalid physical name `{table_name}`"),
            });
        }
        validate_owned_cas_table(connection, metatable, &table_name)?;
    }
    Ok(())
}

fn validate_owned_cas_table(
    connection: &Connection,
    owner: &Metatable,
    table_name: &str,
) -> Result<(), CatalogError> {
    if !table_is_strict(connection, table_name)? {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: owner.interpretation.clone(),
            reason: format!("owned child `{table_name}` must be STRICT in main"),
        });
    }
    let columns = table_columns(connection, table_name)?;
    let expected = [
        ("id", "INTEGER", false, 1_u32),
        ("digest", "BLOB", true, 0),
        ("data", "BLOB", false, 0),
    ];
    if columns.len() != expected.len()
        || !columns.iter().zip(expected).all(
            |((actual_name, actual_type, not_null, pk), expected)| {
                actual_name == expected.0
                    && actual_type == expected.1
                    && *not_null == expected.2
                    && *pk == expected.3
            },
        )
    {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: owner.interpretation.clone(),
            reason: format!("owned child `{table_name}` has the wrong CAS shape"),
        });
    }
    Ok(())
}

fn validate_fixed_table(
    connection: &Connection,
    metatable: &Metatable,
    expected_table: &str,
    expected_columns: &[(&str, &str, bool, u32)],
    contract: &str,
) -> Result<(), CatalogError> {
    if metatable.table_name != expected_table {
        return Err(CatalogError::WrongInterpretationTable {
            interpretation: metatable.interpretation.clone(),
            expected: expected_table.to_owned(),
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
            reason: format!("columns do not match the {contract} contract"),
        });
    }
    Ok(())
}

fn validate_kv_metatable(
    connection: &Connection,
    metatable: &Metatable,
    kind: O256,
    expected_columns: &[(&str, &str, bool, u32)],
    expected_without_rowid: bool,
) -> Result<(), CatalogError> {
    let expected = metatable_name(MetatableKind::new(kind));
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
    if table_is_without_rowid(connection, &metatable.table_name)? != expected_without_rowid {
        return Err(CatalogError::InvalidExtensionSchema {
            interpretation: metatable.interpretation.clone(),
            reason: String::from("WITHOUT ROWID policy does not match the KV contract"),
        });
    }
    let columns = table_columns(connection, &metatable.table_name)?;
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
            reason: String::from("columns do not match the KV relation contract"),
        });
    }
    Ok(())
}

type PhysicalColumn = (String, String, bool, u32);
type PhysicalForeignKey = (String, String, String);

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

fn table_foreign_keys(
    connection: &Connection,
    table: &str,
) -> Result<Vec<PhysicalForeignKey>, CatalogError> {
    let mut statement = connection
        .prepare(&format!(
            "PRAGMA main.foreign_key_list({})",
            quote_identifier(table)
        ))
        .map_err(|source| CatalogError::ValidationSqlite { source })?;
    statement
        .query_map((), |row| {
            Ok((
                row.get::<_, String>(3)?,
                row.get::<_, String>(2)?,
                row.get::<_, String>(4)?,
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

fn table_is_without_rowid(connection: &Connection, table: &str) -> Result<bool, CatalogError> {
    connection
        .query_row(
            "SELECT wr FROM pragma_table_list WHERE schema = 'main' AND name = ?1",
            [table],
            |row| row.get::<_, i64>(0),
        )
        .optional()
        .map(|without_rowid| without_rowid == Some(1))
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
        BlobRequest, BlobResolver, CasEntry, CasLoad, CreateCasInstanceOutcome, HashAddress,
        HashAlgorithm, InstallOutcome, ResolveError, TempCasLoad, TrustedDb, TrustedDbError,
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
    fn kv_relations_install_as_one_catalog_family() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert!(matches!(
            database.indexed_kv(),
            Err(TrustedDbError::MissingKvRelations)
        ));
        assert!(matches!(
            database.direct_kv(),
            Err(TrustedDbError::MissingKvRelations)
        ));
        assert_eq!(
            database.install_kv_relations().unwrap(),
            InstallOutcome::Installed
        );
        assert_eq!(
            database.install_kv_relations().unwrap(),
            InstallOutcome::AlreadyPresent
        );
        assert_eq!(database.generation(), 1);
        assert_eq!(database.catalog().metatables().len(), 2);
    }

    #[test]
    fn indexed_kv_preserves_identity_across_mutable_values() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_kv_relations().unwrap();
        let mut kv = database.indexed_kv().unwrap();
        assert_eq!(kv.entry(b"k").unwrap(), None);

        let id = kv.set(b"k", None).unwrap();
        assert_eq!(
            kv.entry(b"k").unwrap(),
            Some(super::IndexedKvEntry {
                id,
                key: b"k".to_vec(),
                value: None,
            })
        );
        assert_eq!(kv.set(b"k", Some(b"v")).unwrap(), id);
        assert_eq!(kv.entry(b"k").unwrap().unwrap().value, Some(b"v".to_vec()));
        assert_eq!(kv.set(b"k", None).unwrap(), id);
        assert_eq!(kv.entry(b"k").unwrap().unwrap().value, None);
    }

    #[test]
    fn direct_kv_distinguishes_absence_pending_and_value() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_kv_relations().unwrap();
        let mut kv = database.direct_kv().unwrap();
        assert_eq!(kv.entry(b"k").unwrap(), None);

        kv.set(b"k", None).unwrap();
        assert_eq!(
            kv.entry(b"k").unwrap(),
            Some(super::DirectKvEntry {
                key: b"k".to_vec(),
                value: None,
            })
        );
        kv.set(b"k", Some(b"v")).unwrap();
        assert_eq!(kv.entry(b"k").unwrap().unwrap().value, Some(b"v".to_vec()));
    }

    #[test]
    fn finite_hash_algorithms_define_distinct_local_ids() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert!(matches!(
            database.hash_algorithms(),
            Err(TrustedDbError::MissingHashCasRelations)
        ));
        assert_eq!(
            database.install_hash_cas_relations().unwrap(),
            InstallOutcome::Installed
        );
        assert_eq!(
            database.install_hash_cas_relations().unwrap(),
            InstallOutcome::AlreadyPresent
        );
        let entries = database.hash_algorithms().unwrap().entries().unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].algorithm, HashAlgorithm::Blake3);
        assert_eq!(entries[1].algorithm, HashAlgorithm::Sha256);
        assert_ne!(entries[0].id, entries[1].id);
    }

    #[test]
    fn mixed_cas_qualifies_equal_data_by_hash_algorithm() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_hash_cas_relations().unwrap();
        let data = b"same bytes";
        let mut cas = database.mixed_hash_cas().unwrap();
        let (blake3_id, blake3) = cas.put(HashAlgorithm::Blake3, data).unwrap();
        let (sha256_id, sha256) = cas.put(HashAlgorithm::Sha256, data).unwrap();

        assert_ne!(blake3, sha256);
        assert_ne!(blake3_id, sha256_id);
        assert_eq!(
            cas.entry(blake3).unwrap().unwrap().data,
            Some(data.to_vec())
        );
        assert_eq!(
            cas.entry(sha256).unwrap().unwrap().data,
            Some(data.to_vec())
        );
    }

    #[test]
    fn mixed_cas_validates_with_the_selected_algorithm() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_hash_cas_relations().unwrap();
        let data = b"expected";
        let address = HashAddress {
            algorithm: HashAlgorithm::Sha256,
            digest: HashAlgorithm::Sha256.digest(data),
        };
        let mut cas = database.mixed_hash_cas().unwrap();
        let id = cas.declare(address).unwrap();
        assert_eq!(cas.entry(address).unwrap().unwrap().data, None);
        assert!(matches!(
            cas.provide(address, b"different"),
            Err(TrustedDbError::ContentHashMismatch { .. })
        ));
        assert_eq!(cas.entry(address).unwrap().unwrap().data, None);
        assert_eq!(cas.provide(address, data).unwrap(), id);
    }

    #[test]
    fn temp_cache_is_computational_state_outside_the_bootstrap_catalog() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        assert!(matches!(
            database.blake3_temp_cache(),
            Err(TrustedDbError::MissingBlake3TempCache)
        ));
        assert_eq!(
            database.install_blake3_temp_cache().unwrap(),
            InstallOutcome::Installed
        );
        assert_eq!(
            database.install_blake3_temp_cache().unwrap(),
            InstallOutcome::AlreadyPresent
        );
        assert_eq!(database.generation(), 0);
        assert!(database.catalog().metatables().is_empty());
    }

    #[test]
    fn fused_lookup_copies_main_into_temp_before_calling_effects() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_blake3_cas().unwrap();
        database.install_blake3_temp_cache().unwrap();
        let data = b"persistent source".to_vec();
        let hash = O256::blake3(&data);
        database.blake3_cas().unwrap().put(&data).unwrap();
        let calls = Rc::new(Cell::new(0));
        database
            .register_blob_resolver(
                "unused",
                FakeResolver {
                    calls: Rc::clone(&calls),
                    answer: Some(b"wrong".to_vec()),
                },
            )
            .unwrap();

        let TempCasLoad::Resident(entry) = database.load_blake3_cached(hash).unwrap() else {
            panic!("main CAS should populate temp");
        };
        assert_eq!(entry.data, Some(data));
        assert_eq!(calls.get(), 0);
        assert!(
            database
                .blake3_temp_cache()
                .unwrap()
                .entry(hash)
                .unwrap()
                .unwrap()
                .data
                .is_some()
        );
    }

    #[test]
    fn resolver_hit_populates_temp_without_promoting_main() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_blake3_cas().unwrap();
        database.install_blake3_temp_cache().unwrap();
        let data = b"effect candidate".to_vec();
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

        let TempCasLoad::Resident(entry) = database.load_blake3_cached(hash).unwrap() else {
            panic!("resolver should populate temp");
        };
        assert_eq!(entry.data, Some(data));
        assert_eq!(calls.get(), 1);
        assert_eq!(database.blake3_cas().unwrap().entry(hash).unwrap(), None);

        assert!(matches!(
            database.load_blake3_cached(hash).unwrap(),
            TempCasLoad::Resident(_)
        ));
        assert_eq!(calls.get(), 1);
    }

    #[test]
    fn lying_resolver_leaves_only_a_pending_temp_entry() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_blake3_cas().unwrap();
        database.install_blake3_temp_cache().unwrap();
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
            database.load_blake3_cached(hash),
            Err(TrustedDbError::ContentHashMismatch { .. })
        ));
        assert_eq!(
            database
                .blake3_temp_cache()
                .unwrap()
                .entry(hash)
                .unwrap()
                .unwrap()
                .data,
            None
        );
        assert_eq!(database.blake3_cas().unwrap().entry(hash).unwrap(), None);
    }

    #[test]
    fn owner_registry_creates_multiple_parameterized_cas_tables() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_hash_cas_relations().unwrap();
        assert_eq!(
            database.install_cas_instance_registry().unwrap(),
            InstallOutcome::Installed
        );
        assert_eq!(
            database.install_cas_instance_registry().unwrap(),
            InstallOutcome::AlreadyPresent
        );
        let CreateCasInstanceOutcome::Created(blake3_instance) = database
            .create_cas_instance("objects_blake3", HashAlgorithm::Blake3)
            .unwrap()
        else {
            panic!("fresh instance");
        };
        let CreateCasInstanceOutcome::Created(sha256_instance) = database
            .create_cas_instance("objects_sha256", HashAlgorithm::Sha256)
            .unwrap()
        else {
            panic!("fresh instance");
        };
        assert_ne!(blake3_instance, sha256_instance);
        assert_eq!(
            database
                .create_cas_instance("objects_blake3", HashAlgorithm::Blake3)
                .unwrap(),
            CreateCasInstanceOutcome::AlreadyPresent(blake3_instance)
        );

        let definitions = database.cas_instances().unwrap();
        assert_eq!(definitions.len(), 2);
        assert_eq!(definitions[0].table_name, "objects_blake3");
        assert_eq!(definitions[0].algorithm, HashAlgorithm::Blake3);
        assert_eq!(definitions[1].table_name, "objects_sha256");
        assert_eq!(definitions[1].algorithm, HashAlgorithm::Sha256);
    }

    #[test]
    fn owned_instances_apply_one_algorithm_per_physical_table() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_hash_cas_relations().unwrap();
        database.install_cas_instance_registry().unwrap();
        database
            .create_cas_instance("objects_blake3", HashAlgorithm::Blake3)
            .unwrap();
        database
            .create_cas_instance("objects_sha256", HashAlgorithm::Sha256)
            .unwrap();
        let data = b"same bytes";

        let (blake3_id, blake3_address) = database
            .cas_instance("objects_blake3")
            .unwrap()
            .put(data)
            .unwrap();
        let (sha256_id, sha256_address) = database
            .cas_instance("objects_sha256")
            .unwrap()
            .put(data)
            .unwrap();
        assert_eq!(blake3_id.get(), 1);
        assert_eq!(sha256_id.get(), 1);
        assert_ne!(blake3_address, sha256_address);
        assert!(matches!(
            database
                .cas_instance("objects_blake3")
                .unwrap()
                .entry(sha256_address),
            Err(TrustedDbError::CasInstanceAddressAlgorithm { .. })
        ));
    }

    #[test]
    fn unique_owner_rejects_conflicts_and_unowned_tables() {
        let mut database = TrustedDb::create_in_memory().unwrap();
        database.install_hash_cas_relations().unwrap();
        database.install_cas_instance_registry().unwrap();
        database
            .create_cas_instance("owned", HashAlgorithm::Blake3)
            .unwrap();
        assert!(matches!(
            database.create_cas_instance("owned", HashAlgorithm::Sha256),
            Err(TrustedDbError::CasInstanceAlgorithmConflict { .. })
        ));
        assert!(matches!(
            database.create_cas_instance("covalence_meta_forbidden", HashAlgorithm::Blake3),
            Err(TrustedDbError::InvalidCasInstanceName { .. })
        ));

        database
            .connection
            .execute_batch("CREATE TABLE unowned (x INTEGER) STRICT;")
            .unwrap();
        assert!(matches!(
            database.create_cas_instance("unowned", HashAlgorithm::Blake3),
            Err(TrustedDbError::UnownedTableExists { .. })
        ));
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
