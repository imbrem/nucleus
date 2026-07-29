use std::borrow::Cow;

use bytes::Bytes;
use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension;

use crate::catalog::quote_identifier;
use crate::{
    Connection, Database, Exclusive, HandleError, RegistryInvariant, RegistrySession, Standard,
    Table,
};

const STORE_SQL: &str = include_str!("../sql/cas/store.sql");
const HASH_SQL: &str = include_str!("../sql/cas/address.sql");
const RESOLVE_SQL: &str = include_str!("../sql/cas/resolve.sql");
const RESERVE_SQL: &str = include_str!("../sql/cas/reserve.sql");
const GET_SQL: &str = include_str!("../sql/cas/fetch_id.sql");
const GET_BY_HASH_SQL: &str = include_str!("../sql/cas/fetch.sql");
const EVICT_SQL: &str = include_str!("../sql/cas/evict.sql");
const REMOVE_SQL: &str = include_str!("../sql/cas/remove.sql");
const FILL_SQL: &str = include_str!("../sql/cas/fill.sql");
const FILL_STATE_SQL: &str = include_str!("../sql/cas/fill_state.sql");
const CREATE_SQL: &str = include_str!("../sql/cas/create.sql");
const REGISTER_SQL: &str = include_str!("../sql/cas/register.sql");

/// Connection-local integer identity for an entry in a CAS.
///
/// This identity is meaningful only within the Neutron connection that
/// returned it. The content hash is the stable identity across connections.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CasId(i64);

impl CasId {
    /// Returns the underlying connection-local integer.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// A capability for one content-addressed store.
///
/// A user-defined CAS owns an exclusive table capability. The standard
/// connection CAS is owned directly by [`Standard`].
#[derive(Debug)]
pub struct Cas<'conn> {
    connection: &'conn sqlite::Connection,
    qualified_table: Option<String>,
    _table: Option<Table<'conn, Standard, Exclusive>>,
}

impl Connection<Standard> {
    /// Returns this connection's default content-addressed store.
    #[must_use]
    pub const fn cas(&self) -> Cas<'_> {
        Cas {
            connection: self.sqlite(),
            qualified_table: None,
            _table: None,
        }
    }
}

impl<I: RegistryInvariant> RegistrySession<'_, I> {
    /// Returns the connection's standard content-addressed store.
    #[must_use]
    pub const fn cas(&self) -> Cas<'_> {
        Cas {
            connection: self.connection.sqlite(),
            qualified_table: None,
            _table: None,
        }
    }
}

impl Database<'_, Standard, Exclusive> {
    /// Creates a catalogued CAS table and returns a capability which owns it.
    ///
    /// # Errors
    ///
    /// Returns an error if the name is reserved, storage creation fails, or
    /// the new table capability cannot be acquired.
    pub fn create_cas(&self, name: impl Into<String>) -> Result<Cas<'_>, CasError> {
        let name = name.into();
        if name.starts_with("cov_conn_") || name.starts_with("cov_db_") {
            return Err(CasError::ReservedName { name });
        }

        let database = quote_identifier(self.name());
        let table = quote_identifier(&name);
        let qualified_table = format!("{database}.{table}");
        let catalog_name = if self.name() == "temp" {
            "cov_conn_catalog"
        } else {
            "cov_db_catalog"
        };
        let qualified_catalog = format!("{database}.{}", quote_identifier(catalog_name));
        let create = CREATE_SQL.replace("{table}", &qualified_table);
        let register = REGISTER_SQL.replace("{catalog}", &qualified_catalog);

        let transaction = self.sqlite().unchecked_transaction().context(CreateSnafu)?;
        transaction.execute_batch(&create).context(CreateSnafu)?;
        transaction
            .execute(&register, [&name])
            .context(CreateSnafu)?;
        transaction.commit().context(CreateSnafu)?;

        let table = self.exclusive_table(name).context(HandleSnafu)?;
        Ok(Cas {
            connection: table.sqlite(),
            qualified_table: Some(qualified_table),
            _table: Some(table),
        })
    }
}

impl Cas<'_> {
    fn sql<'sql>(&self, standard: &'sql str) -> Cow<'sql, str> {
        self.qualified_table.as_ref().map_or_else(
            || Cow::Borrowed(standard),
            |table| Cow::Owned(standard.replace("temp.cov_conn_cas", table)),
        )
    }

    /// Computes the stable content address of `data`.
    #[must_use]
    pub fn hash(&self, data: &[u8]) -> O256 {
        O256::from_bytes(data)
    }

    /// Stores `data` in this CAS and returns its stable content address.
    ///
    /// Nucleus computes the stable [`O256`] content address. An existing address
    /// with different resident bytes indicates corruption or a hash collision
    /// and is rejected.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be written or its existing
    /// state conflicts with the computed content address.
    pub fn store(&self, data: &[u8]) -> Result<O256, CasError> {
        let hash = self.hash(data);
        self.store_with_hash(hash, data)?;
        Ok(hash)
    }

    /// Fetches resident bytes by stable content address.
    ///
    /// Missing and unresolved addresses return `None`.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be queried.
    pub fn fetch(&self, hash: O256) -> Result<Option<Bytes>, CasError> {
        self.connection
            .query_row(
                self.sql(GET_BY_HASH_SQL).as_ref(),
                [hash.as_bytes().as_slice()],
                |row| row.get::<_, Option<Vec<u8>>>(0),
            )
            .optional()
            .context(FetchSnafu)
            .map(Option::flatten)
            .map(|data| data.map(Bytes::from))
    }

    /// Interns `data` and returns its canonical connection-local ID.
    ///
    /// This is the indexed extension of [`store`](Self::store). Repeatedly
    /// storing the same bytes returns the same ID.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be written or its existing
    /// state conflicts with the computed content address.
    pub fn intern(&self, data: &[u8]) -> Result<CasId, CasError> {
        let hash = self.hash(data);
        self.store_with_hash(hash, data)
    }

    fn store_with_hash(&self, hash: O256, data: &[u8]) -> Result<CasId, CasError> {
        self.connection
            .query_row(
                self.sql(STORE_SQL).as_ref(),
                (hash.as_bytes().as_slice(), data),
                |row| row.get::<_, i64>(0).map(CasId),
            )
            .optional()
            .context(StoreSnafu)?
            .ok_or(CasError::HashCollision { hash })
    }

    /// Returns the stable content address for a connection-local CAS ID.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be queried or contains a
    /// malformed address.
    pub fn address(&self, id: CasId) -> Result<Option<O256>, CasError> {
        let bytes = self
            .connection
            .query_row(self.sql(HASH_SQL).as_ref(), [id.0], |row| {
                row.get::<_, Vec<u8>>(0)
            })
            .optional()
            .context(AddressSnafu)?;
        bytes.map(|bytes| decode_address(id, bytes)).transpose()
    }

    /// Resolves a stable content address to its connection-local CAS ID.
    ///
    /// Both resident and unresolved entries have local IDs. A missing address
    /// returns `None` without changing the CAS.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be queried.
    pub fn resolve(&self, hash: O256) -> Result<Option<CasId>, CasError> {
        self.connection
            .query_row(
                self.sql(RESOLVE_SQL).as_ref(),
                [hash.as_bytes().as_slice()],
                |row| row.get::<_, i64>(0).map(CasId),
            )
            .optional()
            .context(ResolveSnafu)
    }

    /// Returns the existing local ID for `hash`, or reserves an unresolved one.
    ///
    /// This operation changes only connection-local index state. It does not
    /// claim that bytes for `hash` are resident.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be updated or queried.
    pub fn reserve(&self, hash: O256) -> Result<CasId, CasError> {
        self.connection
            .execute(self.sql(RESERVE_SQL).as_ref(), [hash.as_bytes().as_slice()])
            .context(ReserveSnafu)?;
        self.connection
            .query_row(
                self.sql(RESOLVE_SQL).as_ref(),
                [hash.as_bytes().as_slice()],
                |row| row.get::<_, i64>(0).map(CasId),
            )
            .context(ReserveSnafu)
    }

    /// Fetches resident bytes by connection-local CAS ID.
    ///
    /// Missing IDs and unresolved entries both return `None`.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be queried.
    pub fn fetch_id(&self, id: CasId) -> Result<Option<Bytes>, CasError> {
        self.connection
            .query_row(self.sql(GET_SQL).as_ref(), [id.0], |row| {
                row.get::<_, Option<Vec<u8>>>(0)
            })
            .optional()
            .context(FetchSnafu)
            .map(Option::flatten)
            .map(|data| data.map(Bytes::from))
    }

    /// Fills an existing local ID with its matching resident bytes.
    ///
    /// The ID must already exist, and the content address computed from `data`
    /// must match the address recorded for it. Returns `true` when the entry
    /// already contained resident data, which is replaced.
    ///
    /// # Errors
    ///
    /// Returns an error when the ID is missing, the content address does not
    /// match, or the CAS cannot be accessed.
    pub fn fill(&self, id: CasId, data: &[u8]) -> Result<bool, CasError> {
        let state = self
            .connection
            .query_row(self.sql(FILL_STATE_SQL).as_ref(), [id.0], |row| {
                Ok((row.get::<_, Vec<u8>>(0)?, row.get::<_, bool>(1)?))
            })
            .optional()
            .context(FillSnafu)?
            .ok_or(CasError::MissingId { id })?;
        let expected = decode_address(id, state.0)?;
        let actual = self.hash(data);
        if actual != expected {
            return Err(CasError::AddressMismatch {
                id,
                expected,
                actual,
            });
        }

        self.connection
            .execute(self.sql(FILL_SQL).as_ref(), (id.0, data))
            .context(FillSnafu)?;
        Ok(state.1)
    }

    /// Evicts resident bytes while preserving the local ID and address.
    ///
    /// Returns `true` when resident bytes were removed. Missing IDs and
    /// already-unresolved entries return `false`.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be updated.
    pub fn evict(&self, id: CasId) -> Result<bool, CasError> {
        self.connection
            .execute(self.sql(EVICT_SQL).as_ref(), [id.0])
            .context(EvictSnafu)
            .map(|changed| changed != 0)
    }

    /// Removes a complete entry from the connection-local CAS index.
    ///
    /// Returns `true` when the ID existed. After removal, both its local
    /// identity and any resident bytes are forgotten.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be updated.
    pub fn remove(&self, id: CasId) -> Result<bool, CasError> {
        self.connection
            .execute(self.sql(REMOVE_SQL).as_ref(), [id.0])
            .context(RemoveSnafu)
            .map(|changed| changed != 0)
    }
}

fn decode_address(id: CasId, bytes: Vec<u8>) -> Result<O256, CasError> {
    <[u8; 32]>::try_from(bytes)
        .map(O256::from_array)
        .map_err(|_| CasError::MalformedHash { id })
}

/// Failure to create or access a Nucleus CAS.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CasError {
    /// User-defined storage cannot use a Nucleus-reserved table name.
    #[snafu(display("CAS table name {name:?} is reserved by Nucleus"))]
    ReservedName { name: String },

    /// A CAS table could not be created and catalogued.
    #[snafu(display("could not create CAS storage: {source}"))]
    Create { source: sqlite::Error },

    /// The CAS table capability could not be acquired.
    #[snafu(display("could not acquire the CAS table: {source}"))]
    Handle { source: HandleError },

    /// Bytes could not be stored.
    #[snafu(display("could not store bytes in the CAS: {source}"))]
    Store {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// Different resident bytes have the same content address.
    #[snafu(display("hash collision at content address {hash}"))]
    HashCollision {
        /// Conflicting stable content address.
        hash: O256,
    },

    /// An entry contains a malformed stable address.
    #[snafu(display("CAS entry {id:?} contains a malformed content address"))]
    MalformedHash {
        /// Connection-local identity of the malformed entry.
        id: CasId,
    },

    /// A content address could not be loaded for a local ID.
    #[snafu(display("could not load a content address from the CAS: {source}"))]
    Address {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// A content address could not be resolved to a local ID.
    #[snafu(display("could not resolve an address in the CAS: {source}"))]
    Resolve {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// An unresolved address could not be reserved.
    #[snafu(display("could not reserve an address in the CAS: {source}"))]
    Reserve {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// Resident bytes could not be loaded.
    #[snafu(display("could not load bytes from the CAS: {source}"))]
    Fetch {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// Resident bytes could not be evicted.
    #[snafu(display("could not evict bytes from the CAS: {source}"))]
    Evict {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// A connection-local CAS entry could not be removed.
    #[snafu(display("could not remove an entry from the CAS: {source}"))]
    Remove {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// A connection-local ID does not exist.
    #[snafu(display("CAS entry {id:?} does not exist"))]
    MissingId {
        /// Missing connection-local identity.
        id: CasId,
    },

    /// Bytes do not have the address recorded for an entry.
    #[snafu(display("bytes for CAS entry {id:?} have address {actual}, expected {expected}"))]
    AddressMismatch {
        /// Connection-local identity being filled.
        id: CasId,
        /// Address recorded for the identity.
        expected: O256,
        /// Address computed from the supplied bytes.
        actual: O256,
    },

    /// An existing CAS entry could not be filled.
    #[snafu(display("could not fill an entry in the CAS: {source}"))]
    Fill {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CONNECTION_CAS, CONNECTION_CAS_INTERPRETATION};

    #[test]
    fn stores_hashes_and_resolves_bytes() {
        let connection = Connection::open_in_memory().expect("open connection");

        let cas = connection.cas();
        let hash = cas.store(b"hello").expect("store");
        let id = cas.resolve(hash).expect("resolve hit").expect("known hash");
        assert_eq!(cas.address(id).expect("load hash"), Some(hash));
        assert_eq!(hash, cas.hash(b"hello"));
        assert_eq!(
            cas.fetch_id(id).expect("fetch by ID"),
            Some(Bytes::from_static(b"hello"))
        );
        assert_eq!(
            cas.fetch(hash).expect("fetch by hash"),
            Some(Bytes::from_static(b"hello"))
        );
    }

    #[test]
    fn repeated_identical_store_returns_same_id() {
        let connection = Connection::open_in_memory().expect("open connection");

        let first = connection.cas().intern(b"same").expect("first intern");
        let second = connection.cas().intern(b"same").expect("second intern");

        assert_eq!(first, second);
        let rows = connection
            .neutron
            .sqlite()
            .query_row("SELECT count(*) FROM temp.cov_conn_cas", (), |row| {
                row.get::<_, i64>(0)
            })
            .expect("count rows");
        assert_eq!(rows, 1);
    }

    #[test]
    fn conflicting_store_is_rejected() {
        let connection = Connection::open_in_memory().expect("open connection");
        let hash = O256::from_bytes(b"correct");
        connection
            .neutron
            .sqlite()
            .execute(
                "INSERT INTO temp.cov_conn_cas (hash, data) VALUES (?1, ?2)",
                (hash.as_bytes().as_slice(), b"corrupt".as_slice()),
            )
            .expect("inject conflicting row");

        assert!(matches!(
            connection.cas().store(b"correct"),
            Err(CasError::HashCollision { hash: collision }) if collision == hash
        ));
        assert_eq!(
            connection
                .cas()
                .fetch(hash)
                .expect("fetch stored assertion"),
            Some(Bytes::from_static(b"corrupt"))
        );
    }

    #[test]
    fn different_values_have_independent_ids_and_hashes() {
        let connection = Connection::open_in_memory().expect("open connection");

        let cas = connection.cas();
        let first = cas.intern(b"first").expect("intern first");
        let second = cas.intern(b"second").expect("intern second");

        assert_ne!(first, second);
        assert_ne!(
            cas.address(first).expect("hash first"),
            cas.address(second).expect("hash second")
        );
    }

    #[test]
    fn unknown_ids_and_hashes_are_absent() {
        let connection = Connection::open_in_memory().expect("open connection");

        let cas = connection.cas();
        assert_eq!(cas.address(CasId(i64::MAX)).expect("hash miss"), None);
        assert_eq!(cas.fetch_id(CasId(i64::MAX)).expect("fetch miss"), None);
        assert_eq!(
            cas.resolve(O256::from_bytes(b"missing"))
                .expect("resolve miss"),
            None
        );
    }

    #[test]
    fn default_cas_is_connection_local() {
        let first = Connection::open_in_memory().expect("open first connection");
        let second = Connection::open_in_memory().expect("open second connection");

        let id = first.cas().intern(b"private").expect("intern");
        let hash = first
            .cas()
            .address(id)
            .expect("load hash")
            .expect("known ID");
        assert_eq!(second.cas().resolve(hash).expect("resolve"), None);
    }

    #[test]
    fn default_cas_is_not_part_of_database_images() {
        let connection = Connection::open_in_memory().expect("open connection");
        let id = connection.cas().intern(b"ephemeral").expect("intern");
        let hash = connection
            .cas()
            .address(id)
            .expect("load hash")
            .expect("known ID");

        let image = connection.serialize().expect("serialize main");
        let restored = Connection::deserialize(&image).expect("deserialize main");

        let temp_tables = restored
            .neutron
            .sqlite()
            .query_row(
                "SELECT count(*) FROM temp.sqlite_schema WHERE type = 'table'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("inspect unchecked connection");
        assert_eq!(temp_tables, 0);
        let _ = hash;
    }

    #[test]
    fn store_fills_a_matching_unresolved_row() {
        let connection = Connection::open_in_memory().expect("open connection");
        let hash = O256::from_bytes(b"now resident");
        let cas = connection.cas();
        let declared_id = cas.reserve(hash).expect("reserve address");

        assert_eq!(cas.resolve(hash).expect("resolve"), Some(declared_id));
        assert_eq!(cas.fetch_id(declared_id).expect("fetch unresolved"), None);
        assert_eq!(cas.fetch(hash).expect("fetch unresolved by hash"), None);
        let stored_id = cas.intern(b"now resident").expect("intern");
        assert_eq!(stored_id, declared_id);
        assert_eq!(
            cas.fetch_id(stored_id).expect("fetch resident"),
            Some(Bytes::from_static(b"now resident"))
        );
    }

    #[test]
    fn resolve_does_not_intern_a_missing_hash() {
        let connection = Connection::open_in_memory().expect("open connection");
        let hash = O256::from_bytes(b"missing");

        assert_eq!(
            connection.cas().resolve(hash).expect("resolve missing"),
            None
        );
        let rows = connection
            .neutron
            .sqlite()
            .query_row("SELECT count(*) FROM temp.cov_conn_cas", (), |row| {
                row.get::<_, i64>(0)
            })
            .expect("count rows");
        assert_eq!(rows, 0);
    }

    #[test]
    fn reserve_is_idempotent() {
        let connection = Connection::open_in_memory().expect("open connection");
        let hash = O256::from_bytes(b"eventually available");

        let cas = connection.cas();
        let first = cas.reserve(hash).expect("first reserve");
        let second = cas.reserve(hash).expect("second reserve");

        assert_eq!(first, second);
        assert_eq!(cas.address(first).expect("hash"), Some(hash));
    }

    #[test]
    fn evicts_data_and_removes_entries() {
        let connection = Connection::open_in_memory().expect("open connection");
        let cas = connection.cas();
        let id = cas.intern(b"temporary").expect("intern");
        let hash = cas.address(id).expect("address").expect("known ID");

        assert!(cas.evict(id).expect("evict resident data"));
        assert!(!cas.evict(id).expect("evict unresolved entry"));
        assert_eq!(cas.address(id).expect("preserved address"), Some(hash));
        assert_eq!(cas.resolve(hash).expect("preserved ID"), Some(id));
        assert_eq!(cas.fetch_id(id).expect("fetch unresolved"), None);

        assert!(cas.remove(id).expect("remove entry"));
        assert!(!cas.remove(id).expect("remove missing entry"));
        assert_eq!(cas.address(id).expect("removed address"), None);
        assert_eq!(cas.resolve(hash).expect("removed ID"), None);
    }

    #[test]
    fn fills_only_existing_ids_with_matching_data() {
        let connection = Connection::open_in_memory().expect("open connection");
        let cas = connection.cas();
        let expected = cas.hash(b"expected");
        let id = cas.reserve(expected).expect("reserve");

        assert!(matches!(
            cas.fill(id, b"different"),
            Err(CasError::AddressMismatch {
                id: mismatch_id,
                expected: mismatch_expected,
                actual,
            }) if mismatch_id == id
                && mismatch_expected == expected
                && actual == cas.hash(b"different")
        ));
        assert_eq!(cas.fetch_id(id).expect("still unresolved"), None);

        assert!(!cas.fill(id, b"expected").expect("fill placeholder"));
        assert!(cas.fill(id, b"expected").expect("replace resident data"));
        assert_eq!(
            cas.fetch_id(id).expect("fetch"),
            Some(Bytes::from_static(b"expected"))
        );

        assert!(matches!(
            cas.fill(CasId(i64::MAX), b"expected"),
            Err(CasError::MissingId { id: missing }) if missing == CasId(i64::MAX)
        ));
    }

    #[test]
    fn fill_replaces_existing_data_after_validating_the_address() {
        let connection = Connection::open_in_memory().expect("open connection");
        let cas = connection.cas();
        let hash = cas.hash(b"authoritative");
        let id = cas.reserve(hash).expect("reserve");
        connection
            .neutron
            .sqlite()
            .execute(
                "UPDATE temp.cov_conn_cas SET data = ?2 WHERE object_id = ?1",
                (id.0, b"stale".as_slice()),
            )
            .expect("inject stale data");

        assert!(cas.fill(id, b"authoritative").expect("replace stale data"));
        assert_eq!(
            cas.fetch_id(id).expect("fetch"),
            Some(Bytes::from_static(b"authoritative"))
        );
    }

    #[test]
    fn default_cas_is_registered_by_role() {
        let connection = Connection::open_in_memory().expect("open connection");
        let registration = connection
            .neutron
            .sqlite()
            .query_row(
                "SELECT table_name, interpretation
                 FROM temp.cov_conn_catalog
                 WHERE table_name = ?1",
                [CONNECTION_CAS],
                |row| Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?)),
            )
            .expect("read registration");

        assert_eq!(
            registration,
            (
                String::from(CONNECTION_CAS),
                String::from(CONNECTION_CAS_INTERPRETATION)
            )
        );
    }
}
