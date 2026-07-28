use covalence_lib_hash::O256;
use covalence_neutron::{Bytes, Connection as RawConnection};
use covalence_nucleus::{CasTable, CasTableError, Connection, DatabaseError, ValidationError};

const CATALOG_SQL: &str = "
    CREATE TABLE cov_catalog (
        table_name TEXT PRIMARY KEY,
        interpretation TEXT NOT NULL
    ) STRICT, WITHOUT ROWID;";

const MEANINGS_SQL: &str = "
    CREATE TABLE meanings (
        table_name TEXT NOT NULL PRIMARY KEY,
        interpretation TEXT NOT NULL
    ) STRICT, WITHOUT ROWID;
    INSERT INTO cov_catalog VALUES ('meanings', 'cov.table-meanings/v0');";

#[test]
fn indexed_cas_supports_resident_and_declared_objects() {
    let connection = Connection::create_in_memory().expect("create database");
    let meanings = connection
        .create_table_meanings("meanings")
        .expect("create meanings");
    let objects = meanings.create_cas("objects").expect("create CAS");

    let resident_id = objects.intern(b"resident").expect("intern");
    assert_eq!(
        objects.intern(b"resident").expect("intern again"),
        resident_id
    );
    let resident_hash = objects.address(resident_id).expect("address").expect("row");
    assert_eq!(
        objects.resolve(resident_hash).expect("resolve"),
        Some(resident_id)
    );
    assert_eq!(
        objects.fetch_id(resident_id).expect("fetch"),
        Some(Vec::from(b"resident"))
    );

    let pending_hash = O256::from_bytes(b"pending");
    let pending_id = objects.declare(pending_hash).expect("declare");
    assert_eq!(objects.fetch_id(pending_id).expect("fetch pending"), None);
    assert!(matches!(
        objects.fill(pending_id, b"wrong"),
        Err(CasTableError::AddressMismatch { .. })
    ));
    assert!(!objects.fill(pending_id, b"pending").expect("fill"));
    assert!(objects.fill(pending_id, b"pending").expect("refill"));
    assert!(objects.evict(pending_id).expect("evict"));
    assert_eq!(
        objects.address(pending_id).expect("address"),
        Some(pending_hash)
    );
    assert_eq!(objects.fetch(pending_hash).expect("fetch evicted"), None);
}

#[test]
fn multiple_owned_cas_tables_round_trip_with_local_ids() {
    let connection = Connection::create_in_memory().expect("create database");
    let meanings = connection
        .create_table_meanings("meanings")
        .expect("create meanings");
    let alpha = meanings.create_cas("alpha").expect("create alpha");
    let beta = meanings.create_cas("beta").expect("create beta");
    let alpha_id = alpha.intern(b"same").expect("intern alpha");
    let beta_id = beta.intern(b"same").expect("intern beta");
    assert_eq!(alpha_id.get(), beta_id.get());
    assert_eq!(
        alpha.address(alpha_id).expect("alpha address"),
        beta.address(beta_id).expect("beta address")
    );

    let image = connection.serialize().expect("serialize");
    let restored = Connection::from_image(&image).expect("restore");
    let tables = restored.cas_tables().expect("discover CAS tables");
    assert_eq!(
        tables.iter().map(CasTable::name).collect::<Vec<_>>(),
        ["alpha", "beta"]
    );
}

#[test]
fn import_rehashes_resident_content_but_accepts_placeholders() {
    let expected = O256::from_bytes(b"expected");
    let corrupt = image_with_schema(&format!(
        "{MEANINGS_SQL}
         CREATE TABLE objects (
            object_id INTEGER PRIMARY KEY,
            hash BLOB NOT NULL UNIQUE,
            data BLOB
         ) STRICT;
         INSERT INTO objects VALUES (1, X'{expected}', X'00');
         INSERT INTO meanings VALUES ('objects', 'cov.cas.indexed/v0');"
    ));
    assert_cas_error(&corrupt, |error| {
        matches!(error, CasTableError::AddressMismatch { .. })
    });

    let placeholder = image_with_schema(&format!(
        "{MEANINGS_SQL}
         CREATE TABLE objects (
            object_id INTEGER PRIMARY KEY,
            hash BLOB NOT NULL UNIQUE,
            data BLOB
         ) STRICT;
         INSERT INTO objects VALUES (1, X'{expected}', NULL);
         INSERT INTO meanings VALUES ('objects', 'cov.cas.indexed/v0');"
    ));
    let restored = Connection::from_image(&placeholder).expect("accept placeholder");
    assert_eq!(
        restored.cas_tables().expect("discover")[0]
            .fetch(expected)
            .expect("fetch"),
        None
    );
}

#[test]
fn import_rejects_malformed_addresses_and_geometry() {
    let malformed_hash = image_with_schema(&format!(
        "{MEANINGS_SQL}
             CREATE TABLE objects (
                object_id INTEGER PRIMARY KEY,
                hash BLOB NOT NULL UNIQUE,
                data BLOB
             ) STRICT;
             INSERT INTO objects VALUES (1, zeroblob(31), NULL);
             INSERT INTO meanings VALUES ('objects', 'cov.cas.indexed/v0');"
    ));
    assert_cas_error(&malformed_hash, |error| {
        matches!(error, CasTableError::MalformedHash { .. })
    });

    let missing_unique = image_with_schema(&format!(
        "{MEANINGS_SQL}
             CREATE TABLE objects (
                object_id INTEGER PRIMARY KEY,
                hash BLOB NOT NULL,
                data BLOB
             ) STRICT;
             INSERT INTO meanings VALUES ('objects', 'cov.cas.indexed/v0');"
    ));
    assert_cas_error(&missing_unique, |error| {
        matches!(error, CasTableError::MalformedTable { .. })
    });
}

fn assert_cas_error(image: &Bytes, predicate: impl FnOnce(&CasTableError) -> bool) {
    let Err(DatabaseError::Validate {
        source: ValidationError::CasTable { source },
    }) = Connection::from_image(image)
    else {
        panic!("expected CAS validation failure");
    };
    assert!(predicate(&source), "unexpected error: {source}");
}

fn image_with_schema(schema: &str) -> Bytes {
    let connection = RawConnection::open_in_memory().expect("open raw database");
    connection
        .sqlite()
        .execute_batch(CATALOG_SQL)
        .expect("create catalog");
    connection
        .sqlite()
        .execute_batch(schema)
        .expect("create schema");
    connection.serialize().expect("serialize database")
}
