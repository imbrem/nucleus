use covalence_lib_hash::O256;
use covalence_neutron::{Bytes, Connection as RawConnection};
use covalence_nucleus::{CasTable, CasTableError, Connection, DatabaseError, ValidationError};

const CATALOG_SQL: &str = "
    CREATE TABLE cov_catalog (
        table_name TEXT PRIMARY KEY,
        interpretation TEXT NOT NULL
    ) STRICT, WITHOUT ROWID;";

#[test]
fn multiple_persistent_cas_tables_round_trip_independently() {
    let connection = Connection::create_in_memory().expect("create database");
    let alpha = connection.create_cas_table("alpha").expect("create alpha");
    let beta = connection.create_cas_table("beta").expect("create beta");
    let shared = alpha.store(b"shared").expect("store alpha shared");
    assert_eq!(
        beta.store(b"shared").expect("store beta shared"),
        shared,
        "stable addresses do not depend on the containing table"
    );
    let private = beta.store(b"beta only").expect("store beta private");
    assert_eq!(alpha.fetch(private).expect("fetch alpha miss"), None);

    let image = connection.serialize().expect("serialize");
    let restored = Connection::from_image(&image).expect("restore");
    let tables = restored.cas_tables().expect("discover CAS tables");
    assert_eq!(
        tables.iter().map(CasTable::name).collect::<Vec<_>>(),
        ["alpha", "beta"]
    );
    assert_eq!(
        tables[0].fetch(shared).expect("fetch alpha"),
        Some(Vec::from(b"shared"))
    );
    assert_eq!(
        tables[1].fetch(private).expect("fetch beta"),
        Some(Vec::from(b"beta only"))
    );
}

#[test]
fn import_rehashes_every_resident_value() {
    let expected = O256::from_bytes(b"expected");
    let image = image_with_schema(&format!(
        "CREATE TABLE hostile (
            hash BLOB NOT NULL PRIMARY KEY,
            data BLOB NOT NULL
        ) STRICT, WITHOUT ROWID;
        INSERT INTO hostile VALUES (X'{expected}', X'00');
        INSERT INTO cov_catalog VALUES ('hostile', 'cov.cas/v0');"
    ));

    assert!(matches!(
        Connection::from_image(&image),
        Err(DatabaseError::Validate {
            source: ValidationError::CasTable {
                source: CasTableError::AddressMismatch { .. }
            }
        })
    ));
}

#[test]
fn import_rejects_malformed_hashes_and_noncanonical_layouts() {
    let malformed_hash = image_with_schema(
        "CREATE TABLE malformed (
            hash BLOB NOT NULL PRIMARY KEY,
            data BLOB NOT NULL
        ) STRICT, WITHOUT ROWID;
        INSERT INTO malformed VALUES (zeroblob(31), X'00');
        INSERT INTO cov_catalog VALUES ('malformed', 'cov.cas/v0');",
    );
    assert!(matches!(
        Connection::from_image(&malformed_hash),
        Err(DatabaseError::Validate {
            source: ValidationError::CasTable {
                source: CasTableError::MalformedHash { .. }
            }
        })
    ));

    let rowid = image_with_schema(
        "CREATE TABLE rowid_cas (
            hash BLOB NOT NULL UNIQUE,
            data BLOB NOT NULL
        ) STRICT;
        INSERT INTO cov_catalog VALUES ('rowid_cas', 'cov.cas/v0');",
    );
    assert!(matches!(
        Connection::from_image(&rowid),
        Err(DatabaseError::Validate {
            source: ValidationError::CasTable {
                source: CasTableError::MalformedTable { .. }
            }
        })
    ));
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
        .expect("create test schema");
    connection.serialize().expect("serialize database")
}
