use covalence_lib_hash::O256;
use covalence_neutron::{Bytes, Connection as RawConnection};
use covalence_nucleus::{
    ByteLengthReferenceError, CasTableError, Connection, DatabaseError, ValidationError,
};

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

const CAS_SQL: &str = "
    CREATE TABLE z_objects (
        object_id INTEGER PRIMARY KEY,
        hash BLOB NOT NULL UNIQUE,
        data BLOB
    ) STRICT;
    INSERT INTO meanings VALUES ('z_objects', 'cov.cas.indexed/v0');";

const REFERENCES_SQL: &str = "
    CREATE TABLE a_lengths (
        cas_table TEXT NOT NULL,
        hash BLOB NOT NULL,
        byte_length INTEGER NOT NULL,
        PRIMARY KEY (cas_table, hash)
    ) STRICT, WITHOUT ROWID;
    INSERT INTO meanings VALUES (
        'a_lengths',
        'cov.bytes.length-reference/v0'
    );";

#[test]
fn one_relation_references_several_cas_instances_by_stable_address() {
    let connection = Connection::create_in_memory().expect("create database");
    let meanings = connection
        .create_table_meanings("meanings")
        .expect("create meanings");
    let alpha = meanings.create_cas("alpha").expect("create alpha");
    let beta = meanings.create_cas("beta").expect("create beta");
    let lengths = meanings
        .create_byte_length_references("lengths")
        .expect("create references");

    let alpha_shared = lengths
        .record(&alpha, b"shared")
        .expect("record alpha shared");
    let beta_shared = lengths
        .record(&beta, b"shared")
        .expect("record beta shared");
    let beta_private = lengths
        .record(&beta, b"beta only")
        .expect("record beta private");
    assert_eq!(alpha_shared.hash, beta_shared.hash);

    let image = connection.serialize().expect("serialize");
    let restored = Connection::from_image(&image).expect("restore");
    let relations = restored
        .byte_length_reference_tables()
        .expect("discover references");
    let facts = relations[0].facts().expect("load facts");
    assert_eq!(facts.len(), 3);
    for expected in [alpha_shared, beta_shared, beta_private] {
        assert!(facts.contains(&expected));
    }
}

#[test]
fn wrappers_from_different_connections_cannot_be_combined() {
    let first = Connection::create_in_memory().expect("create first");
    let first_meanings = first
        .create_table_meanings("meanings")
        .expect("create first meanings");
    let lengths = first_meanings
        .create_byte_length_references("lengths")
        .expect("create references");

    let second = Connection::create_in_memory().expect("create second");
    let second_meanings = second
        .create_table_meanings("meanings")
        .expect("create second meanings");
    let objects = second_meanings.create_cas("objects").expect("create CAS");

    assert!(matches!(
        lengths.record(&objects, b"value"),
        Err(ByteLengthReferenceError::DifferentConnection)
    ));
}

#[test]
fn import_requires_cas_meaning_and_resident_content() {
    let hash = O256::from_bytes(b"value");
    let wrong_meaning = image_with_schema(&format!(
        "{MEANINGS_SQL}
         CREATE TABLE z_objects (
            bytes BLOB NOT NULL PRIMARY KEY,
            byte_length INTEGER NOT NULL
         ) STRICT, WITHOUT ROWID;
         INSERT INTO meanings VALUES ('z_objects', 'cov.bytes.length/v0');
         {REFERENCES_SQL}
         INSERT INTO a_lengths VALUES ('z_objects', X'{hash}', 5);"
    ));
    assert_reference_error(&wrong_meaning, |error| {
        matches!(error, ByteLengthReferenceError::WrongTargetMeaning { .. })
    });

    let placeholder = image_with_schema(&format!(
        "{MEANINGS_SQL}
         {CAS_SQL}
         {REFERENCES_SQL}
         INSERT INTO z_objects VALUES (1, X'{hash}', NULL);
         INSERT INTO a_lengths VALUES ('z_objects', X'{hash}', 5);"
    ));
    assert_reference_error(&placeholder, |error| {
        matches!(error, ByteLengthReferenceError::MissingObject { .. })
    });
}

#[test]
fn import_rechecks_target_content_and_claimed_length() {
    let hash = O256::from_bytes(b"value");
    let wrong_length = image_with_schema(&format!(
        "{MEANINGS_SQL}
         {CAS_SQL}
         {REFERENCES_SQL}
         INSERT INTO z_objects VALUES (1, X'{hash}', X'76616c7565');
         INSERT INTO a_lengths VALUES ('z_objects', X'{hash}', 4);"
    ));
    assert_reference_error(&wrong_length, |error| {
        matches!(error, ByteLengthReferenceError::False { .. })
    });

    let expected = O256::from_bytes(b"expected");
    let corrupt_target = image_with_schema(&format!(
        "{MEANINGS_SQL}
         {CAS_SQL}
         {REFERENCES_SQL}
         INSERT INTO z_objects VALUES (1, X'{expected}', X'00');
         INSERT INTO a_lengths VALUES ('z_objects', X'{expected}', 1);"
    ));
    assert_reference_error(&corrupt_target, |error| {
        matches!(
            error,
            ByteLengthReferenceError::Cas {
                source: CasTableError::AddressMismatch { .. }
            }
        )
    });
}

#[test]
fn import_rejects_malformed_reference_rows_and_layouts() {
    let malformed_hash = image_with_schema(&format!(
        "{MEANINGS_SQL}
         {CAS_SQL}
         {REFERENCES_SQL}
         INSERT INTO a_lengths VALUES ('z_objects', zeroblob(31), 0);"
    ));
    assert_reference_error(&malformed_hash, |error| {
        matches!(error, ByteLengthReferenceError::MalformedHash { .. })
    });

    let negative = image_with_schema(&format!(
        "{MEANINGS_SQL}
         {CAS_SQL}
         {REFERENCES_SQL}
         INSERT INTO a_lengths VALUES ('z_objects', zeroblob(32), -1);"
    ));
    assert_reference_error(&negative, |error| {
        matches!(error, ByteLengthReferenceError::NegativeLength { .. })
    });

    let rowid = image_with_schema(&format!(
        "{MEANINGS_SQL}
         CREATE TABLE a_lengths (
            cas_table TEXT NOT NULL,
            hash BLOB NOT NULL,
            byte_length INTEGER NOT NULL
         ) STRICT;
         INSERT INTO meanings VALUES (
            'a_lengths',
            'cov.bytes.length-reference/v0'
         );"
    ));
    assert_reference_error(&rowid, |error| {
        matches!(error, ByteLengthReferenceError::MalformedTable { .. })
    });
}

fn assert_reference_error(
    image: &Bytes,
    predicate: impl FnOnce(&ByteLengthReferenceError) -> bool,
) {
    let Err(DatabaseError::Validate {
        source: ValidationError::ByteLengthReference { source },
    }) = Connection::from_image(image)
    else {
        panic!("expected cross-table reference validation failure");
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
