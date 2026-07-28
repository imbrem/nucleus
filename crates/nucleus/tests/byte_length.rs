use covalence_neutron::{Bytes, Connection as RawConnection};
use covalence_nucleus::{
    ByteLengthError, ByteLengthFact, ByteLengths, Connection, DatabaseError, ValidationError,
};

const CATALOG_SQL: &str = "
    CREATE TABLE cov_catalog (
        table_name TEXT PRIMARY KEY,
        interpretation TEXT NOT NULL
    ) STRICT, WITHOUT ROWID;";

#[test]
fn facts_check_and_measure_byte_lengths() {
    assert!(matches!(
        ByteLengthFact::new(b"three".to_vec(), 3),
        Err(ByteLengthError::False {
            claimed: 3,
            actual: 5
        })
    ));
    let fact = ByteLengthFact::measure(b"three".to_vec()).expect("measure");
    assert_eq!(fact.bytes(), b"three");
    assert_eq!(fact.length(), 5);
}

#[test]
fn wrappers_discover_multiple_direct_relations() {
    let connection = Connection::create_in_memory().expect("create database");
    let words = connection
        .create_byte_lengths("words")
        .expect("create words");
    let binary = connection
        .create_byte_lengths("binary")
        .expect("create binary");
    words
        .insert(ByteLengthFact::measure(b"hello".to_vec()).expect("measure word"))
        .expect("insert word");
    binary
        .insert(ByteLengthFact::measure(vec![0, 1, 2]).expect("measure bytes"))
        .expect("insert bytes");

    let image = connection.serialize().expect("serialize");
    let restored = Connection::from_image(&image).expect("restore");
    let relations = restored
        .byte_length_tables()
        .expect("discover byte-length tables");
    assert_eq!(
        relations.iter().map(ByteLengths::name).collect::<Vec<_>>(),
        ["binary", "words"]
    );
    assert_eq!(relations[0].facts().expect("binary facts")[0].length(), 3);
    assert_eq!(relations[1].facts().expect("word facts")[0].length(), 5);
}

#[test]
fn canonical_schema_rejects_false_rows_locally() {
    let raw = raw_database(
        "CREATE TABLE lengths (
            bytes BLOB NOT NULL PRIMARY KEY,
            byte_length INTEGER NOT NULL
                CHECK (byte_length >= 0 AND byte_length = length(bytes))
        ) STRICT, WITHOUT ROWID;
        INSERT INTO cov_catalog VALUES ('lengths', 'cov.bytes.length/v0');",
    );
    assert!(
        raw.sqlite()
            .execute("INSERT INTO lengths VALUES (X'0102', 1)", ())
            .is_err()
    );
    assert!(
        raw.sqlite()
            .execute("INSERT INTO lengths VALUES (X'0102', -1)", ())
            .is_err()
    );
}

#[test]
fn import_rechecks_rows_instead_of_trusting_constraints() {
    let false_length = image_with_schema(
        "CREATE TABLE lengths (
            bytes BLOB NOT NULL PRIMARY KEY,
            byte_length INTEGER NOT NULL
        ) STRICT, WITHOUT ROWID;
        INSERT INTO lengths VALUES (X'0102', 1);
        INSERT INTO cov_catalog VALUES ('lengths', 'cov.bytes.length/v0');",
    );
    assert_byte_length_error(&false_length, |error| {
        matches!(
            error,
            ByteLengthError::False {
                claimed: 1,
                actual: 2
            }
        )
    });

    let negative = image_with_schema(
        "CREATE TABLE lengths (
            bytes BLOB NOT NULL PRIMARY KEY,
            byte_length INTEGER NOT NULL
        ) STRICT, WITHOUT ROWID;
        INSERT INTO lengths VALUES (X'01', -1);
        INSERT INTO cov_catalog VALUES ('lengths', 'cov.bytes.length/v0');",
    );
    assert_byte_length_error(&negative, |error| {
        matches!(error, ByteLengthError::NegativeLength { .. })
    });
}

#[test]
fn import_rejects_noncanonical_layouts() {
    let rowid = image_with_schema(
        "CREATE TABLE lengths (
            bytes BLOB NOT NULL UNIQUE,
            byte_length INTEGER NOT NULL
        ) STRICT;
        INSERT INTO cov_catalog VALUES ('lengths', 'cov.bytes.length/v0');",
    );
    assert_byte_length_error(&rowid, |error| {
        matches!(error, ByteLengthError::MalformedTable { .. })
    });
}

fn assert_byte_length_error(image: &Bytes, predicate: impl FnOnce(&ByteLengthError) -> bool) {
    let Err(DatabaseError::Validate {
        source: ValidationError::ByteLength { source },
    }) = Connection::from_image(image)
    else {
        panic!("expected byte-length validation failure");
    };
    assert!(predicate(&source), "unexpected error: {source}");
}

fn image_with_schema(schema: &str) -> Bytes {
    raw_database(schema)
        .serialize()
        .expect("serialize database")
}

fn raw_database(schema: &str) -> RawConnection {
    let connection = RawConnection::open_in_memory().expect("open raw database");
    connection
        .sqlite()
        .execute_batch(CATALOG_SQL)
        .expect("create catalog");
    connection
        .sqlite()
        .execute_batch(schema)
        .expect("create schema");
    connection
}
