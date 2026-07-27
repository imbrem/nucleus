use covalence_lib_hash::O256;
use covalence_neutron::{Bytes, Connection as RawConnection};
use covalence_nucleus::{
    ByteLengthError, CasTableError, Connection, DatabaseError, ValidationError,
};

const CATALOG_SQL: &str = "
    CREATE TABLE cov_catalog (
        table_name TEXT PRIMARY KEY,
        interpretation TEXT NOT NULL
    ) STRICT, WITHOUT ROWID;";

const CAS_SQL: &str = "
    CREATE TABLE objects (
        hash BLOB NOT NULL PRIMARY KEY,
        data BLOB NOT NULL
    ) STRICT, WITHOUT ROWID;
    INSERT INTO cov_catalog VALUES ('objects', 'cov.cas/v0');";

const LENGTHS_SQL: &str = "
    CREATE TABLE lengths (
        cas_table TEXT NOT NULL,
        hash BLOB NOT NULL,
        length INTEGER NOT NULL,
        PRIMARY KEY (cas_table, hash)
    ) STRICT, WITHOUT ROWID;
    INSERT INTO cov_catalog VALUES ('lengths', 'cov.bytes.length/v0');";

#[test]
fn one_relation_can_describe_objects_in_several_cas_tables() {
    let connection = Connection::create_in_memory().expect("create database");
    let alpha = connection.create_cas_table("alpha").expect("create alpha");
    let beta = connection.create_cas_table("beta").expect("create beta");
    let lengths = connection
        .create_byte_lengths("lengths")
        .expect("create lengths");

    let shared_alpha = lengths
        .record(&alpha, b"shared")
        .expect("record shared in alpha");
    let shared_beta = lengths
        .record(&beta, b"shared")
        .expect("record shared in beta");
    let private_beta = lengths
        .record(&beta, b"beta only")
        .expect("record private beta value");

    assert_eq!(shared_alpha.hash, shared_beta.hash);
    assert_ne!(shared_beta.hash, private_beta.hash);
    let shared_hash = shared_alpha.hash;
    let private_hash = private_beta.hash;

    let image = connection.serialize().expect("serialize");
    let restored = Connection::from_image(&image).expect("restore");
    let relations = restored
        .byte_length_tables()
        .expect("discover byte-length relations");
    assert_eq!(relations.len(), 1);
    assert_eq!(relations[0].name(), "lengths");
    let facts = relations[0].facts().expect("load facts");
    assert_eq!(facts.len(), 3);
    for expected in [shared_alpha, shared_beta, private_beta] {
        assert!(facts.contains(&expected));
    }

    let tables = restored.cas_tables().expect("discover CAS tables");
    assert_eq!(
        tables[0].fetch(shared_hash).expect("fetch alpha"),
        Some(Vec::from(b"shared"))
    );
    assert_eq!(
        tables[1].fetch(private_hash).expect("fetch beta"),
        Some(Vec::from(b"beta only"))
    );
}

#[test]
fn wrappers_from_different_connections_cannot_form_relationships() {
    let first = Connection::create_in_memory().expect("create first database");
    let second = Connection::create_in_memory().expect("create second database");
    let lengths = first
        .create_byte_lengths("lengths")
        .expect("create lengths");
    let objects = second.create_cas_table("objects").expect("create objects");

    assert!(matches!(
        lengths.record(&objects, b"value"),
        Err(ByteLengthError::DifferentConnection)
    ));
}

#[test]
fn import_requires_a_catalogued_resident_cas_object() {
    let hash = O256::from_bytes(b"value");

    let absent_cas = image_with_schema(&format!(
        "{LENGTHS_SQL}
         INSERT INTO lengths VALUES ('missing', X'{hash}', 5);"
    ));
    assert_byte_length_error(&absent_cas, |error| {
        matches!(error, ByteLengthError::MissingCas { .. })
    });

    let absent_object = image_with_schema(&format!(
        "{CAS_SQL}
         {LENGTHS_SQL}
         INSERT INTO lengths VALUES ('objects', X'{hash}', 5);"
    ));
    assert_byte_length_error(&absent_object, |error| {
        matches!(error, ByteLengthError::MissingObject { .. })
    });
}

#[test]
fn import_rechecks_target_content_and_claimed_length() {
    let value_hash = O256::from_bytes(b"value");
    let wrong_length = image_with_schema(&format!(
        "{CAS_SQL}
         {LENGTHS_SQL}
         INSERT INTO objects VALUES (X'{value_hash}', X'76616c7565');
         INSERT INTO lengths VALUES ('objects', X'{value_hash}', 4);"
    ));
    assert_byte_length_error(&wrong_length, |error| {
        matches!(error, ByteLengthError::WrongLength { .. })
    });

    let expected = O256::from_bytes(b"expected");
    let corrupt_cas = image_with_schema(&format!(
        "{CAS_SQL}
         {LENGTHS_SQL}
         INSERT INTO objects VALUES (X'{expected}', X'00');
         INSERT INTO lengths VALUES ('objects', X'{expected}', 1);"
    ));
    assert_byte_length_error(&corrupt_cas, |error| {
        matches!(
            error,
            ByteLengthError::Cas {
                source: CasTableError::AddressMismatch { .. }
            }
        )
    });
}

#[test]
fn import_rejects_malformed_relationship_rows_and_layouts() {
    let malformed_hash = image_with_schema(&format!(
        "{CAS_SQL}
             {LENGTHS_SQL}
             INSERT INTO lengths VALUES ('objects', zeroblob(31), 0);"
    ));
    assert_byte_length_error(&malformed_hash, |error| {
        matches!(error, ByteLengthError::MalformedHash { .. })
    });

    let negative_length = image_with_schema(&format!(
        "{CAS_SQL}
             {LENGTHS_SQL}
             INSERT INTO lengths VALUES ('objects', zeroblob(32), -1);"
    ));
    assert_byte_length_error(&negative_length, |error| {
        matches!(error, ByteLengthError::NegativeLength { .. })
    });

    let rowid = image_with_schema(
        "CREATE TABLE lengths (
            cas_table TEXT NOT NULL,
            hash BLOB NOT NULL,
            length INTEGER NOT NULL
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
