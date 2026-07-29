use covalence_lib_hash::O256;
use covalence_neutron::{Bytes, Connection as RawConnection};
use covalence_nucleus::{
    CasTableError, Connection, DatabaseError, DerivedObjectError, ValidationError,
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
    CREATE TABLE objects (
        object_id INTEGER PRIMARY KEY,
        hash BLOB NOT NULL UNIQUE,
        data BLOB
    ) STRICT;
    INSERT INTO meanings VALUES ('objects', 'cov.cas.indexed/v0');";

const KEYED_SQL: &str = "
    CREATE TABLE keyed (
        object_id INTEGER PRIMARY KEY REFERENCES objects (object_id),
        key BLOB NOT NULL,
        bytes BLOB NOT NULL
    ) STRICT;
    INSERT INTO meanings VALUES ('keyed', 'cov.cas.blake3-keyed/v0');";

const CONTEXT_SQL: &str = "
    CREATE TABLE contextual (
        object_id INTEGER PRIMARY KEY REFERENCES objects (object_id),
        context TEXT NOT NULL,
        bytes BLOB NOT NULL
    ) STRICT;
    INSERT INTO meanings VALUES ('contextual', 'cov.cas.blake3-context/v0');";

#[test]
fn keyed_and_context_preimages_represent_unresolved_cas_objects() {
    let connection = Connection::create_in_memory().expect("create database");
    let meanings = connection
        .create_table_meanings("meanings")
        .expect("create meanings");
    let objects = meanings.create_cas("objects").expect("create CAS");
    let keyed = meanings
        .create_keyed_objects("keyed", &objects)
        .expect("create keyed objects");
    let contextual = meanings
        .create_context_objects("contextual", &objects)
        .expect("create context objects");

    let key = O256::from_bytes(b"key");
    let keyed_id = keyed.insert(&objects, key, b"value").expect("insert keyed");
    let context_id = contextual
        .insert(&objects, "nucleus test context", b"value")
        .expect("insert context");
    assert_eq!(
        objects.address(keyed_id).expect("keyed address"),
        Some(O256::with_key(&key, b"value"))
    );
    assert_eq!(
        objects.address(context_id).expect("context address"),
        Some(O256::with_key("nucleus test context", b"value"))
    );
    assert_eq!(objects.fetch_id(keyed_id).expect("keyed data"), None);
    assert_eq!(objects.fetch_id(context_id).expect("context data"), None);

    let image = connection.serialize().expect("serialize");
    let restored = Connection::from_image(&image).expect("restore");
    let keyed_tables = restored.keyed_object_tables().expect("discover keyed");
    assert_eq!(keyed_tables[0].name(), "keyed");
    assert_eq!(keyed_tables[0].cas_table(), "objects");
    assert_eq!(keyed_tables[0].objects().expect("read keyed")[0].key, key);
    let context_tables = restored.context_object_tables().expect("discover contexts");
    assert_eq!(context_tables[0].name(), "contextual");
    assert_eq!(context_tables[0].cas_table(), "objects");
    assert_eq!(
        context_tables[0].objects().expect("read contexts")[0].context,
        "nucleus test context"
    );
}

#[test]
fn typed_creation_and_insertion_enforce_connection_and_target() {
    let first = Connection::create_in_memory().expect("create first");
    let first_meanings = first
        .create_table_meanings("meanings")
        .expect("create first meanings");
    let first_cas = first_meanings
        .create_cas("objects")
        .expect("create first CAS");
    let other_cas = first_meanings
        .create_cas("other")
        .expect("create other CAS");
    let keyed = first_meanings
        .create_keyed_objects("keyed", &first_cas)
        .expect("create keyed");
    assert!(matches!(
        keyed.insert(&other_cas, O256::from_bytes(b"key"), b"value"),
        Err(DerivedObjectError::WrongTarget { .. })
    ));

    let second = Connection::create_in_memory().expect("create second");
    let second_meanings = second
        .create_table_meanings("meanings")
        .expect("create second meanings");
    let second_cas = second_meanings
        .create_cas("objects")
        .expect("create second CAS");
    assert!(matches!(
        keyed.insert(&second_cas, O256::from_bytes(b"key"), b"value"),
        Err(DerivedObjectError::DifferentConnection)
    ));
    assert!(matches!(
        first_meanings.create_context_objects("contextual", &second_cas),
        Err(covalence_nucleus::TableMeaningError::DifferentConnection)
    ));
}

#[test]
fn import_rejects_false_missing_and_occupied_preimages() {
    let key = O256::from_bytes(b"key");
    let expected = O256::with_key(&key, b"expected");
    let false_preimage = image_with_schema(&format!(
        "{MEANINGS_SQL}
         {CAS_SQL}
         {KEYED_SQL}
         INSERT INTO objects VALUES (1, X'{expected}', NULL);
         INSERT INTO keyed VALUES (1, X'{key}', X'77726f6e67');"
    ));
    assert_derived_error(&false_preimage, |error| {
        matches!(error, DerivedObjectError::FalsePreimage { .. })
    });

    let missing = image_with_schema(&format!(
        "{MEANINGS_SQL}
         {CAS_SQL}
         {KEYED_SQL}
         INSERT INTO keyed VALUES (7, X'{key}', X'76616c7565');"
    ));
    assert_derived_error(&missing, |error| {
        matches!(error, DerivedObjectError::MissingObject { .. })
    });

    let ordinary_hash = O256::from_bytes(b"ordinary");
    let occupied = image_with_schema(&format!(
        "{MEANINGS_SQL}
         {CAS_SQL}
         {CONTEXT_SQL}
         INSERT INTO objects VALUES (1, X'{ordinary_hash}', X'6f7264696e617279');
         INSERT INTO contextual VALUES (1, 'context', X'76616c7565');"
    ));
    assert_derived_error(&occupied, |error| {
        matches!(error, DerivedObjectError::OccupiedObject { .. })
    });
}

#[test]
fn import_rejects_bad_keys_foreign_keys_and_target_meanings() {
    let malformed_key = image_with_schema(&format!(
        "{MEANINGS_SQL}
             {CAS_SQL}
             {KEYED_SQL}
             INSERT INTO objects VALUES (1, zeroblob(32), NULL);
             INSERT INTO keyed VALUES (1, zeroblob(31), X'00');"
    ));
    assert_derived_error(&malformed_key, |error| {
        matches!(error, DerivedObjectError::MalformedKey { .. })
    });

    let no_foreign_key = image_with_schema(&format!(
        "{MEANINGS_SQL}
             {CAS_SQL}
             CREATE TABLE keyed (
                object_id INTEGER PRIMARY KEY,
                key BLOB NOT NULL,
                bytes BLOB NOT NULL
             ) STRICT;
             INSERT INTO meanings VALUES ('keyed', 'cov.cas.blake3-keyed/v0');"
    ));
    assert_derived_error(&no_foreign_key, |error| {
        matches!(error, DerivedObjectError::MalformedForeignKey { .. })
    });

    let wrong_target = image_with_schema(&format!(
        "{MEANINGS_SQL}
             CREATE TABLE z_lengths (
                object_id INTEGER PRIMARY KEY,
                hash BLOB NOT NULL UNIQUE,
                data BLOB
             ) STRICT;
             CREATE TABLE a_keyed (
                object_id INTEGER PRIMARY KEY REFERENCES z_lengths (object_id),
                key BLOB NOT NULL,
                bytes BLOB NOT NULL
             ) STRICT;
             INSERT INTO meanings VALUES
                ('z_lengths', 'cov.bytes.length/v0'),
                ('a_keyed', 'cov.cas.blake3-keyed/v0');"
    ));
    assert_derived_error(&wrong_target, |error| {
        matches!(error, DerivedObjectError::WrongTargetMeaning { .. })
    });
}

#[test]
fn import_surfaces_corrupt_target_cas_before_accepting_preimages() {
    let key = O256::from_bytes(b"key");
    let expected = O256::with_key(&key, b"value");
    let corrupt = image_with_schema(&format!(
        "{MEANINGS_SQL}
         {CAS_SQL}
         {KEYED_SQL}
         INSERT INTO objects VALUES (1, X'{expected}', X'00');
         INSERT INTO keyed VALUES (1, X'{key}', X'76616c7565');"
    ));
    assert_derived_error(&corrupt, |error| {
        matches!(
            error,
            DerivedObjectError::Cas {
                source: CasTableError::AddressMismatch { .. }
            }
        )
    });
}

fn assert_derived_error(image: &Bytes, predicate: impl FnOnce(&DerivedObjectError) -> bool) {
    let Err(DatabaseError::Validate {
        source: ValidationError::DerivedObject { source },
    }) = Connection::from_image(image)
    else {
        panic!("expected derived-object validation failure");
    };
    assert!(predicate(&source), "unexpected error: {source}");
}

fn image_with_schema(schema: &str) -> Bytes {
    let connection = RawConnection::open_in_memory().expect("open raw database");
    connection
        .sqlite()
        .execute_batch("PRAGMA foreign_keys = OFF;")
        .expect("disable foreign-key enforcement for adversarial image");
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
