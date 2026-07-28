use covalence_neutron::{Bytes, Connection as RawConnection};
use covalence_nucleus::{
    AdditionFact, ByteLengthFact, CatalogError, Connection, DatabaseError, TableMeaning,
    TableMeaningError, ValidationError,
};

const CATALOG_SQL: &str = "
    CREATE TABLE cov_catalog (
        table_name TEXT PRIMARY KEY,
        interpretation TEXT NOT NULL
    ) STRICT, WITHOUT ROWID;";

const MEANING_SCHEMA: &str = "
    table_name TEXT NOT NULL PRIMARY KEY,
    interpretation TEXT NOT NULL
";

const LENGTH_SCHEMA: &str = "
    bytes BLOB NOT NULL PRIMARY KEY,
    byte_length INTEGER NOT NULL
";

#[test]
fn one_meaning_table_owns_several_compiled_relations() {
    let connection = Connection::create_in_memory().expect("create database");
    let definitions = connection
        .create_table_meanings("definitions")
        .expect("create meanings");
    let sums = definitions
        .create_addition("owned_sums")
        .expect("create owned addition");
    let lengths = definitions
        .create_byte_lengths("owned_lengths")
        .expect("create owned lengths");
    sums.insert(AdditionFact::sum(20, 22).expect("sum"))
        .expect("insert sum");
    lengths
        .insert(ByteLengthFact::measure(b"meaning".to_vec()).expect("measure"))
        .expect("insert length");

    assert_eq!(
        definitions.meanings().expect("read meanings"),
        [
            ("owned_lengths".to_owned(), TableMeaning::ByteLength),
            ("owned_sums".to_owned(), TableMeaning::Addition),
        ]
    );

    let image = connection.serialize().expect("serialize");
    let restored = Connection::from_image(&image).expect("restore");
    assert_eq!(
        restored.table_meaning_tables().expect("discover meanings")[0].name(),
        "definitions"
    );
    assert_eq!(
        restored.additions().expect("discover additions")[0]
            .facts()
            .expect("read sums")[0],
        AdditionFact::sum(20, 22).expect("sum")
    );
    assert_eq!(
        restored.byte_length_tables().expect("discover lengths")[0]
            .facts()
            .expect("read lengths")[0]
            .length(),
        7
    );
}

#[test]
fn typed_creation_rejects_an_existing_owner() {
    let connection = Connection::create_in_memory().expect("create database");
    connection
        .create_byte_lengths("already_owned")
        .expect("create direct relation");
    let definitions = connection
        .create_table_meanings("definitions")
        .expect("create meanings");
    assert!(matches!(
        definitions.create_byte_lengths("already_owned"),
        Err(TableMeaningError::AlreadyInterpreted { .. })
    ));
}

#[test]
fn import_rejects_duplicate_and_nested_ownership() {
    let duplicate = image_with_schema(&format!(
        "CREATE TABLE meanings_a ({MEANING_SCHEMA}) STRICT, WITHOUT ROWID;
         CREATE TABLE meanings_b ({MEANING_SCHEMA}) STRICT, WITHOUT ROWID;
         CREATE TABLE child ({LENGTH_SCHEMA}) STRICT, WITHOUT ROWID;
         INSERT INTO meanings_a VALUES ('child', 'cov.bytes.length/v0');
         INSERT INTO meanings_b VALUES ('child', 'cov.bytes.length/v0');
         INSERT INTO cov_catalog VALUES
            ('meanings_a', 'cov.table-meanings/v0'),
            ('meanings_b', 'cov.table-meanings/v0');"
    ));
    assert!(matches!(
        Connection::from_image(&duplicate),
        Err(DatabaseError::Validate {
            source: ValidationError::Catalog {
                source: CatalogError::DuplicateMeaning { .. }
            }
        })
    ));

    let nested = image_with_schema(&format!(
        "CREATE TABLE meanings ({MEANING_SCHEMA}) STRICT, WITHOUT ROWID;
         CREATE TABLE nested ({MEANING_SCHEMA}) STRICT, WITHOUT ROWID;
         INSERT INTO meanings VALUES ('nested', 'cov.table-meanings/v0');
         INSERT INTO cov_catalog VALUES ('meanings', 'cov.table-meanings/v0');"
    ));
    assert!(matches!(
        Connection::from_image(&nested),
        Err(DatabaseError::Validate {
            source: ValidationError::Catalog {
                source: CatalogError::NestedMeaningTable { .. }
            }
        })
    ));
}

#[test]
fn import_rejects_malformed_or_unknown_meaning_relations() {
    let malformed = image_with_schema(
        "CREATE TABLE meanings (
            table_name TEXT PRIMARY KEY,
            interpretation TEXT NOT NULL
         ) STRICT;
         INSERT INTO cov_catalog VALUES ('meanings', 'cov.table-meanings/v0');",
    );
    assert!(matches!(
        Connection::from_image(&malformed),
        Err(DatabaseError::Validate {
            source: ValidationError::Catalog {
                source: CatalogError::MalformedMeaningTable { .. }
            }
        })
    ));

    let unknown = image_with_schema(&format!(
        "CREATE TABLE meanings ({MEANING_SCHEMA}) STRICT, WITHOUT ROWID;
         CREATE TABLE child (value INTEGER PRIMARY KEY) STRICT;
         INSERT INTO meanings VALUES ('child', 'cov.future/v0');
         INSERT INTO cov_catalog VALUES ('meanings', 'cov.table-meanings/v0');"
    ));
    assert!(matches!(
        Connection::from_image(&unknown),
        Err(DatabaseError::Validate {
            source: ValidationError::UnknownInterpretation { .. }
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
        .expect("create schema");
    connection.serialize().expect("serialize database")
}
