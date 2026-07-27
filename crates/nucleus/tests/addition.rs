use covalence_neutron::{Bytes, Connection as RawConnection};
use covalence_nucleus::{Addition, AdditionError, AdditionFact, Connection, DatabaseError};

const CATALOG_SQL: &str = "
    CREATE TABLE cov_catalog (
        table_name TEXT PRIMARY KEY,
        interpretation TEXT NOT NULL
    ) STRICT, WITHOUT ROWID;";

#[test]
fn checked_facts_reject_falsehood_and_machine_overflow() {
    assert!(matches!(
        AdditionFact::new(4, 2, 3),
        Err(AdditionError::False { .. })
    ));
    for (lhs, rhs) in [(i64::MAX, 1), (i64::MIN, -1)] {
        assert!(matches!(
            AdditionFact::sum(lhs, rhs),
            Err(AdditionError::Overflow { .. })
        ));
    }
}

#[test]
fn wrappers_discover_and_use_multiple_catalogued_relations() {
    let connection = Connection::create_in_memory().expect("create database");
    let naturals = connection
        .create_addition("naturals")
        .expect("create naturals");
    let integers = connection
        .create_addition("integers")
        .expect("create integers");

    naturals
        .insert(AdditionFact::sum(20, 22).expect("sum"))
        .expect("insert natural");
    integers
        .insert(AdditionFact::sum(i64::MIN, 1).expect("sum"))
        .expect("insert integer");

    let additions = connection.additions().expect("discover additions");
    assert_eq!(
        additions.iter().map(Addition::name).collect::<Vec<_>>(),
        ["integers", "naturals"]
    );
    assert_eq!(
        additions[0].facts().expect("load integers"),
        [AdditionFact {
            tm: i64::MIN + 1,
            lhs: i64::MIN,
            rhs: 1,
        }]
    );
    assert_eq!(
        additions[1].facts().expect("load naturals"),
        [AdditionFact {
            tm: 42,
            lhs: 20,
            rhs: 22,
        }]
    );
}

#[test]
fn canonical_schema_rejects_false_and_overflowing_rows_locally() {
    let raw = raw_database(
        "CREATE TABLE addition (
            tm INTEGER NOT NULL,
            lhs INTEGER NOT NULL,
            rhs INTEGER NOT NULL,
            PRIMARY KEY (tm, lhs, rhs),
            CHECK (typeof(lhs + rhs) = 'integer' AND tm = lhs + rhs)
        ) STRICT, WITHOUT ROWID;
        INSERT INTO cov_catalog VALUES ('addition', 'cov.addition/v0');",
    );

    assert!(
        raw.sqlite()
            .execute("INSERT INTO addition VALUES (4, 2, 3)", ())
            .is_err()
    );
    for (tm, lhs, rhs) in [(i64::MIN, i64::MAX, 1), (i64::MAX, i64::MIN, -1)] {
        assert!(
            raw.sqlite()
                .execute("INSERT INTO addition VALUES (?1, ?2, ?3)", (tm, lhs, rhs),)
                .is_err()
        );
    }
}

#[test]
fn import_rechecks_rows_instead_of_trusting_sql_constraints() {
    let bytes = image_with_schema(
        "CREATE TABLE hostile (
            tm INTEGER NOT NULL,
            lhs INTEGER NOT NULL,
            rhs INTEGER NOT NULL,
            PRIMARY KEY (tm, lhs, rhs)
        ) STRICT, WITHOUT ROWID;
        INSERT INTO hostile VALUES (4, 2, 3);
        INSERT INTO cov_catalog VALUES ('hostile', 'cov.addition/v0');",
    );

    assert!(matches!(
        Connection::from_image(&bytes),
        Err(DatabaseError::Validate {
            source: covalence_nucleus::ValidationError::Addition {
                source: AdditionError::False { .. }
            }
        })
    ));
}

#[test]
fn import_rejects_noncanonical_layouts_and_unknown_meanings() {
    let rowid = image_with_schema(
        "CREATE TABLE addition (
            tm INTEGER NOT NULL,
            lhs INTEGER NOT NULL,
            rhs INTEGER NOT NULL
        ) STRICT;
        INSERT INTO addition VALUES (3, 1, 2);
        INSERT INTO cov_catalog VALUES ('addition', 'cov.addition/v0');",
    );
    assert!(matches!(
        Connection::from_image(&rowid),
        Err(DatabaseError::Validate {
            source: covalence_nucleus::ValidationError::Addition {
                source: AdditionError::MalformedTable { .. }
            }
        })
    ));

    let unknown = image_with_schema(
        "CREATE TABLE mystery (
            tm INTEGER NOT NULL,
            lhs INTEGER NOT NULL,
            rhs INTEGER NOT NULL,
            PRIMARY KEY (tm, lhs, rhs)
        ) STRICT, WITHOUT ROWID;
        INSERT INTO cov_catalog VALUES ('mystery', 'cov.unknown/v0');",
    );
    assert!(matches!(
        Connection::from_image(&unknown),
        Err(DatabaseError::Validate {
            source: covalence_nucleus::ValidationError::UnknownInterpretation { .. }
        })
    ));
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
        .expect("create test schema");
    connection
}
