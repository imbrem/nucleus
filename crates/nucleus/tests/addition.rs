use covalence_nucleus::{AdditionError, AdditionFact, Connection};

#[test]
fn checked_rules_are_the_only_public_theorem_constructors() {
    let false_row = AdditionFact {
        tm: 4,
        lhs: 2,
        rhs: 3,
    };
    assert!(matches!(
        AdditionFact::new(false_row.tm, false_row.lhs, false_row.rhs),
        Err(AdditionError::False { .. })
    ));
    assert!(matches!(
        AdditionFact::sum(i64::MAX, 1),
        Err(AdditionError::Overflow { .. })
    ));
}

#[test]
fn empty_table_stays_trusted_through_theorem_only_insertion() {
    let connection = Connection::open_in_memory().unwrap();
    let catalog = connection.catalog("main").unwrap();
    let mut addition = catalog.create_addition("user addition facts").unwrap();
    let raw = AdditionFact {
        tm: 42,
        lhs: 20,
        rhs: 22,
    };

    assert!(!addition.contains(&raw).unwrap());
    let theorem = AdditionFact::new(raw.tm, raw.lhs, raw.rhs).unwrap();
    addition.insert(&theorem).unwrap();
    assert!(addition.contains(&raw).unwrap());
    assert_eq!(addition.facts().unwrap(), [theorem]);
}

#[test]
fn infrastructure_names_are_not_user_tables() {
    let connection = Connection::open_in_memory().unwrap();
    let catalog = connection.catalog("main").unwrap();
    for name in ["", "cov_db_claims", "cov_conn_claims", "sqlite_claims"] {
        assert!(matches!(
            catalog.create_addition(name),
            Err(AdditionError::ReservedName { .. })
        ));
    }
}
