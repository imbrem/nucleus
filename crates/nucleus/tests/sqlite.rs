#[test]
fn sqlite_is_available_to_consumers() {
    assert_eq!(covalence_nucleus::smoke(), 42);
}

#[test]
fn trusted_database_exposes_only_checked_bool_writes() {
    use covalence_neutron::BOOL_VALUES_RELATION_V0;
    use covalence_nucleus::{InsertOutcome, TrustedDb};

    let mut database = TrustedDb::create_in_memory().unwrap();
    let mut relation = database.bool_relation(BOOL_VALUES_RELATION_V0).unwrap();

    assert_eq!(relation.insert(true).unwrap(), InsertOutcome::Inserted);
    assert_eq!(relation.values().unwrap(), vec![true]);
}
