use covalence_nucleus::{Connection, HandleError, Registry};

#[test]
fn shared_database_handles_reference_count_their_lease() {
    let mut connection = Connection::open_in_memory().unwrap();
    let session = connection.enter(Registry).unwrap();
    let first = session.shared_database("main").unwrap();
    let second = session.shared_database("main").unwrap();

    assert!(matches!(
        session.exclusive_database("main"),
        Err(HandleError::Conflict)
    ));

    drop(first);
    drop(second);
    session.exclusive_database("main").unwrap();
}

#[test]
fn tables_are_derived_from_database_handles_and_locked_independently() {
    let mut connection = Connection::open_in_memory().unwrap();
    let session = connection.enter(Registry).unwrap();
    let database = session.exclusive_database("main").unwrap();
    let table = database.exclusive_table("cov_db_catalog").unwrap();

    assert_eq!(table.database_name(), "main");
    assert_eq!(table.name(), "cov_db_catalog");
    assert!(matches!(
        database.shared_table("cov_db_catalog"),
        Err(HandleError::Conflict)
    ));

    drop(table);
    database.shared_table("cov_db_catalog").unwrap();
}

#[test]
fn handles_reject_unknown_storage_objects() {
    let mut connection = Connection::open_in_memory().unwrap();
    let session = connection.enter(Registry).unwrap();

    assert!(matches!(
        session.shared_database("missing"),
        Err(HandleError::UnknownDatabase { .. })
    ));

    let database = session.shared_database("main").unwrap();
    assert!(matches!(
        database.shared_table("missing"),
        Err(HandleError::UnknownTable { .. })
    ));
}
