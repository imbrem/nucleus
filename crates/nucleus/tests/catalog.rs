use covalence_nucleus::Connection;

#[test]
fn wraps_catalog_without_exposing_unchecked_registration() {
    let connection = Connection::open_in_memory().unwrap();
    assert_eq!(connection.catalog("main").unwrap().database_name(), "main");
}
