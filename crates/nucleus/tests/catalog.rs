use covalence_nucleus::Connection;

#[test]
fn wraps_catalog_without_exposing_unchecked_registration() {
    let connection = Connection::open_in_memory().unwrap();
    let main = connection.catalog("main").unwrap();
    assert_eq!(main.database_name(), "main");
    assert!(main.is_main());
    assert!(!main.is_conn());

    let conn = connection.catalog("temp").unwrap();
    assert_eq!(conn.database_name(), "temp");
    assert!(conn.is_conn());
    assert!(!conn.is_main());
}
