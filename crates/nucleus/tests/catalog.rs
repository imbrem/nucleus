use covalence_nucleus::{CatalogEntry, Connection, Unchecked};

#[test]
fn exposes_connection_and_main_catalog_roles() {
    let connection = Connection::open_in_memory().unwrap();

    let conn = connection.catalog("temp").unwrap();
    assert!(conn.is_conn());
    assert!(!conn.is_main());
    assert!(conn.entries().unwrap().contains(&CatalogEntry {
        table_id: 3,
        table_name: String::from("cov_conn_default_cas"),
        interpretation: String::from("cov.cas.default/v0"),
    }));

    let main = connection.catalog("main").unwrap();
    assert!(!main.is_conn());
    assert!(main.is_main());
    assert!(main.entries().unwrap().is_empty());
}

#[test]
fn opens_a_file_database_without_admitting_the_standard_invariant() {
    let path = std::env::temp_dir().join(format!(
        "nucleus-catalog-{}-{}.sqlite",
        std::process::id(),
        std::thread::current().name().unwrap_or("test")
    ));
    let connection = Connection::open(&path).unwrap();
    let _: &Connection<Unchecked> = &connection;
    drop(connection);
    std::fs::remove_file(path).unwrap();
}
