use covalence_neutron::{CatalogEntry, CatalogError, Connection};

#[test]
fn creates_reopens_and_uses_main_catalog() {
    let connection = Connection::open_in_memory().unwrap();
    let catalog = connection.catalog("main").unwrap();
    catalog.register("facts", "example/v0").unwrap();
    assert_eq!(
        catalog.entries().unwrap(),
        [CatalogEntry {
            table_name: String::from("facts"),
            interpretation: String::from("example/v0"),
        }]
    );
    assert_eq!(
        connection.catalog("main").unwrap().entries().unwrap().len(),
        1
    );
}

#[test]
fn rejects_temp_missing_and_malformed_catalogs() {
    let connection = Connection::open_in_memory().unwrap();
    assert!(matches!(
        connection.catalog("temp"),
        Err(CatalogError::TemporaryDatabase)
    ));
    assert!(matches!(
        connection.catalog("missing"),
        Err(CatalogError::MissingDatabase { .. })
    ));
    connection
        .sqlite()
        .execute_batch("CREATE TABLE cov_db_catalog (wrong INTEGER) STRICT;")
        .unwrap();
    assert!(matches!(
        connection.catalog("main"),
        Err(CatalogError::Malformed { .. })
    ));
}

#[test]
fn supports_attached_non_temporary_databases() {
    let connection = Connection::open_in_memory().unwrap();
    connection
        .sqlite()
        .execute_batch("ATTACH DATABASE ':memory:' AS aux;")
        .unwrap();
    let catalog = connection.catalog("aux").unwrap();
    assert_eq!(catalog.database_name(), "aux");
    catalog.register("terms", "example/terms/v0").unwrap();
    assert_eq!(catalog.entries().unwrap()[0].table_name, "terms");
}
