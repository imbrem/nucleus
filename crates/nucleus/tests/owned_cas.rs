use bytes::Bytes;
use covalence_nucleus::{CasError, CatalogEntry, Connection, HandleError, Registry};

#[test]
fn a_cas_owns_an_exclusive_capability_to_its_catalogued_table() {
    let mut connection = Connection::open_in_memory().unwrap();
    {
        let session = connection.enter(Registry).unwrap();
        let database = session.exclusive_database("main").unwrap();
        let cas = database.create_cas("objects").unwrap();
        let hash = cas.store(b"owned").unwrap();

        assert_eq!(cas.fetch(hash).unwrap(), Some(Bytes::from_static(b"owned")));
        assert!(matches!(
            database.shared_table("objects"),
            Err(HandleError::Conflict)
        ));
    }

    assert!(
        connection
            .catalog("main")
            .unwrap()
            .entries()
            .unwrap()
            .contains(&CatalogEntry {
                table_id: 1,
                table_name: String::from("objects"),
                interpretation: String::from("cov.cas/v0"),
            })
    );
}

#[test]
fn user_cas_tables_cannot_claim_reserved_names() {
    let mut connection = Connection::open_in_memory().unwrap();
    let session = connection.enter(Registry).unwrap();
    let database = session.exclusive_database("main").unwrap();

    assert!(matches!(
        database.create_cas("cov_db_objects"),
        Err(CasError::ReservedName { .. })
    ));
    assert!(matches!(
        database.create_cas("cov_conn_objects"),
        Err(CasError::ReservedName { .. })
    ));
}

#[test]
fn cas_table_names_are_sql_identifiers_not_sql_source() {
    let mut connection = Connection::open_in_memory().unwrap();
    {
        let session = connection.enter(Registry).unwrap();
        let database = session.exclusive_database("main").unwrap();
        let cas = database
            .create_cas("odd\"; DROP TABLE cov_db_catalog; --")
            .unwrap();
        let hash = cas.store(b"quoted").unwrap();
        assert_eq!(
            cas.fetch(hash).unwrap(),
            Some(Bytes::from_static(b"quoted"))
        );
    }

    assert!(connection.catalog("main").unwrap().entries().is_ok());
}
