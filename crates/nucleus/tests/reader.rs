use covalence_nucleus::Connection;

#[test]
fn database_reader_is_confined_to_one_database() {
    let mut connection = Connection::open_in_memory().unwrap();
    let mut reader = connection.database_reader("temp");

    let tables = reader
        .query(
            "SELECT table_name FROM temp.cov_conn_catalog ORDER BY table_id",
            [],
            |rows| {
                let mut tables = Vec::new();
                while let Some(row) = rows.next()? {
                    tables.push(row.get::<_, String>(0)?);
                }
                Ok(tables)
            },
        )
        .unwrap();
    assert!(tables.iter().any(|table| table == "cov_conn_catalog"));

    assert!(
        reader
            .query_row("SELECT count(*) FROM main.cov_db_catalog", [], |row| {
                row.get::<_, i64>(0)
            })
            .is_err()
    );
}

#[test]
fn table_reader_is_confined_to_one_table() {
    let mut connection = Connection::open_in_memory().unwrap();
    let mut reader = connection.table_reader("temp", "cov_conn_catalog");

    let catalog_rows = reader
        .query_row(
            "SELECT count(upper(table_name)) FROM temp.cov_conn_catalog",
            [],
            |row| row.get::<_, i64>(0),
        )
        .unwrap();
    assert!(catalog_rows > 0);

    assert!(
        reader
            .query_row("SELECT count(*) FROM temp.cov_conn_attached", [], |row| {
                row.get::<_, i64>(0)
            })
            .is_err()
    );
}

#[test]
fn reader_denies_connection_and_database_side_effects() {
    let mut connection = Connection::open_in_memory().unwrap();

    {
        let mut reader = connection.database_reader("temp");
        for sql in [
            "DELETE FROM temp.cov_conn_catalog",
            "PRAGMA query_only = ON",
            "BEGIN",
            "ATTACH ':memory:' AS other",
            "SELECT load_extension('missing')",
        ] {
            assert!(
                reader.query(sql, [], |_| Ok(())).is_err(),
                "reader unexpectedly authorized {sql}"
            );
        }
    }

    // A denied statement must not leave a stale authorizer behind.
    let count = connection
        .database_reader("main")
        .query_row("SELECT count(*) FROM main.cov_db_catalog", [], |row| {
            row.get::<_, i64>(0)
        })
        .unwrap();
    assert_eq!(count, 0);
}
