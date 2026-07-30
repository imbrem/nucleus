use covalence_nucleus::{Connection, ReadOnly, Standard};

#[test]
fn borrowed_read_only_protocol_exposes_only_scoped_readers() {
    let mut connection = Connection::open_in_memory().unwrap();

    {
        let mut read_only = connection.view_mut(ReadOnly).unwrap();
        let count = read_only
            .database_reader("temp")
            .query_row("SELECT count(*) FROM temp.cov_conn_catalog", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert!(count > 0);

        assert!(
            read_only
                .table_reader("temp", "cov_conn_catalog")
                .query("DELETE FROM temp.cov_conn_catalog", [], |_| Ok(()))
                .is_err()
        );
    }

    let count = connection
        .database_reader("main")
        .query_row("SELECT count(*) FROM main.cov_db_catalog", [], |row| {
            row.get::<_, i64>(0)
        })
        .unwrap();
    assert_eq!(count, 0);
}

#[test]
fn owned_read_only_protocol_returns_the_connection() {
    let connection = Connection::open_in_memory().unwrap();
    let read_only = connection.into_view(ReadOnly).unwrap();
    let connection = read_only.into_connection();
    let _: Connection<Standard> = connection;
}
