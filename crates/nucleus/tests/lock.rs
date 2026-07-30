use covalence_nucleus::{Connection, Lock, LockError, MutableConnectionCarrier, SessionProtocol};

fn lock_count(connection: &mut Connection, table: &str) -> i64 {
    connection
        .table_reader("temp", table)
        .query_row(&format!("SELECT count(*) FROM temp.{table}"), [], |row| {
            row.get(0)
        })
        .unwrap()
}

#[test]
fn shared_database_view_supplies_inherited_table_views() {
    let mut connection = Connection::open_in_memory().unwrap();

    {
        let mut database = connection.view_mut(Lock::database("main")).unwrap();
        assert_eq!(database.database_name(), "main");

        let mut table = database.table("cov_db_catalog").unwrap();
        assert_eq!(table.database_name(), "main");
        assert_eq!(table.table_name(), "cov_db_catalog");
        let count = table
            .reader()
            .query_row("SELECT count(*) FROM main.cov_db_catalog", [], |row| {
                row.get::<_, i64>(0)
            })
            .unwrap();
        assert_eq!(count, 0);
    }

    assert_eq!(lock_count(&mut connection, "cov_conn_db_lock"), 0);
    assert_eq!(lock_count(&mut connection, "cov_conn_tab_lock"), 0);
}

#[test]
fn exclusive_database_session_clears_retained_table_locks() {
    let mut connection = Connection::open_in_memory().unwrap();

    {
        let mut session = connection.session(Lock::database("main")).unwrap();
        session.table("cov_db_catalog").unwrap().retain_lock();

        assert_eq!(
            session
                .table_reader("temp", "cov_conn_tab_lock")
                .query_row("SELECT count(*) FROM temp.cov_conn_tab_lock", [], |row| row
                    .get::<_, i64>(0))
                .unwrap(),
            1
        );

        // A second table view shares the same logical row.
        drop(session.table("cov_db_catalog").unwrap());
        assert_eq!(
            session
                .database_reader("temp")
                .query_row(
                    "SELECT ref_count FROM temp.cov_conn_tab_lock
                     WHERE db_name = 'main' AND table_name = 'cov_db_catalog'",
                    [],
                    |row| row.get::<_, i64>(0)
                )
                .unwrap(),
            1
        );
    }

    assert_eq!(lock_count(&mut connection, "cov_conn_db_lock"), 0);
    assert_eq!(lock_count(&mut connection, "cov_conn_tab_lock"), 0);
}

#[test]
fn root_session_clears_retained_and_forgotten_child_locks() {
    let mut connection = Connection::open_in_memory().unwrap();

    {
        let mut locks = connection.session(Lock).unwrap();

        {
            let _retained = locks.view(Lock::database("main")).unwrap().retain_lock();
        }

        let forgotten = locks.session(Lock::database("temp")).unwrap();
        std::mem::forget(forgotten);

        assert_eq!(
            locks
                .table_reader("temp", "cov_conn_db_lock")
                .query_row("SELECT count(*) FROM temp.cov_conn_db_lock", [], |row| row
                    .get::<_, i64>(
                    0
                ))
                .unwrap(),
            2
        );
    }

    assert_eq!(lock_count(&mut connection, "cov_conn_db_lock"), 0);
    assert_eq!(lock_count(&mut connection, "cov_conn_tab_lock"), 0);
}

#[test]
fn retained_database_lock_blocks_an_incompatible_session() {
    let mut connection = Connection::open_in_memory().unwrap();
    let carrier = connection
        .view_mut(Lock::database("main"))
        .unwrap()
        .retain_lock();

    let (error, mut carrier) = Lock::database("main").enter(carrier).unwrap_err();
    assert!(matches!(error, LockError::Conflict));
    assert_eq!(
        carrier
            .connection_mut()
            .table_reader("temp", "cov_conn_db_lock")
            .query_row("SELECT count(*) FROM temp.cov_conn_db_lock", [], |row| row
                .get::<_, i64>(
                0
            ))
            .unwrap(),
        1
    );
}

#[test]
fn forgotten_session_leaves_a_fail_closed_lock() {
    let mut connection = Connection::open_in_memory().unwrap();
    let session = connection.session(Lock::database("main")).unwrap();
    std::mem::forget(session);

    assert!(matches!(
        connection.session(Lock::database("main")),
        Err(LockError::Conflict)
    ));
    assert_eq!(lock_count(&mut connection, "cov_conn_db_lock"), 1);
}

#[test]
fn owned_session_can_restore_its_connection() {
    let connection = Connection::open_in_memory().unwrap();
    let session = connection.into_session(Lock::database("main")).unwrap();
    let mut connection = session.finish().unwrap().into_connection();

    assert_eq!(lock_count(&mut connection, "cov_conn_db_lock"), 0);
}
