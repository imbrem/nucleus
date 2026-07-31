CREATE TEMP TABLE cov_conn_tab_lock (
    db_name TEXT NOT NULL,
    table_name TEXT NOT NULL,
    ref_count INTEGER NOT NULL CHECK (ref_count > 0),
    PRIMARY KEY (db_name, table_name)
) STRICT, WITHOUT ROWID;
