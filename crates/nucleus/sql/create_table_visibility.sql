CREATE TEMP TABLE cov_conn_tabvis (
    db_name TEXT NOT NULL,
    table_name TEXT NOT NULL,
    lock_type TEXT NOT NULL CHECK (lock_type IN ('SHARED', 'EXCLUSIVE')),
    ref_count INTEGER NOT NULL CHECK (ref_count > 0),
    owner_type TEXT,
    PRIMARY KEY (db_name, table_name),
    CHECK (
        (lock_type = 'SHARED' AND owner_type IS NULL) OR
        (lock_type = 'EXCLUSIVE' AND owner_type IS NOT NULL)
    )
) STRICT, WITHOUT ROWID;
