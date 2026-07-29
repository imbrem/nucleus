CREATE TEMP TABLE cov_conn_dbvis (
    db_name TEXT PRIMARY KEY,
    lock_type TEXT NOT NULL CHECK (lock_type IN ('SHARED', 'EXCLUSIVE')),
    ref_count INTEGER NOT NULL CHECK (ref_count > 0),
    owner_type TEXT,
    CHECK (
        (lock_type = 'SHARED' AND owner_type IS NULL) OR
        (lock_type = 'EXCLUSIVE' AND owner_type IS NOT NULL)
    )
) STRICT, WITHOUT ROWID;
