CREATE TEMP TABLE cov_conn_db_lock (
    db_name TEXT PRIMARY KEY,
    mode TEXT NOT NULL CHECK (mode IN ('SHARED', 'EXCLUSIVE')),
    ref_count INTEGER NOT NULL CHECK (ref_count > 0),
    CHECK (mode = 'SHARED' OR ref_count = 1)
) STRICT, WITHOUT ROWID;
