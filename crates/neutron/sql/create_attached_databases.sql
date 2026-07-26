CREATE TEMP TABLE cov_conn_attached (
    database_id  INTEGER PRIMARY KEY,
    schema_name  TEXT NOT NULL UNIQUE,
    storage_kind TEXT CHECK (
        storage_kind IS NULL
        OR storage_kind IN ('temp', 'memory', 'file')
    ),
    is_exclusive INTEGER CHECK (
        is_exclusive IS NULL
        OR is_exclusive IN (0, 1)
    )
) STRICT;
