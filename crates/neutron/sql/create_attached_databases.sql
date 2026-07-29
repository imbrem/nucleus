CREATE TEMP TABLE cov_conn_attached (
    database_id INTEGER PRIMARY KEY,
    schema_name TEXT NOT NULL UNIQUE,
    is_trusted INTEGER NOT NULL CHECK (is_trusted IN (0, 1)),
    is_exclusive INTEGER NOT NULL CHECK (is_exclusive IN (0, 1))
) STRICT;
