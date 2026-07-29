CREATE TEMP TABLE cov_conn_default_cas (
    object_id INTEGER PRIMARY KEY,
    hash BLOB NOT NULL UNIQUE CHECK (length(hash) = 32),
    data BLOB,
    CHECK (data IS NULL OR length(hash) = 32)
) STRICT;
