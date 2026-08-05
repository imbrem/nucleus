CREATE TEMP TABLE cov_conn_attached (
    database_id INTEGER PRIMARY KEY,
    schema_name TEXT NOT NULL UNIQUE
) STRICT;
