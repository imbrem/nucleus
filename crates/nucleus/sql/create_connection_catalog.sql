CREATE TEMP TABLE cov_conn_catalog (
    table_id       INTEGER PRIMARY KEY,
    table_name     TEXT NOT NULL UNIQUE,
    interpretation TEXT NOT NULL
) STRICT;
