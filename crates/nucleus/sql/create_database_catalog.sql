CREATE TABLE main.cov_db_catalog (
    table_id       INTEGER PRIMARY KEY,
    table_name     TEXT NOT NULL UNIQUE,
    interpretation TEXT NOT NULL
) STRICT;
