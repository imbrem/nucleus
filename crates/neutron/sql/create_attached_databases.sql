CREATE TEMP TABLE cov_conn_attached (
    database_id   INTEGER PRIMARY KEY,
    sqlite_name   TEXT NOT NULL UNIQUE,
    database_role TEXT NOT NULL CHECK (database_role IN ('main', 'aux')),
    is_exclusive  INTEGER NOT NULL CHECK (is_exclusive IN (0, 1)),
    vfs_id        INTEGER NOT NULL REFERENCES cov_conn_vfs(vfs_id)
) STRICT;
