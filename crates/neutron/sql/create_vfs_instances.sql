CREATE TEMP TABLE cov_conn_vfs (
    vfs_id      INTEGER PRIMARY KEY,
    vfs_name    TEXT,
    is_readonly INTEGER NOT NULL CHECK (is_readonly IN (0, 1))
) STRICT;
