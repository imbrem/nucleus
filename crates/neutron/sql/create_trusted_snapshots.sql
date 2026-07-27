CREATE TEMP TABLE cov_conn_trusted_snapshots (
    snapshot_hash BLOB PRIMARY KEY CHECK (length(snapshot_hash) = 32),
    justification BLOB CHECK (
        justification IS NULL OR length(justification) = 32
    )
) STRICT;
