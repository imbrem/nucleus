CREATE TEMP TABLE cov_conn_trusted_keys (
    key_id BLOB PRIMARY KEY CHECK (length(key_id) = 32)
) STRICT;
