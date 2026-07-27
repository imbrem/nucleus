CREATE TEMP TABLE cov_conn_signing_keys (
    key_id BLOB PRIMARY KEY CHECK (length(key_id) = 32)
) STRICT;
