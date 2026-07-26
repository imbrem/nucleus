UPDATE cov_conn_attached
SET storage_kind = ?2,
    is_exclusive = ?3
WHERE schema_name = ?1;
