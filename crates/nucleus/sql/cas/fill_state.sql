SELECT hash, data IS NOT NULL
FROM temp.cov_conn_default_cas
WHERE object_id = ?1
