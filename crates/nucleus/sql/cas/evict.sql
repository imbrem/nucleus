UPDATE temp.cov_conn_cas
SET data = NULL
WHERE object_id = ?1 AND data IS NOT NULL
