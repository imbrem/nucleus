INSERT INTO temp.cov_conn_cas (hash, data)
VALUES (?1, ?2)
ON CONFLICT (hash) DO UPDATE SET data = excluded.data
WHERE cov_conn_cas.data IS NULL OR cov_conn_cas.data = excluded.data
RETURNING object_id
