INSERT INTO temp.cov_conn_cas (hash, data)
VALUES (?1, ?2)
ON CONFLICT (hash) DO UPDATE SET data = excluded.data
WHERE data IS NULL OR data = excluded.data
RETURNING object_id
