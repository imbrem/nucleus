INSERT INTO temp.cov_conn_db_lock (db_name, mode, ref_count)
VALUES (?1, 'SHARED', 1)
ON CONFLICT (db_name) DO UPDATE
SET ref_count = ref_count + 1
WHERE mode = 'SHARED'
RETURNING ref_count;
