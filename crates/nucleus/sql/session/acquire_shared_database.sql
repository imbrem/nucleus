INSERT INTO temp.cov_conn_dbvis (db_name, lock_type, ref_count, owner_type)
VALUES (?1, 'SHARED', 1, NULL)
ON CONFLICT (db_name) DO UPDATE
SET ref_count = ref_count + 1
WHERE lock_type = 'SHARED'
RETURNING ref_count;
