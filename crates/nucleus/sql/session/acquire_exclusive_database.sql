INSERT OR IGNORE INTO temp.cov_conn_dbvis (db_name, lock_type, ref_count, owner_type)
VALUES (?1, 'EXCLUSIVE', 1, ?2)
RETURNING ref_count;
