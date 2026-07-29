INSERT OR IGNORE INTO temp.cov_conn_tabvis
    (db_name, table_name, lock_type, ref_count, owner_type)
VALUES (?1, ?2, 'EXCLUSIVE', 1, ?3)
RETURNING ref_count;
