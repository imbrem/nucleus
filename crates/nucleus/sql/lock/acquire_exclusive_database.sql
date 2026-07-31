INSERT INTO temp.cov_conn_db_lock (db_name, mode, ref_count)
SELECT ?1, 'EXCLUSIVE', 1
WHERE NOT EXISTS (
    SELECT 1 FROM temp.cov_conn_db_lock WHERE db_name = ?1
)
AND NOT EXISTS (
    SELECT 1 FROM temp.cov_conn_tab_lock WHERE db_name = ?1
)
RETURNING ref_count;
