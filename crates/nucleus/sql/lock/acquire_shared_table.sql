INSERT INTO temp.cov_conn_tab_lock (db_name, table_name, ref_count)
SELECT ?1, ?2, 1
WHERE EXISTS (
    SELECT 1
    FROM temp.cov_conn_db_lock
    WHERE db_name = ?1 AND mode = 'EXCLUSIVE'
)
ON CONFLICT (db_name, table_name) DO UPDATE
SET ref_count = ref_count + 1
RETURNING ref_count;
