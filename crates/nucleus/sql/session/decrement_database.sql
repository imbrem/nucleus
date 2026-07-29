UPDATE temp.cov_conn_dbvis
SET ref_count = ref_count - 1
WHERE db_name = ?1 AND ref_count > 1;
