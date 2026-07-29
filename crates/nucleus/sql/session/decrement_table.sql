UPDATE temp.cov_conn_tabvis
SET ref_count = ref_count - 1
WHERE db_name = ?1 AND table_name = ?2 AND ref_count > 1;
