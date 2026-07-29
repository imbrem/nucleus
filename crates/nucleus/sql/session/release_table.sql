DELETE FROM temp.cov_conn_tabvis
WHERE db_name = ?1 AND table_name = ?2 AND ref_count = 1;
