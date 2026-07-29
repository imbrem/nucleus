DELETE FROM temp.cov_conn_dbvis
WHERE db_name = ?1 AND ref_count = 1;
