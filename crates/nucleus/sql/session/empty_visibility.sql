SELECT
    (SELECT count(*) FROM temp.cov_conn_dbvis) +
    (SELECT count(*) FROM temp.cov_conn_tabvis)
