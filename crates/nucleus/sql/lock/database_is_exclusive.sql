SELECT ?1 = 'temp' OR EXISTS (
    SELECT 1
    FROM temp.cov_conn_attached
    WHERE schema_name = ?1 AND is_exclusive
);
