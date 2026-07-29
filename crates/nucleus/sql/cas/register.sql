INSERT INTO {catalog} (table_id, table_name, interpretation)
SELECT
    coalesce(max(table_id), 0) + 1,
    ?1,
    'cov.cas/v0'
FROM {catalog};
