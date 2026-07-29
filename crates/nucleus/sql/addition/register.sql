INSERT INTO {catalog} (table_id, table_name, interpretation)
VALUES (
    (SELECT COALESCE(MAX(table_id), 0) + 1 FROM {catalog}),
    ?1,
    ?2
)
