SELECT count(*) FROM {schema}.sqlite_schema
WHERE type = 'trigger' AND tbl_name = ?1
