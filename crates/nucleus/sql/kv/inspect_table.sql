SELECT type, ncol, wr, strict
FROM pragma_table_list
WHERE schema = 'main' AND name = ?1;
