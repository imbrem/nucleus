SELECT name, type, "notnull", pk, hidden
FROM pragma_table_xinfo(?1, 'main')
ORDER BY cid;
