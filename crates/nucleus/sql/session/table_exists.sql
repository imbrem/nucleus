SELECT EXISTS (
    SELECT 1
    FROM pragma_table_list
    WHERE schema = ?1 AND name = ?2
);
