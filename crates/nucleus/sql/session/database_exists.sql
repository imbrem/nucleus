SELECT EXISTS (
    SELECT 1
    FROM pragma_database_list
    WHERE name = ?1
);
