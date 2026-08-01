INSERT INTO {table} (key, value)
VALUES (?1, ?2)
ON CONFLICT (key) DO UPDATE SET value = excluded.value;
