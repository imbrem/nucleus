INSERT INTO {objects} (blake3, size)
VALUES (?1, ?2)
RETURNING file_id;
