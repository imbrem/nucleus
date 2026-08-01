CREATE TABLE {objects} (
    file_id INTEGER PRIMARY KEY CHECK (file_id > 0),
    blake3  BLOB UNIQUE CHECK (blake3 IS NULL OR length(blake3) = 32),
    size    INTEGER CHECK (size IS NULL OR size >= 0)
) STRICT;
