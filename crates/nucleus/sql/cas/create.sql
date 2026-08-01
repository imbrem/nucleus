CREATE TABLE main.cov_db_cas (
    blake3 BLOB PRIMARY KEY CHECK (length(blake3) = 32),
    blob    BLOB,
    size    INTEGER CHECK (size IS NULL OR size >= 0),
    CHECK (blob IS NULL OR (size IS NOT NULL AND size = length(blob)))
) STRICT, WITHOUT ROWID;
