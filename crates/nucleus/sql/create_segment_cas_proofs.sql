CREATE TABLE {proofs} (
    file_id     INTEGER NOT NULL REFERENCES {objects}(file_id),
    first_chunk INTEGER NOT NULL CHECK (first_chunk >= 0),
    chunks      INTEGER NOT NULL CHECK (chunks > 0),
    blake3_cv   BLOB NOT NULL CHECK (length(blake3_cv) = 32),
    PRIMARY KEY (file_id, first_chunk, chunks)
) STRICT, WITHOUT ROWID;
