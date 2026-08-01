INSERT INTO main.cov_db_cas (blake3, blob, size)
VALUES (?1, ?2, length(?2))
ON CONFLICT (blake3) DO UPDATE SET
    blob = excluded.blob,
    size = excluded.size
WHERE (
        cov_db_cas.blob IS NULL
        AND (cov_db_cas.size IS NULL OR cov_db_cas.size = excluded.size)
    )
    OR cov_db_cas.blob = excluded.blob
RETURNING TRUE
