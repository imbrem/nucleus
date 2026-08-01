INSERT INTO main.cov_db_cas (blake3, size)
VALUES (?1, ?2)
ON CONFLICT (blake3) DO UPDATE SET
    size = COALESCE(cov_db_cas.size, excluded.size)
WHERE cov_db_cas.size IS NULL
   OR excluded.size IS NULL
   OR cov_db_cas.size = excluded.size
RETURNING TRUE
