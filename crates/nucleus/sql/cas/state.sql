SELECT size, blob IS NOT NULL
FROM main.cov_db_cas
WHERE blake3 = ?1
