UPDATE main.cov_db_cas
SET blob = NULL
WHERE blake3 = ?1 AND blob IS NOT NULL
