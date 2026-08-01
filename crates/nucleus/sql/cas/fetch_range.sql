SELECT substr(blob, ?2, ?3), size
FROM main.cov_db_cas
WHERE blake3 = ?1
