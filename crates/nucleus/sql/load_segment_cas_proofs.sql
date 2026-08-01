SELECT first_chunk, chunks, blake3_cv
FROM {proofs}
WHERE file_id = ?1
ORDER BY first_chunk, chunks;
