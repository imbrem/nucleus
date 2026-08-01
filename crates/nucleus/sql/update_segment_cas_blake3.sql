UPDATE {objects}
SET blake3 = ?2
WHERE file_id = ?1
  AND blake3 IS ?3
  AND size IS ?4;
