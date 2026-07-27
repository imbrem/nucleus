SELECT vfs.vfs_id, vfs.vfs_name, vfs.is_readonly
FROM cov_conn_attached AS database
JOIN cov_conn_vfs AS vfs ON vfs.vfs_id = database.vfs_id
WHERE database.database_id = ?1;
