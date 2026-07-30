INSERT INTO temp.cov_conn_cas (hash, data)
VALUES (?1, NULL)
ON CONFLICT (hash) DO NOTHING
