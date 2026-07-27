use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;

use crate::{Connection, TRUSTED_SNAPSHOTS_INTERPRETATION, connection::register_table};

impl Connection {
    /// Records that a signing capability for `key` is installed.
    ///
    /// # Errors
    ///
    /// Returns an error when connection metadata cannot be updated.
    pub fn record_signing_key(&self, key: O256) -> Result<(), TrustMetadataError> {
        self.sqlite()
            .execute(
                "INSERT OR IGNORE INTO temp.cov_conn_signing_keys (key_id) VALUES (?1)",
                [key.as_ref()],
            )
            .context(UpdateSnafu)?;
        Ok(())
    }

    /// Records that this connection trusts a verifier for `key`.
    ///
    /// # Errors
    ///
    /// Returns an error when connection metadata cannot be updated.
    pub fn record_trusted_key(&self, key: O256) -> Result<(), TrustMetadataError> {
        self.sqlite()
            .execute(
                "INSERT OR IGNORE INTO temp.cov_conn_trusted_keys (key_id) VALUES (?1)",
                [key.as_ref()],
            )
            .context(UpdateSnafu)?;
        Ok(())
    }

    /// Creates another direct-hash trusted-snapshot table.
    ///
    /// # Errors
    ///
    /// Returns an error for reserved names, duplicates, or database failures.
    pub fn create_trusted_snapshot_table(&mut self, name: &str) -> Result<(), TrustMetadataError> {
        if !name.starts_with("cov_conn_") {
            return Err(TrustMetadataError::InvalidName {
                name: name.to_owned(),
            });
        }
        let quoted = quote_identifier(name);
        let transaction = self.sqlite_mut().transaction().context(UpdateSnafu)?;
        transaction
            .execute(
                &format!(
                    "CREATE TEMP TABLE {quoted} (
                        snapshot_hash BLOB PRIMARY KEY
                            CHECK (length(snapshot_hash) = 32),
                        justification BLOB CHECK (
                            justification IS NULL OR length(justification) = 32
                        )
                    ) STRICT"
                ),
                (),
            )
            .context(UpdateSnafu)?;
        let id = transaction
            .query_row(
                "SELECT COALESCE(MAX(table_id), 0) + 1 FROM temp.cov_conn_catalog",
                (),
                |row| row.get::<_, i64>(0),
            )
            .context(UpdateSnafu)?;
        register_table(&transaction, id, name, TRUSTED_SNAPSHOTS_INTERPRETATION)
            .map_err(|source| TrustMetadataError::Register { source })?;
        transaction.commit().context(UpdateSnafu)
    }

    /// Records one accepted snapshot hash and optional evidence hash.
    ///
    /// # Errors
    ///
    /// Returns an error unless `table` is a registered trusted-snapshot table
    /// or connection metadata cannot be updated.
    pub fn record_trusted_snapshot(
        &self,
        table: &str,
        snapshot: O256,
        justification: Option<O256>,
    ) -> Result<(), TrustMetadataError> {
        ensure_snapshot_table(self.sqlite(), table)?;
        let quoted = quote_identifier(table);
        self.sqlite()
            .execute(
                &format!(
                    "INSERT INTO temp.{quoted} (snapshot_hash, justification)
                     VALUES (?1, ?2)
                     ON CONFLICT (snapshot_hash)
                     DO UPDATE SET justification = excluded.justification"
                ),
                (
                    snapshot.as_ref(),
                    justification.as_ref().map(O256::as_bytes),
                ),
            )
            .context(UpdateSnafu)?;
        Ok(())
    }

    /// Tests whether a registered table records a snapshot as trusted.
    ///
    /// # Errors
    ///
    /// Returns an error unless `table` is a registered trusted-snapshot table
    /// or metadata cannot be queried.
    pub fn snapshot_is_trusted(
        &self,
        table: &str,
        snapshot: O256,
    ) -> Result<bool, TrustMetadataError> {
        ensure_snapshot_table(self.sqlite(), table)?;
        let quoted = quote_identifier(table);
        self.sqlite()
            .query_row(
                &format!(
                    "SELECT EXISTS(
                        SELECT 1 FROM temp.{quoted} WHERE snapshot_hash = ?1
                    )"
                ),
                [snapshot.as_ref()],
                |row| row.get::<_, bool>(0),
            )
            .context(QuerySnafu)
    }
}

fn ensure_snapshot_table(
    connection: &sqlite::Connection,
    table: &str,
) -> Result<(), TrustMetadataError> {
    let registered = connection
        .query_row(
            "SELECT EXISTS(
                SELECT 1 FROM temp.cov_conn_catalog
                WHERE table_name = ?1 AND interpretation = ?2
            )",
            (table, TRUSTED_SNAPSHOTS_INTERPRETATION),
            |row| row.get::<_, bool>(0),
        )
        .context(QuerySnafu)?;
    if registered {
        Ok(())
    } else {
        Err(TrustMetadataError::NotSnapshotTable {
            name: table.to_owned(),
        })
    }
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

/// Failure to maintain connection-local trust metadata.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum TrustMetadataError {
    /// A connection table name is invalid.
    #[snafu(display("connection trust table name {name:?} is invalid"))]
    InvalidName {
        /// Rejected name.
        name: String,
    },

    /// A table is not registered with the trusted-snapshot interpretation.
    #[snafu(display("{name:?} is not a registered trusted-snapshot table"))]
    NotSnapshotTable {
        /// Rejected table name.
        name: String,
    },

    /// Connection metadata could not be updated.
    #[snafu(display("could not update connection trust metadata: {source}"))]
    Update {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// Connection metadata could not be queried.
    #[snafu(display("could not query connection trust metadata: {source}"))]
    Query {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// A connection table could not be registered.
    #[snafu(display("could not register connection trust metadata: {source}"))]
    Register {
        /// Underlying connection initialization failure.
        source: crate::ConnectionError,
    },
}
