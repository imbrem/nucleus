use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;
use sqlite::vfs::ConnectionVfsExt as _;

use crate::Connection;

impl Connection {
    /// Returns the actual VFS pointer identity used by an attached database.
    ///
    /// This queries `SQLITE_FCNTL_VFS_POINTER`; it does not infer identity from
    /// a URI, registered name, or connection configuration.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot report a VFS pointer for `database`.
    pub fn database_vfs(
        &self,
        database: &str,
    ) -> Result<sqlite::vfs::VfsIdentity, DatabaseVfsError> {
        self.sqlite()
            .database_vfs(database)
            .context(InspectSnafu { database })
    }

    /// Verifies that an attached database uses the expected registered VFS.
    ///
    /// This comparison is based on the actual `sqlite3_vfs` pointers after the
    /// database has been attached, rather than on names used to request a VFS.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot report the database's VFS or the
    /// reported pointer does not match `expected`.
    pub fn verify_database_vfs(
        &self,
        database: &str,
        expected: &sqlite::vfs::RegisteredVfs,
    ) -> Result<(), DatabaseVfsError> {
        let actual = self.database_vfs(database)?;
        if actual != expected.identity() {
            return Err(DatabaseVfsError::Unexpected {
                database: database.to_owned(),
            });
        }
        Ok(())
    }
}

/// Failure to inspect or verify an attached database's VFS.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum DatabaseVfsError {
    /// `SQLite` could not report the VFS used by the database.
    #[snafu(display("could not inspect the VFS used by database {database:?}: {source}"))]
    Inspect {
        /// Database/schema name passed to `SQLite`.
        database: String,
        /// Lower-level VFS identity query failure.
        source: sqlite::vfs::VfsIdentityError,
    },

    /// The attached database uses a different VFS pointer than expected.
    #[snafu(display("database {database:?} does not use the expected VFS"))]
    Unexpected {
        /// Database/schema whose actual VFS did not match.
        database: String,
    },
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::sync::Arc;

    use super::*;
    use sqlite::vfs::{ReadOnlyVfs, register_unique};

    fn image() -> Arc<[u8]> {
        let source = Connection::open_in_memory().expect("open source");
        source
            .sqlite()
            .execute_batch("CREATE TABLE value (n INTEGER); INSERT INTO value VALUES (42);")
            .expect("populate source");
        Arc::from(
            source
                .serialize()
                .expect("serialize source")
                .to_vec()
                .into_boxed_slice(),
        )
    }

    #[test]
    fn verifies_actual_vfs_pointer_after_attach() {
        let logical_path = "verified.sqlite";
        let registered = register_unique(ReadOnlyVfs::new(HashMap::from([(
            logical_path.to_owned(),
            image(),
        )])))
        .expect("register VFS");
        let uri = format!(
            "file:{logical_path}?mode=ro&immutable=1&vfs={}",
            registered.name()
        );
        let connection = Connection::open_in_memory().expect("open destination");
        connection
            .sqlite()
            .execute("ATTACH DATABASE ?1 AS imported", [&uri])
            .expect("attach image");

        connection
            .verify_database_vfs("imported", &registered)
            .expect("verify attached VFS");
        assert!(matches!(
            connection.verify_database_vfs("main", &registered),
            Err(DatabaseVfsError::Unexpected { database }) if database == "main"
        ));
    }
}
