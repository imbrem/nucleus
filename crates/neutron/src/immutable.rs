use std::collections::HashMap;
use std::sync::Arc;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;
use sqlite::vfs::{ReadOnlyVfs, RegisteredVfs, register_unique};

use crate::{Connection, DatabaseVfsError};

const LOGICAL_PATH: &str = "immutable.sqlite";
const DATABASE_IS_ATTACHED_SQL: &str =
    "SELECT EXISTS(SELECT 1 FROM pragma_database_list WHERE name = ?1)";

/// One fixed resident database image exposed through a private immutable VFS.
///
/// This is a hash-free mechanical `SQLite` capability. It assigns no schema,
/// content address, validity, trust, or logical interpretation to the bytes.
/// Clones share the exact bytes and registered VFS identity.
#[derive(Clone)]
pub struct ImmutableImage {
    inner: Arc<ImmutableImageInner>,
}

struct ImmutableImageInner {
    bytes: Arc<[u8]>,
    registered: RegisteredVfs,
}

impl ImmutableImage {
    /// Registers one fixed byte string through a fresh process-local read-only VFS.
    ///
    /// Registered VFS state remains allocated for the process lifetime, even after
    /// all handles are dropped. Callers should therefore deduplicate and bound
    /// untrusted inputs before registering them.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot register the private VFS.
    pub fn register(bytes: Arc<[u8]>) -> Result<Self, ImmutableImageError> {
        let registered = register_unique(ReadOnlyVfs::new(HashMap::from([(
            LOGICAL_PATH.to_owned(),
            Arc::clone(&bytes),
        )])))
        .context(RegisterSnafu)?;
        Ok(Self {
            inner: Arc::new(ImmutableImageInner { bytes, registered }),
        })
    }

    /// Returns the exact uninterpreted bytes served by this handle.
    #[must_use]
    pub fn bytes(&self) -> &[u8] {
        &self.inner.bytes
    }

    /// Attaches the image read-only and verifies `SQLite`'s actual VFS pointer.
    ///
    /// The generated VFS name is only a selector. Success is based on checking
    /// the post-attach `sqlite3_vfs*` identity. A failed pointer check is followed
    /// by a best-effort detach.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid or occupied schema name, attachment
    /// failure, or actual VFS pointer mismatch.
    pub fn attach(&self, connection: &Connection, schema: &str) -> Result<(), ImmutableImageError> {
        if schema.is_empty() || schema.contains('\0') {
            return Err(ImmutableImageError::InvalidSchemaName);
        }
        let attached = connection
            .sqlite()
            .query_row(DATABASE_IS_ATTACHED_SQL, [schema], |row| {
                row.get::<_, bool>(0)
            })
            .context(InspectSnafu)?;
        if attached {
            return Err(ImmutableImageError::AlreadyAttached {
                schema: schema.to_owned(),
            });
        }

        let uri = format!(
            "file:{LOGICAL_PATH}?mode=ro&immutable=1&vfs={}",
            self.inner.registered.name()
        );
        let quoted = quote_identifier(schema);
        connection
            .sqlite()
            .execute(&format!("ATTACH DATABASE ?1 AS {quoted}"), [&uri])
            .context(AttachSnafu {
                schema: schema.to_owned(),
            })?;
        if let Err(source) = self.verify(connection, schema) {
            let _ = connection
                .sqlite()
                .execute(&format!("DETACH DATABASE {quoted}"), ());
            return Err(ImmutableImageError::Verify {
                schema: schema.to_owned(),
                source,
            });
        }
        Ok(())
    }

    /// Verifies that an attached schema still uses this handle's actual VFS pointer.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot report the pointer or it differs from
    /// this handle's registered VFS identity.
    pub fn verify(&self, connection: &Connection, schema: &str) -> Result<(), DatabaseVfsError> {
        connection.verify_database_vfs(schema, &self.inner.registered)
    }
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

/// Failure to register, attach, or verify an immutable resident image.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ImmutableImageError {
    /// The private VFS could not be registered.
    #[snafu(display("could not register immutable SQLite VFS: {source}"))]
    Register { source: sqlite::vfs::RegisterError },
    /// The schema name is empty or contains a NUL byte.
    #[snafu(display("invalid SQLite schema name"))]
    InvalidSchemaName,
    /// The schema name is already attached.
    #[snafu(display("SQLite schema {schema:?} is already attached"))]
    AlreadyAttached { schema: String },
    /// The attached-database list could not be inspected.
    #[snafu(display("could not inspect attached SQLite databases: {source}"))]
    Inspect { source: sqlite::Error },
    /// `SQLite` could not attach the private immutable image.
    #[snafu(display("could not attach SQLite schema {schema:?}: {source}"))]
    Attach {
        schema: String,
        source: sqlite::Error,
    },
    /// The attached schema did not use this handle's actual VFS pointer.
    #[snafu(display("could not verify the VFS used by SQLite schema {schema:?}: {source}"))]
    Verify {
        schema: String,
        source: DatabaseVfsError,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn image() -> Arc<[u8]> {
        let source = Connection::open_in_memory().expect("open source");
        source
            .sqlite()
            .execute_batch(
                "CREATE TABLE example(value TEXT NOT NULL);
                 INSERT INTO example VALUES ('shared');",
            )
            .expect("populate source");
        Arc::from(source.serialize().expect("serialize").as_ref())
    }

    #[test]
    fn one_handle_is_reused_by_two_connections() {
        let mounted = ImmutableImage::register(image()).expect("register image");
        let first = Connection::open_in_memory().expect("open first");
        let second = Connection::open_in_memory().expect("open second");
        mounted.attach(&first, "library").expect("attach first");
        mounted.attach(&second, "library").expect("attach second");
        for connection in [&first, &second] {
            mounted
                .verify(connection, "library")
                .expect("verify actual pointer");
            assert_eq!(
                connection
                    .sqlite()
                    .query_row("SELECT value FROM library.example", (), |row| {
                        row.get::<_, String>(0)
                    })
                    .expect("read image"),
                "shared"
            );
            assert!(
                connection
                    .sqlite()
                    .execute("UPDATE library.example SET value = 'changed'", ())
                    .is_err()
            );
        }
        assert!(mounted.verify(&first, "main").is_err());
    }

    #[test]
    fn rejects_invalid_and_occupied_schema_names() {
        let mounted = ImmutableImage::register(image()).expect("register image");
        let connection = Connection::open_in_memory().expect("open connection");
        assert!(mounted.attach(&connection, "").is_err());
        assert!(mounted.attach(&connection, "bad\0name").is_err());
        mounted
            .attach(&connection, "library")
            .expect("attach image");
        assert!(matches!(
            mounted.attach(&connection, "library"),
            Err(ImmutableImageError::AlreadyAttached { .. })
        ));
    }
}
