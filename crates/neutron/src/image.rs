use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::sql::{self, Param};
use crate::{Bytes, Connection, ConnectionError};

const NEXT_DATABASE_ID_SQL: &str =
    "SELECT COALESCE(MAX(database_id), 0) + 1 FROM temp.cov_conn_attached";
const REGISTER_DATABASE_SQL: &str =
    "INSERT INTO temp.cov_conn_attached (database_id, schema_name) VALUES (?1, ?2)";
const FIND_DATABASE_SQL: &str =
    "SELECT database_id FROM temp.cov_conn_attached WHERE schema_name = ?1";
const UNREGISTER_DATABASE_SQL: &str = "DELETE FROM temp.cov_conn_attached WHERE schema_name = ?1";
const DATABASE_IS_ATTACHED_SQL: &str =
    "SELECT EXISTS(SELECT 1 FROM pragma_database_list WHERE name = ?1)";

impl Connection {
    /// Serializes the `main` database as an owned `SQLite` database image.
    ///
    /// Connection-local Neutron metadata lives in `temp` and is not included.
    /// The returned bytes no longer borrow this connection.
    ///
    /// # Errors
    ///
    /// Returns an error when `SQLite` cannot serialize the database.
    pub fn serialize(&self) -> Result<Bytes, ImageError> {
        let image = self.sqlite().serialize(c"main").context(SerializeSnafu)?;
        Ok(Bytes::from(image.to_vec()))
    }

    /// Creates an in-memory Neutron connection from an `SQLite` database image.
    ///
    /// The image is copied into `SQLite`'s allocator and handed over, so the
    /// returned connection does not borrow from the input and the database it
    /// holds is writable. Neutron's connection-local metadata is rebuilt in
    /// `temp`.
    ///
    /// This is a low-level image operation, not content verification. Callers
    /// establishing trust from a content address must verify `bytes` first.
    ///
    /// # Errors
    ///
    /// Returns an error when the in-memory connection cannot be opened, the
    /// image cannot be installed, or Neutron metadata cannot be initialized.
    pub fn deserialize(bytes: &Bytes) -> Result<Self, ImageError> {
        let sqlite = sqlite::Connection::open_in_memory().context(OpenSnafu)?;
        let image = sqlite::SqlBytes::copy_from_slice(bytes.as_ref()).context(DeserializeSnafu)?;
        sqlite
            .deserialize(c"main", image)
            .context(DeserializeSnafu)?;
        Self::from_sqlite(sqlite).context(InitializeSnafu)
    }

    /// Attaches `bytes` as a new, writable in-memory database.
    ///
    /// The attached database is private to this connection and registered in
    /// Neutron's connection-local database catalog. The returned value is its
    /// connection-local database identifier.
    ///
    /// # Errors
    ///
    /// Returns an error when the schema name is already in use, the image
    /// cannot be installed, or the database cannot be registered.
    pub fn attach_deserialized(
        &mut self,
        schema_name: &str,
        bytes: &Bytes,
    ) -> Result<i64, ImageError> {
        let attached = self
            .query_row(
                DATABASE_IS_ATTACHED_SQL,
                &[Param::Text(schema_name)],
                |row| row.boolean(0),
            )
            .context(AttachSnafu)?
            .unwrap_or(false);
        if attached {
            return Err(ImageError::AlreadyAttached {
                schema_name: schema_name.to_owned(),
            });
        }

        let database_id = self
            .query_row(NEXT_DATABASE_ID_SQL, &[], |row| row.integer(0))
            .context(RegisterSnafu)?
            .unwrap_or(1);
        let schema = quote_identifier(schema_name);
        let name = sql::c_string(schema_name).context(DeserializeSnafu)?;
        let image = sqlite::SqlBytes::copy_from_slice(bytes.as_ref()).context(DeserializeSnafu)?;
        self.execute_batch(&format!("ATTACH DATABASE ':memory:' AS {schema}"))
            .context(AttachSnafu)?;

        if let Err(error) = self.sqlite().deserialize(&name, image) {
            self.detach_after_failed_attach(&schema);
            return Err(ImageError::Deserialize { source: error });
        }

        if let Err(error) = self.execute(
            REGISTER_DATABASE_SQL,
            &[Param::Integer(database_id), Param::Text(schema_name)],
        ) {
            self.detach_after_failed_attach(&schema);
            return Err(ImageError::Register { source: error });
        }

        Ok(database_id)
    }

    /// Detaches a database and removes it from Neutron's connection catalog.
    ///
    /// # Errors
    ///
    /// Returns an error if `schema_name` is not a Neutron-managed attachment,
    /// or if `SQLite` cannot detach it. A failed detach restores the catalog row.
    pub fn detach(&self, schema_name: &str) -> Result<(), ImageError> {
        let database_id = self
            .query_row(FIND_DATABASE_SQL, &[Param::Text(schema_name)], |row| {
                row.integer(0)
            })
            .context(DetachSnafu)?
            .ok_or_else(|| ImageError::NotAttached {
                schema_name: schema_name.to_owned(),
            })?;
        self.execute(UNREGISTER_DATABASE_SQL, &[Param::Text(schema_name)])
            .context(DetachSnafu)?;

        let schema = quote_identifier(schema_name);
        if let Err(source) = self.execute_batch(&format!("DETACH DATABASE {schema}")) {
            let _ = self.execute(
                REGISTER_DATABASE_SQL,
                &[Param::Integer(database_id), Param::Text(schema_name)],
            );
            return Err(ImageError::Detach { source });
        }
        Ok(())
    }

    fn detach_after_failed_attach(&self, quoted_schema: &str) {
        let _ = self.execute_batch(&format!("DETACH DATABASE {quoted_schema}"));
    }
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

/// Failure to serialize or deserialize a Neutron database image.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ImageError {
    /// The database could not be serialized.
    #[snafu(display("could not serialize SQLite database: {source}"))]
    Serialize {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// The destination in-memory database could not be opened.
    #[snafu(display("could not open destination SQLite database: {source}"))]
    Open {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// The database image could not be installed.
    #[snafu(display("could not deserialize SQLite database: {source}"))]
    Deserialize {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// A new in-memory database could not be attached.
    #[snafu(display("could not attach in-memory SQLite database: {source}"))]
    Attach {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// The requested schema name is already attached.
    #[snafu(display("database schema {schema_name:?} is already attached"))]
    AlreadyAttached {
        /// Conflicting `SQLite` schema name.
        schema_name: String,
    },

    /// The requested schema is not managed by Neutron.
    #[snafu(display("database schema {schema_name:?} is not attached through Neutron"))]
    NotAttached {
        /// Missing `SQLite` schema name.
        schema_name: String,
    },

    /// An attached database could not be detached cleanly.
    #[snafu(display("could not detach Neutron database: {source}"))]
    Detach {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// An attached database could not be recorded in Neutron's catalog.
    #[snafu(display("could not register attached Neutron database: {source}"))]
    Register {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// Neutron's connection-local metadata could not be initialized.
    #[snafu(display("could not initialize deserialized Neutron database: {source}"))]
    Initialize {
        /// Underlying Neutron connection error.
        source: ConnectionError,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ATTACHED_DATABASES, CONNECTION_CATALOG};

    #[test]
    fn round_trips_main_database() {
        let connection = Connection::open_in_memory().expect("open source");
        connection
            .execute_batch(
                "CREATE TABLE example (
                    id INTEGER PRIMARY KEY,
                    value TEXT NOT NULL
                ) STRICT;
                INSERT INTO example (value) VALUES ('hello'), ('world');",
            )
            .expect("populate source");

        let bytes = connection.serialize().expect("serialize");
        assert!(bytes.starts_with(b"SQLite format 3\0"));

        let restored = Connection::deserialize(&bytes).expect("deserialize");
        let values = restored
            .query_all("SELECT value FROM example ORDER BY id", &[], |row| {
                row.text(0)
            })
            .expect("read restored data");
        assert_eq!(values, ["hello", "world"]);
    }

    #[test]
    fn serialized_bytes_are_owned() {
        let bytes = {
            let connection = Connection::open_in_memory().expect("open source");
            connection
                .execute_batch("CREATE TABLE example (value INTEGER) STRICT;")
                .expect("populate source");
            connection.serialize().expect("serialize")
        };

        let restored = Connection::deserialize(&bytes).expect("deserialize after source drop");
        let exists = restored
            .query_row(
                "SELECT count(*) FROM main.sqlite_schema
             WHERE type = 'table' AND name = 'example'",
                &[],
                |row| row.integer(0),
            )
            .expect("inspect restored schema");
        assert_eq!(exists, Some(1));
    }

    #[test]
    fn connection_metadata_is_rebuilt_not_serialized() {
        let connection = Connection::open_in_memory().expect("open source");
        let bytes = connection.serialize().expect("serialize");
        let restored = Connection::deserialize(&bytes).expect("deserialize");

        let temp_tables = restored
            .query_all(
                "SELECT name FROM temp.sqlite_schema
             WHERE type = 'table'
             ORDER BY name",
                &[],
                |row| row.text(0),
            )
            .expect("read metadata");
        assert_eq!(temp_tables, [ATTACHED_DATABASES, CONNECTION_CATALOG]);
    }

    #[test]
    fn attaches_deserialized_database() {
        let source = Connection::open_in_memory().expect("open source");
        source
            .execute_batch(
                "CREATE TABLE example (value TEXT NOT NULL) STRICT;
                 INSERT INTO example VALUES ('attached');",
            )
            .expect("populate source");
        let bytes = source.serialize().expect("serialize");

        let mut connection = Connection::open_in_memory().expect("open destination");
        let database_id = connection
            .attach_deserialized("aux", &bytes)
            .expect("attach image");

        let value = connection
            .query_row("SELECT value FROM aux.example", &[], |row| row.text(0))
            .expect("query attached image");
        assert_eq!(value.as_deref(), Some("attached"));
        assert_eq!(
            connection
                .query_row(
                    "SELECT schema_name FROM temp.cov_conn_attached
                 WHERE database_id = ?1",
                    &[Param::Integer(database_id)],
                    |row| row.text(0),
                )
                .expect("query database catalog")
                .as_deref(),
            Some("aux")
        );
    }

    #[test]
    fn attach_quotes_schema_name() {
        let source = Connection::open_in_memory().expect("open source");
        source
            .execute_batch("CREATE TABLE example (value INTEGER) STRICT;")
            .expect("populate source");
        let bytes = source.serialize().expect("serialize");

        let mut connection = Connection::open_in_memory().expect("open destination");
        connection
            .attach_deserialized("quoted\"name", &bytes)
            .expect("attach quoted schema");

        let exists = connection
            .query_row(
                "SELECT count(*) FROM \"quoted\"\"name\".sqlite_schema
             WHERE name = 'example'",
                &[],
                |row| row.integer(0),
            )
            .expect("query quoted schema");
        assert_eq!(exists, Some(1));
    }

    #[test]
    fn attach_rejects_an_existing_neutron_database() {
        let source = Connection::open_in_memory().expect("open source");
        source
            .execute_batch("CREATE TABLE example (value INTEGER) STRICT;")
            .expect("populate source");
        let bytes = source.serialize().expect("serialize");

        let mut connection = Connection::open_in_memory().expect("open destination");
        connection
            .attach_deserialized("aux", &bytes)
            .expect("attach image");

        assert!(matches!(
            connection.attach_deserialized("aux", &bytes),
            Err(ImageError::AlreadyAttached { schema_name }) if schema_name == "aux"
        ));
    }

    #[test]
    fn detach_removes_the_schema_and_allows_its_name_to_be_reused() {
        let source = Connection::open_in_memory().expect("open source");
        let bytes = source.serialize().expect("serialize");
        let mut connection = Connection::open_in_memory().expect("open destination");
        connection
            .attach_deserialized("aux", &bytes)
            .expect("attach image");

        connection.detach("aux").expect("detach image");
        assert_eq!(
            connection
                .query_row(
                    "SELECT count(*) FROM pragma_database_list WHERE name = 'aux'",
                    &[],
                    |row| row.integer(0),
                )
                .expect("query schemas"),
            Some(0)
        );
        connection
            .attach_deserialized("aux", &bytes)
            .expect("reuse schema name");
    }

    #[test]
    fn attach_rejects_a_database_attached_outside_neutron() {
        let source = Connection::open_in_memory().expect("open source");
        let bytes = source.serialize().expect("serialize");
        let mut connection = Connection::open_in_memory().expect("open destination");
        connection
            .execute_batch("ATTACH DATABASE ':memory:' AS external")
            .expect("attach through SQLite");

        assert!(matches!(
            connection.attach_deserialized("external", &bytes),
            Err(ImageError::AlreadyAttached { schema_name }) if schema_name == "external"
        ));
    }
}
