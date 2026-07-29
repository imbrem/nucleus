use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_sqlite as sqlite;

use crate::{Bytes, Connection};
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
        let data = self
            .sqlite()
            .serialize(sqlite::MAIN_DB)
            .context(SerializeSnafu)?;
        Ok(Bytes::copy_from_slice(&data))
    }

    /// Creates an in-memory Neutron connection from a `SQLite` database image.
    ///
    /// `SQLite` takes its own copy of `bytes`; the returned connection does not
    /// borrow from the input. Neutron adds no connection-local metadata.
    ///
    /// This is a low-level image operation, not content verification. Callers
    /// establishing trust from a content address must verify `bytes` first.
    ///
    /// # Errors
    ///
    /// Returns an error when the in-memory connection cannot be opened, the
    /// image cannot be installed.
    pub fn deserialize(bytes: &Bytes) -> Result<Self, ImageError> {
        let mut sqlite = sqlite::Connection::open_in_memory().context(OpenSnafu)?;
        sqlite
            .deserialize_read_exact(sqlite::MAIN_DB, bytes.as_ref(), bytes.len(), false)
            .context(DeserializeSnafu)?;
        Ok(Self::from_sqlite(sqlite))
    }

    /// Attaches `bytes` as a new, writable in-memory database.
    ///
    /// The attached database is private to this connection. Neutron assigns no
    /// application identity or semantics to it.
    ///
    /// # Errors
    ///
    /// Returns an error when the schema name is already in use, the image
    /// cannot be installed.
    pub fn attach_deserialized(
        &mut self,
        schema_name: &str,
        bytes: &Bytes,
    ) -> Result<(), ImageError> {
        let attached = self
            .sqlite()
            .query_row(DATABASE_IS_ATTACHED_SQL, [schema_name], |row| {
                row.get::<_, bool>(0)
            })
            .context(AttachSnafu)?;
        if attached {
            return Err(ImageError::AlreadyAttached {
                schema_name: schema_name.to_owned(),
            });
        }

        let schema = quote_identifier(schema_name);
        self.sqlite()
            .execute(&format!("ATTACH DATABASE ':memory:' AS {schema}"), ())
            .context(AttachSnafu)?;

        if let Err(error) = self.sqlite_mut().deserialize_read_exact(
            schema_name,
            bytes.as_ref(),
            bytes.len(),
            false,
        ) {
            self.detach_after_failed_attach(&schema);
            return Err(ImageError::Deserialize { source: error });
        }

        Ok(())
    }

    fn detach_after_failed_attach(&self, quoted_schema: &str) {
        let _ = self
            .sqlite()
            .execute(&format!("DETACH DATABASE {quoted_schema}"), ());
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trips_main_database() {
        let connection = Connection::open_in_memory().expect("open source");
        connection
            .sqlite()
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
            .sqlite()
            .prepare("SELECT value FROM example ORDER BY id")
            .expect("prepare query")
            .query_map((), |row| row.get::<_, String>(0))
            .expect("query restored data")
            .collect::<sqlite::Result<Vec<_>>>()
            .expect("read restored data");
        assert_eq!(values, ["hello", "world"]);
    }

    #[test]
    fn serialized_bytes_are_owned() {
        let bytes = {
            let connection = Connection::open_in_memory().expect("open source");
            connection
                .sqlite()
                .execute_batch("CREATE TABLE example (value INTEGER) STRICT;")
                .expect("populate source");
            connection.serialize().expect("serialize")
        };

        let restored = Connection::deserialize(&bytes).expect("deserialize after source drop");
        let exists = restored
            .sqlite()
            .query_row(
                "SELECT count(*) FROM main.sqlite_schema
                 WHERE type = 'table' AND name = 'example'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("inspect restored schema");
        assert_eq!(exists, 1);
    }

    #[test]
    fn deserialization_adds_no_temp_tables() {
        let connection = Connection::open_in_memory().expect("open source");
        let bytes = connection.serialize().expect("serialize");
        let restored = Connection::deserialize(&bytes).expect("deserialize");

        let temp_tables = restored
            .sqlite()
            .prepare(
                "SELECT name FROM temp.sqlite_schema
                 WHERE type = 'table'
                 ORDER BY name",
            )
            .expect("prepare metadata query")
            .query_map((), |row| row.get::<_, String>(0))
            .expect("query metadata")
            .collect::<sqlite::Result<Vec<_>>>()
            .expect("read metadata");
        assert!(temp_tables.is_empty());
    }

    #[test]
    fn attaches_deserialized_database() {
        let source = Connection::open_in_memory().expect("open source");
        source
            .sqlite()
            .execute_batch(
                "CREATE TABLE example (value TEXT NOT NULL) STRICT;
                 INSERT INTO example VALUES ('attached');",
            )
            .expect("populate source");
        let bytes = source.serialize().expect("serialize");

        let mut connection = Connection::open_in_memory().expect("open destination");
        connection
            .attach_deserialized("aux", &bytes)
            .expect("attach image");

        let value = connection
            .sqlite()
            .query_row("SELECT value FROM aux.example", (), |row| {
                row.get::<_, String>(0)
            })
            .expect("query attached image");
        assert_eq!(value, "attached");
    }

    #[test]
    fn attach_quotes_schema_name() {
        let source = Connection::open_in_memory().expect("open source");
        source
            .sqlite()
            .execute_batch("CREATE TABLE example (value INTEGER) STRICT;")
            .expect("populate source");
        let bytes = source.serialize().expect("serialize");

        let mut connection = Connection::open_in_memory().expect("open destination");
        connection
            .attach_deserialized("quoted\"name", &bytes)
            .expect("attach quoted schema");

        let exists = connection
            .sqlite()
            .query_row(
                "SELECT count(*) FROM \"quoted\"\"name\".sqlite_schema
                 WHERE name = 'example'",
                (),
                |row| row.get::<_, i64>(0),
            )
            .expect("query quoted schema");
        assert_eq!(exists, 1);
    }

    #[test]
    fn attach_rejects_an_existing_neutron_database() {
        let source = Connection::open_in_memory().expect("open source");
        source
            .sqlite()
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
    fn attach_rejects_a_database_attached_outside_neutron() {
        let source = Connection::open_in_memory().expect("open source");
        let bytes = source.serialize().expect("serialize");
        let mut connection = Connection::open_in_memory().expect("open destination");
        connection
            .sqlite()
            .execute("ATTACH DATABASE ':memory:' AS external", ())
            .expect("attach through SQLite");

        assert!(matches!(
            connection.attach_deserialized("external", &bytes),
            Err(ImageError::AlreadyAttached { schema_name }) if schema_name == "external"
        ));
    }
}
