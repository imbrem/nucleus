use std::collections::HashMap;
use std::sync::Arc;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;
use sqlite::vfs::{ReadOnlyVfs, register_unique};

use super::Repl;
use crate::Connection;

const DATABASE_IS_ATTACHED_SQL: &str =
    "SELECT EXISTS(SELECT 1 FROM pragma_database_list WHERE name = ?1)";

impl Connection<Repl> {
    /// Stores a complete resident image and returns its content address.
    ///
    /// Existing matching bytes are deduplicated. Different bytes at the same
    /// address are rejected as a collision.
    ///
    /// # Errors
    ///
    /// Returns an error if this address already contains different bytes.
    pub fn put_image(&mut self, bytes: &[u8]) -> Result<O256, ImageError> {
        let hash = O256::from_bytes(bytes);
        self.put_verified_image(hash, bytes)?;
        Ok(hash)
    }

    /// Stores a complete resident image after checking its expected address.
    ///
    /// # Errors
    ///
    /// Returns an error if the bytes do not hash to `expected` or the resident
    /// entry at that address contains different bytes.
    pub fn put_verified_image(&mut self, expected: O256, bytes: &[u8]) -> Result<(), ImageError> {
        let actual = O256::from_bytes(bytes);
        if actual != expected {
            return Err(ImageError::AddressMismatch { expected, actual });
        }

        let (_, repl) = self.parts_mut();
        match repl.images.get(&expected) {
            Some(existing) if existing.as_ref() != bytes => {
                Err(ImageError::HashCollision { hash: expected })
            }
            Some(_) => Ok(()),
            None => {
                repl.images.insert(expected, Arc::from(bytes));
                Ok(())
            }
        }
    }

    /// Returns whether an image is resident in this REPL kernel.
    #[must_use]
    pub fn has_image(&self, hash: O256) -> bool {
        self.protocol().images.contains_key(&hash)
    }

    /// Returns the number of complete resident images.
    #[must_use]
    pub fn resident_image_count(&self) -> usize {
        self.protocol().images.len()
    }

    /// Serializes the writable in-memory `main` database.
    ///
    /// # Errors
    ///
    /// Returns an error if `SQLite` cannot serialize the database.
    pub fn serialize_main(
        &mut self,
    ) -> Result<covalence_neutron::Bytes, covalence_neutron::ImageError> {
        let (neutron, _) = self.parts_mut();
        neutron.serialize()
    }

    /// Attaches a complete resident image through its own immutable VFS.
    ///
    /// The requested VFS name is not trusted. After `ATTACH`, this method asks
    /// `SQLite` for the schema's actual `sqlite3_vfs*` and compares it with the
    /// registered pointer before returning success.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid or occupied schema name, a missing
    /// image, VFS registration or attachment failure, or a post-attach VFS
    /// pointer mismatch.
    pub fn attach_immutable_image(&mut self, hash: O256, schema: &str) -> Result<(), ImageError> {
        if schema.is_empty() || schema.contains('\0') {
            return Err(ImageError::InvalidSchemaName);
        }

        let (neutron, repl) = self.parts_mut();
        let bytes = repl
            .images
            .get(&hash)
            .cloned()
            .ok_or(ImageError::MissingImage { hash })?;
        let attached = neutron
            .sqlite()
            .query_row(DATABASE_IS_ATTACHED_SQL, [schema], |row| {
                row.get::<_, bool>(0)
            })
            .context(InspectSnafu)?;
        if attached {
            return Err(ImageError::AlreadyAttached {
                schema: schema.to_owned(),
            });
        }

        let logical_path = format!("{hash}.sqlite");
        let registered = register_unique(ReadOnlyVfs::new(HashMap::from([(
            logical_path.clone(),
            bytes,
        )])))
        .context(RegisterSnafu)?;
        let uri = format!(
            "file:{logical_path}?mode=ro&immutable=1&vfs={}",
            registered.name()
        );
        let quoted_schema = quote_identifier(schema);
        neutron
            .sqlite()
            .execute(&format!("ATTACH DATABASE ?1 AS {quoted_schema}"), [&uri])
            .context(AttachSnafu {
                schema: schema.to_owned(),
            })?;

        if let Err(source) = neutron.verify_database_vfs(schema, &registered) {
            let _ = neutron
                .sqlite()
                .execute(&format!("DETACH DATABASE {quoted_schema}"), ());
            return Err(ImageError::Verify {
                schema: schema.to_owned(),
                source,
            });
        }
        Ok(())
    }
}

fn quote_identifier(identifier: &str) -> String {
    format!("\"{}\"", identifier.replace('"', "\"\""))
}

/// Failure to store or attach a complete resident database image.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ImageError {
    /// Supplied bytes do not have the expected content address.
    #[snafu(display("database image has address {actual}, expected {expected}"))]
    AddressMismatch {
        /// Expected address supplied by the caller.
        expected: O256,
        /// Address computed from the supplied bytes.
        actual: O256,
    },

    /// Different resident bytes have the same content address.
    #[snafu(display("different database image bytes share content address {hash}"))]
    HashCollision {
        /// Colliding content address.
        hash: O256,
    },

    /// The requested image is not resident.
    #[snafu(display("database image {hash} is not resident"))]
    MissingImage {
        /// Missing content address.
        hash: O256,
    },

    /// The requested schema name is empty or contains a NUL byte.
    #[snafu(display("invalid SQLite schema name"))]
    InvalidSchemaName,

    /// The requested schema name is already attached.
    #[snafu(display("SQLite schema {schema:?} is already attached"))]
    AlreadyAttached {
        /// Conflicting schema name.
        schema: String,
    },

    /// The attached-database list could not be inspected.
    #[snafu(display("could not inspect attached SQLite databases: {source}"))]
    Inspect {
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The immutable VFS could not be registered.
    #[snafu(display("could not register immutable SQLite VFS: {source}"))]
    Register {
        /// Lower-level registration failure.
        source: sqlite::vfs::RegisterError,
    },

    /// The resident image could not be attached.
    #[snafu(display("could not attach SQLite schema {schema:?}: {source}"))]
    Attach {
        /// Requested schema name.
        schema: String,
        /// Underlying `SQLite` failure.
        source: sqlite::Error,
    },

    /// The attached schema did not use the registered VFS pointer.
    #[snafu(display("could not verify the VFS used by SQLite schema {schema:?}: {source}"))]
    Verify {
        /// Attached schema name.
        schema: String,
        /// Pointer inspection or mismatch failure.
        source: covalence_neutron::DatabaseVfsError,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repl::{Outcome, QueryResult, Value};

    fn image() -> Vec<u8> {
        let mut source = Connection::<Repl>::open_in_memory().expect("open source");
        source
            .execute_batch(
                "CREATE TABLE example(value TEXT NOT NULL);
                 INSERT INTO example VALUES ('immutable');",
            )
            .expect("populate source");
        source.serialize_main().expect("serialize source").to_vec()
    }

    #[test]
    fn stores_deduplicated_verified_images() {
        let bytes = image();
        let hash = O256::from_bytes(&bytes);
        let mut connection = Connection::<Repl>::open_in_memory().expect("open destination");

        assert_eq!(connection.put_image(&bytes).unwrap(), hash);
        connection.put_verified_image(hash, &bytes).unwrap();
        assert!(connection.has_image(hash));
        assert_eq!(connection.resident_image_count(), 1);

        let wrong = O256::from_bytes(b"different");
        assert!(matches!(
            connection.put_verified_image(wrong, &bytes),
            Err(ImageError::AddressMismatch { expected, actual })
                if expected == wrong && actual == hash
        ));
        assert_eq!(connection.resident_image_count(), 1);
    }

    #[test]
    fn attaches_and_queries_an_immutable_image() {
        let bytes = image();
        let mut connection = Connection::<Repl>::open_in_memory().expect("open destination");
        let hash = connection.put_image(&bytes).expect("store image");
        connection
            .attach_immutable_image(hash, "library")
            .expect("attach image");

        assert_eq!(
            connection
                .run("SELECT value FROM library.example", &[])
                .expect("query image"),
            Outcome::Rows(QueryResult {
                columns: vec!["value".to_owned()],
                rows: vec![vec![Value::Text("immutable".to_owned())]],
            })
        );
        assert!(
            connection
                .run("INSERT INTO library.example VALUES ('changed')", &[])
                .is_err()
        );
    }

    #[test]
    fn quotes_schema_names_and_rejects_collisions() {
        let bytes = image();
        let mut connection = Connection::<Repl>::open_in_memory().expect("open destination");
        let hash = connection.put_image(&bytes).expect("store image");
        connection
            .attach_immutable_image(hash, "quoted\"name")
            .expect("attach quoted schema");
        assert!(matches!(
            connection.attach_immutable_image(hash, "quoted\"name"),
            Err(ImageError::AlreadyAttached { schema }) if schema == "quoted\"name"
        ));
        assert!(connection.attach_immutable_image(hash, "").is_err());
    }

    #[test]
    fn rejects_missing_and_malformed_images() {
        let mut connection = Connection::<Repl>::open_in_memory().expect("open destination");
        let missing = O256::from_bytes(b"missing");
        assert!(matches!(
            connection.attach_immutable_image(missing, "missing"),
            Err(ImageError::MissingImage { hash }) if hash == missing
        ));

        let malformed = connection.put_image(b"not sqlite").expect("store bytes");
        assert!(
            connection
                .attach_immutable_image(malformed, "malformed")
                .is_err()
        );
    }
}
