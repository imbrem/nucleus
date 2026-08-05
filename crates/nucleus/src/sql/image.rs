use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;
use sqlite::vfs::{ReadOnlyVfs, RegisteredVfs, register_unique};

use super::Sql;
use crate::Connection;

/// Maximum accepted byte length of a complete database image.
///
/// The first immutable store is intentionally simple: a complete image is
/// admitted whole into memory and mounted read-only, so admission is bounded
/// rather than streamed. Streaming or paged access behind the same VFS seam
/// is a later extension.
pub const MAX_IMAGE_BYTES: usize = 64 * 1024 * 1024;

const DATABASE_IS_ATTACHED_SQL: &str =
    "SELECT EXISTS(SELECT 1 FROM pragma_database_list WHERE name = ?1)";

/// The process-local content-addressed image store.
///
/// This is a totally immutable [`ReadOnlyVfs`] whose logical paths are
/// content addresses: entries are only ever inserted, an address always
/// serves the same bytes, and `SQLite` resolves them on read. Richer views,
/// such as a copy-on-write VFS, can later be layered on top of this store
/// rather than replacing it.
#[derive(Clone)]
struct ImageCas {
    vfs: ReadOnlyVfs<Arc<[u8]>>,
    registered: RegisteredVfs,
}

/// Returns handles to the lazily registered image CAS.
///
/// Registration happens at most once per process; the registered name is
/// routing data only and every attachment re-verifies the actual pointer.
fn image_cas() -> Result<ImageCas, sqlite::vfs::RegisterError> {
    static IMAGE_CAS: Mutex<Option<ImageCas>> = Mutex::new(None);
    let mut slot = IMAGE_CAS.lock().unwrap_or_else(PoisonError::into_inner);
    if let Some(existing) = slot.as_ref() {
        return Ok(existing.clone());
    }
    let vfs = ReadOnlyVfs::new(HashMap::new());
    let registered = register_unique(vfs.clone())?;
    let cas = ImageCas { vfs, registered };
    *slot = Some(cas.clone());
    Ok(cas)
}

fn image_path(hash: O256) -> String {
    format!("{hash}.sqlite")
}

impl Connection<Sql> {
    /// Stores a complete image in the process-local store and returns its
    /// content address.
    ///
    /// Existing matching bytes are deduplicated. Different bytes at the same
    /// address are rejected as a collision.
    ///
    /// # Errors
    ///
    /// Returns an error for an oversized image, a store registration failure,
    /// or an address that already contains different bytes.
    pub fn put_image(&mut self, bytes: &[u8]) -> Result<O256, ImageError> {
        let hash = O256::from_bytes(bytes);
        self.put_verified_image(hash, bytes)?;
        Ok(hash)
    }

    /// Stores a complete image after checking its expected content address.
    ///
    /// # Errors
    ///
    /// Returns an error for an oversized image, a store registration failure,
    /// bytes that do not hash to `expected`, or an existing entry at that
    /// address with different bytes.
    pub fn put_verified_image(&mut self, expected: O256, bytes: &[u8]) -> Result<(), ImageError> {
        if bytes.len() > MAX_IMAGE_BYTES {
            return Err(ImageError::TooLarge {
                size: bytes.len(),
                limit: MAX_IMAGE_BYTES,
            });
        }
        let actual = O256::from_bytes(bytes);
        if actual != expected {
            return Err(ImageError::AddressMismatch { expected, actual });
        }

        let cas = image_cas().context(RegisterSnafu)?;
        let path = image_path(expected);
        match cas.vfs.get(&path) {
            Some(existing) if existing.as_ref() != bytes => {
                Err(ImageError::HashCollision { hash: expected })
            }
            Some(_) => Ok(()),
            None => {
                drop(cas.vfs.insert(path, Arc::from(bytes)));
                Ok(())
            }
        }
    }

    /// Returns whether an image is resident in the process-local store.
    #[must_use]
    pub fn has_image(&self, hash: O256) -> bool {
        image_cas().is_ok_and(|cas| cas.vfs.get(&image_path(hash)).is_some())
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

    /// Serializes `main` or one verified immutable attachment as owned bytes.
    ///
    /// Arbitrary attached databases are rejected. For a non-`main` schema,
    /// success depends on checking its actual post-attach VFS pointer against
    /// the process-local immutable image-store VFS.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid schema, an attachment not backed by the
    /// verified immutable VFS, or a database that `SQLite` cannot serialize.
    pub fn serialize_snapshot(
        &mut self,
        schema: &str,
    ) -> Result<covalence_neutron::Bytes, ImageError> {
        if schema.is_empty() || schema.contains('\0') {
            return Err(ImageError::InvalidSchemaName);
        }
        let (neutron, _) = self.parts_mut();
        if schema != "main" {
            let cas = image_cas().context(RegisterSnafu)?;
            neutron
                .verify_database_vfs(schema, &cas.registered)
                .context(VerifySnafu {
                    schema: schema.to_owned(),
                })?;
        }
        neutron.serialize_database(schema).context(SerializeSnafu {
            schema: schema.to_owned(),
        })
    }

    /// Attaches a resident image immutably under `schema`.
    ///
    /// The image is served by content address through the process-local
    /// store's read-only VFS; the bytes are never interpreted by this layer.
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

        let cas = image_cas().context(RegisterSnafu)?;
        let path = image_path(hash);
        if cas.vfs.get(&path).is_none() {
            return Err(ImageError::MissingImage { hash });
        }

        let (neutron, _) = self.parts_mut();
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

        let uri = format!(
            "file:{path}?mode=ro&immutable=1&vfs={}",
            cas.registered.name()
        );
        let quoted_schema = quote_identifier(schema);
        neutron
            .sqlite()
            .execute(&format!("ATTACH DATABASE ?1 AS {quoted_schema}"), [&uri])
            .context(AttachSnafu {
                schema: schema.to_owned(),
            })?;

        if let Err(source) = neutron.verify_database_vfs(schema, &cas.registered) {
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

/// Failure to store or attach a complete database image.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ImageError {
    /// `SQLite` could not serialize the selected snapshot.
    #[snafu(display("could not serialize SQLite schema {schema:?}: {source}"))]
    Serialize {
        /// Selected database schema.
        schema: String,
        /// Mechanical `SQLite` serialization failure.
        source: covalence_neutron::ImageError,
    },

    /// The supplied image exceeds the admission bound.
    #[snafu(display("database image of {size} bytes exceeds the {limit}-byte limit"))]
    TooLarge {
        /// Byte length of the rejected image.
        size: usize,
        /// Maximum accepted byte length.
        limit: usize,
    },

    /// Supplied bytes do not have the expected content address.
    #[snafu(display("database image has address {actual}, expected {expected}"))]
    AddressMismatch {
        /// Expected address supplied by the caller.
        expected: O256,
        /// Address computed from the supplied bytes.
        actual: O256,
    },

    /// Different stored bytes have the same content address.
    #[snafu(display("different database image bytes share content address {hash}"))]
    HashCollision {
        /// Colliding content address.
        hash: O256,
    },

    /// The requested image is not resident in the store.
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

    /// The image store's VFS could not be registered.
    #[snafu(display("could not register the immutable SQLite image store: {source}"))]
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
    use crate::sql::{Outcome, QueryResult, Value};

    fn image() -> Vec<u8> {
        let mut source = Connection::<Sql>::open_in_memory().expect("open source");
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
        let mut connection = Connection::<Sql>::open_in_memory().expect("open destination");

        assert_eq!(connection.put_image(&bytes).unwrap(), hash);
        connection.put_verified_image(hash, &bytes).unwrap();
        assert!(connection.has_image(hash));

        let wrong = O256::from_bytes(b"different");
        assert!(matches!(
            connection.put_verified_image(wrong, &bytes),
            Err(ImageError::AddressMismatch { expected, actual })
                if expected == wrong && actual == hash
        ));
        assert!(!connection.has_image(wrong));
    }

    #[test]
    fn bounds_admitted_images() {
        let mut connection = Connection::<Sql>::open_in_memory().expect("open destination");
        let oversized = vec![0_u8; MAX_IMAGE_BYTES + 1];
        assert!(matches!(
            connection.put_image(&oversized),
            Err(ImageError::TooLarge { size, limit })
                if size == MAX_IMAGE_BYTES + 1 && limit == MAX_IMAGE_BYTES
        ));
        assert!(!connection.has_image(O256::from_bytes(&oversized)));
    }

    #[test]
    fn attaches_and_queries_an_immutable_image() {
        let bytes = image();
        let mut connection = Connection::<Sql>::open_in_memory().expect("open destination");
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
    fn snapshots_only_main_or_verified_immutable_attachments() {
        let bytes = image();
        let mut connection = Connection::<Sql>::open_in_memory().expect("open destination");
        connection
            .execute_batch("CREATE TABLE local(value INTEGER); INSERT INTO local VALUES (42);")
            .expect("populate main");
        let hash = connection.put_image(&bytes).expect("store image");
        connection
            .attach_immutable_image(hash, "library")
            .expect("attach immutable image");
        connection
            .execute_batch("ATTACH DATABASE ':memory:' AS arbitrary")
            .expect("attach arbitrary database");

        for schema in ["main", "library"] {
            let snapshot = connection
                .serialize_snapshot(schema)
                .expect("serialize allowed snapshot");
            assert!(snapshot.starts_with(b"SQLite format 3\0"));
        }
        assert!(matches!(
            connection.serialize_snapshot("arbitrary"),
            Err(ImageError::Verify { schema, .. }) if schema == "arbitrary"
        ));
    }

    #[test]
    fn shares_one_stored_image_across_connections() {
        let bytes = image();
        let mut first = Connection::<Sql>::open_in_memory().expect("open first");
        let mut second = Connection::<Sql>::open_in_memory().expect("open second");
        let hash = first.put_image(&bytes).expect("store image");

        // The store is content-addressed and process-local, so a second
        // connection can attach the same address without re-admitting bytes.
        assert!(second.has_image(hash));
        for connection in [&mut first, &mut second] {
            connection
                .attach_immutable_image(hash, "library")
                .expect("attach image");
            assert!(matches!(
                connection
                    .run("SELECT count(*) FROM library.example", &[])
                    .expect("query image"),
                Outcome::Rows(result) if result.rows == [[Value::Integer(1)]]
            ));
        }
    }

    #[test]
    fn quotes_schema_names_and_rejects_collisions() {
        let bytes = image();
        let mut connection = Connection::<Sql>::open_in_memory().expect("open destination");
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
        let mut connection = Connection::<Sql>::open_in_memory().expect("open destination");
        let missing = O256::from_bytes(b"missing");
        assert!(matches!(
            connection.attach_immutable_image(missing, "missing"),
            Err(ImageError::MissingImage { hash }) if hash == missing
        ));

        // Malformed bytes are admitted (the store never interprets them) but
        // fail to attach, leaving no schema behind.
        let malformed = connection.put_image(b"not sqlite").expect("store bytes");
        assert!(matches!(
            connection.attach_immutable_image(malformed, "malformed"),
            Err(ImageError::Attach { schema, .. }) if schema == "malformed"
        ));
        assert!(matches!(
            connection
                .run(
                    "SELECT count(*) FROM pragma_database_list WHERE name = 'malformed'",
                    &[],
                )
                .expect("inspect attached databases"),
            Outcome::Rows(result) if result.rows == [[Value::Integer(0)]]
        ));
    }
}
