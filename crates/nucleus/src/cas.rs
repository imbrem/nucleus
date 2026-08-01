use std::ops::Range;

use bytes::Bytes;
use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::Blake3Hash;
use covalence_lib_sqlite::{self as sqlite, OptionalExtension};
use covalence_neutron as neutron;

const CREATE_SQL: &str = include_str!("../sql/cas/create.sql");
const STORE_SQL: &str = include_str!("../sql/cas/store.sql");
const FETCH_SQL: &str = include_str!("../sql/cas/fetch.sql");
const FETCH_RANGE_SQL: &str = include_str!("../sql/cas/fetch_range.sql");
const RESERVE_SQL: &str = include_str!("../sql/cas/reserve.sql");
const STATE_SQL: &str = include_str!("../sql/cas/state.sql");
const EVICT_SQL: &str = include_str!("../sql/cas/evict.sql");

/// An in-memory `SQLite` database maintained as a BLAKE3 content-addressed store.
///
/// The wrapper owns its connection and does not expose it, so every mutation
/// preserves the CAS invariant. Persistent and externally supplied databases
/// will require a separate checked-loading API.
#[derive(Debug)]
pub struct Cas {
    connection: neutron::Connection,
}

impl Cas {
    /// Creates an empty, in-memory content-addressed store.
    ///
    /// # Errors
    ///
    /// Returns an error when the in-memory connection or CAS table cannot be
    /// created.
    pub fn create() -> Result<Self, CasError> {
        let connection = neutron::Connection::open_in_memory().context(OpenSnafu)?;
        connection
            .sqlite()
            .execute_batch(CREATE_SQL)
            .context(CreateSnafu)?;
        Ok(Self { connection })
    }

    /// Erases the CAS invariant and returns the permeable raw connection.
    ///
    /// The returned connection may freely mutate or remove the CAS table and
    /// therefore carries none of this wrapper's guarantees.
    #[must_use]
    pub fn into_connection(self) -> neutron::Connection {
        self.connection
    }

    /// Computes the pure, unkeyed BLAKE3 digest of `data`.
    #[must_use]
    pub fn hash(&self, data: impl AsRef<[u8]>) -> Blake3Hash {
        Blake3Hash::from_bytes(data)
    }

    /// Stores `data` and returns its BLAKE3 content address.
    ///
    /// Storing the same bytes repeatedly is idempotent. A conflicting resident
    /// value or known size at the computed address is reported as corruption.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be written or contains conflicting
    /// state at the computed address.
    pub fn store(&self, data: impl AsRef<[u8]>) -> Result<Blake3Hash, CasError> {
        let data = data.as_ref();
        let blake3 = self.hash(data);
        self.store_at(blake3, data)?;
        Ok(blake3)
    }

    fn store_at(&self, blake3: Blake3Hash, data: &[u8]) -> Result<(), CasError> {
        let stored = self
            .connection
            .sqlite()
            .query_row(STORE_SQL, (blake3.as_bytes().as_slice(), data), |row| {
                row.get::<_, bool>(0)
            })
            .optional()
            .context(StoreSnafu)?;

        if stored.is_none() {
            return Err(CasError::Conflict { blake3 });
        }
        Ok(())
    }

    /// Reserves a non-resident address with an optional known size.
    ///
    /// This changes only local index and availability state; it does not claim
    /// that bytes for `blake3` are resident. Returns `true` when the address
    /// already existed. A newly supplied size fills an unknown size but cannot
    /// replace a conflicting one.
    ///
    /// # Errors
    ///
    /// Returns an error when the size is not representable, conflicts with an
    /// existing row, or the CAS cannot be written.
    pub fn reserve(&self, blake3: Blake3Hash, size: Option<u64>) -> Result<bool, CasError> {
        let existing = self.state(blake3)?;
        let size = size
            .map(|size| i64::try_from(size).map_err(|_| CasError::UnsupportedSize { size }))
            .transpose()?;
        let reserved = self
            .connection
            .sqlite()
            .query_row(
                RESERVE_SQL,
                (blake3.as_bytes().as_slice(), size),
                |_| Ok(()),
            )
            .optional()
            .context(StoreSnafu)?;
        if reserved.is_none() {
            return Err(CasError::Conflict { blake3 });
        }
        Ok(existing.is_some())
    }

    /// Fills an existing placeholder with bytes matching its address.
    ///
    /// Returns `true` when resident bytes were already present.
    ///
    /// # Errors
    ///
    /// Returns an error when the address is missing, the bytes hash to another
    /// address, the known size conflicts, or the CAS cannot be accessed.
    pub fn fill(&self, blake3: Blake3Hash, data: impl AsRef<[u8]>) -> Result<bool, CasError> {
        let data = data.as_ref();
        let actual = self.hash(data);
        if actual != blake3 {
            return Err(CasError::AddressMismatch {
                expected: blake3,
                actual,
            });
        }
        let Some((size, resident)) = self.state(blake3)? else {
            return Err(CasError::Missing { blake3 });
        };
        if let Some(size) = size {
            let actual_size = u64::try_from(data.len())
                .map_err(|_| CasError::UnsupportedSize { size: u64::MAX })?;
            if size != actual_size {
                return Err(CasError::SizeMismatch {
                    blake3,
                    expected: size,
                    actual: actual_size,
                });
            }
        }
        self.store_at(blake3, data)?;
        Ok(resident)
    }

    /// Evicts resident bytes while retaining the address and known size.
    ///
    /// Returns `true` when bytes were removed. Missing and already unresolved
    /// addresses return `false`.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be written.
    pub fn evict(&self, blake3: Blake3Hash) -> Result<bool, CasError> {
        self.connection
            .sqlite()
            .execute(EVICT_SQL, [blake3.as_bytes().as_slice()])
            .context(StoreSnafu)
            .map(|changed| changed != 0)
    }

    /// Fetches a resident blob by BLAKE3 content address.
    ///
    /// Missing addresses and unresolved placeholders both return `None`.
    ///
    /// # Errors
    ///
    /// Returns an error when the CAS cannot be queried.
    pub fn fetch(&self, blake3: Blake3Hash) -> Result<Option<Bytes>, CasError> {
        self.connection
            .sqlite()
            .query_row(FETCH_SQL, [blake3.as_bytes().as_slice()], |row| {
                row.get::<_, Option<Vec<u8>>>(0)
            })
            .optional()
            .context(FetchSnafu)
            .map(Option::flatten)
            .map(|blob| blob.map(Bytes::from))
    }

    /// Fetches an exact byte range from a resident blob.
    ///
    /// The bytes are sliced by `SQLite`, avoiding materialization of the whole
    /// blob in Rust. Missing addresses and unresolved placeholders return
    /// `None`. A range beyond a known object size is rejected.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid or unsupported range, an out-of-bounds
    /// range, or a database failure.
    pub fn fetch_range(
        &self,
        blake3: Blake3Hash,
        range: Range<u64>,
    ) -> Result<Option<Bytes>, CasError> {
        if range.start > range.end {
            return Err(CasError::InvalidRange { range });
        }
        let start = i64::try_from(range.start)
            .ok()
            .and_then(|start| start.checked_add(1))
            .ok_or_else(|| CasError::UnsupportedRange {
                range: range.clone(),
            })?;
        let length =
            i64::try_from(range.end - range.start).map_err(|_| CasError::UnsupportedRange {
                range: range.clone(),
            })?;

        let result = self
            .connection
            .sqlite()
            .query_row(
                FETCH_RANGE_SQL,
                (blake3.as_bytes().as_slice(), start, length),
                |row| {
                    Ok((
                        row.get::<_, Option<Vec<u8>>>(0)?,
                        row.get::<_, Option<i64>>(1)?,
                    ))
                },
            )
            .optional()
            .context(FetchSnafu)?;

        let Some((blob, known_size)) = result else {
            return Ok(None);
        };
        if let Some(size) = known_size {
            let size = u64::try_from(size).map_err(|_| CasError::MalformedSize { size })?;
            if range.end > size {
                return Err(CasError::RangeOutOfBounds { range, size });
            }
        }
        Ok(blob.map(Bytes::from))
    }

    fn state(&self, blake3: Blake3Hash) -> Result<Option<(Option<u64>, bool)>, CasError> {
        self.connection
            .sqlite()
            .query_row(STATE_SQL, [blake3.as_bytes().as_slice()], |row| {
                Ok((row.get::<_, Option<i64>>(0)?, row.get::<_, bool>(1)?))
            })
            .optional()
            .context(FetchSnafu)?
            .map(|(size, resident)| {
                let size = size
                    .map(|size| u64::try_from(size).map_err(|_| CasError::MalformedSize { size }))
                    .transpose()?;
                Ok((size, resident))
            })
            .transpose()
    }
}

/// Failure to create or access a flat `SQLite` CAS.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CasError {
    /// The private in-memory Neutron connection could not be opened.
    #[snafu(display("could not open the CAS database: {source}"))]
    Open {
        /// Underlying Neutron connection error.
        source: neutron::ConnectionError,
    },

    /// The flat CAS table could not be created.
    #[snafu(display("could not create the CAS table: {source}"))]
    Create {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// Bytes could not be stored.
    #[snafu(display("could not store bytes in the CAS: {source}"))]
    Store {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// Existing state conflicts with the bytes for an address.
    #[snafu(display("conflicting CAS state at BLAKE3 address {blake3}"))]
    Conflict {
        /// Conflicting pure BLAKE3 address.
        blake3: Blake3Hash,
    },

    /// Supplied bytes do not have the requested address.
    #[snafu(display("bytes hash to {actual}, not requested BLAKE3 address {expected}"))]
    AddressMismatch {
        /// Requested address.
        expected: Blake3Hash,
        /// Address computed from supplied bytes.
        actual: Blake3Hash,
    },

    /// An address has not been reserved.
    #[snafu(display("BLAKE3 address {blake3} is not present in the CAS"))]
    Missing {
        /// Missing address.
        blake3: Blake3Hash,
    },

    /// A known size disagrees with supplied bytes.
    #[snafu(display(
        "BLAKE3 address {blake3} has size {expected}, but supplied bytes have size {actual}"
    ))]
    SizeMismatch {
        /// Address with conflicting size state.
        blake3: Blake3Hash,
        /// Previously known size.
        expected: u64,
        /// Supplied byte length.
        actual: u64,
    },

    /// An object size cannot be represented by `SQLite`.
    #[snafu(display("object size {size} is too large for SQLite"))]
    UnsupportedSize {
        /// Unsupported size.
        size: u64,
    },

    /// Resident bytes could not be fetched.
    #[snafu(display("could not fetch bytes from the CAS: {source}"))]
    Fetch {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },

    /// An object has an invalid known size.
    #[snafu(display("CAS object has invalid known size {size}"))]
    MalformedSize {
        /// Invalid stored size.
        size: i64,
    },

    /// A byte range has its bounds reversed.
    #[snafu(display("invalid byte range {range:?}"))]
    InvalidRange {
        /// Invalid range.
        range: Range<u64>,
    },

    /// A byte range cannot be represented by `SQLite`.
    #[snafu(display("byte range {range:?} is too large for SQLite"))]
    UnsupportedRange {
        /// Unsupported range.
        range: Range<u64>,
    },

    /// A byte range extends past an object's known size.
    #[snafu(display("byte range {range:?} extends past object size {size}"))]
    RangeOutOfBounds {
        /// Out-of-bounds range.
        range: Range<u64>,
        /// Known object size.
        size: u64,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stores_and_fetches_pure_blake3_objects() {
        let cas = Cas::create().expect("create CAS");

        let address = cas.store(b"hello").expect("store bytes");

        assert_eq!(address, Blake3Hash::from_bytes(b"hello"));
        assert_eq!(cas.hash(b"hello"), address);
        assert_eq!(
            cas.fetch(address).expect("fetch bytes"),
            Some(Bytes::from_static(b"hello"))
        );
        assert_eq!(cas.store(b"hello").expect("repeat store"), address);
    }

    #[test]
    fn missing_and_unresolved_objects_are_not_resident() {
        let cas = Cas::create().expect("create CAS");
        let missing = cas.hash(b"missing");
        assert_eq!(cas.fetch(missing).expect("fetch missing"), None);

        let unresolved = cas.hash(b"known later");
        cas.connection
            .sqlite()
            .execute(
                "INSERT INTO main.cov_db_cas (blake3, size) VALUES (?1, ?2)",
                (unresolved.as_bytes().as_slice(), 11_i64),
            )
            .expect("reserve placeholder");

        assert_eq!(cas.fetch(unresolved).expect("fetch unresolved"), None);
        assert_eq!(
            cas.fetch_range(unresolved, 0..11)
                .expect("fetch unresolved range"),
            None
        );
        assert_eq!(
            cas.store(b"known later").expect("fill placeholder"),
            unresolved
        );
        assert_eq!(
            cas.fetch(unresolved).expect("fetch filled"),
            Some(Bytes::from_static(b"known later"))
        );
    }

    #[test]
    fn conflicting_rows_are_rejected_without_overwrite() {
        let cas = Cas::create().expect("create CAS");
        let address = cas.hash(b"right");
        cas.connection
            .sqlite()
            .execute(
                "INSERT INTO main.cov_db_cas (blake3, blob, size) VALUES (?1, ?2, ?3)",
                (address.as_bytes().as_slice(), b"wrong".as_slice(), 5_i64),
            )
            .expect("inject conflict");

        assert!(matches!(
            cas.store(b"right"),
            Err(CasError::Conflict { blake3 }) if blake3 == address
        ));
        assert_eq!(
            cas.fetch(address).expect("fetch original row"),
            Some(Bytes::from_static(b"wrong"))
        );

        let sized = cas.hash(b"four");
        cas.connection
            .sqlite()
            .execute(
                "INSERT INTO main.cov_db_cas (blake3, size) VALUES (?1, ?2)",
                (sized.as_bytes().as_slice(), 99_i64),
            )
            .expect("inject conflicting size");
        assert!(matches!(
            cas.store(b"four"),
            Err(CasError::Conflict { blake3 }) if blake3 == sized
        ));
    }

    #[test]
    fn fetches_exact_ranges_without_loading_the_whole_blob() {
        let cas = Cas::create().expect("create CAS");
        let address = cas.store(b"abcdefgh").expect("store bytes");

        assert_eq!(
            cas.fetch_range(address, 2..6).expect("middle range"),
            Some(Bytes::from_static(b"cdef"))
        );
        assert_eq!(
            cas.fetch_range(address, 8..8).expect("empty range"),
            Some(Bytes::new())
        );
        let reversed = Range { start: 4, end: 3 };
        assert!(matches!(
            cas.fetch_range(address, reversed.clone()),
            Err(CasError::InvalidRange { range }) if range == reversed
        ));
        assert!(matches!(
            cas.fetch_range(address, 0..9),
            Err(CasError::RangeOutOfBounds { range, size: 8 }) if range == (0..9)
        ));
        assert!(matches!(
            cas.fetch_range(address, u64::MAX..u64::MAX),
            Err(CasError::UnsupportedRange { .. })
        ));
    }

    #[test]
    fn schema_enforces_address_and_resident_size_invariants() {
        let cas = Cas::create().expect("create CAS");
        assert!(
            cas.connection
                .sqlite()
                .execute(
                    "INSERT INTO main.cov_db_cas (blake3) VALUES (?1)",
                    [b"short".as_slice()],
                )
                .is_err()
        );

        let address = cas.hash(b"blob");
        assert!(
            cas.connection
                .sqlite()
                .execute(
                    "INSERT INTO main.cov_db_cas (blake3, blob, size) VALUES (?1, ?2, ?3)",
                    (address.as_bytes().as_slice(), b"blob".as_slice(), 3_i64),
                )
                .is_err()
        );
    }

    #[test]
    fn erasure_returns_a_permeable_raw_connection() {
        let raw = Cas::create().expect("create CAS").into_connection();
        raw.sqlite()
            .execute("DROP TABLE main.cov_db_cas", ())
            .expect("raw connection is intentionally unrestricted");
    }

    #[test]
    fn placeholders_fill_evict_and_refill_without_changing_identity() {
        let cas = Cas::create().expect("create CAS");
        let address = cas.hash(b"eventual bytes");

        assert!(!cas.reserve(address, Some(14)).expect("reserve new"));
        assert!(cas.reserve(address, Some(14)).expect("reserve existing"));
        assert_eq!(cas.fetch(address).expect("unresolved fetch"), None);
        assert!(!cas.fill(address, b"eventual bytes").expect("first fill"));
        assert!(cas.fill(address, b"eventual bytes").expect("repeat fill"));
        assert_eq!(
            cas.fetch(address).expect("resident fetch"),
            Some(Bytes::from_static(b"eventual bytes"))
        );

        assert!(cas.evict(address).expect("evict resident"));
        assert!(!cas.evict(address).expect("repeat eviction"));
        assert_eq!(cas.fetch(address).expect("evicted fetch"), None);
        assert!(!cas.fill(address, b"eventual bytes").expect("refill"));
    }

    #[test]
    fn placeholder_conflicts_are_non_mutating() {
        let cas = Cas::create().expect("create CAS");
        let data = b"four";
        let address = cas.hash(data);
        cas.reserve(address, Some(5)).expect("reserve wrong size");

        assert!(matches!(
            cas.reserve(address, Some(4)),
            Err(CasError::Conflict { blake3 }) if blake3 == address
        ));
        assert!(matches!(
            cas.fill(address, data),
            Err(CasError::SizeMismatch {
                blake3,
                expected: 5,
                actual: 4,
            }) if blake3 == address
        ));
        assert_eq!(cas.fetch(address).expect("still unresolved"), None);

        let other = cas.hash(b"other");
        assert!(matches!(
            cas.fill(other, data),
            Err(CasError::AddressMismatch { expected, actual })
                if expected == other && actual == address
        ));
        assert_eq!(cas.fetch(other).expect("not implicitly reserved"), None);
    }

    #[test]
    fn fill_requires_an_existing_placeholder() {
        let cas = Cas::create().expect("create CAS");
        let address = cas.hash(b"missing row");
        assert!(matches!(
            cas.fill(address, b"missing row"),
            Err(CasError::Missing { blake3 }) if blake3 == address
        ));
    }

    #[test]
    fn reservation_preserves_and_refines_size_state() {
        let cas = Cas::create().expect("create CAS");
        let address = cas.hash(b"four");

        assert!(!cas.reserve(address, None).expect("reserve unknown size"));
        assert_eq!(
            cas.state(address).expect("read unknown state"),
            Some((None, false))
        );
        assert!(cas.reserve(address, Some(4)).expect("learn size"));
        assert_eq!(
            cas.state(address).expect("read known state"),
            Some((Some(4), false))
        );
        assert!(cas.reserve(address, None).expect("preserve known size"));
        assert_eq!(
            cas.state(address).expect("read preserved state"),
            Some((Some(4), false))
        );

        cas.fill(address, b"four").expect("fill placeholder");
        assert!(cas.reserve(address, Some(4)).expect("reserve resident"));
        assert!(matches!(
            cas.reserve(address, Some(5)),
            Err(CasError::Conflict { blake3 }) if blake3 == address
        ));
        assert!(cas.evict(address).expect("evict resident"));
        assert_eq!(
            cas.state(address).expect("read evicted state"),
            Some((Some(4), false))
        );
        assert!(matches!(
            cas.fill(address, b"four!"),
            Err(CasError::AddressMismatch { expected, .. }) if expected == address
        ));
        assert_eq!(
            cas.state(address).expect("failed fill is non-mutating"),
            Some((Some(4), false))
        );
    }
}
