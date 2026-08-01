use std::{
    error::Error,
    fmt,
    fs::File,
    io::{self, Read},
    ops::Range,
    path::{Path, PathBuf},
};

use covalence_lib_hash::Blake3Hash;

use crate::VerifiedRange;

/// Complete owned bytes checked against an exact size and pure-BLAKE3 root.
#[derive(Debug, Eq, PartialEq)]
pub struct Blake3Bytes {
    root: Blake3Hash,
    size: u64,
    bytes: Box<[u8]>,
}

impl Blake3Bytes {
    /// Authenticated pure-BLAKE3 root.
    #[must_use]
    pub const fn root(&self) -> Blake3Hash {
        self.root
    }

    /// Exact complete byte length.
    #[must_use]
    pub const fn size(&self) -> u64 {
        self.size
    }

    /// Complete authenticated bytes.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Consumes the checked object and returns its controlled bytes.
    #[must_use]
    pub fn into_bytes(self) -> Box<[u8]> {
        self.bytes
    }

    /// Converts the complete object into a capability installable in [`crate::Blake3Mmap`].
    #[must_use]
    pub fn into_verified_range(self) -> VerifiedRange {
        let size = self.size();
        VerifiedRange::new(
            self.root,
            size,
            Range {
                start: 0,
                end: size,
            },
            self.bytes.into_vec(),
        )
    }
}

/// Streams untrusted bytes into owned storage and checks exact size and BLAKE3.
///
/// This is also the transport-neutral synchronous URL adapter: callers may
/// pass any HTTP response body implementing [`Read`]. Network status, redirects,
/// content encoding, and TLS policy remain the transport's untrusted concern.
///
/// At most `expected_size + 1` candidate bytes are retained. One extra byte is
/// sufficient to reject an overlong response without buffering an unbounded
/// malicious body.
///
/// # Errors
///
/// Returns an error for an unrepresentable/allocation-failing expected size,
/// failed input, a short or long object, or a BLAKE3 mismatch.
pub fn load_blake3_reader(
    reader: impl Read,
    expected_size: u64,
    expected_root: Blake3Hash,
) -> Result<Blake3Bytes, LoadError> {
    let expected = usize::try_from(expected_size).map_err(|_| LoadError::SizeTooLarge {
        size: expected_size,
    })?;
    let limit = expected.checked_add(1).ok_or(LoadError::SizeTooLarge {
        size: expected_size,
    })?;
    let mut capture = Capture::new(reader, limit, expected_size)?;
    let actual_root = Blake3Hash::from_reader(&mut capture).map_err(LoadError::Read)?;
    let bytes = capture.into_bytes();

    let actual_size = u64::try_from(bytes.len()).map_err(|_| LoadError::SizeTooLarge {
        size: expected_size,
    })?;
    match bytes.len().cmp(&expected) {
        std::cmp::Ordering::Less => Err(LoadError::Short {
            expected: expected_size,
            actual: actual_size,
        }),
        std::cmp::Ordering::Greater => Err(LoadError::Long {
            expected: expected_size,
        }),
        std::cmp::Ordering::Equal if actual_root != expected_root => Err(LoadError::HashMismatch {
            expected: expected_root,
            actual: actual_root,
        }),
        std::cmp::Ordering::Equal => Ok(Blake3Bytes {
            root: actual_root,
            size: actual_size,
            bytes: bytes.into_boxed_slice(),
        }),
    }
}

/// Opens a path as untrusted storage and checks its exact size and BLAKE3 root.
///
/// File metadata is not trusted as the size check: the opened handle is streamed
/// through [`load_blake3_reader`], which detects concurrent short/long content.
///
/// # Errors
///
/// Returns [`LoadError::Open`] when the path cannot be opened, or any error from
/// [`load_blake3_reader`].
pub fn load_blake3_path(
    path: impl AsRef<Path>,
    expected_size: u64,
    expected_root: Blake3Hash,
) -> Result<Blake3Bytes, LoadError> {
    let path = path.as_ref();
    let file = File::open(path).map_err(|source| LoadError::Open {
        path: path.to_path_buf(),
        source,
    })?;
    load_blake3_reader(file, expected_size, expected_root)
}

/// Failure to load one complete pure-BLAKE3 object.
#[derive(Debug)]
pub enum LoadError {
    /// The expected byte count cannot be retained in this process.
    SizeTooLarge { size: u64 },
    /// Owned storage for the bounded candidate could not be reserved.
    Allocation { size: u64 },
    /// A path could not be opened.
    Open { path: PathBuf, source: io::Error },
    /// Candidate transport or file input failed while streaming.
    Read(io::Error),
    /// Input ended before the exact expected size.
    Short { expected: u64, actual: u64 },
    /// Input supplied at least one byte beyond the exact expected size.
    Long { expected: u64 },
    /// Exact-size bytes did not have the expected pure-BLAKE3 root.
    HashMismatch {
        expected: Blake3Hash,
        actual: Blake3Hash,
    },
}

impl fmt::Display for LoadError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SizeTooLarge { size } => {
                write!(formatter, "object size {size} cannot fit this process")
            }
            Self::Allocation { size } => {
                write!(formatter, "could not reserve storage for {size} bytes")
            }
            Self::Open { path, source } => {
                write!(formatter, "could not open {}: {source}", path.display())
            }
            Self::Read(source) => write!(formatter, "could not read candidate bytes: {source}"),
            Self::Short { expected, actual } => {
                write!(
                    formatter,
                    "expected {expected} bytes but input ended at {actual}"
                )
            }
            Self::Long { expected } => {
                write!(formatter, "input exceeds the expected {expected} bytes")
            }
            Self::HashMismatch { expected, actual } => {
                write!(
                    formatter,
                    "expected BLAKE3 {expected} but computed {actual}"
                )
            }
        }
    }
}

impl Error for LoadError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Open { source, .. } | Self::Read(source) => Some(source),
            Self::SizeTooLarge { .. }
            | Self::Allocation { .. }
            | Self::Short { .. }
            | Self::Long { .. }
            | Self::HashMismatch { .. } => None,
        }
    }
}

struct Capture<R> {
    reader: R,
    bytes: Vec<u8>,
    limit: usize,
}

impl<R> Capture<R> {
    fn new(reader: R, limit: usize, expected_size: u64) -> Result<Self, LoadError> {
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(limit)
            .map_err(|_| LoadError::Allocation {
                size: expected_size,
            })?;
        Ok(Self {
            reader,
            bytes,
            limit,
        })
    }

    fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

impl<R: Read> Read for Capture<R> {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        let remaining = self.limit - self.bytes.len();
        if remaining == 0 || output.is_empty() {
            return Ok(0);
        }
        let selected = output.len().min(remaining);
        let read = self.reader.read(&mut output[..selected])?;
        if read > selected {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "reader reported more bytes than its selected buffer",
            ));
        }
        self.bytes.extend_from_slice(&output[..read]);
        Ok(read)
    }
}
