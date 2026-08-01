use std::{
    error::Error,
    fmt,
    fs::File,
    io::{self, Read, Seek, SeekFrom},
    ops::Range,
};

use covalence_lib_hash::{
    Blake3Hash,
    blake3::{Blake3ProofNode, Blake3ProofState, ProofStateError},
};

const CHUNK_BYTES: u64 = 1_024;

/// Owned bytes freshly authenticated as a range of one pure-BLAKE3 object.
///
/// Only this crate constructs this capability. Its object identity prevents a
/// mapped file from combining ranges authenticated under different roots.
pub struct VerifiedRange {
    root: Blake3Hash,
    size: u64,
    range: Range<u64>,
    bytes: Vec<u8>,
}

impl VerifiedRange {
    pub(crate) fn new(root: Blake3Hash, size: u64, range: Range<u64>, bytes: Vec<u8>) -> Self {
        Self {
            root,
            size,
            range,
            bytes,
        }
    }

    /// Pure-BLAKE3 root which authenticated the bytes.
    #[must_use]
    pub const fn root(&self) -> Blake3Hash {
        self.root
    }

    /// Complete object's byte length.
    #[must_use]
    pub const fn size(&self) -> u64 {
        self.size
    }

    /// Exact authenticated byte range.
    #[must_use]
    pub const fn range(&self) -> &Range<u64> {
        &self.range
    }

    /// Authenticated bytes for [`Self::range`].
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Consumes the capability and returns its bytes.
    #[must_use]
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }

    pub(crate) fn into_parts(self) -> (Blake3Hash, u64, Range<u64>, Vec<u8>) {
        (self.root, self.size, self.range, self.bytes)
    }
}

/// A regular file whose returned ranges are freshly checked against BLAKE3.
///
/// Owning a [`File`] does not exclude path-based or duplicated writers. Proof
/// nodes are cached, but every returned range is copied and authenticated
/// again. The wrapper deliberately exposes no unchecked read operation.
pub struct Blake3File {
    file: File,
    root: Blake3Hash,
    proof: Blake3ProofState,
}

impl Blake3File {
    /// Wraps untrusted file storage with fixed BLAKE3 geometry and an expected root.
    ///
    /// This does not read the file or trust its current length.
    ///
    /// # Errors
    ///
    /// Returns an error if the fixed proof geometry cannot be allocated.
    pub fn new(file: File, size: u64, root: Blake3Hash) -> Result<Self, ProofStateError> {
        Ok(Self {
            file,
            root,
            proof: Blake3ProofState::new(size, Some(root))?,
        })
    }

    /// Expected pure-BLAKE3 root.
    #[must_use]
    pub const fn root(&self) -> Blake3Hash {
        self.root
    }

    /// Fixed complete byte length.
    #[must_use]
    pub const fn size(&self) -> u64 {
        self.proof.size()
    }

    /// Cached proof evidence. It does not make bytes in the file stable.
    #[must_use]
    pub const fn proof_state(&self) -> &Blake3ProofState {
        &self.proof
    }

    /// Adds untrusted canonical CV evidence atomically.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid, conflicting, or root-inconsistent evidence.
    pub fn insert_nodes(
        &mut self,
        nodes: impl IntoIterator<Item = Blake3ProofNode>,
    ) -> Result<(), ProofStateError> {
        self.proof.insert_nodes(nodes)
    }

    /// Freshly reads and authenticates an exact byte range.
    ///
    /// The physical read is rounded out to native 1 KiB BLAKE3 chunks. The
    /// returned capability contains only the caller-requested bytes.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid geometry, failed or short I/O, missing
    /// proof evidence, contradictory bytes, or a root mismatch.
    pub fn read_verified(&mut self, range: Range<u64>) -> Result<VerifiedRange, FileProofError> {
        validate_range(&range, self.size())?;
        if range.is_empty() {
            return Ok(VerifiedRange::new(
                self.root,
                self.size(),
                range,
                Vec::new(),
            ));
        }

        let disclosed_start = range.start / CHUNK_BYTES * CHUNK_BYTES;
        let disclosed_end = range
            .end
            .div_ceil(CHUNK_BYTES)
            .saturating_mul(CHUNK_BYTES)
            .min(self.size());
        let disclosed_len = usize::try_from(disclosed_end - disclosed_start)
            .map_err(|_| FileProofError::RangeTooLarge)?;
        let mut disclosed = vec![0; disclosed_len];
        self.file
            .seek(SeekFrom::Start(disclosed_start))
            .and_then(|_| self.file.read_exact(&mut disclosed))
            .map_err(FileProofError::Io)?;

        self.proof
            .insert_aligned(disclosed_start, &disclosed)
            .map_err(FileProofError::Proof)?;
        if self.proof.claimed_root() != Some(self.root) {
            return Err(FileProofError::MissingEvidence);
        }

        let start = usize::try_from(range.start - disclosed_start)
            .map_err(|_| FileProofError::RangeTooLarge)?;
        let len =
            usize::try_from(range.end - range.start).map_err(|_| FileProofError::RangeTooLarge)?;
        Ok(VerifiedRange::new(
            self.root,
            self.size(),
            range,
            disclosed[start..start + len].to_vec(),
        ))
    }

    /// Recovers the untrusted file and accumulated proof state.
    #[must_use]
    pub fn into_parts(self) -> (File, Blake3ProofState) {
        (self.file, self.proof)
    }
}

/// Failure to freshly authenticate a regular-file range.
#[derive(Debug)]
pub enum FileProofError {
    /// Empty/reversed or out-of-bounds byte range.
    InvalidRange { range: Range<u64>, size: u64 },
    /// The physical range cannot be represented in this process.
    RangeTooLarge,
    /// The file could not provide the exact selected bytes.
    Io(io::Error),
    /// Supplied bytes or proof nodes contradicted fixed BLAKE3 evidence.
    Proof(ProofStateError),
    /// More outside CV evidence is needed to connect these bytes to the root.
    MissingEvidence,
}

impl fmt::Display for FileProofError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRange { range, size } => {
                write!(
                    formatter,
                    "invalid byte range {range:?} for file of size {size}"
                )
            }
            Self::RangeTooLarge => formatter.write_str("byte range is too large for this process"),
            Self::Io(error) => write!(formatter, "could not read candidate file bytes: {error}"),
            Self::Proof(error) => write!(formatter, "BLAKE3 evidence rejected: {error}"),
            Self::MissingEvidence => {
                formatter.write_str("more BLAKE3 evidence is required for this range")
            }
        }
    }
}

impl Error for FileProofError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            Self::Proof(error) => Some(error),
            Self::InvalidRange { .. } | Self::RangeTooLarge | Self::MissingEvidence => None,
        }
    }
}

fn validate_range(range: &Range<u64>, size: u64) -> Result<(), FileProofError> {
    if range.start <= range.end && range.end <= size {
        Ok(())
    } else {
        Err(FileProofError::InvalidRange {
            range: range.clone(),
            size,
        })
    }
}
