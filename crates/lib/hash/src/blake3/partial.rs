//! Sparse BLAKE3 snapshots and synchronous range sources.

use std::{fmt, ops::Range};

use blake3::hazmat;

use super::{Blake3, Blake3Cv, Blake3Hash};
use crate::{Namespace, Obj, Opaque};

const CHUNK_BYTES: u64 = blake3::CHUNK_LEN as u64;
const MASK_DOMAIN: &[u8] = b"nucleus blake3 leaf mask v0\0";
const PARTIAL_DOMAIN: &[u8] = b"nucleus partial blake3 snapshot v0\0";
const UNKNOWN: Blake3Cv = Blake3Cv::from_array([0; 32]);

/// Namespace of canonical BLAKE3 leaf-presence masks.
pub struct Blake3LeafMask;

impl Namespace for Blake3LeafMask {
    const BYTES: usize = 32;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<32>;
}

/// Hash of a snapshot's canonical leaf-presence mask.
pub type Blake3LeafMaskHash = Obj<Blake3LeafMask>;

/// Namespace of incomplete BLAKE3 snapshot roots.
///
/// These values commit to geometry, presence, and every retained leaf CV. They
/// are deliberately distinct from BLAKE3 digests.
pub struct Blake3PartialRootNamespace;

impl Namespace for Blake3PartialRootNamespace {
    const BYTES: usize = 32;
    type Bytes = [u8; Self::BYTES];
    type Opaque = Opaque<32>;
}

/// Commitment to an incomplete BLAKE3 snapshot.
pub type Blake3PartialRoot = Obj<Blake3PartialRootNamespace>;

/// Root exposed by a sparse snapshot.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Blake3SnapshotRoot {
    /// Some leaves remain unknown.
    Partial(Blake3PartialRoot),
    /// Every leaf is known, so this is the ordinary BLAKE3 digest.
    Complete(Blake3Hash),
}

/// Result of filling one leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Fill {
    /// The leaf was previously unknown.
    Inserted,
    /// The same leaf hash was already retained.
    AlreadyPresent,
}

/// Invalid sparse-snapshot operation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Blake3SnapshotError {
    /// The logical byte length cannot be represented on this platform.
    SnapshotTooLarge,
    /// A leaf index is outside the snapshot.
    LeafOutOfBounds { leaf: usize, leaves: usize },
    /// Bytes do not have the exact length of this BLAKE3 leaf.
    InvalidLeafLength {
        leaf: usize,
        expected: usize,
        actual: usize,
    },
    /// A retained leaf CV differs from the supplied bytes.
    LeafHashMismatch { leaf: usize },
}

impl fmt::Display for Blake3SnapshotError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::SnapshotTooLarge => formatter.write_str("BLAKE3 snapshot is too large"),
            Self::LeafOutOfBounds { leaf, leaves } => {
                write!(formatter, "leaf {leaf} is outside a {leaves}-leaf snapshot")
            }
            Self::InvalidLeafLength {
                leaf,
                expected,
                actual,
            } => write!(
                formatter,
                "leaf {leaf} has {actual} bytes; expected {expected}"
            ),
            Self::LeafHashMismatch { leaf } => {
                write!(formatter, "leaf {leaf} has a different BLAKE3 hash")
            }
        }
    }
}

impl std::error::Error for Blake3SnapshotError {}

/// Sparse leaf-CV snapshot for one BLAKE3 input.
///
/// Unknown leaves occupy canonical all-zero CV slots. Presence is represented
/// separately, so an actual all-zero CV remains representable. Raw bytes are
/// intentionally not retained here. A zero slot means “absent”; it is never
/// the CV of an implicitly hashed zero-filled leaf.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Blake3Snapshot {
    bytes: u64,
    cvs: Vec<Blake3Cv>,
    present: Vec<u64>,
    single_root: Option<Blake3Hash>,
}

impl Blake3Snapshot {
    /// Constructs an empty sparse snapshot for `bytes` logical bytes.
    ///
    /// # Errors
    ///
    /// Returns an error when the geometry cannot be represented on this
    /// platform.
    pub fn new(bytes: u64) -> Result<Self, Blake3SnapshotError> {
        let leaves_u64 = if bytes == 0 {
            0
        } else {
            bytes.div_ceil(CHUNK_BYTES)
        };
        let leaves =
            usize::try_from(leaves_u64).map_err(|_| Blake3SnapshotError::SnapshotTooLarge)?;
        let words = leaves
            .checked_add(63)
            .ok_or(Blake3SnapshotError::SnapshotTooLarge)?
            / 64;
        Ok(Self {
            bytes,
            cvs: vec![UNKNOWN; leaves],
            present: vec![0; words],
            single_root: None,
        })
    }

    /// Returns the logical byte length.
    #[must_use]
    pub const fn bytes(&self) -> u64 {
        self.bytes
    }

    /// Returns the number of BLAKE3 leaves.
    #[must_use]
    pub const fn leaves(&self) -> usize {
        self.cvs.len()
    }

    /// Returns whether all leaf hashes are known.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        (0..self.leaves()).all(|leaf| self.contains(leaf))
    }

    /// Returns whether `leaf` has a retained CV.
    #[must_use]
    pub fn contains(&self, leaf: usize) -> bool {
        leaf < self.leaves() && self.present[leaf / 64] & (1_u64 << (leaf % 64)) != 0
    }

    /// Returns a retained leaf CV.
    #[must_use]
    pub fn leaf(&self, leaf: usize) -> Option<Blake3Cv> {
        self.contains(leaf).then(|| self.cvs[leaf])
    }

    /// Returns all canonical CV slots, including zeros for unknown leaves.
    #[must_use]
    pub fn canonical_cvs(&self) -> &[Blake3Cv] {
        &self.cvs
    }

    /// Hashes and fills one exactly positioned BLAKE3 leaf.
    ///
    /// Repeating the same fill is idempotent. Supplying bytes with a different
    /// CV for an already-known leaf is rejected.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid leaf or length, or a retained hash
    /// mismatch.
    pub fn fill(
        &mut self,
        leaf: usize,
        bytes: impl AsRef<[u8]>,
    ) -> Result<Fill, Blake3SnapshotError> {
        let bytes = bytes.as_ref();
        let expected = self.leaf_len(leaf)?;
        if bytes.len() != expected {
            return Err(Blake3SnapshotError::InvalidLeafLength {
                leaf,
                expected,
                actual: bytes.len(),
            });
        }
        let offset = u64::try_from(leaf)
            .ok()
            .and_then(|leaf| leaf.checked_mul(CHUNK_BYTES))
            .ok_or(Blake3SnapshotError::SnapshotTooLarge)?;
        let cv = Blake3Cv::from_subtree(offset, bytes);
        if self.contains(leaf) {
            if self.cvs[leaf] != cv {
                return Err(Blake3SnapshotError::LeafHashMismatch { leaf });
            }
            return Ok(Fill::AlreadyPresent);
        }
        self.cvs[leaf] = cv;
        self.present[leaf / 64] |= 1_u64 << (leaf % 64);
        if self.leaves() == 1 {
            self.single_root = Some(Obj::<Blake3>::from_bytes(bytes));
        }
        Ok(Fill::Inserted)
    }

    /// Canonical hash of the leaf-presence mask.
    #[must_use]
    pub fn leaf_mask(&self) -> Blake3LeafMaskHash {
        let mut hasher = blake3::Hasher::new();
        hasher.update(MASK_DOMAIN);
        hasher.update(&self.bytes.to_le_bytes());
        hasher.update(&(self.leaves() as u64).to_le_bytes());
        for word in &self.present {
            hasher.update(&word.to_le_bytes());
        }
        Obj::from_array(*hasher.finalize().as_bytes())
    }

    /// Returns a partial commitment or the proper BLAKE3 root when complete.
    #[must_use]
    pub fn root(&self) -> Blake3SnapshotRoot {
        self.complete_root().map_or_else(
            || Blake3SnapshotRoot::Partial(self.partial_root()),
            Blake3SnapshotRoot::Complete,
        )
    }

    /// Returns the ordinary BLAKE3 root only when every leaf is known.
    #[must_use]
    pub fn complete_root(&self) -> Option<Blake3Hash> {
        if !self.is_complete() {
            return None;
        }
        match self.leaves() {
            0 => Some(Obj::<Blake3>::from_bytes([])),
            1 => self.single_root,
            _ => {
                let split = hazmat::left_subtree_len(self.bytes);
                let left = self.subtree_cv(0, split);
                let right = self.subtree_cv(split, self.bytes - split);
                Some(left.root(right))
            }
        }
    }

    fn partial_root(&self) -> Blake3PartialRoot {
        let mut hasher = blake3::Hasher::new();
        hasher.update(PARTIAL_DOMAIN);
        hasher.update(&self.bytes.to_le_bytes());
        hasher.update(self.leaf_mask().as_bytes());
        for cv in &self.cvs {
            hasher.update(cv.as_bytes());
        }
        Obj::from_array(*hasher.finalize().as_bytes())
    }

    fn leaf_len(&self, leaf: usize) -> Result<usize, Blake3SnapshotError> {
        if leaf >= self.leaves() {
            return Err(Blake3SnapshotError::LeafOutOfBounds {
                leaf,
                leaves: self.leaves(),
            });
        }
        let start = (leaf as u64) * CHUNK_BYTES;
        usize::try_from((self.bytes - start).min(CHUNK_BYTES))
            .map_err(|_| Blake3SnapshotError::SnapshotTooLarge)
    }

    fn subtree_cv(&self, offset: u64, length: u64) -> Blake3Cv {
        if length <= CHUNK_BYTES {
            return self.cvs[(offset / CHUNK_BYTES) as usize];
        }
        let left_length = hazmat::left_subtree_len(length);
        self.subtree_cv(offset, left_length)
            .merge(self.subtree_cv(offset + left_length, length - left_length))
    }
}

/// Synchronous byte-range source.
///
/// Implementations may represent HTTP range requests, files, or in-memory
/// objects. Returned bytes remain untrusted until checked against retained CVs
/// or a completed snapshot root.
pub trait Blake3RangeSource {
    /// Storage or transport error.
    type Error;

    /// Fetches exactly `range`.
    ///
    /// # Errors
    ///
    /// Returns a source-specific storage or transport error.
    fn fetch(&mut self, range: Range<u64>) -> Result<Vec<u8>, Self::Error>;
}

/// Failure while filling a sparse snapshot from a range source.
#[derive(Debug, Eq, PartialEq)]
pub enum Blake3RangeError<E> {
    /// The requested range is empty or outside the logical input.
    InvalidRange {
        range: Range<u64>,
        total_length: u64,
    },
    /// Range arithmetic cannot be represented.
    Overflow,
    /// The underlying source failed.
    Source { range: Range<u64>, source: E },
    /// A source returned a different number of bytes than requested.
    InvalidLength {
        range: Range<u64>,
        expected: usize,
        actual: usize,
    },
    /// Snapshot validation failed.
    Snapshot(Blake3SnapshotError),
}

impl<E: fmt::Display> fmt::Display for Blake3RangeError<E> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidRange {
                range,
                total_length,
            } => write!(
                formatter,
                "invalid range {}..{} for {total_length} bytes",
                range.start, range.end
            ),
            Self::Overflow => formatter.write_str("BLAKE3 range arithmetic overflowed"),
            Self::Source { range, source } => {
                write!(
                    formatter,
                    "source failed for {}..{}: {source}",
                    range.start, range.end
                )
            }
            Self::InvalidLength {
                range,
                expected,
                actual,
            } => write!(
                formatter,
                "source returned {actual} bytes for {}..{}; expected {expected}",
                range.start, range.end
            ),
            Self::Snapshot(error) => error.fmt(formatter),
        }
    }
}

impl<E: std::error::Error + 'static> std::error::Error for Blake3RangeError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Source { source, .. } => Some(source),
            Self::Snapshot(error) => Some(error),
            _ => None,
        }
    }
}

/// Range-source wrapper retaining page bytes separately from sparse CV state.
pub struct CachedBlake3Source<S> {
    source: S,
    snapshot: Blake3Snapshot,
    pages: Vec<Option<Vec<u8>>>,
}

impl<S> CachedBlake3Source<S> {
    /// Wraps a source for an input of `bytes` logical bytes.
    ///
    /// # Errors
    ///
    /// Returns an error when the snapshot geometry is too large.
    pub fn new(bytes: u64, source: S) -> Result<Self, Blake3SnapshotError> {
        let snapshot = Blake3Snapshot::new(bytes)?;
        let pages = vec![None; snapshot.leaves()];
        Ok(Self {
            source,
            snapshot,
            pages,
        })
    }

    /// Returns the sparse snapshot.
    #[must_use]
    pub const fn snapshot(&self) -> &Blake3Snapshot {
        &self.snapshot
    }

    /// Returns whether raw bytes for `leaf` are resident.
    #[must_use]
    pub fn is_resident(&self, leaf: usize) -> bool {
        self.pages.get(leaf).is_some_and(Option::is_some)
    }

    /// Evicts raw bytes while retaining the leaf CV.
    ///
    /// Returns whether bytes were resident.
    ///
    /// # Errors
    ///
    /// Returns an error when `leaf` is outside the snapshot.
    pub fn evict(&mut self, leaf: usize) -> Result<bool, Blake3SnapshotError> {
        let leaves = self.pages.len();
        let page = self
            .pages
            .get_mut(leaf)
            .ok_or(Blake3SnapshotError::LeafOutOfBounds { leaf, leaves })?;
        Ok(page.take().is_some())
    }

    /// Decomposes the wrapper into source and sparse snapshot.
    #[must_use]
    pub fn into_parts(self) -> (S, Blake3Snapshot) {
        (self.source, self.snapshot)
    }
}

impl<S: Blake3RangeSource> CachedBlake3Source<S> {
    /// Fetches a range, filling every covering BLAKE3 leaf.
    ///
    /// Earlier unknown leaves remain absent with canonical zero CV slots; the
    /// wrapper does not synthesize or hash zero-filled bytes. Covering leaves
    /// are fetched in full, checked against retained CVs, and cached outside
    /// the snapshot.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid ranges, source failures, short responses,
    /// or a changed leaf hash.
    pub fn fetch(&mut self, range: Range<u64>) -> Result<Vec<u8>, Blake3RangeError<S::Error>> {
        if range.start >= range.end || range.end > self.snapshot.bytes() {
            return Err(Blake3RangeError::InvalidRange {
                range,
                total_length: self.snapshot.bytes(),
            });
        }
        let first =
            usize::try_from(range.start / CHUNK_BYTES).map_err(|_| Blake3RangeError::Overflow)?;
        let last = usize::try_from((range.end - 1) / CHUNK_BYTES)
            .map_err(|_| Blake3RangeError::Overflow)?;
        for leaf in first..=last {
            if self.pages[leaf].is_none() {
                self.fetch_leaf(leaf)?;
            }
        }

        let expected =
            usize::try_from(range.end - range.start).map_err(|_| Blake3RangeError::Overflow)?;
        let mut output = Vec::with_capacity(expected);
        for leaf in first..=last {
            let page = self
                .pages
                .get(leaf)
                .and_then(Option::as_ref)
                .ok_or(Blake3RangeError::Overflow)?;
            let page_start = (leaf as u64) * CHUNK_BYTES;
            let start = usize::try_from(range.start.saturating_sub(page_start))
                .map_err(|_| Blake3RangeError::Overflow)?;
            let end = usize::try_from((range.end - page_start).min(page.len() as u64))
                .map_err(|_| Blake3RangeError::Overflow)?;
            output.extend_from_slice(&page[start..end]);
        }
        debug_assert_eq!(output.len(), expected);
        Ok(output)
    }

    fn fetch_leaf(&mut self, leaf: usize) -> Result<(), Blake3RangeError<S::Error>> {
        let start = (leaf as u64)
            .checked_mul(CHUNK_BYTES)
            .ok_or(Blake3RangeError::Overflow)?;
        let end = start
            .checked_add(CHUNK_BYTES)
            .ok_or(Blake3RangeError::Overflow)?
            .min(self.snapshot.bytes());
        let range = start..end;
        let bytes =
            self.source
                .fetch(range.clone())
                .map_err(|source| Blake3RangeError::Source {
                    range: range.clone(),
                    source,
                })?;
        let expected = usize::try_from(end - start).map_err(|_| Blake3RangeError::Overflow)?;
        if bytes.len() != expected {
            return Err(Blake3RangeError::InvalidLength {
                range,
                expected,
                actual: bytes.len(),
            });
        }
        self.snapshot
            .fill(leaf, &bytes)
            .map_err(Blake3RangeError::Snapshot)?;
        self.pages[leaf] = Some(bytes);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::{cell::RefCell, convert::Infallible, rc::Rc};

    use super::*;

    fn patterned(len: usize) -> Vec<u8> {
        (0..len)
            .map(|index| u8::try_from(index % 251).unwrap())
            .collect()
    }

    #[test]
    fn unknown_leaves_are_canonical_zeros_with_a_stable_mask() {
        let mut snapshot = Blake3Snapshot::new(3 * CHUNK_BYTES + 17).unwrap();

        assert_eq!(snapshot.leaves(), 4);
        assert!(
            snapshot
                .canonical_cvs()
                .iter()
                .all(|cv| *cv == Blake3Cv::from_array([0; 32]))
        );
        assert_eq!(
            snapshot.leaf_mask().to_string(),
            "a0f62cb9f434c8e792ec7b90557e78c979b91656e3742b1771ab7d9725beb673"
        );
        assert!(matches!(snapshot.root(), Blake3SnapshotRoot::Partial(_)));

        let third = patterned(blake3::CHUNK_LEN);
        assert_eq!(snapshot.fill(2, &third), Ok(Fill::Inserted));
        assert!(!snapshot.contains(0));
        assert!(!snapshot.contains(1));
        assert!(snapshot.contains(2));
        assert_eq!(snapshot.canonical_cvs()[0], Blake3Cv::from_array([0; 32]));
        assert_ne!(
            snapshot.leaf_mask(),
            Blake3Snapshot::new(3 * CHUNK_BYTES + 17)
                .unwrap()
                .leaf_mask()
        );
    }

    #[test]
    fn complete_snapshots_produce_the_standard_blake3_root() {
        for len in [
            0,
            1,
            blake3::CHUNK_LEN,
            blake3::CHUNK_LEN + 1,
            3 * blake3::CHUNK_LEN + 17,
            5 * blake3::CHUNK_LEN,
        ] {
            let input = patterned(len);
            let mut snapshot = Blake3Snapshot::new(len as u64).unwrap();
            for (leaf, bytes) in input.chunks(blake3::CHUNK_LEN).enumerate() {
                snapshot.fill(leaf, bytes).unwrap();
            }

            assert_eq!(
                snapshot.root(),
                Blake3SnapshotRoot::Complete(Blake3Hash::from_bytes(&input)),
                "length {len}"
            );
        }
    }

    #[derive(Clone)]
    struct MemorySource(Rc<RefCell<Vec<u8>>>);

    impl Blake3RangeSource for MemorySource {
        type Error = Infallible;

        fn fetch(&mut self, range: Range<u64>) -> Result<Vec<u8>, Self::Error> {
            let start = usize::try_from(range.start).unwrap();
            let end = usize::try_from(range.end).unwrap();
            Ok(self.0.borrow()[start..end].to_vec())
        }
    }

    #[test]
    fn ranges_fill_covering_pages_and_leave_preceding_leaves_unknown() {
        let input = patterned(4 * blake3::CHUNK_LEN + 17);
        let mut source = CachedBlake3Source::new(
            input.len() as u64,
            MemorySource(Rc::new(RefCell::new(input.clone()))),
        )
        .unwrap();
        let range = (2 * CHUNK_BYTES + 11)..(3 * CHUNK_BYTES + 23);
        let start = usize::try_from(range.start).unwrap();
        let end = usize::try_from(range.end).unwrap();

        assert_eq!(source.fetch(range.clone()).unwrap(), input[start..end]);
        assert!(!source.snapshot().contains(0));
        assert!(!source.snapshot().contains(1));
        assert!(source.snapshot().contains(2));
        assert!(source.snapshot().contains(3));
        assert!(!source.snapshot().contains(4));
        assert!(!source.is_resident(1));
        assert!(source.is_resident(2));
        assert!(matches!(
            source.snapshot().root(),
            Blake3SnapshotRoot::Partial(_)
        ));
    }

    #[test]
    fn eviction_retains_hash_and_rejects_changed_refills() {
        let input = patterned(2 * blake3::CHUNK_LEN);
        let shared = Rc::new(RefCell::new(input));
        let mut source =
            CachedBlake3Source::new(2 * CHUNK_BYTES, MemorySource(Rc::clone(&shared))).unwrap();

        source.fetch(0..32).unwrap();
        let retained = source.snapshot().leaf(0);
        assert_eq!(source.evict(0), Ok(true));
        assert_eq!(source.snapshot().leaf(0), retained);
        assert!(!source.is_resident(0));

        shared.borrow_mut()[0] ^= 1;
        assert!(matches!(
            source.fetch(0..32),
            Err(Blake3RangeError::Snapshot(
                Blake3SnapshotError::LeafHashMismatch { leaf: 0 }
            ))
        ));
        assert!(!source.is_resident(0));
        assert_eq!(source.snapshot().leaf(0), retained);
    }

    #[test]
    fn repeated_identical_fill_is_idempotent() {
        let bytes = patterned(blake3::CHUNK_LEN);
        let mut snapshot = Blake3Snapshot::new(CHUNK_BYTES).unwrap();

        assert_eq!(snapshot.fill(0, &bytes), Ok(Fill::Inserted));
        assert_eq!(snapshot.fill(0, &bytes), Ok(Fill::AlreadyPresent));
    }
}
