use std::{error::Error, fmt, io, ops::Range};

use covalence_lib_hash::Blake3Hash;
use memmap2::MmapMut;

use crate::checked::VerifiedRange;

/// Meaning of bytes in one mapped range.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RangeState {
    /// Physical zero-fill or discarded storage with no semantic byte value.
    Unknown,
    /// Bytes authenticated against this mapped object's original BLAKE3 root.
    Verified,
    /// Locally authoritative bytes no longer certified by the original root.
    Dirty,
}

/// Requirement imposed by a mapped read.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RangeRequirement {
    /// Every byte must be initialized locally or authenticated.
    Known,
    /// Every byte must still be authenticated by the original root.
    Verified,
}

/// One maximal run of byte state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateSpan {
    range: Range<u64>,
    state: RangeState,
}

impl StateSpan {
    /// Covered half-open byte range.
    #[must_use]
    pub const fn range(&self) -> &Range<u64> {
        &self.range
    }

    /// Meaning of every byte in the range.
    #[must_use]
    pub const fn state(&self) -> RangeState {
        self.state
    }
}

/// Zero-initialized anonymous storage for one BLAKE3-addressed file.
///
/// Physical zeroes begin as [`RangeState::Unknown`]. Authenticated ranges can
/// be installed from [`crate::Blake3File`], and all local writes become Dirty.
/// No mutable slice escapes this type, so its state map covers every mutation.
pub struct Blake3Mmap {
    root: Blake3Hash,
    size: u64,
    bytes: Option<MmapMut>,
    states: StateMap,
}

impl Blake3Mmap {
    /// Allocates a volatile anonymous mapping for the complete object.
    ///
    /// # Errors
    ///
    /// Returns an error if `size` cannot fit the address space, anonymous maps
    /// are unsupported, or the operating system refuses the mapping.
    pub fn new(size: u64, root: Blake3Hash) -> io::Result<Self> {
        let length = usize::try_from(size).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "file size does not fit this address space",
            )
        })?;
        Ok(Self {
            root,
            size,
            bytes: (length != 0)
                .then(|| MmapMut::map_anon(length))
                .transpose()?,
            states: StateMap::new(size),
        })
    }

    /// Original pure-BLAKE3 root.
    #[must_use]
    pub const fn root(&self) -> Blake3Hash {
        self.root
    }

    /// Fixed complete byte length.
    #[must_use]
    pub const fn size(&self) -> u64 {
        self.size
    }

    /// Maximal, ordered state runs covering the complete mapping.
    #[must_use]
    pub fn states(&self) -> &[StateSpan] {
        &self.states.spans
    }

    /// Reads bytes known either through authentication or a local write.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid geometry or the first Unknown subrange.
    pub fn read_known(&self, range: Range<u64>) -> Result<&[u8], RangeError> {
        self.read_requiring(range, RangeRequirement::Known)
    }

    /// Reads bytes still authenticated by the original root.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid geometry or the first Unknown/Dirty subrange.
    pub fn read_verified(&self, range: Range<u64>) -> Result<&[u8], RangeError> {
        self.read_requiring(range, RangeRequirement::Verified)
    }

    /// Writes local bytes and marks precisely the touched range Dirty.
    ///
    /// # Errors
    ///
    /// Returns an error if the write overflows or falls outside the mapping.
    pub fn write(&mut self, offset: u64, bytes: impl AsRef<[u8]>) -> Result<(), RangeError> {
        let bytes = bytes.as_ref();
        let length = u64::try_from(bytes.len()).map_err(|_| RangeError::RangeTooLarge)?;
        let end = offset
            .checked_add(length)
            .ok_or_else(|| self.invalid(offset..u64::MAX))?;
        let range = offset..end;
        self.validate(&range)?;
        let indices = Self::indices(&range);
        self.states.set(range, RangeState::Dirty)?;
        self.bytes_mut()[indices].copy_from_slice(bytes);
        Ok(())
    }

    /// Installs bytes freshly authenticated for this exact object.
    ///
    /// Dirty bytes are never silently overwritten.
    ///
    /// # Errors
    ///
    /// Returns an error if the capability belongs to another root/size or
    /// intersects a local Dirty range.
    pub fn install(&mut self, verified: VerifiedRange) -> Result<(), RangeError> {
        let (root, size, range, bytes) = verified.into_parts();
        if root != self.root || size != self.size() {
            return Err(RangeError::ObjectMismatch {
                expected_root: self.root,
                expected_size: self.size(),
                actual_root: root,
                actual_size: size,
            });
        }
        let expected = range.end - range.start;
        let actual = u64::try_from(bytes.len()).map_err(|_| RangeError::RangeTooLarge)?;
        if actual != expected {
            return Err(RangeError::ByteLengthMismatch {
                range,
                expected,
                actual,
            });
        }
        if let Some(span) = self
            .states
            .first_matching(&range, |state| state == RangeState::Dirty)
        {
            return Err(RangeError::DirtyOverlap {
                range: intersection(&range, &span.range),
            });
        }
        let indices = Self::indices(&range);
        self.states.set(range, RangeState::Verified)?;
        self.bytes_mut()[indices].copy_from_slice(&bytes);
        Ok(())
    }

    /// Discards bytes, physically restores zeroes, and marks the range Unknown.
    ///
    /// # Errors
    ///
    /// Returns an error for an invalid or out-of-bounds range.
    pub fn discard(&mut self, range: Range<u64>) -> Result<(), RangeError> {
        self.validate(&range)?;
        let indices = Self::indices(&range);
        self.states.set(range, RangeState::Unknown)?;
        self.bytes_mut()[indices].fill(0);
        Ok(())
    }

    fn read_requiring(
        &self,
        range: Range<u64>,
        requirement: RangeRequirement,
    ) -> Result<&[u8], RangeError> {
        self.validate(&range)?;
        let accepted = |state| match requirement {
            RangeRequirement::Known => state != RangeState::Unknown,
            RangeRequirement::Verified => state == RangeState::Verified,
        };
        if let Some(span) = self.states.first_matching(&range, |state| !accepted(state)) {
            return Err(RangeError::Unavailable {
                range: intersection(&range, &span.range),
                state: span.state,
                requirement,
            });
        }
        Ok(&self.bytes()[Self::indices(&range)])
    }

    fn validate(&self, range: &Range<u64>) -> Result<(), RangeError> {
        if range.start <= range.end && range.end <= self.size() {
            Ok(())
        } else {
            Err(self.invalid(range.clone()))
        }
    }

    fn invalid(&self, range: Range<u64>) -> RangeError {
        RangeError::InvalidRange {
            range,
            size: self.size(),
        }
    }

    fn indices(range: &Range<u64>) -> Range<usize> {
        usize::try_from(range.start).expect("validated mapping offset")
            ..usize::try_from(range.end).expect("validated mapping offset")
    }

    fn bytes(&self) -> &[u8] {
        self.bytes.as_deref().unwrap_or_default()
    }

    fn bytes_mut(&mut self) -> &mut [u8] {
        self.bytes.as_deref_mut().unwrap_or_default()
    }
}

/// Invalid state transition or byte-range access.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RangeError {
    /// Empty ranges are valid; reversed/out-of-bounds ranges are not.
    InvalidRange { range: Range<u64>, size: u64 },
    /// A host-side byte slice length could not be represented.
    RangeTooLarge,
    /// Storage for the byte-state map could not be reserved.
    Allocation,
    /// The first subrange which did not meet a read requirement.
    Unavailable {
        range: Range<u64>,
        state: RangeState,
        requirement: RangeRequirement,
    },
    /// Authenticated bytes belong to another complete object.
    ObjectMismatch {
        expected_root: Blake3Hash,
        expected_size: u64,
        actual_root: Blake3Hash,
        actual_size: u64,
    },
    /// A capability's owned bytes do not cover its claimed range exactly.
    ByteLengthMismatch {
        range: Range<u64>,
        expected: u64,
        actual: u64,
    },
    /// Installing old authenticated bytes would overwrite local changes.
    DirtyOverlap { range: Range<u64> },
}

impl fmt::Display for RangeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl Error for RangeError {}

struct StateMap {
    spans: Vec<StateSpan>,
}

impl StateMap {
    fn new(size: u64) -> Self {
        Self {
            spans: (size != 0)
                .then_some(StateSpan {
                    range: 0..size,
                    state: RangeState::Unknown,
                })
                .into_iter()
                .collect(),
        }
    }

    fn first_matching(
        &self,
        range: &Range<u64>,
        predicate: impl Fn(RangeState) -> bool,
    ) -> Option<&StateSpan> {
        self.spans
            .iter()
            .find(|span| overlaps(&span.range, range) && predicate(span.state))
    }

    fn set(&mut self, range: Range<u64>, state: RangeState) -> Result<(), RangeError> {
        if range.is_empty() {
            return Ok(());
        }
        let capacity = self
            .spans
            .len()
            .checked_add(2)
            .ok_or(RangeError::Allocation)?;
        let mut output = Vec::new();
        output
            .try_reserve_exact(capacity)
            .map_err(|_| RangeError::Allocation)?;
        for span in self.spans.drain(..) {
            if !overlaps(&span.range, &range) {
                push_merged(&mut output, span);
                continue;
            }
            if span.range.start < range.start {
                push_merged(
                    &mut output,
                    StateSpan {
                        range: span.range.start..range.start,
                        state: span.state,
                    },
                );
            }
            let middle = StateSpan {
                range: span.range.start.max(range.start)..span.range.end.min(range.end),
                state,
            };
            push_merged(&mut output, middle);
            if range.end < span.range.end {
                push_merged(
                    &mut output,
                    StateSpan {
                        range: range.end..span.range.end,
                        state: span.state,
                    },
                );
            }
        }
        self.spans = output;
        Ok(())
    }
}

fn push_merged(spans: &mut Vec<StateSpan>, span: StateSpan) {
    if let Some(previous) = spans.last_mut()
        && previous.range.end == span.range.start
        && previous.state == span.state
    {
        previous.range.end = span.range.end;
    } else {
        spans.push(span);
    }
}

fn overlaps(left: &Range<u64>, right: &Range<u64>) -> bool {
    left.start < right.end && right.start < left.end
}

fn intersection(left: &Range<u64>, right: &Range<u64>) -> Range<u64> {
    left.start.max(right.start)..left.end.min(right.end)
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::Blake3Hash;

    use crate::checked::VerifiedRange;

    use super::{Blake3Mmap, RangeError, RangeState, StateSpan};

    #[test]
    fn anonymous_pages_start_zero_but_semantically_unknown() {
        let root = Blake3Hash::from_bytes([7; 32]);
        let mapped = Blake3Mmap::new(32, root).expect("anonymous mapping");

        assert_eq!(mapped.bytes(), &[0; 32]);
        assert_eq!(
            mapped.states(),
            &[StateSpan {
                range: 0..32,
                state: RangeState::Unknown,
            }]
        );
    }

    #[test]
    fn empty_object_does_not_require_an_operating_system_mapping() {
        let root = Blake3Hash::from_bytes([]);
        let mapped = Blake3Mmap::new(0, root).expect("empty mapping");

        assert!(mapped.bytes.is_none());
        assert!(mapped.states().is_empty());
        assert_eq!(mapped.read_verified(0..0).expect("empty read"), b"");
    }

    #[test]
    fn installation_defensively_checks_capability_byte_length() {
        let root = Blake3Hash::from_bytes([3; 8]);
        let mut mapped = Blake3Mmap::new(8, root).expect("anonymous mapping");
        let malformed = VerifiedRange::new(root, 8, 2..6, vec![1, 2]);

        assert!(matches!(
            mapped.install(malformed),
            Err(RangeError::ByteLengthMismatch {
                range,
                expected: 4,
                actual: 2,
            }) if range == (2..6)
        ));
        assert_eq!(mapped.states()[0].state(), RangeState::Unknown);
    }

    #[test]
    fn state_updates_split_and_coalesce_maximal_runs() {
        let root = Blake3Hash::from_bytes([9; 32]);
        let mut mapped = Blake3Mmap::new(12, root).expect("anonymous mapping");

        mapped.write(2, [1, 2, 3]).expect("first write");
        mapped.write(5, [4, 5]).expect("adjacent write");
        assert_eq!(
            mapped.states(),
            &[
                StateSpan {
                    range: 0..2,
                    state: RangeState::Unknown,
                },
                StateSpan {
                    range: 2..7,
                    state: RangeState::Dirty,
                },
                StateSpan {
                    range: 7..12,
                    state: RangeState::Unknown,
                },
            ]
        );

        mapped.discard(3..6).expect("discard middle");
        assert_eq!(&mapped.bytes()[3..6], &[0; 3]);
        assert_eq!(
            mapped.states(),
            &[
                StateSpan {
                    range: 0..2,
                    state: RangeState::Unknown,
                },
                StateSpan {
                    range: 2..3,
                    state: RangeState::Dirty,
                },
                StateSpan {
                    range: 3..6,
                    state: RangeState::Unknown,
                },
                StateSpan {
                    range: 6..7,
                    state: RangeState::Dirty,
                },
                StateSpan {
                    range: 7..12,
                    state: RangeState::Unknown,
                },
            ]
        );
    }
}
