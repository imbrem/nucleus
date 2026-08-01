//! I/O-free algebra for partial BLAKE3 trees.
//!
//! This module deliberately does not fetch bytes, retain file handles, or run
//! proof strategies. It only describes canonical BLAKE3 geometry and combines
//! untrusted chaining-value evidence. A transport or cache can therefore use
//! these types without becoming part of the verification core.

use std::{collections::BTreeMap, fmt, ops::Range};

use blake3::hazmat;

use super::{Blake3, Blake3Cv, Blake3Hash};
use crate::Obj;

const CHUNK_BYTES: u64 = blake3::CHUNK_LEN as u64;

/// A non-empty, half-open byte span in a BLAKE3 input.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Blake3Span {
    offset: u64,
    length: u64,
}

impl Blake3Span {
    /// Constructs a non-empty span.
    ///
    /// This checks arithmetic only. Whether the span is a canonical node in a
    /// particular BLAKE3 tree depends on that tree's total input length.
    #[must_use]
    pub const fn new(offset: u64, length: u64) -> Option<Self> {
        if length == 0 || offset.checked_add(length).is_none() {
            None
        } else {
            Some(Self { offset, length })
        }
    }

    /// Byte offset from the beginning of the complete input.
    #[must_use]
    pub const fn offset(self) -> u64 {
        self.offset
    }

    /// Number of bytes covered by this span.
    #[must_use]
    pub const fn length(self) -> u64 {
        self.length
    }

    /// Exclusive end offset.
    #[must_use]
    pub const fn end(self) -> u64 {
        self.offset + self.length
    }

    /// Converts the span to a range.
    #[must_use]
    pub const fn range(self) -> Range<u64> {
        self.offset..self.end()
    }
}

/// How much derivable evidence to retain when hashing bytes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Blake3Retention {
    /// Retain only the maximal canonical nodes covered by the segment.
    #[default]
    Frontier,
    /// Retain every canonical node down to BLAKE3 chunks.
    ///
    /// This is larger, but preserves the children needed by later mutation or
    /// fine-grained comparison. It still does not retain the input bytes.
    Dense,
}

/// Result of comparing claims about an aligned range of two partial trees.
///
/// This is an algebraic comparison, not proof verification. `ClaimsEqual`
/// becomes authenticated equality only when both trees have separately been
/// tied to a trusted root.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Blake3RangeComparison {
    /// Every canonical claim needed for the range was known and equal.
    ClaimsEqual,
    /// At least one pair of comparable claims differed.
    ClaimsDifferent(Blake3Span),
    /// The trees did not contain enough compatible evidence to decide.
    Unknown(Blake3Span),
}

/// Invalid partial-tree geometry or incompatible evidence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Blake3PartialError {
    /// A total length, offset, or range calculation overflowed.
    Overflow,
    /// A segment was empty or not aligned to BLAKE3 chunk boundaries.
    InvalidSegment {
        offset: u64,
        length: u64,
        total_length: u64,
    },
    /// A requested comparison range was empty, out of bounds, or unaligned.
    InvalidRange {
        start: u64,
        end: u64,
        total_length: u64,
    },
    /// A supplied span is not a node in the canonical tree.
    NonCanonicalNode(Blake3Span),
    /// Two pieces of evidence assign different CVs to the same derived node.
    ConflictingNode(Blake3Span),
    /// Segments describe inputs with different total lengths.
    TotalLengthMismatch { left: u64, right: u64 },
    /// A single-chunk root was attached to a multi-chunk input.
    InvalidSingleChunkRoot { total_length: u64 },
    /// Two pieces of evidence carry different single-chunk root digests.
    ConflictingSingleChunkRoot,
}

impl fmt::Display for Blake3PartialError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Overflow => formatter.write_str("BLAKE3 tree geometry overflowed"),
            Self::InvalidSegment {
                offset,
                length,
                total_length,
            } => write!(
                formatter,
                "invalid BLAKE3 segment {offset}..{} for {total_length} bytes",
                offset.saturating_add(length)
            ),
            Self::InvalidRange {
                start,
                end,
                total_length,
            } => write!(
                formatter,
                "invalid aligned BLAKE3 range {start}..{end} for {total_length} bytes"
            ),
            Self::NonCanonicalNode(span) => write!(
                formatter,
                "{}..{} is not a canonical BLAKE3 node",
                span.offset(),
                span.end()
            ),
            Self::ConflictingNode(span) => write!(
                formatter,
                "conflicting BLAKE3 evidence for {}..{}",
                span.offset(),
                span.end()
            ),
            Self::TotalLengthMismatch { left, right } => {
                write!(formatter, "BLAKE3 input lengths differ: {left} and {right}")
            }
            Self::InvalidSingleChunkRoot { total_length } => write!(
                formatter,
                "a {total_length}-byte BLAKE3 input does not use a single-chunk root"
            ),
            Self::ConflictingSingleChunkRoot => {
                formatter.write_str("conflicting single-chunk BLAKE3 roots")
            }
        }
    }
}

impl std::error::Error for Blake3PartialError {}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Blake3Node {
    /// Canonical position claimed by this node.
    pub span: Blake3Span,
    /// Non-root chaining value claimed for the span.
    pub cv: Blake3Cv,
}

/// Chaining-value evidence for one contiguous, chunk-aligned file segment.
///
/// Values contain no I/O object. They may be serialized, cached, combined, or
/// treated as untrusted proof material. Construction from bytes records either
/// a minimal frontier or a dense tree, according to [`Blake3Retention`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Blake3Segment {
    total_length: u64,
    range: Range<u64>,
    nodes: Vec<Blake3Node>,
    single_chunk_root: Option<Blake3Hash>,
}

impl Blake3Segment {
    /// Hashes a contiguous, chunk-aligned segment of a complete input.
    ///
    /// The segment must begin on a 1024-byte chunk boundary. Its end must also
    /// be aligned unless it is the end of the complete input.
    ///
    /// # Errors
    ///
    /// Returns an error when the segment geometry overflows, exceeds the total
    /// input, or is not chunk-aligned.
    pub fn from_bytes(
        total_length: u64,
        offset: u64,
        bytes: impl AsRef<[u8]>,
        retention: Blake3Retention,
    ) -> Result<Self, Blake3PartialError> {
        let bytes = bytes.as_ref();
        let length = u64::try_from(bytes.len()).map_err(|_| Blake3PartialError::Overflow)?;
        let end = valid_segment(total_length, offset, length)?;
        let target = offset..end;
        let mut spans = Vec::new();

        if total_length > 0 {
            visit_forest(total_length, |span| {
                if !overlaps(&target, span) {
                    return Visit::Prune;
                }
                if !contains(&target, span) {
                    return Visit::Descend;
                }
                spans.push(span);
                match retention {
                    Blake3Retention::Frontier => Visit::Prune,
                    Blake3Retention::Dense => Visit::Descend,
                }
            });
        }

        let mut nodes = Vec::with_capacity(spans.len());
        for span in spans {
            let start = usize::try_from(span.offset() - offset)
                .map_err(|_| Blake3PartialError::Overflow)?;
            let len = usize::try_from(span.length()).map_err(|_| Blake3PartialError::Overflow)?;
            let data = bytes
                .get(start..start + len)
                .ok_or(Blake3PartialError::Overflow)?;
            nodes.push(Blake3Node {
                span,
                cv: Blake3Cv::from_subtree(span.offset(), data),
            });
        }

        let single_chunk_root = (target == (0..total_length) && total_length <= CHUNK_BYTES)
            .then(|| Obj::<Blake3>::from_bytes(bytes));
        Ok(Self {
            total_length,
            range: target,
            nodes,
            single_chunk_root,
        })
    }

    /// Constructs a segment from untrusted chaining-value evidence.
    ///
    /// Nodes must be canonical for `total_length` and contained by `range`.
    /// They may leave holes and may redundantly contain both parents and
    /// children. `single_chunk_root` is an untrusted assertion used only for an
    /// input of at most one chunk, where a CV cannot be converted to a root.
    ///
    /// # Errors
    ///
    /// Returns an error for invalid segment geometry, non-canonical nodes,
    /// nodes outside the segment, or contradictory retained evidence.
    pub fn from_evidence(
        total_length: u64,
        range: Range<u64>,
        nodes: impl IntoIterator<Item = Blake3Node>,
        single_chunk_root: Option<Blake3Hash>,
    ) -> Result<Self, Blake3PartialError> {
        let length =
            range
                .end
                .checked_sub(range.start)
                .ok_or(Blake3PartialError::InvalidSegment {
                    offset: range.start,
                    length: 0,
                    total_length,
                })?;
        valid_segment(total_length, range.start, length)?;
        if single_chunk_root.is_some() && (total_length > CHUNK_BYTES || range != (0..total_length))
        {
            return Err(Blake3PartialError::InvalidSingleChunkRoot { total_length });
        }
        let nodes = nodes.into_iter().collect::<Vec<_>>();
        for node in &nodes {
            if !canonical_node(total_length, node.span) {
                return Err(Blake3PartialError::NonCanonicalNode(node.span));
            }
            if !contains(&range, node.span) {
                return Err(Blake3PartialError::InvalidSegment {
                    offset: range.start,
                    length,
                    total_length,
                });
            }
        }
        let segment = Self {
            total_length,
            range,
            nodes,
            single_chunk_root,
        };
        // Reuse the tree algebra to reject contradictory dense evidence.
        Blake3PartialTree::from_segment(segment.clone())?;
        Ok(segment)
    }

    /// Total byte length of the complete input.
    #[must_use]
    pub const fn total_length(&self) -> u64 {
        self.total_length
    }

    /// Byte range represented by this segment.
    #[must_use]
    pub fn range(&self) -> Range<u64> {
        self.range.clone()
    }

    /// Number of retained chaining values.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Retained node assertions, in canonical traversal order when the segment
    /// was produced by [`Self::from_bytes`]. Consumers must not rely on order
    /// for segments produced by [`Self::from_evidence`].
    #[must_use]
    pub fn nodes(&self) -> impl ExactSizeIterator<Item = Blake3Node> + '_ {
        self.nodes.iter().copied()
    }

    /// Combines two compatible segments into a partial tree.
    ///
    /// # Errors
    ///
    /// Returns an error when the segments have different total lengths or
    /// contain contradictory evidence.
    pub fn combine(self, other: Self) -> Result<Blake3PartialTree, Blake3PartialError> {
        Blake3PartialTree::from_segment(self)?.insert_segment(other)
    }
}

/// Partial knowledge of the canonical BLAKE3 tree for one complete input.
///
/// Missing nodes are holes, not zero-filled data. The map may retain both a
/// parent and its children, allowing dense evidence to remain useful for
/// mutation. [`Self::frontier`] projects it to a minimal representation. This
/// type validates geometry and internal consistency, not authenticity: every
/// node and root imported as evidence remains an untrusted claim.
///
/// Validation is intentionally straightforward in this experiment. It checks
/// each retained node against canonical geometry and checks redundant parents
/// against derivable children. Dense maps therefore cost roughly
/// `O(nodes * log(nodes))` to validate; a production mutation structure may
/// maintain this invariant incrementally instead.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Blake3PartialTree {
    total_length: u64,
    nodes: BTreeMap<Blake3Span, Blake3Cv>,
    single_chunk_root: Option<Blake3Hash>,
}

impl Blake3PartialTree {
    /// Constructs a tree containing only holes.
    #[must_use]
    pub const fn empty(total_length: u64) -> Self {
        Self {
            total_length,
            nodes: BTreeMap::new(),
            single_chunk_root: None,
        }
    }

    /// Constructs a tree from one segment and validates all retained evidence.
    ///
    /// # Errors
    ///
    /// Returns an error when the segment contains invalid or contradictory
    /// evidence.
    pub fn from_segment(segment: Blake3Segment) -> Result<Self, Blake3PartialError> {
        let mut tree = Self::empty(segment.total_length);
        tree.insert_segment_in_place(segment)?;
        Ok(tree)
    }

    /// Total byte length represented by this tree.
    #[must_use]
    pub const fn total_length(&self) -> u64 {
        self.total_length
    }

    /// Number of retained chaining values, including redundant dense nodes.
    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Adds a segment, returning the combined tree.
    ///
    /// # Errors
    ///
    /// Returns an error when the segment has a different total length or
    /// contains evidence that contradicts the tree.
    pub fn insert_segment(mut self, segment: Blake3Segment) -> Result<Self, Blake3PartialError> {
        self.insert_segment_in_place(segment)?;
        Ok(self)
    }

    /// Adds a segment in place.
    ///
    /// Overlap is allowed when it agrees. Conflicts are rejected even when one
    /// side supplies a parent and the other side supplies only its children.
    ///
    /// # Errors
    ///
    /// Returns an error when the segment has a different total length, invalid
    /// geometry, or evidence that contradicts the tree.
    pub fn insert_segment_in_place(
        &mut self,
        segment: Blake3Segment,
    ) -> Result<(), Blake3PartialError> {
        if self.total_length != segment.total_length {
            return Err(Blake3PartialError::TotalLengthMismatch {
                left: self.total_length,
                right: segment.total_length,
            });
        }
        if segment.single_chunk_root.is_some() && self.total_length > CHUNK_BYTES {
            return Err(Blake3PartialError::InvalidSingleChunkRoot {
                total_length: self.total_length,
            });
        }
        if let (Some(left), Some(right)) = (self.single_chunk_root, segment.single_chunk_root)
            && left != right
        {
            return Err(Blake3PartialError::ConflictingSingleChunkRoot);
        }

        let old_nodes = self.nodes.clone();
        let old_root = self.single_chunk_root;
        for node in segment.nodes {
            if !canonical_node(self.total_length, node.span) {
                self.nodes = old_nodes;
                return Err(Blake3PartialError::NonCanonicalNode(node.span));
            }
            if let Some(existing) = self.nodes.insert(node.span, node.cv)
                && existing != node.cv
            {
                self.nodes = old_nodes;
                return Err(Blake3PartialError::ConflictingNode(node.span));
            }
        }
        self.single_chunk_root = self.single_chunk_root.or(segment.single_chunk_root);
        if let Err(error) = self.validate() {
            self.nodes = old_nodes;
            self.single_chunk_root = old_root;
            return Err(error);
        }
        Ok(())
    }

    /// Returns the claimed ordinary BLAKE3 root when the tree is complete.
    ///
    /// Empty inputs have a root without evidence. Inputs of at most one chunk
    /// require the root output retained while hashing bytes: a chunk CV cannot
    /// be converted to a root digest because the BLAKE3 `ROOT` flag changes the
    /// compression output. Larger inputs are rooted from their final two CVs.
    ///
    /// As with every value in this module, a single-chunk root supplied through
    /// [`Blake3Segment::from_evidence`] is an untrusted assertion. A verifier
    /// must authenticate it or hash the disclosed chunk bytes itself.
    ///
    /// # Errors
    ///
    /// Returns an error if retained parent and child evidence conflicts.
    pub fn claimed_root(&self) -> Result<Option<Blake3Hash>, Blake3PartialError> {
        self.validate()?;
        if self.total_length == 0 {
            return Ok(Some(Obj::<Blake3>::from_bytes([])));
        }
        if self.total_length <= CHUNK_BYTES {
            return Ok(self.single_chunk_root);
        }
        let (left, right) = root_children(self.total_length);
        let Some(left) = self.derived_cv(left) else {
            return Ok(None);
        };
        let Some(right) = self.derived_cv(right) else {
            return Ok(None);
        };
        Ok(Some(left.root(right)))
    }

    /// Returns maximal known nodes and discards redundant descendants.
    ///
    /// # Errors
    ///
    /// Returns an error if retained parent and child evidence conflicts.
    pub fn frontier(&self) -> Result<Vec<(Blake3Span, Blake3Cv)>, Blake3PartialError> {
        self.validate()?;
        let mut output = Vec::new();
        if self.total_length > 0 {
            visit_forest(self.total_length, |span| {
                if let Some(cv) = self.derived_cv(span) {
                    output.push((span, cv));
                    Visit::Prune
                } else if !self.has_evidence_within(span) {
                    Visit::Prune
                } else {
                    Visit::Descend
                }
            });
        }
        Ok(output)
    }

    /// Returns the canonical holes that still prevent root reconstruction.
    ///
    /// # Errors
    ///
    /// Returns an error if retained parent and child evidence conflicts.
    pub fn holes(&self) -> Result<Vec<Blake3Span>, Blake3PartialError> {
        self.validate()?;
        if self.total_length == 0 || self.single_chunk_root.is_some() {
            return Ok(Vec::new());
        }
        if self.total_length <= CHUNK_BYTES {
            return Ok(vec![Blake3Span {
                offset: 0,
                length: self.total_length,
            }]);
        }
        let mut output = Vec::new();
        visit_forest(self.total_length, |span| {
            if self.derived_cv(span).is_some() {
                Visit::Prune
            } else if !self.has_evidence_within(span) || span.length() <= CHUNK_BYTES {
                output.push(span);
                Visit::Prune
            } else {
                Visit::Descend
            }
        });
        Ok(output)
    }

    /// Compares claims about a chunk-aligned range using known evidence.
    ///
    /// `ClaimsEqual` means the available CV claims match under BLAKE3's
    /// collision-resistance assumption; it does not authenticate either tree.
    /// A mismatch wins over an unrelated hole; otherwise the first unknown
    /// canonical span is returned.
    ///
    /// # Errors
    ///
    /// Returns an error for different total lengths, invalid range geometry,
    /// or internally contradictory evidence.
    pub fn compare_aligned(
        &self,
        other: &Self,
        range: Range<u64>,
    ) -> Result<Blake3RangeComparison, Blake3PartialError> {
        if self.total_length != other.total_length {
            return Err(Blake3PartialError::TotalLengthMismatch {
                left: self.total_length,
                right: other.total_length,
            });
        }
        valid_range(self.total_length, &range)?;
        self.validate()?;
        other.validate()?;

        if self.total_length <= CHUNK_BYTES {
            let span = Blake3Span {
                offset: 0,
                length: self.total_length,
            };
            match (self.single_chunk_root, other.single_chunk_root) {
                (Some(left), Some(right)) if left != right => {
                    return Ok(Blake3RangeComparison::ClaimsDifferent(span));
                }
                (Some(_), Some(_)) => return Ok(Blake3RangeComparison::ClaimsEqual),
                _ => {}
            }
        }

        let mut unknown = None;
        let mut different = None;
        visit_forest(self.total_length, |span| {
            if different.is_some() || !overlaps(&range, span) {
                return Visit::Prune;
            }
            if contains(&range, span) {
                match (self.derived_cv(span), other.derived_cv(span)) {
                    (Some(left), Some(right)) if left != right => {
                        different = Some(span);
                        return Visit::Prune;
                    }
                    (Some(_), Some(_)) => return Visit::Prune,
                    _ => {}
                }
            }
            if span.length() <= CHUNK_BYTES
                || !self.has_evidence_within(span)
                || !other.has_evidence_within(span)
            {
                unknown.get_or_insert(span);
                Visit::Prune
            } else {
                Visit::Descend
            }
        });
        if let Some(span) = different {
            return Ok(Blake3RangeComparison::ClaimsDifferent(span));
        }
        Ok(unknown.map_or(
            Blake3RangeComparison::ClaimsEqual,
            Blake3RangeComparison::Unknown,
        ))
    }

    fn validate(&self) -> Result<(), Blake3PartialError> {
        for &span in self.nodes.keys() {
            if !canonical_node(self.total_length, span) {
                return Err(Blake3PartialError::NonCanonicalNode(span));
            }
        }
        if self.single_chunk_root.is_some() && self.total_length > CHUNK_BYTES {
            return Err(Blake3PartialError::InvalidSingleChunkRoot {
                total_length: self.total_length,
            });
        }
        for (&span, &stored) in &self.nodes {
            if let Some(derived) = self.derived_from_children(span)
                && stored != derived
            {
                return Err(Blake3PartialError::ConflictingNode(span));
            }
        }
        Ok(())
    }

    fn derived_cv(&self, span: Blake3Span) -> Option<Blake3Cv> {
        if let Some(cv) = self.nodes.get(&span) {
            return Some(*cv);
        }
        if !self.has_evidence_within(span) {
            return None;
        }
        self.derived_from_children(span)
    }

    fn derived_from_children(&self, span: Blake3Span) -> Option<Blake3Cv> {
        if span.length() <= CHUNK_BYTES {
            return None;
        }
        let (left, right) = children(span);
        match (self.derived_cv(left), self.derived_cv(right)) {
            (Some(left), Some(right)) => Some(left.merge(right)),
            _ => None,
        }
    }

    fn has_evidence_within(&self, span: Blake3Span) -> bool {
        let start = Blake3Span {
            offset: span.offset(),
            length: 0,
        };
        let end = Blake3Span {
            offset: span.end(),
            length: 0,
        };
        self.nodes
            .range(start..end)
            .any(|(candidate, _)| candidate.end() <= span.end())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Visit {
    Descend,
    Prune,
}

fn valid_segment(total_length: u64, offset: u64, length: u64) -> Result<u64, Blake3PartialError> {
    let end = offset
        .checked_add(length)
        .ok_or(Blake3PartialError::Overflow)?;
    let empty_input = total_length == 0 && offset == 0 && length == 0;
    let aligned = offset.is_multiple_of(CHUNK_BYTES)
        && (end == total_length || end.is_multiple_of(CHUNK_BYTES));
    if end > total_length || (!empty_input && (length == 0 || !aligned)) {
        return Err(Blake3PartialError::InvalidSegment {
            offset,
            length,
            total_length,
        });
    }
    Ok(end)
}

fn valid_range(total_length: u64, range: &Range<u64>) -> Result<(), Blake3PartialError> {
    let aligned = range.start.is_multiple_of(CHUNK_BYTES)
        && (range.end == total_length || range.end.is_multiple_of(CHUNK_BYTES));
    if range.start >= range.end || range.end > total_length || !aligned {
        return Err(Blake3PartialError::InvalidRange {
            start: range.start,
            end: range.end,
            total_length,
        });
    }
    Ok(())
}

fn contains(range: &Range<u64>, span: Blake3Span) -> bool {
    range.start <= span.offset() && span.end() <= range.end
}

fn overlaps(range: &Range<u64>, span: Blake3Span) -> bool {
    range.start < span.end() && span.offset() < range.end
}

fn children(span: Blake3Span) -> (Blake3Span, Blake3Span) {
    let left_length = hazmat::left_subtree_len(span.length());
    (
        Blake3Span::new(span.offset(), left_length).expect("left child is non-empty"),
        Blake3Span::new(span.offset() + left_length, span.length() - left_length)
            .expect("right child is non-empty"),
    )
}

fn root_children(total_length: u64) -> (Blake3Span, Blake3Span) {
    children(Blake3Span::new(0, total_length).expect("multi-chunk root is non-empty"))
}

fn visit_forest(total_length: u64, mut visitor: impl FnMut(Blake3Span) -> Visit) {
    if total_length == 0 {
        return;
    }
    if total_length <= CHUNK_BYTES {
        visit_node(
            Blake3Span::new(0, total_length).expect("non-empty input"),
            &mut visitor,
        );
        return;
    }
    let (left, right) = root_children(total_length);
    visit_node(left, &mut visitor);
    visit_node(right, &mut visitor);
}

fn visit_node(span: Blake3Span, visitor: &mut impl FnMut(Blake3Span) -> Visit) {
    if visitor(span) == Visit::Descend && span.length() > CHUNK_BYTES {
        let (left, right) = children(span);
        visit_node(left, visitor);
        visit_node(right, visitor);
    }
}

fn canonical_node(total_length: u64, needle: Blake3Span) -> bool {
    let mut found = false;
    visit_forest(total_length, |span| {
        if span == needle {
            found = true;
            Visit::Prune
        } else if span.offset() <= needle.offset() && needle.end() <= span.end() {
            Visit::Descend
        } else {
            Visit::Prune
        }
    });
    found
}

#[cfg(test)]
mod tests {
    use super::*;

    fn input(length: usize, salt: u8) -> Vec<u8> {
        (0..length)
            .map(|index| u8::try_from(index % 251).unwrap() ^ salt)
            .collect()
    }

    fn complete(bytes: &[u8], retention: Blake3Retention) -> Blake3PartialTree {
        Blake3PartialTree::from_segment(
            Blake3Segment::from_bytes(bytes.len() as u64, 0, bytes, retention).unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn complete_trees_match_reference_blake3_at_boundaries() {
        for length in [
            0,
            1,
            blake3::CHUNK_LEN - 1,
            blake3::CHUNK_LEN,
            blake3::CHUNK_LEN + 1,
            2 * blake3::CHUNK_LEN - 1,
            2 * blake3::CHUNK_LEN,
            2 * blake3::CHUNK_LEN + 1,
            3 * blake3::CHUNK_LEN,
            4 * blake3::CHUNK_LEN + 17,
            8 * blake3::CHUNK_LEN,
        ] {
            let bytes = input(length, 0x5a);
            for retention in [Blake3Retention::Frontier, Blake3Retention::Dense] {
                assert_eq!(
                    complete(&bytes, retention).claimed_root().unwrap(),
                    Some(Obj::<Blake3>::from_bytes(&bytes)),
                    "length {length}, retention {retention:?}"
                );
            }
        }
    }

    #[test]
    fn separately_hashed_segments_form_the_reference_root() {
        let bytes = input(7 * blake3::CHUNK_LEN + 31, 3);
        let total = bytes.len() as u64;
        let cuts = [0, 1024, 3072, 5120, bytes.len()];
        let mut tree = Blake3PartialTree::empty(total);
        for pair in cuts.windows(2).rev() {
            let segment = Blake3Segment::from_bytes(
                total,
                pair[0] as u64,
                &bytes[pair[0]..pair[1]],
                Blake3Retention::Frontier,
            )
            .unwrap();
            tree.insert_segment_in_place(segment).unwrap();
        }
        assert!(tree.holes().unwrap().is_empty());
        assert_eq!(
            tree.claimed_root().unwrap(),
            Some(Obj::<Blake3>::from_bytes(&bytes))
        );
    }

    #[test]
    fn holes_are_explicit_and_collapse_when_siblings_arrive() {
        let bytes = input(4 * blake3::CHUNK_LEN, 9);
        let total = bytes.len() as u64;
        let left = Blake3Segment::from_bytes(
            total,
            0,
            &bytes[..blake3::CHUNK_LEN],
            Blake3Retention::Frontier,
        )
        .unwrap();
        let mut tree = Blake3PartialTree::from_segment(left).unwrap();

        assert_eq!(
            tree.holes().unwrap(),
            vec![
                Blake3Span::new(CHUNK_BYTES, CHUNK_BYTES).unwrap(),
                Blake3Span::new(2 * CHUNK_BYTES, 2 * CHUNK_BYTES).unwrap(),
            ],
            "holes are a maximal missing frontier, not one entry per chunk"
        );
        assert_eq!(tree.claimed_root().unwrap(), None);

        tree.insert_segment_in_place(
            Blake3Segment::from_bytes(
                total,
                blake3::CHUNK_LEN as u64,
                &bytes[blake3::CHUNK_LEN..2 * blake3::CHUNK_LEN],
                Blake3Retention::Frontier,
            )
            .unwrap(),
        )
        .unwrap();
        assert_eq!(tree.frontier().unwrap().len(), 1);
        assert_eq!(
            tree.frontier().unwrap()[0].0,
            Blake3Span::new(0, 2048).unwrap()
        );
        assert_eq!(tree.claimed_root().unwrap(), None);
    }

    #[test]
    fn dense_and_frontier_evidence_are_compatible() {
        let bytes = input(8 * blake3::CHUNK_LEN, 11);
        let frontier = complete(&bytes, Blake3Retention::Frontier);
        let dense = complete(&bytes, Blake3Retention::Dense);

        assert!(dense.node_count() > frontier.node_count());
        assert_eq!(dense.frontier().unwrap(), frontier.frontier().unwrap());
        assert_eq!(
            dense
                .compare_aligned(&frontier, 0..bytes.len() as u64)
                .unwrap(),
            Blake3RangeComparison::ClaimsEqual
        );
    }

    #[test]
    fn aligned_comparison_distinguishes_equal_different_and_unknown() {
        let left_bytes = input(4 * blake3::CHUNK_LEN, 0);
        let mut right_bytes = left_bytes.clone();
        right_bytes[2 * blake3::CHUNK_LEN] ^= 1;
        let total = left_bytes.len() as u64;

        let left = complete(&left_bytes, Blake3Retention::Dense);
        let right = complete(&right_bytes, Blake3Retention::Dense);
        assert_eq!(
            left.compare_aligned(&right, 0..2 * CHUNK_BYTES).unwrap(),
            Blake3RangeComparison::ClaimsEqual
        );
        assert!(matches!(
            left.compare_aligned(&right, 2 * CHUNK_BYTES..3 * CHUNK_BYTES)
                .unwrap(),
            Blake3RangeComparison::ClaimsDifferent(_)
        ));

        let partial = Blake3PartialTree::from_segment(
            Blake3Segment::from_bytes(
                total,
                0,
                &left_bytes[..blake3::CHUNK_LEN],
                Blake3Retention::Frontier,
            )
            .unwrap(),
        )
        .unwrap();
        assert!(matches!(
            left.compare_aligned(&partial, CHUNK_BYTES..2 * CHUNK_BYTES)
                .unwrap(),
            Blake3RangeComparison::Unknown(_)
        ));
    }

    #[test]
    fn conflicting_parent_and_children_are_rejected_transactionally() {
        let bytes = input(4 * blake3::CHUNK_LEN, 0);
        let changed = input(4 * blake3::CHUNK_LEN, 1);
        let total = bytes.len() as u64;
        let parent = Blake3Segment::from_bytes(
            total,
            0,
            &bytes[..2 * blake3::CHUNK_LEN],
            Blake3Retention::Frontier,
        )
        .unwrap();
        let children = Blake3Segment::from_bytes(
            total,
            0,
            &changed[..2 * blake3::CHUNK_LEN],
            Blake3Retention::Dense,
        )
        .unwrap();
        let mut tree = Blake3PartialTree::from_segment(parent).unwrap();
        let before = tree.clone();

        assert!(matches!(
            tree.insert_segment_in_place(children),
            Err(Blake3PartialError::ConflictingNode(_))
        ));
        assert_eq!(tree, before);
    }

    #[test]
    fn single_chunk_root_is_not_fabricated_from_a_cv() {
        let bytes = input(127, 7);
        let from_bytes = complete(&bytes, Blake3Retention::Frontier);
        assert_eq!(
            from_bytes.claimed_root().unwrap(),
            Some(Obj::<Blake3>::from_bytes(&bytes))
        );
        assert_ne!(
            from_bytes.frontier().unwrap()[0].1.opaque(),
            Obj::<Blake3>::from_bytes(&bytes).opaque()
        );

        let without_root = Blake3PartialTree {
            total_length: bytes.len() as u64,
            nodes: BTreeMap::from([(
                Blake3Span::new(0, bytes.len() as u64).unwrap(),
                Blake3Cv::from_subtree(0, &bytes),
            )]),
            single_chunk_root: None,
        };
        assert_eq!(without_root.claimed_root().unwrap(), None);
    }

    #[test]
    fn invalid_alignment_is_rejected_before_hashing() {
        assert!(matches!(
            Blake3Segment::from_bytes(4096, 1, [0; 1024], Blake3Retention::Frontier),
            Err(Blake3PartialError::InvalidSegment { .. })
        ));
        let tree = Blake3PartialTree::empty(4096);
        assert!(matches!(
            tree.compare_aligned(&tree, 1..1024),
            Err(Blake3PartialError::InvalidRange { .. })
        ));
    }

    #[test]
    fn external_evidence_is_validated_without_any_io_abstraction() {
        let bytes = input(2 * blake3::CHUNK_LEN, 4);
        let dense =
            Blake3Segment::from_bytes(bytes.len() as u64, 0, &bytes, Blake3Retention::Dense)
                .unwrap();
        let rebuilt =
            Blake3Segment::from_evidence(dense.total_length(), dense.range(), dense.nodes(), None)
                .unwrap();
        assert_eq!(
            Blake3PartialTree::from_segment(rebuilt)
                .unwrap()
                .claimed_root()
                .unwrap(),
            Some(Obj::<Blake3>::from_bytes(&bytes))
        );

        let outside = Blake3Node {
            span: Blake3Span::new(blake3::CHUNK_LEN as u64, blake3::CHUNK_LEN as u64).unwrap(),
            cv: Blake3Cv::from_subtree(blake3::CHUNK_LEN as u64, &bytes[blake3::CHUNK_LEN..]),
        };
        assert!(matches!(
            Blake3Segment::from_evidence(
                bytes.len() as u64,
                0..blake3::CHUNK_LEN as u64,
                [outside],
                None
            ),
            Err(Blake3PartialError::InvalidSegment { .. })
        ));
    }

    #[test]
    fn every_chunk_partition_and_insertion_order_reconstructs_the_same_root() {
        for chunks in 2..=17 {
            let length = chunks * blake3::CHUNK_LEN - (chunks % 5);
            let bytes = input(length, u8::try_from(chunks).unwrap());
            let total = length as u64;
            let mut segments = bytes
                .chunks(blake3::CHUNK_LEN)
                .enumerate()
                .map(|(chunk, data)| {
                    Blake3Segment::from_bytes(
                        total,
                        (chunk * blake3::CHUNK_LEN) as u64,
                        data,
                        if chunk % 2 == 0 {
                            Blake3Retention::Frontier
                        } else {
                            Blake3Retention::Dense
                        },
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();

            for reverse in [false, true] {
                if reverse {
                    segments.reverse();
                }
                let mut tree = Blake3PartialTree::empty(total);
                for segment in segments.iter().cloned() {
                    tree.insert_segment_in_place(segment).unwrap();
                }
                assert_eq!(
                    tree.claimed_root().unwrap(),
                    Some(Obj::<Blake3>::from_bytes(&bytes)),
                    "{chunks} chunks, reverse {reverse}"
                );
                assert!(tree.holes().unwrap().is_empty());
            }
        }
    }

    #[test]
    fn single_chunk_holes_track_root_evidence_not_only_the_cv() {
        let bytes = input(513, 18);
        let span = Blake3Span::new(0, bytes.len() as u64).unwrap();
        let cv = Blake3Cv::from_subtree(0, &bytes);
        let cv_only = Blake3Segment::from_evidence(
            bytes.len() as u64,
            0..bytes.len() as u64,
            [Blake3Node { span, cv }],
            None,
        )
        .unwrap();
        let cv_only = Blake3PartialTree::from_segment(cv_only).unwrap();
        assert_eq!(cv_only.holes().unwrap(), vec![span]);
        assert_eq!(cv_only.claimed_root().unwrap(), None);

        let complete = complete(&bytes, Blake3Retention::Frontier);
        assert!(complete.holes().unwrap().is_empty());
        assert_eq!(
            cv_only
                .compare_aligned(&complete, 0..bytes.len() as u64)
                .unwrap(),
            Blake3RangeComparison::ClaimsEqual,
            "matching CVs can compare equal even though only one side retained the root output"
        );
    }

    #[test]
    fn disagreement_takes_precedence_over_an_independent_hole() {
        let left_bytes = input(4 * blake3::CHUNK_LEN, 23);
        let mut right_bytes = left_bytes.clone();
        right_bytes[0] ^= 1;
        let total = left_bytes.len() as u64;
        let left = complete(&left_bytes, Blake3Retention::Dense);
        let mut right = Blake3PartialTree::empty(total);
        right
            .insert_segment_in_place(
                Blake3Segment::from_bytes(
                    total,
                    0,
                    &right_bytes[..blake3::CHUNK_LEN],
                    Blake3Retention::Frontier,
                )
                .unwrap(),
            )
            .unwrap();

        assert!(matches!(
            left.compare_aligned(&right, 0..total).unwrap(),
            Blake3RangeComparison::ClaimsDifferent(span) if span.offset() == 0
        ));
    }

    #[test]
    fn combining_segments_is_commutative_for_compatible_evidence() {
        let bytes = input(2 * blake3::CHUNK_LEN + 19, 31);
        let total = bytes.len() as u64;
        let left = Blake3Segment::from_bytes(
            total,
            0,
            &bytes[..2 * blake3::CHUNK_LEN],
            Blake3Retention::Dense,
        )
        .unwrap();
        let right = Blake3Segment::from_bytes(
            total,
            2 * CHUNK_BYTES,
            &bytes[2 * blake3::CHUNK_LEN..],
            Blake3Retention::Frontier,
        )
        .unwrap();

        assert_eq!(
            left.clone().combine(right.clone()).unwrap(),
            right.combine(left).unwrap()
        );
    }

    #[test]
    fn evidence_constructor_rejects_noncanonical_and_internally_conflicting_nodes() {
        let bytes = input(4 * blake3::CHUNK_LEN, 41);
        let total = bytes.len() as u64;
        let noncanonical = Blake3Node {
            span: Blake3Span::new(CHUNK_BYTES, 2 * CHUNK_BYTES).unwrap(),
            cv: Blake3Cv::from_array([1; 32]),
        };
        assert_eq!(
            Blake3Segment::from_evidence(total, 0..total, [noncanonical], None),
            Err(Blake3PartialError::NonCanonicalNode(noncanonical.span))
        );

        let dense = Blake3Segment::from_bytes(total, 0, &bytes, Blake3Retention::Dense).unwrap();
        let mut nodes = dense.nodes().collect::<Vec<_>>();
        let parent = nodes
            .iter_mut()
            .find(|node| node.span == Blake3Span::new(0, 2 * CHUNK_BYTES).unwrap())
            .unwrap();
        parent.cv = Blake3Cv::from_array([0xa5; 32]);
        assert!(matches!(
            Blake3Segment::from_evidence(total, 0..total, nodes, None),
            Err(Blake3PartialError::ConflictingNode(span))
                if span == Blake3Span::new(0, 2 * CHUNK_BYTES).unwrap()
        ));
    }

    #[test]
    fn one_chunk_root_assertions_participate_in_comparison_and_merge() {
        let bytes = input(33, 44);
        let total = bytes.len() as u64;
        let span = Blake3Span::new(0, total).unwrap();
        let cv = Blake3Cv::from_subtree(0, &bytes);
        let actual = Obj::<Blake3>::from_bytes(&bytes);
        let wrong = Obj::<Blake3>::from_array([0x5c; 32]);
        let segment = |root| {
            Blake3Segment::from_evidence(total, 0..total, [Blake3Node { span, cv }], Some(root))
                .unwrap()
        };
        let left = Blake3PartialTree::from_segment(segment(actual)).unwrap();
        let right = Blake3PartialTree::from_segment(segment(wrong)).unwrap();

        assert_eq!(
            left.compare_aligned(&right, 0..total).unwrap(),
            Blake3RangeComparison::ClaimsDifferent(span)
        );
        assert_eq!(
            segment(actual).combine(segment(wrong)),
            Err(Blake3PartialError::ConflictingSingleChunkRoot)
        );
    }
}
