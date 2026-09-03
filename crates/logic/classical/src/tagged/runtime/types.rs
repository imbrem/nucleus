/// One aligned power-of-two allocation block.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Block {
    pub(super) base: usize,
    pub(super) size_class: usize,
}

impl Block {
    /// Returns the first word address of the block.
    #[cfg(test)]
    #[must_use]
    pub const fn base(self) -> usize {
        self.base
    }

    /// Returns the allocator size class.
    #[cfg(test)]
    #[must_use]
    pub const fn size_class(self) -> usize {
        self.size_class
    }

    /// Returns the complete block capacity in words.
    #[must_use]
    pub fn capacity(self) -> Option<usize> {
        let shift = u32::try_from(self.size_class).ok()?;
        4_usize.checked_shl(shift)
    }

    pub(super) fn stop(self) -> Option<usize> {
        self.base.checked_add(self.capacity()?)
    }

    pub(super) fn fits(self, size: usize) -> bool {
        self.base >= RESERVED_WORDS
            && self.base.is_multiple_of(4)
            && self.stop().is_some_and(|stop| stop <= size)
    }
}

/// One step of the flat traversal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Token {
    pub(super) tag: u8,
    pub(super) negative: bool,
    /// Child arity for a node, atom identifier for a literal.
    pub(super) value: u32,
}

/// Address ownership recovered so far by one validation pass.
///
/// One ownership bit per word after the reserved prefix.
#[derive(Debug)]
pub(super) struct Coverage {
    pub(super) bits: Vec<u64>,
    pub(super) claimed: usize,
    pub(super) words: usize,
}

impl Coverage {
    pub(super) fn new(size: usize) -> Self {
        let words = size.saturating_sub(RESERVED_WORDS);
        Self {
            bits: vec![0; words.div_ceil(64)],
            claimed: 0,
            words,
        }
    }

    /// Claims every address of `block`, rejecting any address claimed twice.
    ///
    /// Blocks are word-aligned runs, so this touches `capacity / 64` bitmap
    /// words and at most two partial ones.
    pub(super) fn claim(&mut self, block: Block) -> bool {
        let Some(stop) = block.stop() else {
            return false;
        };
        if block.base < RESERVED_WORDS || stop > self.words + RESERVED_WORDS || stop <= block.base {
            return false;
        }
        let start = block.base - RESERVED_WORDS;
        let end = stop - RESERVED_WORDS;
        let (first, last) = (start / 64, (end - 1) / 64);
        let head = u64::MAX << (start % 64);
        let tail = u64::MAX >> (63 - ((end - 1) % 64));
        if first == last {
            let mask = head & tail;
            if self.bits[first] & mask != 0 {
                return false;
            }
            self.bits[first] |= mask;
        } else {
            if self.bits[first] & head != 0 || self.bits[last] & tail != 0 {
                return false;
            }
            if self.bits[first + 1..last].iter().any(|slot| *slot != 0) {
                return false;
            }
            self.bits[first] |= head;
            self.bits[last] |= tail;
            self.bits[first + 1..last].fill(u64::MAX);
        }
        self.claimed += end - start;
        true
    }

    /// Whether every address after the reserved prefix was claimed.
    ///
    /// Claims are disjoint by construction, so this total decides coverage.
    pub(super) const fn complete(&self) -> bool {
        self.claimed == self.words
    }

    pub(super) fn contains(&self, address: usize) -> bool {
        if address < RESERVED_WORDS || address >= self.words + RESERVED_WORDS {
            return false;
        }
        let offset = address - RESERVED_WORDS;
        self.bits[offset / 64] & (1_u64 << (offset % 64)) != 0
    }
}

/// One partially rebuilt node awaiting the rest of its children.
#[derive(Debug)]
pub(super) struct Frame {
    pub(super) tag: u8,
    pub(super) negative: bool,
    pub(super) remaining: usize,
    pub(super) children: Vec<Formula>,
}

pub(super) fn node(tag: u8, negative: bool, children: Vec<Formula>) -> Option<Formula> {
    match tag {
        0 => Some(Formula::And { negative, children }),
        1 => Some(Formula::Or { negative, children }),
        2 => Some(Formula::Sat { negative, children }),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Header {
    pub(super) block: Block,
    pub(super) next: usize,
    pub(super) prev: usize,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum NullablePointer {
    Null,
    Address(usize),
}

use super::{Formula, Hash, RESERVED_WORDS};
