//! Reusable word arrays with intrusive size-class free rings.
//!
//! A live header is `(length << 3) | (tag << 1) | shared`. Length counts
//! payload words, including zeroes. Allocation rounds header plus payload up
//! to a power of two, at least four words. Padding is zero. Tags and payloads
//! are opaque to this layer. A shared allocation is sticky: writes copy it,
//! and release leaves it allocated until the caller compacts the table.

use covalence_lib_error::snafu::Snafu;
use std::{collections::BTreeMap, marker::PhantomData};

const CLASSES: usize = 61;

/// An ephemeral, four-word-aligned address within one table.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ArrayId(usize);

impl ArrayId {
    /// Refines a raw aligned address. Membership is checked by table operations.
    #[must_use]
    pub const fn new(base: usize) -> Option<Self> {
        if base >= 4 && base.is_multiple_of(4) {
            Some(Self(base))
        } else {
            None
        }
    }
    /// Returns the word address of the header.
    #[must_use]
    pub const fn base(self) -> usize {
        self.0
    }
}

/// Decoded fields of an array header.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ArrayHeader<Tag = u8> {
    /// Number of payload slots, including zero-valued slots.
    pub length: usize,
    /// Opaque application tag; the default codec reserves two bits.
    pub tag: Tag,
    /// Whether this allocation must be copied and retained on release.
    pub shared: bool,
}

impl ArrayHeader {
    /// Packs the header fields into one word.
    ///
    /// # Errors
    /// Returns an error if the length or tag does not fit.
    pub fn word(self) -> Result<u64, TableError> {
        let length = u64::try_from(self.length).map_err(|_| TableError::Bound)?;
        if length > u64::MAX >> 3 || self.tag > 3 {
            return Err(TableError::Bound);
        }
        Ok((length << 3) | (u64::from(self.tag) << 1) | u64::from(self.shared))
    }
    /// Decodes one header word without interpreting its tag.
    ///
    /// # Errors
    /// Returns an error if the length does not fit the host.
    pub fn decode(word: u64) -> Result<Self, TableError> {
        Ok(Self {
            length: usize::try_from(word >> 3).map_err(|_| TableError::Bound)?,
            tag: ((word >> 1) & 3) as u8,
            shared: word & 1 != 0,
        })
    }
}

/// Interpretation of the first word of a live array. Free-ring metadata is
/// independent of this codec. Table operations check encode/decode agreement.
pub trait HeaderCodec: Clone + std::fmt::Debug + Eq {
    /// Application-specific tag vocabulary.
    type Tag: Copy + std::fmt::Debug + Eq;
    /// Interprets a raw header word.
    ///
    /// # Errors
    /// Returns an error for an invalid header.
    fn decode(word: u64) -> Result<ArrayHeader<Self::Tag>, TableError>;
    /// Encodes the three fields in the application's layout.
    ///
    /// # Errors
    /// Returns an error when the fields cannot be represented.
    fn encode(header: ArrayHeader<Self::Tag>) -> Result<u64, TableError>;
}

/// Default length/two-tag-bit/shared-bit header codec.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PackedHeader;
impl HeaderCodec for PackedHeader {
    type Tag = u8;
    fn decode(word: u64) -> Result<ArrayHeader, TableError> {
        ArrayHeader::decode(word)
    }
    fn encode(header: ArrayHeader) -> Result<u64, TableError> {
        header.word()
    }
}

fn encode<H: HeaderCodec>(header: ArrayHeader<H::Tag>) -> Result<u64, TableError> {
    let word = H::encode(header)?;
    if H::decode(word)? != header {
        return Err(TableError::Invalid);
    }
    Ok(word)
}

/// A power-of-two allocation, including its header and padding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Block {
    base: usize,
    size_class: usize,
}
impl Block {
    /// Returns the header address.
    #[must_use]
    pub const fn base(self) -> usize {
        self.base
    }
    /// Returns the class with capacity `4 << size_class`.
    #[must_use]
    pub const fn size_class(self) -> usize {
        self.size_class
    }
    /// Returns the complete allocation capacity.
    #[must_use]
    pub fn capacity(self) -> usize {
        4_usize << self.size_class
    }
    fn stop(self) -> usize {
        self.base + self.capacity()
    }
}

/// Failure of a raw table operation. No logical claims are checked here.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum TableError {
    /// Malformed allocation partition or intrusive links.
    #[snafu(display("invalid array table"))]
    Invalid,
    /// Length, tag, or address exceeds the representation bounds.
    #[snafu(display("array table resource bound exceeded"))]
    Bound,
    /// The address is not a live array in this table.
    #[snafu(display("missing array at word {base}"))]
    Missing {
        /// Rejected address.
        base: usize,
    },
    /// The selected payload slot does not exist.
    #[snafu(display("missing array slot {index}"))]
    Slot {
        /// Rejected slot.
        index: usize,
    },
}

/// Flat storage with checked allocation metadata and uninterpreted payloads.
///
/// The maps are derived indexes; the serialized allocator is entirely intrusive.
/// No mutable word slice is exposed, so raw writes cannot corrupt allocation
/// metadata. IDs are local and may be reused after an unshared array is freed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Table<H: HeaderCodec = PackedHeader> {
    codec: PhantomData<H>,
    directory: Option<usize>,
    words: Vec<u64>,
    live: BTreeMap<usize, Block>,
    free: BTreeMap<usize, Block>,
    heads: [Option<usize>; CLASSES],
}

impl<H: HeaderCodec> Default for Table<H> {
    fn default() -> Self {
        Self::new()
    }
}
impl<H: HeaderCodec> Table<H> {
    /// Constructs an empty table with four reserved zero words.
    #[must_use]
    pub fn new() -> Self {
        Self {
            codec: PhantomData,
            directory: None,
            words: vec![0; 4],
            live: BTreeMap::new(),
            free: BTreeMap::new(),
            heads: [None; CLASSES],
        }
    }
    /// Imports exact storage after validating lengths, padding, free rings,
    /// backlinks, and a complete nonoverlapping allocation partition.
    ///
    /// # Errors
    /// Returns an error for malformed storage or representation bounds.
    pub fn from_words(words: Vec<u64>, free_root: u64) -> Result<Self, TableError> {
        if words.get(..4) != Some(&[0; 4]) || (words.len() as u128) > (1_u128 << 63) {
            return Err(TableError::Invalid);
        }
        let mut table = Self {
            words,
            ..Self::new()
        };
        if free_root != 0 {
            let root = address(free_root)?;
            let largest = table.free_header(root)?.0.size_class;
            table.heads[largest] = Some(root);
            table.directory = Some(root);
            for class in 0..largest {
                let value = *table
                    .words
                    .get(root + 4 + class)
                    .ok_or(TableError::Invalid)?;
                if value != 0 {
                    table.heads[class] = Some(address(value)?);
                }
            }
            for class in 0..=largest {
                let Some(head) = table.heads[class] else {
                    continue;
                };
                let mut current = head;
                loop {
                    let (block, next, prev) = table.free_header(current)?;
                    if block.size_class != class
                        || table.free.insert(current, block).is_some()
                        || table.free_header(next)?.2 != current
                        || table.free_header(prev)?.1 != current
                    {
                        return Err(TableError::Invalid);
                    }
                    let used = if current == root { largest } else { 0 };
                    if used > block.capacity() - 4
                        || !table.words[current + 4 + used..block.stop()]
                            .iter()
                            .all(|word| *word == 0)
                    {
                        return Err(TableError::Invalid);
                    }
                    current = next;
                    if current == head {
                        break;
                    }
                }
            }
        }
        let mut base = 4;
        let mut free_seen = 0;
        while base < table.words.len() {
            let block = if let Some(block) = table.free.get(&base) {
                free_seen += 1;
                *block
            } else {
                let header = H::decode(table.words[base])?;
                let block = fitted_block(base, class_for(header.length)?, table.words.len())?;
                if !table.words[base + 1 + header.length..block.stop()]
                    .iter()
                    .all(|word| *word == 0)
                {
                    return Err(TableError::Invalid);
                }
                table.live.insert(base, block);
                block
            };
            base = block.stop();
        }
        if free_seen != table.free.len() {
            return Err(TableError::Invalid);
        }
        Ok(table)
    }
    /// Borrows exact storage, including allocator metadata.
    #[must_use]
    pub fn words(&self) -> &[u64] {
        &self.words
    }
    /// Returns the intrusive directory root, or zero for an empty free list.
    #[must_use]
    pub fn free_root(&self) -> u64 {
        self.heads
            .iter()
            .rev()
            .flatten()
            .next()
            .copied()
            .unwrap_or(0) as u64
    }
    /// Iterates over all live arrays, including retained shared garbage.
    pub fn arrays(&self) -> impl Iterator<Item = ArrayId> + '_ {
        self.live.keys().copied().map(ArrayId)
    }
    /// Iterates over live allocation blocks in address order.
    pub fn live_blocks(&self) -> impl Iterator<Item = Block> + '_ {
        self.live.values().copied()
    }
    /// Iterates over free allocation blocks in address order.
    pub fn free_blocks(&self) -> impl Iterator<Item = Block> + '_ {
        self.free.values().copied()
    }
    /// Borrows the payload slots of a live array.
    ///
    /// # Errors
    /// Returns an error for a missing array.
    pub fn get(&self, id: ArrayId) -> Result<&[u64], TableError> {
        let header = self.header(id)?;
        Ok(&self.words[id.0 + 1..id.0 + 1 + header.length])
    }
    /// Reads the header of a live array.
    ///
    /// # Errors
    /// Returns an error for a missing array.
    pub fn header(&self, id: ArrayId) -> Result<ArrayHeader<H::Tag>, TableError> {
        if !self.live.contains_key(&id.0) {
            return Err(TableError::Missing { base: id.0 });
        }
        H::decode(self.words[id.0])
    }
    /// Marks an array shared permanently, returning the same address.
    ///
    /// # Errors
    /// Returns an error for a missing array.
    pub fn share(&mut self, id: ArrayId) -> Result<ArrayId, TableError> {
        let mut header = self.header(id)?;
        header.shared = true;
        self.words[id.0] = encode::<H>(header)?;
        Ok(id)
    }
    /// Allocates opaque slots, splitting a larger free block when available.
    ///
    /// # Errors
    /// Returns an error for an invalid tag or an unrepresentable allocation.
    pub fn allocate(&mut self, tag: H::Tag, slots: &[u64]) -> Result<ArrayId, TableError> {
        let header = encode::<H>(ArrayHeader {
            length: slots.len(),
            tag,
            shared: false,
        })?;
        let class = class_for(slots.len())?;
        let selected = (class..CLASSES).find_map(|c| self.heads[c].map(|base| (c, base)));
        let block = if let Some((mut c, base)) = selected {
            self.unlink_free(base);
            while c > class {
                c -= 1;
                self.link_free(Block {
                    base: base + (4 << c),
                    size_class: c,
                });
            }
            Block {
                base,
                size_class: class,
            }
        } else {
            let base = self.words.len();
            let capacity = 4_usize
                .checked_shl(u32::try_from(class).map_err(|_| TableError::Bound)?)
                .ok_or(TableError::Bound)?;
            let stop = base
                .checked_add(capacity)
                .filter(|stop| (*stop as u128) <= 1_u128 << 63)
                .ok_or(TableError::Bound)?;
            self.words.resize(stop, 0);
            Block {
                base,
                size_class: class,
            }
        };
        self.words[block.base..block.stop()].fill(0);
        self.words[block.base] = header;
        self.words[block.base + 1..block.base + 1 + slots.len()].copy_from_slice(slots);
        self.live.insert(block.base, block);
        self.write_directory();
        Ok(ArrayId(block.base))
    }
    /// Writes one slot, copying the complete array first when marked shared.
    /// Opaque element ownership is the caller's responsibility.
    ///
    /// # Errors
    /// Returns an error for a missing array/slot or allocation overflow.
    pub fn write(&mut self, id: ArrayId, index: usize, value: u64) -> Result<ArrayId, TableError> {
        let header = self.header(id)?;
        if index >= header.length {
            return Err(TableError::Slot { index });
        }
        let target = if header.shared {
            let slots = self.get(id)?.to_vec();
            self.allocate(header.tag, &slots)?
        } else {
            id
        };
        self.words[target.0 + 1 + index] = value;
        Ok(target)
    }
    /// Replaces the array tag, copying first when shared.
    ///
    /// # Errors
    /// Returns an error for a missing array, invalid tag, or allocation overflow.
    pub fn retag(&mut self, id: ArrayId, tag: H::Tag) -> Result<ArrayId, TableError> {
        let mut header = self.header(id)?;
        header.tag = tag;
        let word = encode::<H>(header)?;
        if header.shared {
            let slots = self.get(id)?.to_vec();
            self.allocate(tag, &slots)
        } else {
            self.words[id.0] = word;
            Ok(id)
        }
    }
    /// Frees an unshared array. A shared array remains allocated and returns
    /// `false`; only caller-driven GC/compaction may reclaim it.
    ///
    /// # Errors
    /// Returns an error for a missing array.
    pub fn release(&mut self, id: ArrayId) -> Result<bool, TableError> {
        if self.header(id)?.shared {
            return Ok(false);
        }
        let block = self
            .live
            .remove(&id.0)
            .ok_or(TableError::Missing { base: id.0 })?;
        self.link_free(block);
        self.write_directory();
        Ok(true)
    }
    fn free_header(&self, base: usize) -> Result<(Block, usize, usize), TableError> {
        let header = self
            .words
            .get(base..base.checked_add(4).ok_or(TableError::Invalid)?)
            .ok_or(TableError::Invalid)?;
        if header[0] != 0 {
            return Err(TableError::Invalid);
        }
        let block = fitted_block(
            base,
            usize::try_from(header[3]).map_err(|_| TableError::Invalid)?,
            self.words.len(),
        )?;
        Ok((block, address(header[1])?, address(header[2])?))
    }
    fn unlink_free(&mut self, base: usize) {
        let block = self.free.remove(&base).expect("indexed free block");
        let next = usize::try_from(self.words[base + 1]).expect("validated free pointer fits host");
        let prev = usize::try_from(self.words[base + 2]).expect("validated free pointer fits host");
        if next == base {
            self.heads[block.size_class] = None;
        } else {
            self.words[next + 2] = prev as u64;
            self.words[prev + 1] = next as u64;
            if self.heads[block.size_class] == Some(base) {
                self.heads[block.size_class] = Some(next);
            }
        }
    }
    fn link_free(&mut self, block: Block) {
        let base = block.base;
        self.words[base..block.stop()].fill(0);
        if let Some(head) = self.heads[block.size_class] {
            let prev =
                usize::try_from(self.words[head + 2]).expect("validated free pointer fits host");
            self.words[base + 1] = head as u64;
            self.words[base + 2] = prev as u64;
            self.words[prev + 1] = base as u64;
            self.words[head + 2] = base as u64;
        } else {
            self.words[base + 1] = base as u64;
            self.words[base + 2] = base as u64;
            self.heads[block.size_class] = Some(base);
        }
        self.words[base + 3] = block.size_class as u64;
        self.free.insert(base, block);
    }
    fn write_directory(&mut self) {
        if let Some(old) = self.directory.take()
            && let Some(block) = self.free.get(&old)
        {
            self.words[old + 4..old + 4 + block.size_class].fill(0);
        }
        if let Some((class, base)) = self
            .heads
            .iter()
            .enumerate()
            .rev()
            .find_map(|(c, h)| h.map(|b| (c, b)))
        {
            self.directory = Some(base);
            for c in 0..class {
                self.words[base + 4 + c] = self.heads[c].unwrap_or(0) as u64;
            }
        }
    }
}

fn address(word: u64) -> Result<usize, TableError> {
    let base = usize::try_from(word).map_err(|_| TableError::Invalid)?;
    if word >= 1 << 63 || ArrayId::new(base).is_none() {
        Err(TableError::Invalid)
    } else {
        Ok(base)
    }
}
fn class_for(length: usize) -> Result<usize, TableError> {
    let capacity = length
        .checked_add(1)
        .and_then(usize::checked_next_power_of_two)
        .ok_or(TableError::Bound)?
        .max(4);
    let class = capacity.trailing_zeros() as usize - 2;
    if class >= CLASSES {
        Err(TableError::Bound)
    } else {
        Ok(class)
    }
}
fn fitted_block(base: usize, class: usize, size: usize) -> Result<Block, TableError> {
    if ArrayId::new(base).is_none() || class >= CLASSES || class + 2 >= usize::BITS as usize {
        return Err(TableError::Invalid);
    }
    let block = Block {
        base,
        size_class: class,
    };
    if base
        .checked_add(block.capacity())
        .is_none_or(|stop| stop > size)
    {
        return Err(TableError::Invalid);
    }
    Ok(block)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn round_trip<H: HeaderCodec>(table: &Table<H>) {
        assert_eq!(
            Table::<H>::from_words(table.words().to_vec(), table.free_root()).unwrap(),
            *table
        );
    }

    #[test]
    fn lengths_preserve_zero_elements_without_a_terminator() {
        let mut table: Table = Table::new();
        let id = table.allocate(2, &[0, 7, 0]).unwrap();
        assert_eq!(table.get(id).unwrap(), [0, 7, 0]);
        assert_eq!(table.words().len(), 8);
        assert_eq!(table.words()[id.base()], 28);
        round_trip(&table);
    }

    #[test]
    fn shared_writes_and_retags_copy_and_release_retains_the_original() {
        let mut table: Table = Table::new();
        let old = table.allocate(0, &[10, 20]).unwrap();
        table.share(old).unwrap();
        let written = table.write(old, 1, 30).unwrap();
        assert_ne!(written, old);
        assert_eq!(table.get(old).unwrap(), [10, 20]);
        assert_eq!(table.get(written).unwrap(), [10, 30]);
        assert!(!table.release(old).unwrap());
        let retagged = table.retag(old, 3).unwrap();
        assert_ne!(retagged, old);
        assert_eq!(table.header(old).unwrap().tag, 0);
        assert_eq!(table.header(retagged).unwrap().tag, 3);
        let same = table.write(written, 0, 99).unwrap();
        assert_eq!(same, written);
        round_trip(&table);
    }

    #[test]
    fn free_rings_split_reuse_and_move_the_directory() {
        let mut table: Table = Table::new();
        let mut ids = Vec::new();
        for length in [0, 8, 2, 20, 5, 1, 70] {
            ids.push(table.allocate(1, &vec![42; length]).unwrap());
        }
        for id in ids {
            assert!(table.release(id).unwrap());
            round_trip(&table);
        }
        let size = table.words().len();
        for _ in 0..12 {
            table.allocate(0, &[1, 2, 3]).unwrap();
            round_trip(&table);
        }
        assert_eq!(table.words().len(), size);
    }

    #[test]
    fn rejected_operations_preserve_exact_storage() {
        let mut table: Table = Table::new();
        let id = table.allocate(1, &[7]).unwrap();
        let before = table.clone();
        assert!(table.allocate(4, &[]).is_err());
        assert!(table.write(id, 1, 8).is_err());
        assert!(table.retag(id, 5).is_err());
        assert_eq!(table, before);
        let mut padding = table.words().to_vec();
        padding[id.base() + 2] = 1;
        assert!(Table::<PackedHeader>::from_words(padding, 0).is_err());
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct OtherHeader;
    impl HeaderCodec for OtherHeader {
        type Tag = u8;
        fn encode(header: ArrayHeader) -> Result<u64, TableError> {
            if header.length >= 1 << 16 {
                return Err(TableError::Bound);
            }
            Ok(header.length as u64
                | (u64::from(header.tag) << 16)
                | (u64::from(header.shared) << 24))
        }
        fn decode(word: u64) -> Result<ArrayHeader, TableError> {
            if word >> 25 != 0 {
                return Err(TableError::Invalid);
            }
            Ok(ArrayHeader {
                length: (word & 0xffff) as usize,
                tag: ((word >> 16) & 255) as u8,
                shared: word & (1 << 24) != 0,
            })
        }
    }

    #[test]
    fn allocator_uses_the_generic_header_interpretation() {
        let mut table = Table::<OtherHeader>::new();
        let id = table.allocate(231, &[0, 10]).unwrap();
        table.share(id).unwrap();
        let copy = table.write(id, 0, 5).unwrap();
        assert_eq!(table.get(copy).unwrap(), [5, 10]);
        assert_eq!(table.header(copy).unwrap().tag, 231);
        assert!(!table.release(id).unwrap());
        round_trip(&table);
    }
}
