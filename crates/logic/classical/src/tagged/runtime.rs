use std::hash::{Hash, Hasher};

use covalence_lib_error::snafu::Snafu;

use super::{Formula, Ref, Sequent, Side, Word, WordError};

const PAYLOAD_WIDTH: u32 = 31;
const RESERVED_WORDS: usize = 4;

/// A failure to validate or canonically pack a tagged runtime arena.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RuntimeError {
    /// Raw storage did not satisfy the complete allocator and ownership check.
    #[snafu(display("invalid tagged runtime arena"))]
    InvalidArena,
    /// An abstract formula or allocation exceeded the fixed runtime bounds.
    #[snafu(display("tagged runtime resource bound exceeded: {reason}"))]
    ResourceBound {
        /// The bound that could not be satisfied.
        reason: &'static str,
    },
    /// A formula could not be represented as a packed word.
    #[snafu(transparent)]
    Word {
        /// Underlying fixed-word construction failure.
        source: WordError,
    },
    /// The canonical builder and ordinary validator disagreed.
    #[snafu(display("canonical tagged runtime output failed its postcheck"))]
    PackerPostcheck,
}

/// One aligned power-of-two allocation block.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Block {
    base: usize,
    size_class: usize,
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

    fn stop(self) -> Option<usize> {
        self.base.checked_add(self.capacity()?)
    }

    fn fits(self, size: usize) -> bool {
        self.base >= RESERVED_WORDS
            && self.base.is_multiple_of(4)
            && self.stop().is_some_and(|stop| stop <= size)
    }
}

/// Untrusted flat storage for the fixed-word runtime.
///
/// Constructing an arena confers no logical authority. Use [`Checked::check`]
/// to validate allocator ownership and recover its abstract syntax.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Arena {
    words: Vec<Word>,
    free_root: Word,
    roots: Vec<(Ref, Ref)>,
}

impl Arena {
    /// Constructs untrusted arena storage without validating it.
    #[must_use]
    pub const fn new(words: Vec<Word>, free_root: Word, roots: Vec<(Ref, Ref)>) -> Self {
        Self {
            words,
            free_root,
            roots,
        }
    }

    /// Returns the complete packed word array.
    #[cfg(test)]
    #[must_use]
    pub fn words(&self) -> &[Word] {
        &self.words
    }

    /// Returns the single intrusive allocator root word.
    #[cfg(test)]
    #[must_use]
    pub const fn free_root(&self) -> Word {
        self.free_root
    }

    /// Returns the sequent table's premise/conclusion root pairs.
    #[cfg(test)]
    #[must_use]
    pub fn roots(&self) -> &[(Ref, Ref)] {
        &self.roots
    }

    /// Consumes the arena and returns its raw parts.
    #[cfg(test)]
    #[must_use]
    pub fn into_parts(self) -> (Vec<Word>, Word, Vec<(Ref, Ref)>) {
        (self.words, self.free_root, self.roots)
    }

    fn word(&self, index: usize) -> Option<Word> {
        self.words.get(index).copied()
    }

    fn pointer(word: Word) -> Option<usize> {
        if word.is_negative() || word.payload() == 0 || word.tag() != 0 {
            return None;
        }
        usize::try_from(word.base()).ok()
    }

    fn optional_pointer(word: Word) -> Option<NullablePointer> {
        if word == Word::ZERO {
            Some(NullablePointer::Null)
        } else {
            Self::pointer(word).map(NullablePointer::Address)
        }
    }

    fn natural(word: Word) -> Option<u32> {
        (!word.is_negative()).then(|| word.payload())
    }

    fn header(&self, base: usize) -> Option<Header> {
        if self.word(base)? != Word::ZERO {
            return None;
        }
        let next = Self::pointer(self.word(base.checked_add(1)?)?)?;
        let prev = Self::pointer(self.word(base.checked_add(2)?)?)?;
        let size_class = usize::try_from(Self::natural(self.word(base.checked_add(3)?)?)?).ok()?;
        if size_class.checked_add(2)? > usize::try_from(PAYLOAD_WIDTH).ok()? {
            return None;
        }
        let block = Block { base, size_class };
        block
            .fits(self.words.len())
            .then_some(Header { block, next, prev })
    }

    fn zero_range(&self, start: usize, count: usize) -> bool {
        start
            .checked_add(count)
            .and_then(|stop| self.words.get(start..stop))
            .is_some_and(|words| words.iter().all(|word| *word == Word::ZERO))
    }

    fn ordinary_node(&self, header: Header) -> bool {
        header
            .block
            .capacity()
            .is_some_and(|capacity| self.zero_range(header.block.base + 4, capacity - 4))
    }

    /// Walks one intrusive free ring, claiming every block it links.
    ///
    /// The claim replaces the former quadratic scan for a revisited base: a
    /// ring that returns to a block it already linked claims an address twice.
    fn walk_ring(
        &self,
        coverage: &mut Coverage,
        head: usize,
        expected_class: usize,
        special: Option<usize>,
    ) -> Option<Vec<Block>> {
        let mut current = head;
        let mut visited = Vec::new();
        // A bound rather than a halting argument: every iteration claims at
        // least four fresh words, so this can only fire on input the claim has
        // already rejected.
        for _ in 0..=self.words.len() {
            let header = self.header(current)?;
            if header.block.size_class != expected_class {
                return None;
            }
            if !coverage.claim(header.block) {
                return None;
            }
            if special != Some(current) && !self.ordinary_node(header) {
                return None;
            }
            let next_header = self.header(header.next)?;
            if next_header.prev != current {
                return None;
            }
            visited.push(header.block);
            if header.next == head {
                return Some(visited);
            }
            current = header.next;
        }
        None
    }

    fn directory_head(&self, root: Header, size_class: usize) -> Option<NullablePointer> {
        let address = root.block.base.checked_add(4)?.checked_add(size_class)?;
        Self::optional_pointer(self.word(address)?)
    }

    fn root_padding(&self, root: Header) -> bool {
        root.block.capacity().is_some_and(|capacity| {
            let spare = capacity - 4;
            root.block.size_class <= spare
                && self.zero_range(
                    root.block.base + 4 + root.block.size_class,
                    spare - root.block.size_class,
                )
        })
    }

    fn decode_free(&self, coverage: &mut Coverage) -> Option<Vec<Block>> {
        let size = u64::try_from(self.words.len()).ok()?;
        if size > (1_u64 << PAYLOAD_WIDTH) {
            return None;
        }
        let root_base = match Self::optional_pointer(self.free_root)? {
            NullablePointer::Null => return Some(Vec::new()),
            NullablePointer::Address(base) => base,
        };
        let root = self.header(root_base)?;
        if !self.root_padding(root) {
            return None;
        }
        let mut blocks = Vec::new();
        for size_class in 0..root.block.size_class {
            if let NullablePointer::Address(head) = self.directory_head(root, size_class)? {
                blocks.extend(self.walk_ring(coverage, head, size_class, None)?);
            }
        }
        blocks.extend(self.walk_ring(
            coverage,
            root_base,
            root.block.size_class,
            Some(root_base),
        )?);
        Some(blocks)
    }

    fn live_block(&self, base: u32) -> Option<Block> {
        let base = usize::try_from(base).ok()?;
        let size_class = usize::try_from(Self::natural(self.word(base)?)?).ok()?;
        if size_class.checked_add(2)? > usize::try_from(PAYLOAD_WIDTH).ok()? {
            return None;
        }
        let block = Block { base, size_class };
        block.fits(self.words.len()).then_some(block)
    }

    /// Borrows one live block's child references, without copying them.
    ///
    /// The payload is a nonzero prefix followed by a zero terminator and zero
    /// padding to the end of the block.
    fn child_words(&self, block: Block) -> Option<&[Word]> {
        if self.live_block(u32::try_from(block.base).ok()?)? != block {
            return None;
        }
        let capacity = block.capacity()?;
        let start = block.base.checked_add(1)?;
        let words = self.words.get(start..start.checked_add(capacity - 1)?)?;
        let terminator = words.iter().position(|word| *word == Word::ZERO)?;
        if !words[terminator..].iter().all(|word| *word == Word::ZERO) {
            return None;
        }
        words.get(..terminator)
    }

    /// Opens a flat traversal of the sequent table.
    fn walk(&self) -> Option<Walk<'_>> {
        if !self.zero_range(0, RESERVED_WORDS) {
            return None;
        }
        let mut coverage = Coverage::new(self.words.len());
        let free = self.decode_free(&mut coverage)?;
        let mut pending = Vec::with_capacity(2 * self.roots.len());
        for (premise, conclusion) in self.roots.iter().rev() {
            pending.push(*conclusion);
            pending.push(*premise);
        }
        Some(Walk {
            arena: self,
            pending,
            coverage,
            free,
        })
    }

    /// Validates this arena and materializes its sequent table in one pass.
    ///
    /// The fold stack is the nesting, so nothing recurses: a completed formula
    /// is pushed into the frame that was waiting for it, and a completed frame
    /// becomes a formula in turn.
    fn decode_table(&self) -> Result<Vec<Sequent>, RuntimeError> {
        let mut walk = self.walk().ok_or(RuntimeError::InvalidArena)?;
        let mut stack: Vec<Frame> = Vec::new();
        let mut roots: Vec<Formula> = Vec::with_capacity(2 * self.roots.len());
        while let Some(token) = walk.step()? {
            let mut formula = if token.tag == 3 {
                Formula::Literal {
                    atom: token.value,
                    negative: token.negative,
                }
            } else {
                let arity = usize::try_from(token.value).map_err(|_| RuntimeError::InvalidArena)?;
                if arity > 0 {
                    stack.push(Frame {
                        tag: token.tag,
                        negative: token.negative,
                        remaining: arity,
                        children: Vec::with_capacity(arity),
                    });
                    continue;
                }
                node(token.tag, token.negative, Vec::new()).ok_or(RuntimeError::InvalidArena)?
            };
            loop {
                let Some(frame) = stack.last_mut() else {
                    roots.push(formula);
                    break;
                };
                frame.children.push(formula);
                frame.remaining -= 1;
                if frame.remaining > 0 {
                    break;
                }
                let Some(frame) = stack.pop() else {
                    return Err(RuntimeError::InvalidArena);
                };
                formula = node(frame.tag, frame.negative, frame.children)
                    .ok_or(RuntimeError::InvalidArena)?;
            }
        }
        walk.finish()?;
        if !stack.is_empty() || roots.len() != 2 * self.roots.len() {
            return Err(RuntimeError::InvalidArena);
        }
        let mut sequents = Vec::with_capacity(self.roots.len());
        let mut decoded = roots.into_iter();
        while let (Some(premise), Some(conclusion)) = (decoded.next(), decoded.next()) {
            sequents.push(Sequent {
                premise,
                conclusion,
            });
        }
        Ok(sequents)
    }
}

/// One step of the flat traversal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Token {
    tag: u8,
    negative: bool,
    /// Child arity for a node, atom identifier for a literal.
    value: u32,
}

/// State for one flat traversal.
///
/// Each descent claims at least four words, so storage bounds the worklist.
struct Walk<'a> {
    arena: &'a Arena,
    pending: Vec<Ref>,
    coverage: Coverage,
    free: Vec<Block>,
}

impl Walk<'_> {
    /// Advances one node, claiming its storage. `Ok(None)` is the idle state.
    ///
    /// Children are pushed in reverse to preserve preorder. Claiming rejects
    /// overlap with free blocks and previously visited nodes.
    fn step(&mut self) -> Result<Option<Token>, RuntimeError> {
        let Some(reference) = self.pending.pop() else {
            return Ok(None);
        };
        let word = reference.word();
        if word.tag() == 3 {
            return Ok(Some(Token {
                tag: 3,
                negative: word.is_negative(),
                value: word.base() / 4,
            }));
        }
        let block = self
            .arena
            .live_block(word.base())
            .ok_or(RuntimeError::InvalidArena)?;
        if !self.coverage.claim(block) {
            return Err(RuntimeError::InvalidArena);
        }
        let children = self
            .arena
            .child_words(block)
            .ok_or(RuntimeError::InvalidArena)?;
        let arity = children.len();
        for child in children.iter().rev() {
            self.pending
                .push(Ref::new(*child).map_err(|_| RuntimeError::InvalidArena)?);
        }
        if word.tag() > 2 {
            return Err(RuntimeError::InvalidArena);
        }
        Ok(Some(Token {
            tag: word.tag(),
            negative: word.is_negative(),
            value: u32::try_from(arity).map_err(|_| RuntimeError::InvalidArena)?,
        }))
    }

    /// Accepts only a drained worklist that claimed all storage.
    fn finish(self) -> Result<Vec<Block>, RuntimeError> {
        if self.pending.is_empty() && self.coverage.complete() {
            Ok(self.free)
        } else {
            Err(RuntimeError::InvalidArena)
        }
    }
}

/// Address ownership recovered so far by one validation pass.
///
/// One ownership bit per word after the reserved prefix.
#[derive(Debug)]
struct Coverage {
    bits: Vec<u64>,
    claimed: usize,
    words: usize,
}

impl Coverage {
    fn new(size: usize) -> Self {
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
    fn claim(&mut self, block: Block) -> bool {
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
    const fn complete(&self) -> bool {
        self.claimed == self.words
    }
}

/// One partially rebuilt node awaiting the rest of its children.
#[derive(Debug)]
struct Frame {
    tag: u8,
    negative: bool,
    remaining: usize,
    children: Vec<Formula>,
}

fn node(tag: u8, negative: bool, children: Vec<Formula>) -> Option<Formula> {
    match tag {
        0 => Some(Formula::And { negative, children }),
        1 => Some(Formula::Or { negative, children }),
        2 => Some(Formula::Sat { negative, children }),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug)]
struct Header {
    block: Block,
    next: usize,
    prev: usize,
}

#[derive(Clone, Copy, Debug)]
enum NullablePointer {
    Null,
    Address(usize),
}

/// An arena that the complete executable validator accepted.
///
/// Decoded syntax is not retained beside the words.
#[derive(Clone, Debug)]
pub struct Checked {
    arena: Arena,
}

impl Checked {
    /// Validates a canonical dense snapshot.
    ///
    /// # Errors
    ///
    /// Returns an error if a root is invalid, storage is malformed, or the
    /// snapshot is not the unique dense encoding of its syntax.
    pub fn from_snapshot(words: Vec<u32>, roots: Vec<(u32, u32)>) -> Result<Self, RuntimeError> {
        let words = words.into_iter().map(Word::from_raw).collect();
        let roots = roots
            .into_iter()
            .map(|(premise, conclusion)| {
                Ok((
                    Ref::new(Word::from_raw(premise))?,
                    Ref::new(Word::from_raw(conclusion))?,
                ))
            })
            .collect::<Result<Vec<_>, WordError>>()?;
        let checked = Self::check(Arena::new(words, Word::ZERO, roots))?;
        let canonical = pack(&checked.decode_sequents()?)?;
        if canonical.raw_snapshot() != checked.raw_snapshot() {
            return Err(RuntimeError::InvalidArena);
        }
        Ok(checked)
    }

    /// Copies the canonical dense snapshot.
    ///
    /// # Panics
    ///
    /// Panics only if this checked value no longer decodes or packs.
    #[must_use]
    pub fn snapshot(&self) -> (Vec<u32>, Vec<(u32, u32)>) {
        let canonical = pack(
            &self
                .decode_sequents()
                .expect("checked storage remains decodable"),
        )
        .expect("checked storage remains representable");
        canonical.raw_snapshot()
    }

    fn raw_snapshot(&self) -> (Vec<u32>, Vec<(u32, u32)>) {
        let words = self.arena.words.iter().map(|word| word.raw()).collect();
        let roots = self
            .arena
            .roots
            .iter()
            .map(|(premise, conclusion)| (premise.word().raw(), conclusion.word().raw()))
            .collect();
        (words, roots)
    }

    /// Validates an untrusted runtime arena.
    ///
    /// This checks the intrusive free rings, unique ownership of every live
    /// subtree, canonical block padding, address bounds, and exact coverage.
    /// It establishes syntax only and does not create a theorem fact.
    ///
    /// # Errors
    ///
    /// Returns an error when any allocator, reference, syntax, or ownership
    /// invariant fails.
    pub(crate) fn check(arena: Arena) -> Result<Self, RuntimeError> {
        let mut walk = arena.walk().ok_or(RuntimeError::InvalidArena)?;
        while walk.step()?.is_some() {}
        walk.finish()?;
        Ok(Self { arena })
    }

    /// Returns the validated raw arena.
    #[cfg(test)]
    #[must_use]
    pub(crate) const fn arena(&self) -> &Arena {
        &self.arena
    }

    /// Materializes the sequent table.
    ///
    /// # Errors
    ///
    /// Returns an error only if the arena stopped validating, which cannot
    /// happen for a value of this type.
    pub fn decode_sequents(&self) -> Result<Vec<Sequent>, RuntimeError> {
        self.arena.decode_table()
    }

    /// Recovers the free blocks from the intrusive allocator root.
    ///
    /// # Panics
    ///
    /// Panics only if the arena stopped validating, which cannot happen for a
    /// value of this type.
    #[must_use]
    #[cfg(test)]
    pub(crate) fn free_blocks(&self) -> Vec<Block> {
        let mut coverage = Coverage::new(self.arena.words.len());
        self.arena
            .decode_free(&mut coverage)
            .expect("a checked arena revalidates")
    }

    pub(crate) fn normalize_matrix_row(&mut self, side: Side, row: usize) -> bool {
        let Some(root) = self.root(0, side) else {
            return false;
        };
        let Some(root_children) = self.child_range(root) else {
            return false;
        };
        let Some(reference) = self
            .arena
            .words
            .get(root_children)
            .and_then(|words| words.get(row))
            .copied()
        else {
            return false;
        };
        let Ok(reference) = Ref::new(reference) else {
            return false;
        };
        let Some(children) = self.child_range(reference) else {
            return false;
        };
        let words = &mut self.arena.words[children];
        words.sort_unstable_by_key(|word| {
            let atom = i32::try_from(word.base() / 4).expect("a packed literal atom fits i32");
            if word.is_negative() { atom } else { -atom }
        });
        let mut write = 0;
        for read in 0..words.len() {
            if write == 0 || words[read] != words[write - 1] {
                words[write] = words[read];
                write += 1;
            }
        }
        words[write..].fill(Word::ZERO);
        true
    }

    pub(crate) fn cross_matrix_row(&mut self, side: Side, row: usize) -> bool {
        let Some(source) = self.root(0, side) else {
            return false;
        };
        let destination_side = match side {
            Side::Left => Side::Right,
            Side::Right => Side::Left,
        };
        let Some(destination) = self.root(0, destination_side) else {
            return false;
        };
        let Some(destination_block) = self.arena.live_block(destination.word().base()) else {
            return false;
        };
        let (Some(source_children), Some(destination_children)) =
            (self.child_range(source), self.child_range(destination))
        else {
            return false;
        };
        let Some(row_word) = self
            .arena
            .words
            .get(source_children.clone())
            .and_then(|words| words.get(row))
            .copied()
        else {
            return false;
        };
        let Ok(row_ref) = Ref::new(row_word) else {
            return false;
        };
        let Some(row_children) = self.child_range(row_ref) else {
            return false;
        };
        let destination_stop = destination_children.end;
        if destination_stop + 1 >= destination_block.stop().unwrap_or(0)
            || self.arena.words[destination_stop] != Word::ZERO
        {
            return false;
        }

        for word in &mut self.arena.words[row_children] {
            *word = word.negated();
        }
        let row_tag = match side {
            Side::Left => 0,
            Side::Right => 1,
        };
        let moved = Ref::new(
            Word::pointer(row_ref.word().base(), row_tag, false)
                .expect("checked address remains representable"),
        )
        .expect("a checked row pointer is nonzero");
        self.arena.words.copy_within(
            source_children.start + row + 1..source_children.end,
            source_children.start + row,
        );
        self.arena.words[source_children.end - 1] = Word::ZERO;
        self.arena.words[destination_stop] = moved.word();
        true
    }

    fn root(&self, index: usize, side: Side) -> Option<Ref> {
        let roots = self.arena.roots.get(index)?;
        Some(match side {
            Side::Left => roots.0,
            Side::Right => roots.1,
        })
    }

    fn child_range(&self, reference: Ref) -> Option<std::ops::Range<usize>> {
        let block = self.arena.live_block(reference.word().base())?;
        let children = self.arena.child_words(block)?;
        let start = block.base + 1;
        Some(start..start + children.len())
    }

    /// Streams this arena's structural token sequence.
    ///
    /// # Panics
    ///
    /// Panics only if the arena stopped validating.
    fn tokens(&self) -> impl Iterator<Item = Token> + '_ {
        let mut walk = self.arena.walk().expect("a checked arena revalidates");
        std::iter::from_fn(move || walk.step().expect("a checked arena revalidates"))
    }
}

impl PartialEq for Checked {
    /// Compares syntax by advancing two traversals in lockstep.
    fn eq(&self, other: &Self) -> bool {
        self.arena.roots.len() == other.arena.roots.len() && self.tokens().eq(other.tokens())
    }
}

impl Eq for Checked {}

impl Hash for Checked {
    /// Hashes roots in table order and formulas in preorder.
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.arena.roots.len().hash(state);
        for token in self.tokens() {
            token.tag.hash(state);
            token.negative.hash(state);
            if token.tag == 3 {
                token.value.hash(state);
            } else {
                usize::try_from(token.value)
                    .expect("a checked arity fits the host")
                    .hash(state);
            }
        }
    }
}

/// Canonically packs an abstract sequent table into fresh dense storage.
///
/// The output begins with four reserved zero words, lays every live block out
/// in preorder using the least fitting size class, has no free blocks, and is
/// accepted only after the ordinary validator recovers the exact input.
///
/// # Errors
///
/// Returns an error if the formula table exceeds fixed-word or host resource
/// bounds, or if the generated candidate fails its independent postcheck.
pub fn pack(sequents: &[Sequent]) -> Result<Checked, RuntimeError> {
    let mut words = vec![Word::ZERO; RESERVED_WORDS];
    let mut roots = Vec::with_capacity(sequents.len());
    for sequent in sequents {
        let premise = build_formula(&mut words, &sequent.premise)?;
        let conclusion = build_formula(&mut words, &sequent.conclusion)?;
        roots.push((premise, conclusion));
    }
    let candidate = Arena::new(words, Word::ZERO, roots);
    let decoded = candidate
        .decode_table()
        .map_err(|_| RuntimeError::PackerPostcheck)?;
    if decoded == sequents {
        Ok(Checked { arena: candidate })
    } else {
        Err(RuntimeError::PackerPostcheck)
    }
}

fn least_size_class(children: usize) -> Result<usize, RuntimeError> {
    let needed = children.checked_add(1).ok_or(RuntimeError::ResourceBound {
        reason: "child count overflow",
    })?;
    let mut size_class = 0_usize;
    let mut capacity = 4_usize;
    while needed >= capacity {
        size_class = size_class
            .checked_add(1)
            .ok_or(RuntimeError::ResourceBound {
                reason: "size class overflow",
            })?;
        capacity = capacity.checked_mul(2).ok_or(RuntimeError::ResourceBound {
            reason: "block capacity overflow",
        })?;
    }
    Ok(size_class)
}

fn build_formula(words: &mut Vec<Word>, formula: &Formula) -> Result<Ref, RuntimeError> {
    match formula {
        Formula::Literal { atom, negative } => Ok(Ref::new(Word::literal(*atom, *negative)?)?),
        Formula::And { negative, children } => build_node(words, 0, *negative, children),
        Formula::Or { negative, children } => build_node(words, 1, *negative, children),
        Formula::Sat { negative, children } => build_node(words, 2, *negative, children),
    }
}

fn build_node(
    words: &mut Vec<Word>,
    tag: u8,
    negative: bool,
    children: &[Formula],
) -> Result<Ref, RuntimeError> {
    let size_class = least_size_class(children.len())?;
    if size_class
        .checked_add(2)
        .is_none_or(|bound| bound > PAYLOAD_WIDTH as usize)
    {
        return Err(RuntimeError::ResourceBound {
            reason: "size class exceeds payload width",
        });
    }
    let base = words.len();
    let block = Block { base, size_class };
    let capacity = block.capacity().ok_or(RuntimeError::ResourceBound {
        reason: "block capacity exceeds host address space",
    })?;
    let stop = block.stop().ok_or(RuntimeError::ResourceBound {
        reason: "block address overflow",
    })?;
    words
        .try_reserve(capacity)
        .map_err(|_| RuntimeError::ResourceBound {
            reason: "arena allocation failed",
        })?;
    words.resize(stop, Word::ZERO);
    words[base] =
        Word::natural(
            u32::try_from(size_class).map_err(|_| RuntimeError::ResourceBound {
                reason: "size class does not fit metadata",
            })?,
        )?;
    for (index, child) in children.iter().enumerate() {
        let reference = build_formula(words, child)?;
        words[base + 1 + index] = reference.word();
    }
    let address = u32::try_from(base).map_err(|_| RuntimeError::ResourceBound {
        reason: "block base does not fit payload",
    })?;
    Ok(Ref::new(Word::pointer(address, tag, negative)?)?)
}
