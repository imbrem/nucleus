use std::hash::{Hash, Hasher};

use covalence_lib_error::snafu::Snafu;

use super::{Formula, Ref, Sequent, Word, WordError};

const PAYLOAD_WIDTH: u64 = 63;
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
    #[must_use]
    pub const fn base(self) -> usize {
        self.base
    }

    /// Returns the allocator size class.
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

/// Untrusted flat storage for the selected fixed-64-bit runtime.
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
    #[must_use]
    pub fn words(&self) -> &[Word] {
        &self.words
    }

    /// Returns the single intrusive allocator root word.
    #[must_use]
    pub const fn free_root(&self) -> Word {
        self.free_root
    }

    /// Returns the sequent table's premise/conclusion root pairs.
    #[must_use]
    pub fn roots(&self) -> &[(Ref, Ref)] {
        &self.roots
    }

    /// Consumes the arena and returns its raw parts.
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

    fn natural(word: Word) -> Option<u64> {
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

    fn live_block(&self, base: u64) -> Option<Block> {
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
        if self.live_block(u64::try_from(block.base).ok()?)? != block {
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

    /// Opens a flat traversal of the whole sequent table.
    ///
    /// Lean: the prologue of `Flat.check?` -- the reserved prefix, the free
    /// rings, and the initial worklist.
    fn walk(&self) -> Option<Walk<'_>> {
        if !self.zero_range(0, RESERVED_WORDS) {
            return None;
        }
        let mut coverage = Coverage::new(self.words.len());
        let free = self.decode_free(&mut coverage)?;
        // Reversed, so the table pops premise-then-conclusion in table order.
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
///
/// Lean: the `output` triple emitted by `Flat.traceStep?`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Token {
    tag: u8,
    negative: bool,
    /// Child arity for a node, atom identifier for a literal.
    value: u64,
}

/// The complete state of one flat traversal.
///
/// Lean: `Flat.TraceState`, except that the output is handed to the caller a
/// step at a time rather than accumulated. Validation, hashing, structural
/// equality and decoding are then four consumers of one traversal.
///
/// There is no fuel counter. Every step down claims at least four fresh words
/// inside `[4, len)`, so the depth this can reach is bounded by storage, and
/// an arena deep enough to exhaust the former counter is rejected by a
/// repeated claim first. Lean: `Flat.traceRun_halts`.
struct Walk<'a> {
    arena: &'a Arena,
    pending: Vec<Ref>,
    coverage: Coverage,
    free: Vec<Block>,
}

impl Walk<'_> {
    /// Advances one node, claiming its storage. `Ok(None)` is the idle state.
    ///
    /// Children are pushed reversed so they pop left first, giving exactly the
    /// preorder a recursive descent would visit. The claim decides unique
    /// ownership against everything already claimed -- the free rings and
    /// every block of every earlier root included.
    ///
    /// Lean: `Flat.traceStep?`.
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
            value: u64::try_from(arity).map_err(|_| RuntimeError::InvalidArena)?,
        }))
    }

    /// Accepts only a drained worklist that claimed the whole of storage.
    ///
    /// Lean: the acceptance condition of `Flat.check?`.
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
/// One bit per word after the reserved prefix. Marking decides the two
/// conjuncts that made the former validator quadratic at once: a block that
/// claims an address twice is exactly a block that overlaps one claimed
/// earlier, and a pass that claims every address covers storage exactly.
///
/// Lean: `Flat.SeparateInvariant` for the first and `Arena.coversStorage` for
/// the second, with `Runtime.Partition.covers_iff_capacitySum` the same
/// replacement of an address scan by a running total.
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
/// The syntax is not stored beside the words. Lean makes the corresponding
/// field `noncomputable` for the same reason: a materialized recursive
/// `Formula` tree is as deep as untrusted storage, and everything that touches
/// it -- copying, comparing, hashing, dropping -- would inherit that depth.
/// Copying a `Checked` is copying its words.
#[derive(Clone, Debug)]
pub struct Checked {
    arena: Arena,
}

impl Checked {
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
    pub fn check(arena: Arena) -> Result<Self, RuntimeError> {
        let mut walk = arena.walk().ok_or(RuntimeError::InvalidArena)?;
        while walk.step()?.is_some() {}
        walk.finish()?;
        Ok(Self { arena })
    }

    /// Returns the validated raw arena.
    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    /// Materializes the sequent table.
    ///
    /// The result is computed, not stored: nothing keeps a recursive syntax
    /// tree alive beside the words. Lean pins the specification rather than
    /// this fold -- `FlatCorrect.hashSequents_inj` says the token stream
    /// determines a unique table, and `decodeMany_of_traceRun` says the
    /// traversal and the syntax agree.
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
    pub fn free_blocks(&self) -> Vec<Block> {
        let mut coverage = Coverage::new(self.arena.words.len());
        self.arena
            .decode_free(&mut coverage)
            .expect("a checked arena revalidates")
    }

    /// Streams this arena's structural token sequence.
    ///
    /// # Panics
    ///
    /// Panics only if the arena stopped validating, which cannot happen for a
    /// value of this type. Lean: `Flat.Checked.hashTrace_eq` states exactly
    /// that the pass is defined on a checked arena.
    fn tokens(&self) -> impl Iterator<Item = Token> + '_ {
        let mut walk = self.arena.walk().expect("a checked arena revalidates");
        std::iter::from_fn(move || walk.step().expect("a checked arena revalidates"))
    }
}

impl PartialEq for Checked {
    /// Compares decoded syntax by advancing two traversals in lockstep.
    ///
    /// This is equality of syntax, not agreement of a digest: Lean's
    /// `FlatCorrect.hashSequents_inj` says equal token streams are equal
    /// sequent tables. Allocator layout is invisible to it, exactly as it was
    /// to the comparison of materialized syntax.
    fn eq(&self, other: &Self) -> bool {
        self.arena.roots.len() == other.arena.roots.len() && self.tokens().eq(other.tokens())
    }
}

impl Eq for Checked {}

impl Hash for Checked {
    /// Feeds the same typed writes the materialized syntax used to feed.
    ///
    /// The traversal visits roots in table order and each root in preorder,
    /// which is what `Hash for Formula` did, so the feed is unchanged down to
    /// the individual `write_u8`/`write_u64`/`write_usize` calls. Lean:
    /// `FlatCorrect.check?_eq_hashSequents` -- one pass serves validation and
    /// hashing.
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
    let built = build_sequents(sequents)?;
    let mut words = vec![Word::ZERO; RESERVED_WORDS];
    words.extend(built.words);
    let candidate = Arena::new(words, Word::ZERO, built.roots);
    // The postcheck is the ordinary validator, run over the candidate exactly
    // as it would run over untrusted bytes, and it recovers the syntax in the
    // same pass.
    let decoded = candidate
        .decode_table()
        .map_err(|_| RuntimeError::PackerPostcheck)?;
    if decoded == sequents {
        Ok(Checked { arena: candidate })
    } else {
        Err(RuntimeError::PackerPostcheck)
    }
}

#[derive(Debug)]
struct Chunk {
    reference: Ref,
    words: Vec<Word>,
}

#[derive(Debug)]
struct Forest {
    references: Vec<Ref>,
    words: Vec<Word>,
}

#[derive(Debug)]
struct RootChunk {
    roots: Vec<(Ref, Ref)>,
    words: Vec<Word>,
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

fn build_formula(base: usize, formula: &Formula) -> Result<Chunk, RuntimeError> {
    match formula {
        Formula::Literal { atom, negative } => {
            let word = Word::literal(*atom, *negative)?;
            Ok(Chunk {
                reference: Ref::new(word)?,
                words: Vec::new(),
            })
        }
        Formula::And { negative, children } => build_node(base, 0, *negative, children),
        Formula::Or { negative, children } => build_node(base, 1, *negative, children),
        Formula::Sat { negative, children } => build_node(base, 2, *negative, children),
    }
}

fn build_node(
    base: usize,
    tag: u8,
    negative: bool,
    children: &[Formula],
) -> Result<Chunk, RuntimeError> {
    let size_class = least_size_class(children.len())?;
    if size_class.checked_add(2).is_none_or(|bound| bound > 63) {
        return Err(RuntimeError::ResourceBound {
            reason: "size class exceeds payload width",
        });
    }
    let block = Block { base, size_class };
    let capacity = block.capacity().ok_or(RuntimeError::ResourceBound {
        reason: "block capacity exceeds host address space",
    })?;
    let stop = block.stop().ok_or(RuntimeError::ResourceBound {
        reason: "block address overflow",
    })?;
    let forest = build_formulas(stop, children)?;
    let mut words = Vec::with_capacity(capacity.checked_add(forest.words.len()).ok_or(
        RuntimeError::ResourceBound {
            reason: "arena length overflow",
        },
    )?);
    words.push(Word::natural(u64::try_from(size_class).map_err(|_| {
        RuntimeError::ResourceBound {
            reason: "size class does not fit metadata",
        }
    })?)?);
    words.extend(forest.references.iter().map(|reference| reference.word()));
    let padding = capacity
        .checked_sub(1 + forest.references.len())
        .filter(|padding| *padding > 0)
        .ok_or(RuntimeError::ResourceBound {
            reason: "live block has no terminator",
        })?;
    words.extend(std::iter::repeat_n(Word::ZERO, padding));
    words.extend(forest.words);
    let base = u64::try_from(base).map_err(|_| RuntimeError::ResourceBound {
        reason: "block base does not fit payload",
    })?;
    let reference = Ref::new(Word::pointer(base, tag, negative)?)?;
    Ok(Chunk { reference, words })
}

fn build_formulas(base: usize, formulas: &[Formula]) -> Result<Forest, RuntimeError> {
    let mut references = Vec::with_capacity(formulas.len());
    let mut words = Vec::new();
    for formula in formulas {
        let child_base = base
            .checked_add(words.len())
            .ok_or(RuntimeError::ResourceBound {
                reason: "arena address overflow",
            })?;
        let chunk = build_formula(child_base, formula)?;
        references.push(chunk.reference);
        words.extend(chunk.words);
    }
    Ok(Forest { references, words })
}

fn build_sequents(sequents: &[Sequent]) -> Result<RootChunk, RuntimeError> {
    let mut roots = Vec::with_capacity(sequents.len());
    let mut words = Vec::new();
    for sequent in sequents {
        let premise_base =
            RESERVED_WORDS
                .checked_add(words.len())
                .ok_or(RuntimeError::ResourceBound {
                    reason: "arena address overflow",
                })?;
        let premise = build_formula(premise_base, &sequent.premise)?;
        words.extend(premise.words);
        let conclusion_base =
            RESERVED_WORDS
                .checked_add(words.len())
                .ok_or(RuntimeError::ResourceBound {
                    reason: "arena address overflow",
                })?;
        let conclusion = build_formula(conclusion_base, &sequent.conclusion)?;
        words.extend(conclusion.words);
        roots.push((premise.reference, conclusion.reference));
    }
    Ok(RootChunk { roots, words })
}
