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

    fn contains(self, address: usize) -> bool {
        self.stop()
            .is_some_and(|stop| self.base <= address && address < stop)
    }

    fn disjoint(self, other: Self) -> bool {
        self.stop().is_some_and(|stop| stop <= other.base)
            || other.stop().is_some_and(|stop| stop <= self.base)
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

    fn walk_ring(
        &self,
        head: usize,
        expected_class: usize,
        special: Option<usize>,
    ) -> Option<Vec<Block>> {
        let mut current = head;
        let mut visited = Vec::new();
        for _ in 0..=self.words.len() {
            if visited.iter().any(|block: &Block| block.base == current) {
                return None;
            }
            let header = self.header(current)?;
            if header.block.size_class != expected_class {
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

    fn decode_free(&self) -> Option<Vec<Block>> {
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
                blocks.extend(self.walk_ring(head, size_class, None)?);
            }
        }
        blocks.extend(self.walk_ring(root_base, root.block.size_class, Some(root_base))?);
        pairwise_disjoint(&blocks).then_some(blocks)
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

    fn read_live(&self, block: Block) -> Option<Vec<Ref>> {
        if self.live_block(u64::try_from(block.base).ok()?)? != block {
            return None;
        }
        let capacity = block.capacity()?;
        let start = block.base.checked_add(1)?;
        let words = self.words.get(start..start.checked_add(capacity - 1)?)?;
        decode_words(words)
    }

    fn decode_ref(
        &self,
        free: &[Block],
        fuel: usize,
        live: &mut Vec<Block>,
        reference: Ref,
    ) -> Option<Formula> {
        let next_fuel = fuel.checked_sub(1)?;
        let word = reference.word();
        if word.tag() == 3 {
            return Some(Formula::Literal {
                atom: word.base() / 4,
                negative: word.is_negative(),
            });
        }
        let block = self.live_block(word.base())?;
        if live.iter().chain(free).any(|owned| !block.disjoint(*owned)) {
            return None;
        }
        let children = self.read_live(block)?;
        live.insert(0, block);
        let mut decoded = Vec::with_capacity(children.len());
        for child in children {
            decoded.push(self.decode_ref(free, next_fuel, live, child)?);
        }
        match word.tag() {
            0 => Some(Formula::And {
                negative: word.is_negative(),
                children: decoded,
            }),
            1 => Some(Formula::Or {
                negative: word.is_negative(),
                children: decoded,
            }),
            2 => Some(Formula::Sat {
                negative: word.is_negative(),
                children: decoded,
            }),
            _ => None,
        }
    }

    fn decode_state(&self) -> Option<Decoded> {
        if !self.zero_range(0, RESERVED_WORDS) {
            return None;
        }
        let free = self.decode_free()?;
        let fuel = self.words.len().checked_add(1)?;
        let mut live = Vec::new();
        let mut sequents = Vec::with_capacity(self.roots.len());
        for (premise, conclusion) in &self.roots {
            let premise = self.decode_ref(&free, fuel, &mut live, *premise)?;
            let conclusion = self.decode_ref(&free, fuel, &mut live, *conclusion)?;
            sequents.push(Sequent {
                premise,
                conclusion,
            });
        }
        if !covers_storage(&live, &free, self.words.len()) {
            return None;
        }
        Some(Decoded {
            sequents,
            live,
            free,
        })
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

#[derive(Clone, Debug)]
struct Decoded {
    sequents: Vec<Sequent>,
    live: Vec<Block>,
    free: Vec<Block>,
}

/// An arena paired with the exact result of the complete executable validator.
#[derive(Clone, Debug)]
pub struct Checked {
    arena: Arena,
    decoded: Decoded,
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
        let decoded = arena.decode_state().ok_or(RuntimeError::InvalidArena)?;
        Ok(Self { arena, decoded })
    }

    /// Returns the validated raw arena.
    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    /// Returns the recursively decoded sequent table.
    #[must_use]
    pub fn sequents(&self) -> &[Sequent] {
        &self.decoded.sequents
    }

    /// Returns the live blocks recovered from the roots.
    #[must_use]
    pub fn live_blocks(&self) -> &[Block] {
        &self.decoded.live
    }

    /// Returns the free blocks recovered from the intrusive allocator root.
    #[must_use]
    pub fn free_blocks(&self) -> &[Block] {
        &self.decoded.free
    }
}

impl PartialEq for Checked {
    fn eq(&self, other: &Self) -> bool {
        self.decoded.sequents == other.decoded.sequents
    }
}

impl Eq for Checked {}

impl Hash for Checked {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.decoded.sequents.len().hash(state);
        for sequent in &self.decoded.sequents {
            sequent.hash(state);
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
    let checked = Checked::check(candidate).map_err(|_| RuntimeError::PackerPostcheck)?;
    if checked.sequents() == sequents {
        Ok(checked)
    } else {
        Err(RuntimeError::PackerPostcheck)
    }
}

fn pairwise_disjoint(blocks: &[Block]) -> bool {
    blocks.iter().enumerate().all(|(index, block)| {
        blocks[index + 1..]
            .iter()
            .all(|other| block.disjoint(*other))
    })
}

fn covers_storage(live: &[Block], free: &[Block], size: usize) -> bool {
    (RESERVED_WORDS..size)
        .all(|address| live.iter().chain(free).any(|block| block.contains(address)))
}

fn decode_words(words: &[Word]) -> Option<Vec<Ref>> {
    let terminator = words.iter().position(|word| *word == Word::ZERO)?;
    if !words[terminator..].iter().all(|word| *word == Word::ZERO) {
        return None;
    }
    words[..terminator]
        .iter()
        .copied()
        .map(Ref::new)
        .collect::<Result<Vec<_>, _>>()
        .ok()
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
