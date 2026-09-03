/// Untrusted flat storage for the fixed-word runtime.
///
/// Constructing an arena confers no logical authority. Use [`Checked::check`]
/// to validate allocator ownership and recover its abstract syntax.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Arena {
    pub(super) words: Vec<Word>,
    pub(super) free_root: Word,
    pub(super) roots: Vec<(Ref, Ref)>,
    /// Logical child counts, indexed only for live blocks.
    pub(super) lengths: Vec<u32>,
}

#[cfg(test)]
std::thread_local! {
    static PAYLOAD_SCANS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

impl Arena {
    /// Constructs untrusted arena storage without validating it.
    #[must_use]
    pub fn new(words: Vec<Word>, free_root: Word, roots: Vec<(Ref, Ref)>) -> Self {
        let length_slots = words.len().div_ceil(4);
        Self {
            words,
            free_root,
            roots,
            lengths: vec![u32::MAX; length_slots],
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

    /// Consumes the arena and returns its raw parts.
    #[cfg(test)]
    #[must_use]
    pub fn into_parts(self) -> (Vec<Word>, Word, Vec<(Ref, Ref)>) {
        (self.words, self.free_root, self.roots)
    }

    pub(super) fn word(&self, index: usize) -> Option<Word> {
        self.words.get(index).copied()
    }

    pub(super) fn pointer(word: Word) -> Option<usize> {
        if word.is_negative() || word.payload() == 0 || word.tag() != 0 {
            return None;
        }
        usize::try_from(word.base()).ok()
    }

    pub(super) fn optional_pointer(word: Word) -> Option<NullablePointer> {
        if word == Word::ZERO {
            Some(NullablePointer::Null)
        } else {
            Self::pointer(word).map(NullablePointer::Address)
        }
    }

    pub(super) fn natural(word: Word) -> Option<u32> {
        (!word.is_negative()).then(|| word.payload())
    }

    pub(super) fn header(&self, base: usize) -> Option<Header> {
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

    pub(super) fn zero_range(&self, start: usize, count: usize) -> bool {
        start
            .checked_add(count)
            .and_then(|stop| self.words.get(start..stop))
            .is_some_and(|words| words.iter().all(|word| *word == Word::ZERO))
    }

    pub(super) fn ordinary_node(&self, header: Header) -> bool {
        header
            .block
            .capacity()
            .is_some_and(|capacity| self.zero_range(header.block.base + 4, capacity - 4))
    }

    /// Walks one intrusive free ring, claiming every block it links.
    ///
    /// The claim replaces the former quadratic scan for a revisited base: a
    /// ring that returns to a block it already linked claims an address twice.
    pub(super) fn walk_ring(
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

    pub(super) fn directory_head(
        &self,
        root: Header,
        size_class: usize,
    ) -> Option<NullablePointer> {
        let address = root.block.base.checked_add(4)?.checked_add(size_class)?;
        Self::optional_pointer(self.word(address)?)
    }

    pub(super) fn root_padding(&self, root: Header) -> bool {
        root.block.capacity().is_some_and(|capacity| {
            let spare = capacity - 4;
            root.block.size_class <= spare
                && self.zero_range(
                    root.block.base + 4 + root.block.size_class,
                    spare - root.block.size_class,
                )
        })
    }

    pub(super) fn decode_free(&self, coverage: &mut Coverage) -> Option<Vec<Block>> {
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

    pub(super) fn live_block(&self, base: u32) -> Option<Block> {
        let base = usize::try_from(base).ok()?;
        let metadata = self.word(base)?.raw();
        let tag = u8::try_from(metadata & 3).ok()?;
        let size_class = usize::try_from((metadata >> 2) & CLASS_MASK).ok()?;
        let refcount = metadata >> 7;
        if tag >= 3 || size_class > MAX_SIZE_CLASS || refcount == 0 || refcount > REFCOUNT_MAX {
            return None;
        }
        let block = Block { base, size_class };
        block.fits(self.words.len()).then_some(block)
    }

    pub(super) fn live_tag(&self, base: u32) -> Option<u8> {
        self.live_block(base)?;
        Some((self.word(usize::try_from(base).ok()?)?.raw() & 3) as u8)
    }

    pub(super) fn live_refcount(&self, block: Block) -> Option<u32> {
        (self.live_block(u32::try_from(block.base).ok()?)? == block)
            .then(|| self.words[block.base].raw() >> 7)
    }

    pub(super) fn increment(&mut self, reference: Ref) -> Result<(), RuntimeError> {
        if reference.word().tag() == 3 {
            return Ok(());
        }
        let block = self
            .live_block(reference.word().base())
            .ok_or(RuntimeError::InvalidArena)?;
        let count = self
            .live_refcount(block)
            .ok_or(RuntimeError::InvalidArena)?;
        if count == REFCOUNT_MAX {
            return Err(RuntimeError::RefcountOverflow);
        }
        self.words[block.base] = Word::from_raw(self.words[block.base].raw() + (1 << 7));
        Ok(())
    }

    pub(super) fn live_metadata(
        tag: u8,
        size_class: usize,
        refcount: u32,
    ) -> Result<Word, RuntimeError> {
        if tag >= 3 || size_class > MAX_SIZE_CLASS || refcount == 0 || refcount > REFCOUNT_MAX {
            return Err(RuntimeError::ResourceBound {
                reason: "live block metadata overflow",
            });
        }
        Ok(Word::from_raw(
            (refcount << 7)
                | (u32::try_from(size_class).map_err(|_| RuntimeError::ResourceBound {
                    reason: "size class does not fit metadata",
                })? << 2)
                | u32::from(tag),
        ))
    }

    /// Borrows one live block's child references, without copying them.
    ///
    /// The payload is a nonzero prefix followed by a zero terminator and zero
    /// padding to the end of the block.
    pub(super) fn child_words(&self, block: Block) -> Option<&[Word]> {
        if self.live_block(u32::try_from(block.base).ok()?)? != block {
            return None;
        }
        let len = usize::try_from(*self.lengths.get(block.base / 4)?).ok()?;
        if len == usize::try_from(u32::MAX).ok()? {
            return None;
        }
        let start = block.base.checked_add(1)?;
        self.words.get(start..start.checked_add(len)?)
    }

    /// Reads and checks the zero-terminated payload during validation only.
    pub(super) fn scan_child_words(&self, block: Block) -> Option<&[Word]> {
        #[cfg(test)]
        PAYLOAD_SCANS.with(|count| count.set(count.get() + 1));
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

    #[cfg(test)]
    pub(super) fn reset_payload_scans() {
        PAYLOAD_SCANS.with(|count| count.set(0));
    }

    #[cfg(test)]
    pub(super) fn payload_scans() -> usize {
        PAYLOAD_SCANS.with(std::cell::Cell::get)
    }

    pub(super) fn child_len(&self, block: Block) -> Option<usize> {
        let len = *self.lengths.get(block.base / 4)?;
        (len != u32::MAX)
            .then(|| usize::try_from(len).ok())
            .flatten()
    }

    pub(super) fn set_child_len(&mut self, block: Block, len: usize) -> Result<(), RuntimeError> {
        let capacity = block.capacity().ok_or(RuntimeError::InvalidArena)?;
        if len.checked_add(1).is_none_or(|needed| needed >= capacity) {
            return Err(RuntimeError::InvalidArena);
        }
        let len = u32::try_from(len).map_err(|_| RuntimeError::ResourceBound {
            reason: "child count does not fit length index",
        })?;
        *self
            .lengths
            .get_mut(block.base / 4)
            .ok_or(RuntimeError::InvalidArena)? = len;
        Ok(())
    }

    pub(super) fn pointer_word(base: usize) -> Result<Word, RuntimeError> {
        let base = u32::try_from(base).map_err(|_| RuntimeError::ResourceBound {
            reason: "block base does not fit payload",
        })?;
        Ok(Word::pointer(base, false)?)
    }

    /// Appends a fresh live block. Reuse is handled by `take_free` first.
    pub(super) fn append_live(&mut self, size_class: usize) -> Result<Block, RuntimeError> {
        let base = self.words.len();
        let block = Block { base, size_class };
        let capacity = block.capacity().ok_or(RuntimeError::ResourceBound {
            reason: "block capacity exceeds host address space",
        })?;
        let stop = block.stop().ok_or(RuntimeError::ResourceBound {
            reason: "block address overflow",
        })?;
        Self::pointer_word(base)?;
        self.reserve_append_words(capacity)?;
        let length_stop = stop.div_ceil(4);
        self.words.resize(stop, Word::ZERO);
        self.lengths.resize(length_stop, u32::MAX);
        self.words[base] =
            Word::natural(
                u32::try_from(size_class).map_err(|_| RuntimeError::ResourceBound {
                    reason: "size class does not fit metadata",
                })?,
            )?;
        Ok(block)
    }

    /// Reserves coupled word and length-index growth before either is mutated.
    pub(super) fn reserve_append_words(&mut self, additional: usize) -> Result<(), RuntimeError> {
        let final_words =
            self.words
                .len()
                .checked_add(additional)
                .ok_or(RuntimeError::ResourceBound {
                    reason: "arena address overflow",
                })?;
        let final_slots = final_words.div_ceil(4);
        self.words
            .try_reserve(additional)
            .map_err(|_| RuntimeError::ResourceBound {
                reason: "arena allocation failed",
            })?;
        self.lengths
            .try_reserve(final_slots.saturating_sub(self.lengths.len()))
            .map_err(|_| RuntimeError::ResourceBound {
                reason: "length index allocation failed",
            })
    }

    pub(super) fn ring_head(&self, class: usize) -> Option<usize> {
        let root = Self::pointer(self.free_root)?;
        let root_header = self.header(root)?;
        match class.cmp(&root_header.block.size_class) {
            Ordering::Greater => None,
            Ordering::Equal => Some(root),
            Ordering::Less => match self.directory_head(root_header, class)? {
                NullablePointer::Null => None,
                NullablePointer::Address(base) => Some(base),
            },
        }
    }

    pub(super) fn set_directory(
        &mut self,
        root: Block,
        class: usize,
        head: Option<usize>,
    ) -> Result<(), RuntimeError> {
        let slot = root
            .base
            .checked_add(4)
            .and_then(|base| base.checked_add(class))
            .ok_or(RuntimeError::ResourceBound {
                reason: "directory address overflow",
            })?;
        self.words[slot] = match head {
            Some(base) => Self::pointer_word(base)?,
            None => Word::ZERO,
        };
        Ok(())
    }

    pub(super) fn unlink_free(&mut self, block: Block) -> Result<(), RuntimeError> {
        let header = self.header(block.base).ok_or(RuntimeError::InvalidArena)?;
        let root_base = Self::pointer(self.free_root).ok_or(RuntimeError::InvalidArena)?;
        if block.base == root_base {
            return Err(RuntimeError::InvalidArena);
        }
        self.words[header.prev + 1] = Self::pointer_word(header.next)?;
        self.words[header.next + 2] = Self::pointer_word(header.prev)?;
        let root = self
            .header(root_base)
            .ok_or(RuntimeError::InvalidArena)?
            .block;
        if self.ring_head(block.size_class) == Some(block.base) {
            self.set_directory(
                root,
                block.size_class,
                (header.next != block.base).then_some(header.next),
            )?;
        }
        self.words[block.base..block.stop().ok_or(RuntimeError::InvalidArena)?].fill(Word::ZERO);
        self.words[block.base] = Word::natural(
            u32::try_from(block.size_class).map_err(|_| RuntimeError::InvalidArena)?,
        )?;
        Ok(())
    }

    pub(super) fn take_free(&mut self, size_class: usize) -> Result<Option<Block>, RuntimeError> {
        let Some(head) = self.ring_head(size_class) else {
            return Ok(None);
        };
        let root = Self::pointer(self.free_root).ok_or(RuntimeError::InvalidArena)?;
        // `free_root` owns the class directory and is never handed to callers.
        // If it is the only largest-class member, allocation appends instead.
        let selected = if head == root {
            let next = self.header(root).ok_or(RuntimeError::InvalidArena)?.next;
            if next == root {
                return Ok(None);
            }
            next
        } else {
            head
        };
        let block = self
            .header(selected)
            .ok_or(RuntimeError::InvalidArena)?
            .block;
        self.unlink_free(block)?;
        Ok(Some(block))
    }

    pub(super) fn allocate(&mut self, size_class: usize) -> Result<Block, RuntimeError> {
        if let Some(block) = self.take_free(size_class)? {
            Ok(block)
        } else {
            self.append_live(size_class)
        }
    }

    pub(super) fn initialize_free(&mut self, block: Block) -> Result<(), RuntimeError> {
        self.words[block.base..block.stop().ok_or(RuntimeError::InvalidArena)?].fill(Word::ZERO);
        let pointer = Self::pointer_word(block.base)?;
        self.words[block.base + 1] = pointer;
        self.words[block.base + 2] = pointer;
        self.words[block.base + 3] = Word::natural(
            u32::try_from(block.size_class).map_err(|_| RuntimeError::InvalidArena)?,
        )?;
        Ok(())
    }

    pub(super) fn free(&mut self, block: Block) -> Result<(), RuntimeError> {
        *self
            .lengths
            .get_mut(block.base / 4)
            .ok_or(RuntimeError::InvalidArena)? = u32::MAX;
        let old_root = Self::optional_pointer(self.free_root).ok_or(RuntimeError::InvalidArena)?;
        let NullablePointer::Address(root_base) = old_root else {
            self.initialize_free(block)?;
            self.free_root = Self::pointer_word(block.base)?;
            return Ok(());
        };
        let root = self
            .header(root_base)
            .ok_or(RuntimeError::InvalidArena)?
            .block;
        if block.size_class > root.size_class {
            let mut heads = Vec::with_capacity(root.size_class);
            for class in 0..root.size_class {
                heads.push(self.ring_head(class));
            }
            // The old root becomes an ordinary member of its class.
            self.words[root.base + 4..root.stop().ok_or(RuntimeError::InvalidArena)?]
                .fill(Word::ZERO);
            self.initialize_free(block)?;
            self.free_root = Self::pointer_word(block.base)?;
            for (class, head) in heads.into_iter().enumerate() {
                self.set_directory(block, class, head)?;
            }
            // The old largest-class ring remains linked. It becomes one
            // directory entry of the new, larger root without reinsertion.
            self.set_directory(block, root.size_class, Some(root.base))?;
            return Ok(());
        }
        self.initialize_free(block)?;
        self.insert_free_ordinary(block)
    }

    pub(super) fn insert_free_ordinary(&mut self, block: Block) -> Result<(), RuntimeError> {
        let root_base = Self::pointer(self.free_root).ok_or(RuntimeError::InvalidArena)?;
        let root = self
            .header(root_base)
            .ok_or(RuntimeError::InvalidArena)?
            .block;
        let head = self.ring_head(block.size_class);
        let anchor = head.unwrap_or(block.base);
        if let Some(head) = head {
            let prev = self.header(head).ok_or(RuntimeError::InvalidArena)?.prev;
            self.words[block.base + 1] = Self::pointer_word(head)?;
            self.words[block.base + 2] = Self::pointer_word(prev)?;
            self.words[prev + 1] = Self::pointer_word(block.base)?;
            self.words[head + 2] = Self::pointer_word(block.base)?;
        } else {
            let pointer = Self::pointer_word(block.base)?;
            self.words[block.base + 1] = pointer;
            self.words[block.base + 2] = pointer;
        }
        if block.size_class < root.size_class && head.is_none() {
            self.set_directory(root, block.size_class, Some(anchor))?;
        }
        Ok(())
    }

    pub(super) fn partition_live(
        &self,
        coverage: &mut Coverage,
    ) -> Result<Vec<Block>, RuntimeError> {
        let mut live = Vec::new();
        let mut base = RESERVED_WORDS;
        while base < self.words.len() {
            let block = if self.words[base] == Word::ZERO {
                self.header(base).ok_or(RuntimeError::InvalidArena)?.block
            } else {
                self.live_block(u32::try_from(base).map_err(|_| RuntimeError::InvalidArena)?)
                    .ok_or(RuntimeError::InvalidArena)?
            };
            if block.base != base {
                return Err(RuntimeError::InvalidArena);
            }
            if self.words[base] != Word::ZERO {
                if !coverage.claim(block) {
                    return Err(RuntimeError::InvalidArena);
                }
                live.push(block);
            } else if !coverage.contains(base) {
                return Err(RuntimeError::InvalidArena);
            }
            base = block.stop().ok_or(RuntimeError::InvalidArena)?;
        }
        if base != self.words.len() || !coverage.complete() {
            return Err(RuntimeError::InvalidArena);
        }
        Ok(live)
    }

    pub(super) fn validate_graph(&self) -> Result<(), RuntimeError> {
        if !self.zero_range(0, RESERVED_WORDS) {
            return Err(RuntimeError::InvalidArena);
        }
        let mut coverage = Coverage::new(self.words.len());
        self.decode_free(&mut coverage)
            .ok_or(RuntimeError::InvalidArena)?;
        let live = self.partition_live(&mut coverage)?;

        let indexed = self.lengths.iter().filter(|len| **len != u32::MAX).count();
        if indexed != 0
            && (indexed != live.len()
                || live.iter().any(|block| {
                    self.scan_child_words(*block)
                        .and_then(|words| u32::try_from(words.len()).ok())
                        != self.lengths.get(block.base / 4).copied()
                }))
        {
            return Err(RuntimeError::InvalidArena);
        }

        let mut incoming = HashMap::<usize, u32>::new();
        for &(left, right) in &self.roots {
            for reference in [left, right] {
                if reference.word().tag() != 3 {
                    let count = incoming
                        .entry(
                            usize::try_from(reference.word().base())
                                .map_err(|_| RuntimeError::InvalidArena)?,
                        )
                        .or_insert(0);
                    *count = count.checked_add(1).ok_or(RuntimeError::InvalidArena)?;
                }
            }
        }
        for block in &live {
            for word in self
                .scan_child_words(*block)
                .ok_or(RuntimeError::InvalidArena)?
            {
                let reference = Ref::new(*word).map_err(|_| RuntimeError::InvalidArena)?;
                if reference.word().tag() != 3 {
                    self.live_block(reference.word().base())
                        .ok_or(RuntimeError::InvalidArena)?;
                    let count = incoming
                        .entry(
                            usize::try_from(reference.word().base())
                                .map_err(|_| RuntimeError::InvalidArena)?,
                        )
                        .or_insert(0);
                    *count = count.checked_add(1).ok_or(RuntimeError::InvalidArena)?;
                }
            }
        }
        for block in &live {
            let count = incoming.get(&block.base).copied().unwrap_or(0);
            if self
                .live_refcount(*block)
                .is_none_or(|stored| stored < count)
            {
                return Err(RuntimeError::InvalidArena);
            }
        }

        let mut colors = HashMap::<usize, u8>::new();
        let mut stack = Vec::new();
        for &(left, right) in &self.roots {
            stack.push((right, false));
            stack.push((left, false));
        }
        while let Some((reference, exiting)) = stack.pop() {
            let word = reference.word();
            if word.tag() == 3 {
                continue;
            }
            if word.tag() != 0 {
                return Err(RuntimeError::InvalidArena);
            }
            let base = usize::try_from(word.base()).map_err(|_| RuntimeError::InvalidArena)?;
            if exiting {
                colors.insert(base, 2);
                continue;
            }
            match colors.get(&base).copied() {
                Some(1) => return Err(RuntimeError::InvalidArena),
                Some(2) => continue,
                _ => {}
            }
            let block = self
                .live_block(word.base())
                .ok_or(RuntimeError::InvalidArena)?;
            let children = self
                .scan_child_words(block)
                .ok_or(RuntimeError::InvalidArena)?;
            colors.insert(base, 1);
            stack.push((reference, true));
            for child in children.iter().rev() {
                stack.push((
                    Ref::new(*child).map_err(|_| RuntimeError::InvalidArena)?,
                    false,
                ));
            }
        }
        Ok(())
    }

    /// Validates this arena and materializes its sequent table in one pass.
    ///
    /// The fold stack is the nesting, so nothing recurses: a completed formula
    /// is pushed into the frame that was waiting for it, and a completed frame
    /// becomes a formula in turn.
    pub(super) fn decode_table(&self) -> Result<Vec<Sequent>, RuntimeError> {
        self.validate_graph()?;
        let mut walk = Expand::new(self);
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

use super::{
    Block, CLASS_MASK, Coverage, Expand, Formula, Frame, HashMap, Header, MAX_SIZE_CLASS,
    NullablePointer, Ordering, PAYLOAD_WIDTH, REFCOUNT_MAX, RESERVED_WORDS, Ref, RuntimeError,
    Sequent, Word, node,
};
