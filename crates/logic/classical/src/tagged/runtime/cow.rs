impl Checked {
    pub(super) fn root(&self, index: usize, side: Side) -> Option<Ref> {
        let roots = self.arena.roots.get(index)?;
        Some(match side {
            Side::Left => roots.0,
            Side::Right => roots.1,
        })
    }

    pub(super) fn child_range(&self, reference: Ref) -> Option<std::ops::Range<usize>> {
        let block = self.arena.live_block(reference.word().base())?;
        let children = self.arena.child_words(block)?;
        let start = block.base + 1;
        Some(start..start + children.len())
    }

    pub(super) fn build_owned(&mut self, formula: &Formula) -> Result<Ref, RuntimeError> {
        enum Task<'a> {
            Visit(&'a Formula),
            Finish {
                tag: u8,
                negative: bool,
                children: usize,
            },
        }
        let mut tasks = vec![Task::Visit(formula)];
        let mut built = Vec::<Ref>::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Formula::Literal { atom, negative }) => {
                    built.push(Ref::new(Word::literal(*atom, *negative)?)?);
                }
                Task::Visit(formula) => {
                    let (tag, negative, children) = match formula {
                        Formula::And { negative, children } => (0, *negative, children),
                        Formula::Or { negative, children } => (1, *negative, children),
                        Formula::Sat { negative, children } => (2, *negative, children),
                        Formula::Literal { .. } => unreachable!(),
                    };
                    tasks.push(Task::Finish {
                        tag,
                        negative,
                        children: children.len(),
                    });
                    tasks.extend(children.iter().rev().map(Task::Visit));
                }
                Task::Finish {
                    tag,
                    negative,
                    children,
                } => {
                    let first = built
                        .len()
                        .checked_sub(children)
                        .ok_or(RuntimeError::InvalidArena)?;
                    let class = least_size_class(children)?;
                    let block = self.arena.allocate(class)?;
                    for (index, child) in built.drain(first..).enumerate() {
                        self.arena.words[block.base + 1 + index] = child.word();
                    }
                    self.arena.words[block.base] = Arena::live_metadata(tag, class, 1)?;
                    self.arena.set_child_len(block, children)?;
                    let base =
                        u32::try_from(block.base).map_err(|_| RuntimeError::ResourceBound {
                            reason: "block base does not fit payload",
                        })?;
                    built.push(Ref::new(Word::pointer(base, negative)?)?);
                }
            }
        }
        built
            .pop()
            .filter(|_| built.is_empty())
            .ok_or(RuntimeError::InvalidArena)
    }

    pub(super) fn prepare_owned(&mut self, formula: &Formula) -> Result<(), RuntimeError> {
        let mut pending = vec![formula];
        let mut appended = 0_usize;
        while let Some(formula) = pending.pop() {
            match formula {
                Formula::Literal { atom, negative } => {
                    Word::literal(*atom, *negative)?;
                }
                Formula::And { children, .. }
                | Formula::Or { children, .. }
                | Formula::Sat { children, .. } => {
                    let class = least_size_class(children.len())?;
                    let capacity = Block {
                        base: RESERVED_WORDS,
                        size_class: class,
                    }
                    .capacity()
                    .ok_or(RuntimeError::ResourceBound {
                        reason: "block capacity exceeds host address space",
                    })?;
                    appended =
                        appended
                            .checked_add(capacity)
                            .ok_or(RuntimeError::ResourceBound {
                                reason: "formula storage overflow",
                            })?;
                    pending.extend(children);
                }
            }
        }
        let final_len =
            self.arena
                .words
                .len()
                .checked_add(appended)
                .ok_or(RuntimeError::ResourceBound {
                    reason: "arena address overflow",
                })?;
        if final_len
            > usize::try_from(1_u64 << PAYLOAD_WIDTH).map_err(|_| RuntimeError::ResourceBound {
                reason: "host address space is too small",
            })?
        {
            return Err(RuntimeError::ResourceBound {
                reason: "arena exceeds word payload",
            });
        }
        self.arena.reserve_append_words(appended)?;
        Ok(())
    }

    pub(super) fn grow_array(&mut self, reference: Ref) -> Result<Ref, RuntimeError> {
        let old = self
            .arena
            .live_block(reference.word().base())
            .ok_or(RuntimeError::InvalidArena)?;
        let new_class = old
            .size_class
            .checked_add(1)
            .ok_or(RuntimeError::ResourceBound {
                reason: "size class overflow",
            })?;
        let new = self.arena.allocate(new_class)?;
        let len = self
            .arena
            .child_len(old)
            .ok_or(RuntimeError::InvalidArena)?;
        self.arena
            .words
            .copy_within(old.base + 1..old.base + 1 + len, new.base + 1);
        let base = u32::try_from(new.base).map_err(|_| RuntimeError::ResourceBound {
            reason: "block base does not fit payload",
        })?;
        let tag = self
            .arena
            .live_tag(reference.word().base())
            .ok_or(RuntimeError::InvalidArena)?;
        self.arena.words[new.base] = Arena::live_metadata(tag, new_class, 1)?;
        self.arena.set_child_len(new, len)?;
        let moved = Ref::new(Word::pointer(base, reference.word().is_negative())?)?;
        self.arena.free(old)?;
        Ok(moved)
    }

    pub(super) fn make_root_unique(
        &mut self,
        index: usize,
        side: Side,
    ) -> Result<Ref, RuntimeError> {
        let reference = self.root(index, side).ok_or(RuntimeError::Index)?;
        let block = self
            .arena
            .live_block(reference.word().base())
            .ok_or(RuntimeError::Shape)?;
        if self
            .arena
            .live_refcount(block)
            .ok_or(RuntimeError::InvalidArena)?
            == 1
        {
            return Ok(reference);
        }
        self.prepare_cow_root(index, side)?;
        let children = self
            .arena
            .child_words(block)
            .ok_or(RuntimeError::InvalidArena)?
            .to_vec();
        let replacement = self.arena.allocate(block.size_class)?;
        let tag = self
            .arena
            .live_tag(reference.word().base())
            .ok_or(RuntimeError::InvalidArena)?;
        self.arena.words[replacement.base] = Arena::live_metadata(tag, block.size_class, 1)?;
        self.arena.set_child_len(replacement, children.len())?;
        for (offset, word) in children.into_iter().enumerate() {
            self.arena.increment(Ref::new(word)?)?;
            self.arena.words[replacement.base + 1 + offset] = word;
        }
        self.arena.words[block.base] =
            Word::from_raw(self.arena.words[block.base].raw() - (1 << 7));
        let base = u32::try_from(replacement.base).map_err(|_| RuntimeError::ResourceBound {
            reason: "block base does not fit payload",
        })?;
        let replacement = Ref::new(Word::pointer(base, reference.word().is_negative())?)?;
        let roots = self.arena.roots.get_mut(index).ok_or(RuntimeError::Index)?;
        match side {
            Side::Left => roots.0 = replacement,
            Side::Right => roots.1 = replacement,
        }
        Ok(replacement)
    }

    pub(super) fn prepare_cow_root(
        &mut self,
        index: usize,
        side: Side,
    ) -> Result<(), RuntimeError> {
        let reference = self.root(index, side).ok_or(RuntimeError::Index)?;
        let block = self
            .arena
            .live_block(reference.word().base())
            .ok_or(RuntimeError::Shape)?;
        if self
            .arena
            .live_refcount(block)
            .ok_or(RuntimeError::InvalidArena)?
            == 1
        {
            return Ok(());
        }
        let mut increments = HashMap::<usize, u32>::new();
        for word in self
            .arena
            .child_words(block)
            .ok_or(RuntimeError::InvalidArena)?
        {
            let child = Ref::new(*word)?;
            if child.word().tag() == 3 {
                continue;
            }
            let child_block = self
                .arena
                .live_block(child.word().base())
                .ok_or(RuntimeError::InvalidArena)?;
            let increment = increments.entry(child_block.base).or_insert(0);
            *increment = increment
                .checked_add(1)
                .ok_or(RuntimeError::RefcountOverflow)?;
        }
        for (base, additions) in increments {
            let child = self
                .arena
                .live_block(u32::try_from(base).map_err(|_| RuntimeError::InvalidArena)?)
                .ok_or(RuntimeError::InvalidArena)?;
            let count = self
                .arena
                .live_refcount(child)
                .ok_or(RuntimeError::InvalidArena)?;
            if count
                .checked_add(additions)
                .is_none_or(|sum| sum > REFCOUNT_MAX)
            {
                return Err(RuntimeError::RefcountOverflow);
            }
        }
        self.arena
            .reserve_append_words(block.capacity().ok_or(RuntimeError::InvalidArena)?)?;
        Ok(())
    }

    pub(super) fn clone_shared(&mut self, reference: Ref) -> Result<Ref, RuntimeError> {
        let block = self
            .arena
            .live_block(reference.word().base())
            .ok_or(RuntimeError::Shape)?;
        let count = self
            .arena
            .live_refcount(block)
            .ok_or(RuntimeError::InvalidArena)?;
        if count == 1 {
            return Ok(reference);
        }
        let children = self
            .arena
            .child_words(block)
            .ok_or(RuntimeError::InvalidArena)?
            .to_vec();
        let mut increments = HashMap::<usize, u32>::new();
        for word in &children {
            let child = Ref::new(*word)?;
            if child.word().tag() != 3 {
                let entry = increments
                    .entry(
                        usize::try_from(child.word().base())
                            .map_err(|_| RuntimeError::InvalidArena)?,
                    )
                    .or_insert(0);
                *entry = entry.checked_add(1).ok_or(RuntimeError::RefcountOverflow)?;
            }
        }
        for (base, additions) in increments {
            let child = self
                .arena
                .live_block(u32::try_from(base).map_err(|_| RuntimeError::InvalidArena)?)
                .ok_or(RuntimeError::InvalidArena)?;
            let child_count = self
                .arena
                .live_refcount(child)
                .ok_or(RuntimeError::InvalidArena)?;
            if child_count
                .checked_add(additions)
                .is_none_or(|sum| sum > REFCOUNT_MAX)
            {
                return Err(RuntimeError::RefcountOverflow);
            }
        }
        self.arena
            .reserve_append_words(block.capacity().ok_or(RuntimeError::InvalidArena)?)?;
        let replacement = self.arena.allocate(block.size_class)?;
        let tag = self
            .arena
            .live_tag(reference.word().base())
            .ok_or(RuntimeError::InvalidArena)?;
        self.arena.words[replacement.base] = Arena::live_metadata(tag, block.size_class, 1)?;
        self.arena.set_child_len(replacement, children.len())?;
        for (offset, word) in children.into_iter().enumerate() {
            self.arena.increment(Ref::new(word)?)?;
            self.arena.words[replacement.base + 1 + offset] = word;
        }
        self.arena.words[block.base] =
            Word::from_raw(self.arena.words[block.base].raw() - (1 << 7));
        let base = u32::try_from(replacement.base).map_err(|_| RuntimeError::ResourceBound {
            reason: "block base does not fit payload",
        })?;
        Ok(Ref::new(Word::pointer(
            base,
            reference.word().is_negative(),
        )?)?)
    }

    pub(super) fn make_path_unique(&mut self, path: &FormulaPath) -> Result<Ref, RuntimeError> {
        self.prepare_path_cow_with(path, &[])?;
        self.make_path_unique_inner(path)
    }

    pub(super) fn prepare_path_cow_with(
        &mut self,
        path: &FormulaPath,
        extra_increments: &[Word],
    ) -> Result<(), RuntimeError> {
        let mut current = self
            .root(path.sequent(), path.side())
            .ok_or(RuntimeError::Index)?;
        let mut cloning = false;
        let mut reserve = 0_usize;
        let mut additions = HashMap::<usize, u32>::new();
        for word in extra_increments {
            let child = Ref::new(*word)?;
            if child.word().tag() != 3 {
                let base =
                    usize::try_from(child.word().base()).map_err(|_| RuntimeError::InvalidArena)?;
                let entry = additions.entry(base).or_insert(0);
                *entry = entry.checked_add(1).ok_or(RuntimeError::RefcountOverflow)?;
            }
        }
        for depth in 0..=path.children().len() {
            if current.word().tag() == 3 {
                return if depth == path.children().len() {
                    Ok(())
                } else {
                    Err(RuntimeError::Shape)
                };
            }
            let block = self
                .arena
                .live_block(current.word().base())
                .ok_or(RuntimeError::Shape)?;
            cloning |= self
                .arena
                .live_refcount(block)
                .is_some_and(|count| count > 1);
            if cloning {
                reserve = reserve
                    .checked_add(block.capacity().ok_or(RuntimeError::InvalidArena)?)
                    .ok_or(RuntimeError::ResourceBound {
                        reason: "path copy capacity overflow",
                    })?;
                for word in self
                    .arena
                    .child_words(block)
                    .ok_or(RuntimeError::InvalidArena)?
                {
                    let child = Ref::new(*word)?;
                    if child.word().tag() != 3 {
                        let base = usize::try_from(child.word().base())
                            .map_err(|_| RuntimeError::InvalidArena)?;
                        let entry = additions.entry(base).or_insert(0);
                        *entry = entry.checked_add(1).ok_or(RuntimeError::RefcountOverflow)?;
                    }
                }
            }
            let Some(&index) = path.children().get(depth) else {
                break;
            };
            let range = self.child_range(current).ok_or(RuntimeError::Shape)?;
            let slot = range
                .start
                .checked_add(index)
                .filter(|slot| *slot < range.end)
                .ok_or(RuntimeError::Index)?;
            current = Ref::new(self.arena.words[slot])?;
        }
        for (base, count) in additions {
            let block = self
                .arena
                .live_block(u32::try_from(base).map_err(|_| RuntimeError::InvalidArena)?)
                .ok_or(RuntimeError::InvalidArena)?;
            if self
                .arena
                .live_refcount(block)
                .and_then(|stored| stored.checked_add(count))
                .is_none_or(|sum| sum > REFCOUNT_MAX)
            {
                return Err(RuntimeError::RefcountOverflow);
            }
        }
        self.arena.reserve_append_words(reserve)?;
        Ok(())
    }

    pub(super) fn make_path_unique_inner(
        &mut self,
        path: &FormulaPath,
    ) -> Result<Ref, RuntimeError> {
        let mut current = self.make_root_unique(path.sequent(), path.side())?;
        for &index in path.children() {
            let range = self.child_range(current).ok_or(RuntimeError::Shape)?;
            let slot = range
                .start
                .checked_add(index)
                .filter(|slot| *slot < range.end)
                .ok_or(RuntimeError::Index)?;
            let child = Ref::new(self.arena.words[slot])?;
            let unique = if child.word().tag() == 3 {
                child
            } else {
                self.clone_shared(child)?
            };
            self.arena.words[slot] = unique.word();
            current = unique;
        }
        Ok(current)
    }

    pub(super) fn replace_path_reference(
        &mut self,
        path: &FormulaPath,
        replacement: Ref,
    ) -> Result<(), RuntimeError> {
        if path.children().is_empty() {
            let roots = self
                .arena
                .roots
                .get_mut(path.sequent())
                .ok_or(RuntimeError::Index)?;
            match path.side() {
                Side::Left => roots.0 = replacement,
                Side::Right => roots.1 = replacement,
            }
            return Ok(());
        }
        let parent_path = FormulaPath::new(
            path.sequent(),
            path.side(),
            path.children()[..path.children().len() - 1].to_vec(),
        );
        let parent = self.resolve_path(&parent_path)?;
        let range = self.child_range(parent).ok_or(RuntimeError::Shape)?;
        let index = *path.children().last().ok_or(RuntimeError::Index)?;
        let slot = range
            .start
            .checked_add(index)
            .filter(|slot| *slot < range.end)
            .ok_or(RuntimeError::Index)?;
        self.arena.words[slot] = replacement.word();
        Ok(())
    }

    pub(super) fn resolve_path(&self, path: &FormulaPath) -> Result<Ref, RuntimeError> {
        let mut current = self
            .root(path.sequent(), path.side())
            .ok_or(RuntimeError::Index)?;
        for &index in path.children() {
            let range = self.child_range(current).ok_or(RuntimeError::Shape)?;
            let slot = range
                .start
                .checked_add(index)
                .filter(|slot| *slot < range.end)
                .ok_or(RuntimeError::Index)?;
            current = Ref::new(self.arena.words[slot])?;
        }
        Ok(current)
    }
}
use super::{
    Arena, Block, Checked, Formula, FormulaPath, HashMap, PAYLOAD_WIDTH, REFCOUNT_MAX,
    RESERVED_WORDS, Ref, RuntimeError, Side, Word, least_size_class,
};
