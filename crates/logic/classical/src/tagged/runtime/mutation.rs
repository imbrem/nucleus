impl Checked {
    pub(crate) fn demorgan_path(&mut self, path: &FormulaPath) -> Result<(), RuntimeError> {
        let reference = self.make_path_unique(path)?;
        if !reference.word().is_negative() {
            return Err(RuntimeError::Shape);
        }
        let block = self
            .arena
            .live_block(reference.word().base())
            .ok_or(RuntimeError::Shape)?;
        let tag = self
            .arena
            .live_tag(reference.word().base())
            .ok_or(RuntimeError::Shape)?;
        let replacement_tag = match tag {
            0 => 1,
            1 => 0,
            _ => return Err(RuntimeError::Shape),
        };
        let range = self.child_range(reference).ok_or(RuntimeError::Shape)?;
        for word in &mut self.arena.words[range] {
            *word = word.negated();
        }
        self.arena.words[block.base] = Arena::live_metadata(replacement_tag, block.size_class, 1)?;
        self.replace_path_reference(
            path,
            Ref::new(Word::pointer(reference.word().base(), false)?)?,
        )
    }

    pub(crate) fn permute_path(
        &mut self,
        path: &FormulaPath,
        order: &[usize],
    ) -> Result<(), RuntimeError> {
        let original = self.resolve_path(path)?;
        let original_range = self.child_range(original).ok_or(RuntimeError::Shape)?;
        if order.len() != original_range.len() {
            return Err(RuntimeError::Index);
        }
        let mut used = vec![false; order.len()];
        for &source in order {
            let slot = used.get_mut(source).ok_or(RuntimeError::Index)?;
            if *slot {
                return Err(RuntimeError::Index);
            }
            *slot = true;
        }
        let reference = self.make_path_unique(path)?;
        let range = self.child_range(reference).ok_or(RuntimeError::Shape)?;
        let old = self.arena.words[range.clone()].to_vec();
        for (destination, &source) in order.iter().enumerate() {
            self.arena.words[range.start + destination] = old[source];
        }
        Ok(())
    }

    pub(crate) fn dedup_local_path(
        &mut self,
        path: &FormulaPath,
        remove: usize,
        retain: usize,
    ) -> Result<(), RuntimeError> {
        let reference = self.make_path_unique(path)?;
        let range = self.child_range(reference).ok_or(RuntimeError::Shape)?;
        if remove == retain || remove >= range.len() || retain >= range.len() {
            return Err(RuntimeError::Index);
        }
        let removed = Ref::new(self.arena.words[range.start + remove])?;
        let retained = Ref::new(self.arena.words[range.start + retain])?;
        let equal = FormulaView {
            checked: self,
            reference: removed,
        }
        .structural_eq(FormulaView {
            checked: self,
            reference: retained,
        });
        if !equal {
            return Err(RuntimeError::Shape);
        }
        self.arena
            .words
            .copy_within(range.start + remove + 1..range.end, range.start + remove);
        self.arena.words[range.end - 1] = Word::ZERO;
        let block = self
            .arena
            .live_block(reference.word().base())
            .ok_or(RuntimeError::Shape)?;
        self.arena.set_child_len(block, range.len() - 1)?;
        self.reclaim(removed)
    }

    pub(crate) fn contradiction_path(
        &mut self,
        path: &FormulaPath,
        first: usize,
        second: usize,
    ) -> Result<(), RuntimeError> {
        let reference = self.make_path_unique(path)?;
        self.arena
            .live_block(reference.word().base())
            .ok_or(RuntimeError::Shape)?;
        let range = self.child_range(reference).ok_or(RuntimeError::Shape)?;
        if first == second || first >= range.len() || second >= range.len() {
            return Err(RuntimeError::Index);
        }
        let left = Ref::new(self.arena.words[range.start + first])?;
        let right = Ref::new(self.arena.words[range.start + second])?;
        let complements = left.word().is_negative() != right.word().is_negative()
            && (FormulaView {
                checked: self,
                reference: left,
            })
            .structural_eq(FormulaView {
                checked: self,
                reference: Ref::new(right.word().negated())?,
            });
        if !complements {
            return Err(RuntimeError::Shape);
        }
        let tag = self
            .arena
            .live_tag(reference.word().base())
            .ok_or(RuntimeError::Shape)?;
        let constant_tag = match tag {
            1 => 0,
            0 | 2 => 1,
            _ => return Err(RuntimeError::Shape),
        };
        let replacement_block = self.arena.allocate(0)?;
        self.arena.words[replacement_block.base] = Arena::live_metadata(constant_tag, 0, 1)?;
        self.arena.set_child_len(replacement_block, 0)?;
        let base =
            u32::try_from(replacement_block.base).map_err(|_| RuntimeError::ResourceBound {
                reason: "block base does not fit payload",
            })?;
        let replacement = Ref::new(Word::pointer(base, reference.word().is_negative())?)?;
        self.replace_path_reference(path, replacement)?;
        self.reclaim(reference)
    }

    pub(crate) fn flatten_path(
        &mut self,
        path: &FormulaPath,
        child_index: usize,
    ) -> Result<(), RuntimeError> {
        let needed_class = self.prepare_flatten(path, child_index)?;
        let mut parent = self.make_path_unique_inner(path)?;
        let parent_tag = self
            .arena
            .live_tag(parent.word().base())
            .ok_or(RuntimeError::Shape)?;
        let parent_range = self.child_range(parent).ok_or(RuntimeError::Shape)?;
        let child_slot = parent_range
            .start
            .checked_add(child_index)
            .filter(|slot| *slot < parent_range.end)
            .ok_or(RuntimeError::Index)?;
        let nested = Ref::new(self.arena.words[child_slot])?;
        let nested_block = self
            .arena
            .live_block(nested.word().base())
            .ok_or(RuntimeError::Shape)?;
        let nested_children = self
            .arena
            .child_words(nested_block)
            .ok_or(RuntimeError::Shape)?
            .to_vec();
        let parent_block = self
            .arena
            .live_block(parent.word().base())
            .ok_or(RuntimeError::Shape)?;
        if needed_class > parent_block.size_class {
            let old_children = self
                .arena
                .child_words(parent_block)
                .ok_or(RuntimeError::Shape)?
                .to_vec();
            let replacement = self.arena.allocate(needed_class)?;
            self.arena.words[replacement.base] = Arena::live_metadata(parent_tag, needed_class, 1)?;
            self.arena.set_child_len(replacement, old_children.len())?;
            for (offset, word) in old_children.into_iter().enumerate() {
                self.arena.words[replacement.base + 1 + offset] = word;
            }
            let base =
                u32::try_from(replacement.base).map_err(|_| RuntimeError::ResourceBound {
                    reason: "block base does not fit payload",
                })?;
            let replacement = Ref::new(Word::pointer(base, parent.word().is_negative())?)?;
            self.replace_path_reference(path, replacement)?;
            self.arena.free(parent_block)?;
            parent = replacement;
        }
        let range = self.child_range(parent).ok_or(RuntimeError::Shape)?;
        let mut replacement = self.arena.words[range.clone()].to_vec();
        replacement.splice(child_index..=child_index, nested_children.iter().copied());
        for word in &nested_children {
            self.arena.increment(Ref::new(*word)?)?;
        }
        self.arena.words[range.start..range.start + replacement.len()]
            .copy_from_slice(&replacement);
        let parent_block = self
            .arena
            .live_block(parent.word().base())
            .ok_or(RuntimeError::Shape)?;
        self.arena.words[range.start + replacement.len()
            ..parent_block.stop().ok_or(RuntimeError::InvalidArena)?]
            .fill(Word::ZERO);
        self.arena.set_child_len(parent_block, replacement.len())?;
        self.reclaim(nested)
    }

    fn prepare_flatten(
        &mut self,
        path: &FormulaPath,
        child_index: usize,
    ) -> Result<usize, RuntimeError> {
        let original_parent = self.resolve_path(path)?;
        let original_range = self
            .child_range(original_parent)
            .ok_or(RuntimeError::Shape)?;
        let original_slot = original_range
            .start
            .checked_add(child_index)
            .filter(|slot| *slot < original_range.end)
            .ok_or(RuntimeError::Index)?;
        let original_nested = Ref::new(self.arena.words[original_slot])?;
        if original_nested.word().tag() == 3 || original_nested.word().is_negative() {
            return Err(RuntimeError::Shape);
        }
        let original_parent_tag = self
            .arena
            .live_tag(original_parent.word().base())
            .ok_or(RuntimeError::Shape)?;
        let original_nested_tag = self
            .arena
            .live_tag(original_nested.word().base())
            .ok_or(RuntimeError::Shape)?;
        if !matches!(
            (original_parent_tag, original_nested_tag),
            (0 | 2, 0) | (1, 1)
        ) {
            return Err(RuntimeError::Shape);
        }
        let original_nested_block = self
            .arena
            .live_block(original_nested.word().base())
            .ok_or(RuntimeError::Shape)?;
        let extra_increments = self
            .arena
            .child_words(original_nested_block)
            .ok_or(RuntimeError::Shape)?
            .to_vec();
        let new_len = original_range
            .len()
            .checked_sub(1)
            .and_then(|len| len.checked_add(extra_increments.len()))
            .ok_or(RuntimeError::ResourceBound {
                reason: "flattened child count overflow",
            })?;
        let needed_class = least_size_class(new_len)?;
        self.prepare_path_cow_with(path, &extra_increments)?;
        Ok(needed_class)
    }

    pub(crate) fn push_root(
        &mut self,
        index: usize,
        side: Side,
        formula: &Formula,
    ) -> Result<(), RuntimeError> {
        self.root(index, side).ok_or(RuntimeError::Index)?;
        self.prepare_cow_root(index, side)?;
        self.prepare_owned(formula)?;
        self.ensure_root_push_capacity(index, side)?;
        let pushed = self.build_owned(formula)?;
        self.push_root_ref(index, side, pushed)?;
        Ok(())
    }

    pub(super) fn push_root_ref(
        &mut self,
        index: usize,
        side: Side,
        pushed: Ref,
    ) -> Result<(), RuntimeError> {
        let root = self.ensure_root_push_capacity(index, side)?;
        let block = self
            .arena
            .live_block(root.word().base())
            .ok_or(RuntimeError::InvalidArena)?;
        let len = self
            .arena
            .child_len(block)
            .ok_or(RuntimeError::InvalidArena)?;
        self.arena.words[block.base + 1 + len] = pushed.word();
        self.arena.set_child_len(block, len + 1)?;
        Ok(())
    }

    pub(super) fn ensure_root_push_capacity(
        &mut self,
        index: usize,
        side: Side,
    ) -> Result<Ref, RuntimeError> {
        let root = self.make_root_unique(index, side)?;
        let block = self
            .arena
            .live_block(root.word().base())
            .ok_or(RuntimeError::Shape)?;
        let len = self.arena.child_len(block).ok_or(RuntimeError::Shape)?;
        let capacity = block.capacity().ok_or(RuntimeError::InvalidArena)?;
        if len + 2 < capacity {
            return Ok(root);
        }
        let grown = self.grow_array(root)?;
        let roots = self.arena.roots.get_mut(index).ok_or(RuntimeError::Index)?;
        match side {
            Side::Left => roots.0 = grown,
            Side::Right => roots.1 = grown,
        }
        Ok(grown)
    }

    pub(crate) fn pop_root(&mut self, index: usize, side: Side) -> Result<Ref, RuntimeError> {
        let root = self.make_root_unique(index, side)?;
        let block = self
            .arena
            .live_block(root.word().base())
            .ok_or(RuntimeError::Shape)?;
        let len = self.arena.child_len(block).ok_or(RuntimeError::Shape)?;
        let slot = block
            .base
            .checked_add(len)
            .ok_or(RuntimeError::InvalidArena)?;
        if len == 0 {
            return Err(RuntimeError::Index);
        }
        let removed = Ref::new(self.arena.words[slot])?;
        self.arena.words[slot] = Word::ZERO;
        self.arena.set_child_len(block, len - 1)?;
        Ok(removed)
    }

    pub(crate) fn cross_root(&mut self, index: usize, source: Side) -> Result<(), RuntimeError> {
        let destination = match source {
            Side::Left => Side::Right,
            Side::Right => Side::Left,
        };
        let source_ref = self.root(index, source).ok_or(RuntimeError::Index)?;
        let destination_ref = self.root(index, destination).ok_or(RuntimeError::Index)?;
        let source_block = self
            .arena
            .live_block(source_ref.word().base())
            .ok_or(RuntimeError::Shape)?;
        if self.arena.child_len(source_block) == Some(0) {
            return Err(RuntimeError::Index);
        }
        let destination_block = self
            .arena
            .live_block(destination_ref.word().base())
            .ok_or(RuntimeError::Shape)?;
        let shared = self
            .arena
            .live_refcount(source_block)
            .is_some_and(|count| count > 1)
            || self
                .arena
                .live_refcount(destination_block)
                .is_some_and(|count| count > 1);
        if shared {
            let mut candidate = self.clone();
            candidate.cross_root_inner(index, source, destination)?;
            *self = candidate;
            return Ok(());
        }
        self.cross_root_inner(index, source, destination)
    }

    pub(super) fn cross_root_inner(
        &mut self,
        index: usize,
        source: Side,
        destination: Side,
    ) -> Result<(), RuntimeError> {
        self.prepare_cow_root(index, source)?;
        self.prepare_cow_root(index, destination)?;
        // Allocate and install destination capacity before detaching the source.
        // Once this succeeds the remaining two word edits cannot fail.
        self.ensure_root_push_capacity(index, destination)?;
        let removed = self.pop_root(index, source)?;
        self.push_root_ref(index, destination, Ref::new(removed.word().negated())?)
    }

    pub(crate) fn reclaim(&mut self, reference: Ref) -> Result<(), RuntimeError> {
        let mut pending = vec![reference];
        while let Some(reference) = pending.pop() {
            if reference.word().tag() == 3 {
                continue;
            }
            let block = self
                .arena
                .live_block(reference.word().base())
                .ok_or(RuntimeError::InvalidArena)?;
            let count = self
                .arena
                .live_refcount(block)
                .ok_or(RuntimeError::InvalidArena)?;
            if count > 1 {
                self.arena.words[block.base] =
                    Word::from_raw(self.arena.words[block.base].raw() - (1 << 7));
                continue;
            }
            let children = self
                .arena
                .child_words(block)
                .ok_or(RuntimeError::InvalidArena)?
                .to_vec();
            for word in children {
                pending.push(Ref::new(word)?);
            }
            self.arena.free(block)?;
        }
        Ok(())
    }

    /// Streams this arena's structural token sequence.
    ///
    /// # Panics
    ///
    /// Panics only if the arena stopped validating.
    pub(super) fn tokens(&self) -> impl Iterator<Item = Token> + '_ {
        let mut walk = Expand::new(&self.arena);
        std::iter::from_fn(move || walk.step().expect("a checked arena revalidates"))
    }
}

use super::{
    Arena, Checked, Expand, Formula, FormulaPath, FormulaView, Ref, RuntimeError, Side, Token,
    Word, least_size_class,
};
