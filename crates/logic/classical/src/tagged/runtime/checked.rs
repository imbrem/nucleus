impl Checked {
    /// Builds checked storage from semantic sequents.
    ///
    /// # Errors
    ///
    /// Returns an error when the formulas exceed the runtime bounds.
    pub fn from_sequents(sequents: &[Sequent]) -> Result<Self, RuntimeError> {
        pack(sequents)
    }

    /// Returns the number of sequent roots.
    #[must_use]
    pub fn len(&self) -> usize {
        self.arena.roots.len()
    }

    /// Returns whether the sequent table is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.arena.roots.is_empty()
    }

    /// Borrows one sequent without decoding its formulas.
    #[must_use]
    pub fn view(&self, index: usize) -> Option<SequentView<'_>> {
        let &(premise, conclusion) = self.arena.roots.get(index)?;
        Some(SequentView {
            premise: FormulaView {
                checked: self,
                reference: premise,
            },
            conclusion: FormulaView {
                checked: self,
                reference: conclusion,
            },
        })
    }
    /// Validates an untrusted runtime arena.
    ///
    /// This checks the free rings, live-block partition, reference counts,
    /// reachable acyclicity, padding, and address bounds.
    /// It establishes syntax only and does not create a theorem fact.
    ///
    /// # Errors
    ///
    /// Returns an error when any allocator, reference, syntax, or ownership
    /// invariant fails.
    #[cfg(test)]
    pub(crate) fn check(mut arena: Arena) -> Result<Self, RuntimeError> {
        arena.validate_graph()?;
        let mut coverage = Coverage::new(arena.words.len());
        arena
            .decode_free(&mut coverage)
            .ok_or(RuntimeError::InvalidArena)?;
        for block in arena.partition_live(&mut coverage)? {
            let len = arena
                .scan_child_words(block)
                .ok_or(RuntimeError::InvalidArena)?
                .len();
            arena.set_child_len(block, len)?;
        }
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
        let Some(root_block) = self.arena.live_block(root.word().base()) else {
            return false;
        };
        if self.arena.live_refcount(root_block) != Some(1) {
            return false;
        }
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
        let Some(row_block) = self.arena.live_block(reference.word().base()) else {
            return false;
        };
        if self.arena.live_refcount(row_block) != Some(1) {
            return false;
        }
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
        if self.arena.set_child_len(row_block, write).is_err() {
            return false;
        }
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
        let Some(source_block) = self.arena.live_block(source.word().base()) else {
            return false;
        };
        if self.arena.live_refcount(source_block) != Some(1)
            || self.arena.live_refcount(destination_block) != Some(1)
        {
            return false;
        }
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
        let Some(row_block) = self.arena.live_block(row_ref.word().base()) else {
            return false;
        };
        if self.arena.live_refcount(row_block) != Some(1) {
            return false;
        }
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
        let Some(count) = self.arena.live_refcount(row_block) else {
            return false;
        };
        let Ok(metadata) = Arena::live_metadata(row_tag, row_block.size_class, count) else {
            return false;
        };
        self.arena.words[row_block.base] = metadata;
        let moved = Ref::new(
            Word::pointer(row_ref.word().base(), false)
                .expect("checked address remains representable"),
        )
        .expect("a checked row pointer is nonzero");
        self.arena.words.copy_within(
            source_children.start + row + 1..source_children.end,
            source_children.start + row,
        );
        self.arena.words[source_children.end - 1] = Word::ZERO;
        self.arena.words[destination_stop] = moved.word();
        if self
            .arena
            .set_child_len(source_block, source_children.len() - 1)
            .is_err()
            || self
                .arena
                .set_child_len(destination_block, destination_children.len() + 1)
                .is_err()
        {
            return false;
        }
        true
    }
}
use super::{
    Arena, Checked, FormulaView, Ref, RuntimeError, Sequent, SequentView, Side, Word, pack,
};
#[cfg(test)]
use super::{Block, Coverage};
