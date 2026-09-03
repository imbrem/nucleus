pub(super) struct Expand<'a> {
    arena: &'a Arena,
    pending: Vec<Ref>,
}

impl<'a> Expand<'a> {
    pub(super) fn new(arena: &'a Arena) -> Self {
        let mut pending = Vec::with_capacity(2 * arena.roots.len());
        for &(left, right) in arena.roots.iter().rev() {
            pending.push(right);
            pending.push(left);
        }
        Self { arena, pending }
    }

    pub(super) fn step(&mut self) -> Result<Option<Token>, RuntimeError> {
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
        let children = self
            .arena
            .child_words(block)
            .ok_or(RuntimeError::InvalidArena)?;
        for child in children.iter().rev() {
            self.pending
                .push(Ref::new(*child).map_err(|_| RuntimeError::InvalidArena)?);
        }
        Ok(Some(Token {
            tag: self
                .arena
                .live_tag(word.base())
                .ok_or(RuntimeError::InvalidArena)?,
            negative: word.is_negative(),
            value: u32::try_from(children.len()).map_err(|_| RuntimeError::InvalidArena)?,
        }))
    }
}

use super::{Arena, Ref, RuntimeError, Token};
