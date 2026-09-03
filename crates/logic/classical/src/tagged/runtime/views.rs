/// An arena that the complete executable validator accepted.
///
/// Decoded syntax is not retained beside the words.
#[derive(Clone, Debug)]
pub struct Checked {
    pub(super) arena: Arena,
}

/// An allocation-free borrowed view of one formula.
#[derive(Clone, Copy)]
pub struct FormulaView<'a> {
    pub(super) checked: &'a Checked,
    pub(super) reference: Ref,
}

/// The semantic constructor of a formula.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FormulaKind {
    And,
    Or,
    Sat,
    Literal,
}

impl FormulaView<'_> {
    /// Returns the semantic formula constructor.
    #[must_use]
    pub fn kind(self) -> FormulaKind {
        match self.tag() {
            0 => FormulaKind::And,
            1 => FormulaKind::Or,
            2 => FormulaKind::Sat,
            _ => FormulaKind::Literal,
        }
    }

    pub(crate) fn tag(self) -> u8 {
        if self.reference.word().tag() == 3 {
            3
        } else {
            self.checked
                .arena
                .live_tag(self.reference.word().base())
                .unwrap_or(3)
        }
    }

    /// Returns whether the formula is complemented.
    #[must_use]
    pub const fn is_negative(self) -> bool {
        self.reference.word().is_negative()
    }

    /// Returns the atom of a literal.
    #[must_use]
    pub fn atom(self) -> Option<u32> {
        if self.tag() == 3 {
            Some(self.reference.word().base() / 4)
        } else {
            None
        }
    }

    /// Returns the number of children, or zero for a literal.
    #[must_use]
    pub fn len(self) -> usize {
        self.checked
            .child_range(self.reference)
            .map_or(0, |range| range.len())
    }

    /// Returns whether this formula has no children.
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Borrows one child without allocating.
    #[must_use]
    pub fn child(self, index: usize) -> Option<Self> {
        let range = self.checked.child_range(self.reference)?;
        let word = *self
            .checked
            .arena
            .words
            .get(range.start.checked_add(index)?)?;
        (index < range.len())
            .then(|| Ref::new(word).ok())
            .flatten()
            .map(|reference| Self {
                checked: self.checked,
                reference,
            })
    }

    /// Compares two formulas structurally, checking packed equality first.
    #[must_use]
    pub fn structural_eq(self, other: FormulaView<'_>) -> bool {
        if self.reference.word() == other.reference.word()
            && std::ptr::eq(self.checked, other.checked)
        {
            return true;
        }
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            if left.tag() != right.tag()
                || left.is_negative() != right.is_negative()
                || left.atom() != right.atom()
                || left.len() != right.len()
            {
                return false;
            }
            for index in (0..left.len()).rev() {
                let (Some(l), Some(r)) = (left.child(index), right.child(index)) else {
                    return false;
                };
                if l.reference.word() != r.reference.word() || !std::ptr::eq(l.checked, r.checked) {
                    pending.push((l, r));
                }
            }
        }
        true
    }
}

/// Allocation-free views of a sequent's two owned roots.
#[derive(Clone, Copy)]
pub struct SequentView<'a> {
    /// Premise formula.
    pub premise: FormulaView<'a>,
    /// Conclusion formula.
    pub conclusion: FormulaView<'a>,
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
use super::{Arena, Hash, Hasher, Ref};
