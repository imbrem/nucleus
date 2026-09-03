use std::hash::{Hash, Hasher};

use smallvec::SmallVec;

/// One signed atom or signed n-ary classical connective.
///
/// `Sat` binds every atom below it as a fresh uninterpreted Boolean variable.
/// Its meaning is therefore independent of an ambient assignment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Formula {
    /// A signed Boolean atom.
    Literal {
        /// The unsigned atom identifier.
        atom: u64,
        /// Whether the atom is complemented.
        negative: bool,
    },
    /// A signed n-ary conjunction.
    And {
        /// Whether the complete conjunction is complemented.
        negative: bool,
        /// Ordered child formulas.
        children: Vec<Self>,
    },
    /// A signed n-ary disjunction.
    Or {
        /// Whether the complete disjunction is complemented.
        negative: bool,
        /// Ordered child formulas.
        children: Vec<Self>,
    },
    /// A signed satisfiability assertion over an implicit conjunction.
    Sat {
        /// Whether the satisfiability assertion is complemented.
        negative: bool,
        /// Formulas interpreted under a fresh assignment.
        children: Vec<Self>,
    },
}

impl Formula {
    /// Returns the same formula with its root polarity complemented.
    #[must_use]
    pub fn negated(mut self) -> Self {
        match &mut self {
            Self::Literal { negative, .. }
            | Self::And { negative, .. }
            | Self::Or { negative, .. }
            | Self::Sat { negative, .. } => *negative = !*negative,
        }
        self
    }

    pub(super) const fn tag(&self) -> u8 {
        match self {
            Self::And { .. } => 0,
            Self::Or { .. } => 1,
            Self::Sat { .. } => 2,
            Self::Literal { .. } => 3,
        }
    }

    pub(super) const fn negative(&self) -> bool {
        match self {
            Self::Literal { negative, .. }
            | Self::And { negative, .. }
            | Self::Or { negative, .. }
            | Self::Sat { negative, .. } => *negative,
        }
    }
}

impl Drop for Formula {
    /// Dismantles a formula with an explicit worklist.
    ///
    /// The derived destructor recurses once per level. Syntax decoded from an
    /// untrusted arena is as deep as that arena, and a destructor can neither
    /// fail nor be skipped, so the depth has to leave the stack. Each node's
    /// child vector is taken out and queued, which leaves behind a node whose
    /// own drop reaches no further.
    ///
    /// The queue is inline for the first few levels, so dismantling the small
    /// formulas that ordinary rules build allocates nothing.
    fn drop(&mut self) {
        let (Self::And { children, .. } | Self::Or { children, .. } | Self::Sat { children, .. }) =
            self
        else {
            return;
        };
        if children.is_empty() {
            return;
        }
        let mut pending: SmallVec<[Vec<Self>; 8]> = SmallVec::new();
        let mut current = std::mem::take(children);
        loop {
            for mut child in current {
                if let Self::And { children, .. }
                | Self::Or { children, .. }
                | Self::Sat { children, .. } = &mut child
                    && !children.is_empty()
                {
                    pending.push(std::mem::take(children));
                }
            }
            let Some(next) = pending.pop() else {
                return;
            };
            current = next;
        }
    }
}

impl Hash for Formula {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.tag().hash(state);
        self.negative().hash(state);
        match self {
            Self::Literal { atom, .. } => atom.hash(state),
            Self::And { children, .. } | Self::Or { children, .. } | Self::Sat { children, .. } => {
                children.len().hash(state);
                for child in children {
                    child.hash(state);
                }
            }
        }
    }
}

/// One implication between tagged classical formulas.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Sequent {
    /// Formula on the left of the turnstile.
    pub premise: Formula,
    /// Formula on the right of the turnstile.
    pub conclusion: Formula,
}

/// Selects one root of a sequent.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Side {
    /// The premise root.
    Left,
    /// The conclusion root.
    Right,
}
