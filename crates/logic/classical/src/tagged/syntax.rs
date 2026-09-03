use std::hash::{Hash, Hasher};

use smallvec::SmallVec;

/// One signed atom or signed n-ary classical connective.
///
/// `Sat` binds every atom below it as a fresh uninterpreted Boolean variable.
/// Its meaning is therefore independent of an ambient assignment.
#[derive(Debug)]
pub enum Formula {
    /// A signed Boolean atom.
    Literal {
        /// The unsigned atom identifier.
        atom: u32,
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

impl Clone for Formula {
    fn clone(&self) -> Self {
        enum Task<'a> {
            Visit(&'a Formula),
            Finish {
                tag: u8,
                negative: bool,
                children: usize,
            },
        }
        let mut tasks = vec![Task::Visit(self)];
        let mut built = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(Self::Literal { atom, negative }) => built.push(Self::Literal {
                    atom: *atom,
                    negative: *negative,
                }),
                Task::Visit(formula) => {
                    let (tag, negative, children) = match formula {
                        Self::And { negative, children } => (0, *negative, children),
                        Self::Or { negative, children } => (1, *negative, children),
                        Self::Sat { negative, children } => (2, *negative, children),
                        Self::Literal { .. } => unreachable!(),
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
                    let first = built.len() - children;
                    let children = built.drain(first..).collect();
                    built.push(match tag {
                        0 => Self::And { negative, children },
                        1 => Self::Or { negative, children },
                        2 => Self::Sat { negative, children },
                        _ => unreachable!(),
                    });
                }
            }
        }
        built.pop().expect("one formula is built")
    }
}

impl PartialEq for Formula {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            if left.tag() != right.tag() || left.negative() != right.negative() {
                return false;
            }
            match (left, right) {
                (Self::Literal { atom: left, .. }, Self::Literal { atom: right, .. })
                    if left == right => {}
                (
                    Self::And { children: left, .. },
                    Self::And {
                        children: right, ..
                    },
                )
                | (
                    Self::Or { children: left, .. },
                    Self::Or {
                        children: right, ..
                    },
                )
                | (
                    Self::Sat { children: left, .. },
                    Self::Sat {
                        children: right, ..
                    },
                ) if left.len() == right.len() => {
                    pending.extend(left.iter().zip(right).rev());
                }
                _ => return false,
            }
        }
        true
    }
}

impl Eq for Formula {}

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
        let mut pending = vec![self];
        while let Some(formula) = pending.pop() {
            formula.tag().hash(state);
            formula.negative().hash(state);
            match formula {
                Self::Literal { atom, .. } => atom.hash(state),
                Self::And { children, .. }
                | Self::Or { children, .. }
                | Self::Sat { children, .. } => {
                    children.len().hash(state);
                    pending.extend(children.iter().rev());
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

/// An abstract route to a formula in a sequent table.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct FormulaPath {
    sequent: usize,
    side: Side,
    children: Vec<usize>,
}

impl FormulaPath {
    /// Constructs a path from a sequent root and child indices.
    #[must_use]
    pub const fn new(sequent: usize, side: Side, children: Vec<usize>) -> Self {
        Self {
            sequent,
            side,
            children,
        }
    }

    /// Returns the sequent-table index.
    #[must_use]
    pub const fn sequent(&self) -> usize {
        self.sequent
    }

    /// Returns the selected side.
    #[must_use]
    pub const fn side(&self) -> Side {
        self.side
    }

    /// Returns the child-index route below the root.
    #[must_use]
    pub fn children(&self) -> &[usize] {
        &self.children
    }
}
