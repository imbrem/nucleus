//! Arena-parametric interface for the Nucleus HOL kernel.
//!
//! [`Kernel`] is an owning wrapper asserting that its arena is sound. The
//! representation boundary is generic, but mutation is deliberately not:
//! each concrete arena representation receives its own inherent kernel API.
//! The CAS relative to which an arena is sound is ghost state in the formal
//! model and is not stored here.

use std::rc::Rc;
use std::sync::Arc;

pub mod dense;
mod row;
pub mod wire;

use row::{Expr, Row};

/// A portable handle to a checked HOL kind row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Kind {
    index: i64,
}

impl Kind {
    #[must_use]
    pub const fn index(self) -> i64 {
        self.index
    }
}

/// A portable handle to a checked HOL type row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Ty {
    index: i64,
}

impl Ty {
    #[must_use]
    pub const fn index(self) -> i64 {
        self.index
    }
}

/// A portable handle to a checked HOL term row.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Tm {
    index: i64,
}

impl Tm {
    #[must_use]
    pub const fn index(self) -> i64 {
        self.index
    }
}

mod sealed {
    pub trait Sealed {}
}

/// A sealed common read boundary for arena representations.
///
/// This trait intentionally has no mutation capability. Concrete kernel
/// representations expose specialized inherent operations instead.
pub trait ArenaRepr: sealed::Sealed {}

impl<T: ArenaRepr + ?Sized> sealed::Sealed for Arc<T> {}
impl<T: ArenaRepr + ?Sized> ArenaRepr for Arc<T> {}

impl<T: ArenaRepr + ?Sized> sealed::Sealed for Rc<T> {}
impl<T: ArenaRepr + ?Sized> ArenaRepr for Rc<T> {}

/// An owning wrapper over an arena admitted as sound.
///
/// Fields and constructors from arbitrary arenas are private: decoding a bare
/// arena is not sufficient to manufacture this witness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Kernel<A: ArenaRepr> {
    pub(crate) arena: A,
}

impl<A: ArenaRepr> Kernel<A> {
    #[must_use]
    pub const fn arena(&self) -> &A {
        &self.arena
    }

    #[must_use]
    pub fn into_arena(self) -> A {
        self.arena
    }
}

/// A representation-erased arena value for read-only dispatch.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Arena {
    Dense(dense::Arena),
}

impl sealed::Sealed for Arena {}
impl ArenaRepr for Arena {}

/// A semantic rejection. Rejection leaves the kernel unchanged.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    ArenaFull,
    IndexOverflow,
}

impl std::fmt::Display for Error {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "HOL kernel rejection: {self:?}")
    }
}

impl std::error::Error for Error {}

#[cfg(test)]
mod tests {
    use std::rc::Rc;
    use std::sync::Arc;

    use super::{Expr, Row, dense};

    #[test]
    fn dense_operations_append_and_duplicate() {
        let mut kernel = dense::Kernel::empty();
        let star = kernel.star().unwrap();
        let first_type = kernel.bool_ty().unwrap();
        let second_type = kernel.bool_ty().unwrap();
        let false_term = kernel.bool_const(false).unwrap();
        let duplicate = kernel.bool_const(false).unwrap();

        assert_eq!(star.index(), 0);
        assert_eq!((first_type.index(), second_type.index()), (1, 2));
        assert_eq!((false_term.index(), duplicate.index()), (3, 4));
        assert_eq!(
            kernel.arena().rows(),
            &[
                Row::syntax(Expr::KindStar),
                Row::syntax(Expr::BoolTy),
                Row::syntax(Expr::BoolTy),
                Row::syntax(Expr::Bool(false)),
                Row::syntax(Expr::Bool(false))
            ]
        );
    }

    #[test]
    fn arc_and_rc_are_read_only_arena_boundaries() {
        fn accepts_representation<A: super::ArenaRepr>(_: &A) {}

        let mut kernel = dense::Kernel::empty();
        kernel.bool_ty().unwrap();
        let arena = kernel.into_arena();
        let arc = Arc::new(arena.clone());
        let rc = Rc::new(arena);

        accepts_representation(&arc);
        accepts_representation(&rc);
        assert_eq!(arc.rows(), &[Row::syntax(Expr::BoolTy)]);
        assert_eq!(rc.rows(), &[Row::syntax(Expr::BoolTy)]);
    }
}
