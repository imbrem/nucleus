//! Arena-parametric interface for the Nucleus HOL kernel.
//!
//! [`Kernel`] is an owning wrapper asserting that its arena is sound. The
//! representation boundary is generic, but mutation is deliberately not:
//! each concrete arena representation receives its own inherent kernel API.
//! The CAS relative to which an arena is sound is ghost state in the formal
//! model and is not stored here.

use std::rc::Rc;
use std::sync::Arc;

pub mod wire;

/// The single syntax-row vocabulary shared by all arena representations and
/// untrusted wire decoding.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Row {
    BoolTy,
    Bool(bool),
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

/// A portable fact with an explicit set of assumptions.
///
/// There is no public unchecked constructor. Future proof rules will be the
/// only way to obtain a `Fact`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fact {
    assumptions: Vec<Tm>,
    conclusion: Tm,
}

impl Fact {
    #[must_use]
    pub fn assumptions(&self) -> impl ExactSizeIterator<Item = &Tm> {
        self.assumptions.iter()
    }

    #[must_use]
    pub const fn conclusion(&self) -> &Tm {
        &self.conclusion
    }
}

mod sealed {
    pub trait Sealed {}
}

/// A sealed common read boundary for arena representations.
///
/// This trait intentionally has no mutation capability. Concrete kernel
/// representations expose specialized inherent operations instead.
pub trait Arena: sealed::Sealed {
    fn rows(&self) -> &[Row];
}

impl<T: Arena + ?Sized> sealed::Sealed for Arc<T> {}
impl<T: Arena + ?Sized> Arena for Arc<T> {
    fn rows(&self) -> &[Row] {
        (**self).rows()
    }
}

impl<T: Arena + ?Sized> sealed::Sealed for Rc<T> {}
impl<T: Arena + ?Sized> Arena for Rc<T> {
    fn rows(&self) -> &[Row] {
        (**self).rows()
    }
}

/// An owning wrapper over an arena admitted as sound.
///
/// Fields and constructors from arbitrary arenas are private: decoding a bare
/// arena is not sufficient to manufacture this witness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Kernel<A: Arena> {
    arena: A,
}

impl<A: Arena> Kernel<A> {
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
///
/// Rust cannot give this enum the name `Arena` because the sealed public trait
/// already occupies that type-namespace name.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AnyArena {
    Dense(dense::Arena),
}

impl sealed::Sealed for AnyArena {}
impl Arena for AnyArena {
    fn rows(&self) -> &[Row] {
        match self {
            Self::Dense(arena) => arena.rows(),
        }
    }
}

/// Dense root-arena storage and its specialized kernel operations.
pub mod dense {
    use super::{Arena as ArenaTrait, Error, Kernel as GenericKernel, Row, Tm, Ty, sealed};

    /// A dense signed-offset arena.
    ///
    /// This value alone is untrusted. Only a `Kernel<Arena>` is an
    /// assumed-sound kernel witness.
    #[derive(Clone, Debug, Default, Eq, PartialEq)]
    pub struct Arena {
        pub(crate) offset: i64,
        pub(crate) rows: Vec<Row>,
    }

    impl Arena {
        #[must_use]
        pub const fn offset(&self) -> i64 {
            self.offset
        }

        #[must_use]
        pub const fn is_empty(&self) -> bool {
            self.rows.is_empty()
        }

        #[must_use]
        pub const fn len(&self) -> usize {
            self.rows.len()
        }

        #[must_use]
        pub fn rows(&self) -> &[Row] {
            &self.rows
        }

        pub(crate) fn from_untrusted(offset: i64, rows: Vec<Row>) -> Self {
            Self { offset, rows }
        }

        fn push(&mut self, row: Row) -> Result<i64, Error> {
            let length = i64::try_from(self.rows.len()).map_err(|_| Error::ArenaFull)?;
            let index = self
                .offset
                .checked_add(length)
                .ok_or(Error::IndexOverflow)?;
            self.rows.push(row);
            Ok(index)
        }
    }

    impl sealed::Sealed for Arena {}
    impl ArenaTrait for Arena {
        fn rows(&self) -> &[Row] {
            self.rows()
        }
    }

    /// The dense kernel specialization.
    pub type Kernel = GenericKernel<Arena>;

    impl GenericKernel<Arena> {
        /// Constructs the empty, sound dense arena.
        ///
        /// Lean: `Nucleus.Hol.Ethane.Kernel.empty` and
        /// `Nucleus.Hol.Ethane.Kernel.empty_sound`.
        #[must_use]
        pub const fn empty() -> Self {
            Self {
                arena: Arena {
                    offset: 0,
                    rows: Vec::new(),
                },
            }
        }

        /// Appends the Boolean type. Repeated calls append repeated rows;
        /// caching and deduplication belong outside the kernel.
        ///
        /// Lean: `Nucleus.Hol.Ethane.Kernel.boolTy` and
        /// `Nucleus.Hol.Ethane.Kernel.boolTy_sound`.
        ///
        /// # Errors
        ///
        /// Returns an error if the signed dense index cannot be represented.
        pub fn bool_ty(&mut self) -> Result<Ty, Error> {
            let index = self.arena.push(Row::BoolTy)?;
            Ok(Ty { index })
        }

        /// Appends a Boolean constant. Repeated calls append repeated rows.
        ///
        /// Lean: `Nucleus.Hol.Ethane.Kernel.bool` and
        /// `Nucleus.Hol.Ethane.Kernel.bool_sound`.
        ///
        /// # Errors
        ///
        /// Returns an error if the signed dense index cannot be represented.
        pub fn bool_const(&mut self, value: bool) -> Result<Tm, Error> {
            let index = self.arena.push(Row::Bool(value))?;
            Ok(Tm { index })
        }
    }

    impl Default for GenericKernel<Arena> {
        fn default() -> Self {
            Self::empty()
        }
    }
}

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

    use super::{Row, dense};

    #[test]
    fn dense_operations_append_and_duplicate() {
        let mut kernel = dense::Kernel::empty();
        let first_type = kernel.bool_ty().unwrap();
        let second_type = kernel.bool_ty().unwrap();
        let false_term = kernel.bool_const(false).unwrap();
        let duplicate = kernel.bool_const(false).unwrap();

        assert_eq!((first_type.index(), second_type.index()), (0, 1));
        assert_eq!((false_term.index(), duplicate.index()), (2, 3));
        assert_eq!(
            kernel.arena().rows(),
            &[Row::BoolTy, Row::BoolTy, Row::Bool(false), Row::Bool(false)]
        );
    }

    #[test]
    fn arc_and_rc_are_read_only_arena_boundaries() {
        fn rows<A: super::Arena>(arena: &A) -> &[Row] {
            arena.rows()
        }

        let mut kernel = dense::Kernel::empty();
        kernel.bool_ty().unwrap();
        let arena = kernel.into_arena();
        let arc = Arc::new(arena.clone());
        let rc = Rc::new(arena);

        assert_eq!(rows(&arc), &[Row::BoolTy]);
        assert_eq!(rows(&rc), &[Row::BoolTy]);
    }
}

#[cfg(test)]
mod conformance;
