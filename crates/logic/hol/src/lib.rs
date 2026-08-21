//! Persistent arena interface for the Nucleus HOL kernel.
//!
//! A [`Kernel`] owns an [`Arena`] that the implementation has checked. Kernel
//! identity is not part of the logic: values may be passed between kernels,
//! and facts carry their assumptions explicitly. The CAS relative to which an
//! arena is sound is ghost state in the formal model and is deliberately not
//! stored here.

pub mod wire;

/// An address in the dense arena representation.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Address(u64);

/// A portable HOL type handle.
///
/// Handles do not contain a kernel identity. Their representation is private,
/// so clients cannot manufacture values that bypass kernel admission.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Ty(TyRepr);

#[derive(Clone, Debug, Eq, PartialEq)]
enum TyRepr {
    Bool,
}

/// A portable HOL term handle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Tm(TmRepr);

#[derive(Clone, Debug, Eq, PartialEq)]
enum TmRepr {
    Bool(bool),
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

#[derive(Clone, Debug, Eq, PartialEq)]
enum Entry {
    Type(Ty),
    Term(Tm),
    #[allow(dead_code, reason = "proof rules are added in the next vertical slice")]
    Fact(Fact),
}

/// A dense arena whose admitted entries are assumed sound by [`Kernel`].
///
/// Fields and insertion primitives are private. This prevents callers from
/// constructing an unchecked arena and wrapping it as a kernel.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Arena {
    entries: Vec<Entry>,
}

impl Arena {
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    fn push(&mut self, entry: Entry) -> Result<Address, Error> {
        let address = u64::try_from(self.entries.len()).map_err(|_| Error::ArenaFull)?;
        self.entries.push(entry);
        Ok(Address(address))
    }
}

/// A semantic rejection. Rejection never yields a replacement arena.
#[non_exhaustive]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Error {
    /// The dense address space has been exhausted.
    ArenaFull,
}

impl std::fmt::Display for Error {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(output, "HOL kernel rejection: {self:?}")
    }
}

impl std::error::Error for Error {}

/// An owning wrapper over an arena admitted as sound.
///
/// The ideal interface is persistent: operations borrow one kernel and return
/// a new one. Mutable methods are equivalent implementation conveniences.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Kernel {
    arena: Arena,
}

impl Kernel {
    /// Constructs the empty, sound arena.
    ///
    /// Lean: `Nucleus.Hol.Ethane.Kernel.empty` and
    /// `Nucleus.Hol.Ethane.Kernel.empty_sound`.
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            arena: Arena {
                entries: Vec::new(),
            },
        }
    }

    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    #[must_use]
    pub fn into_arena(self) -> Arena {
        self.arena
    }

    /// Adds the Boolean type and returns the replacement kernel.
    ///
    /// Lean: `Nucleus.Hol.Ethane.Kernel.boolTy` and
    /// `Nucleus.Hol.Ethane.Kernel.boolTy_sound`.
    ///
    /// # Errors
    ///
    /// Returns [`Error::ArenaFull`] if no dense address remains.
    pub fn bool_ty(&self) -> Result<(Self, Ty), Error> {
        let mut next = self.clone();
        let ty = Ty(TyRepr::Bool);
        next.arena.push(Entry::Type(ty.clone()))?;
        Ok((next, ty))
    }

    /// Adds a Boolean constant and returns the replacement kernel.
    ///
    /// Lean: `Nucleus.Hol.Ethane.Kernel.bool` and
    /// `Nucleus.Hol.Ethane.Kernel.bool_sound`.
    ///
    /// # Errors
    ///
    /// Returns [`Error::ArenaFull`] if no dense address remains.
    pub fn bool_const(&self, value: bool) -> Result<(Self, Tm), Error> {
        let mut next = self.clone();
        let term = Tm(TmRepr::Bool(value));
        next.arena.push(Entry::Term(term.clone()))?;
        Ok((next, term))
    }

    /// In-place optimization of [`Kernel::bool_ty`].
    ///
    /// On success it has exactly the same arena and output as the persistent
    /// operation; on rejection `self` is unchanged.
    ///
    /// # Errors
    ///
    /// Returns [`Error::ArenaFull`] if no dense address remains.
    pub fn bool_ty_mut(&mut self) -> Result<Ty, Error> {
        let ty = Ty(TyRepr::Bool);
        self.arena.push(Entry::Type(ty.clone()))?;
        Ok(ty)
    }

    /// In-place optimization of [`Kernel::bool_const`].
    ///
    /// On rejection `self` is unchanged.
    ///
    /// # Errors
    ///
    /// Returns [`Error::ArenaFull`] if no dense address remains.
    pub fn bool_const_mut(&mut self, value: bool) -> Result<Tm, Error> {
        let term = Tm(TmRepr::Bool(value));
        self.arena.push(Entry::Term(term.clone()))?;
        Ok(term)
    }
}

#[cfg(test)]
mod tests {
    use super::Kernel;

    #[test]
    fn persistent_operations_leave_the_old_kernel_available() {
        let old = Kernel::empty();
        let (with_type, _bool_ty) = old.bool_ty().unwrap();
        let (with_true, _true_term) = with_type.bool_const(true).unwrap();

        assert!(old.arena().is_empty());
        assert_eq!(with_type.arena().len(), 1);
        assert_eq!(with_true.arena().len(), 2);
    }

    #[test]
    fn mutable_boolean_type_matches_persistent_operation() {
        let initial = Kernel::empty();
        let (persistent, persistent_ty) = initial.bool_ty().unwrap();
        let mut optimized = initial;
        let optimized_ty = optimized.bool_ty_mut().unwrap();

        assert_eq!(optimized, persistent);
        assert_eq!(optimized_ty, persistent_ty);
    }

    #[test]
    fn mutable_boolean_matches_persistent_operation() {
        let (initial, _bool_ty) = Kernel::empty().bool_ty().unwrap();
        let (persistent, persistent_term) = initial.bool_const(false).unwrap();
        let mut optimized = initial;
        let optimized_term = optimized.bool_const_mut(false).unwrap();

        assert_eq!(optimized, persistent);
        assert_eq!(optimized_term, persistent_term);
    }
}

#[cfg(test)]
mod conformance;
