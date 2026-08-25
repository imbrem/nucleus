//! Polarity-aware storage and rules for finite classical matrix sequents.
//!
//! A [`ThmRef`] has the semantic shape `CNF ⊢ DNF`: its left side is a
//! conjunction of disjunctive rows, while its right side is a disjunction of
//! conjunctive rows. [`Cnf`] and [`Dnf`] are distinct semantic wrappers over
//! the same polarity-neutral matrix storage.
//!
//! [`ClassicalArena`] is deliberately raw storage, not a logical authority.
//! Its [`ClassicalArena::store`] and [`ClassicalArena::replace`] operations can
//! admit arbitrary rows, and its rule helpers preserve only whatever semantic
//! status their inputs already have. An LCF kernel must keep the arena private
//! and expose only checked rule methods.
//!
//! On the wire an arena is only the normalized list of its live theorem rows,
//! in slot order. Deleted slots and free-list history are omitted; decoding
//! rebuilds dense, all-live slots and an empty free list.

use std::{collections::BTreeSet, num::NonZeroI32};

use covalence_lib_error::snafu::Snafu;
use serde::{
    Deserialize, Deserializer, Serialize, Serializer, de,
    ser::{SerializeSeq, SerializeTuple},
};
use smallvec::SmallVec;

/// A signed, losslessly negatable Boolean literal.
///
/// Negative values denote positive propositions; positive values denote their
/// negations. This is the established Ethane wire convention.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Lit(NonZeroI32);

/// A failure to construct a signed literal.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("invalid signed literal {value}"))]
pub struct LitError {
    /// Rejected signed value.
    pub value: i32,
}

impl Lit {
    /// Constructs a nonzero, losslessly negatable literal.
    ///
    /// # Panics
    ///
    /// Panics if `value` is zero or has magnitude at least `i32::MAX`.
    #[must_use]
    pub const fn new(value: i32) -> Self {
        match Self::try_new(value) {
            Ok(value) => value,
            Err(_) => panic!("literal must be nonzero and losslessly negatable"),
        }
    }

    /// Tries to construct a nonzero, losslessly negatable literal.
    ///
    /// # Errors
    ///
    /// Returns an error unless the unsigned magnitude is nonzero and strictly
    /// below `i32::MAX`.
    pub const fn try_new(value: i32) -> Result<Self, LitError> {
        if value.unsigned_abs() >= i32::MAX as u32 {
            Err(LitError { value })
        } else {
            match NonZeroI32::new(value) {
                Some(value) => Ok(Self(value)),
                None => Err(LitError { value }),
            }
        }
    }

    /// Encodes a positive proposition occurrence from its unsigned magnitude.
    #[must_use]
    pub const fn positive(magnitude: i32) -> Self {
        Self::new(-magnitude.abs())
    }

    /// Returns the signed integer representation.
    #[must_use]
    pub const fn get(self) -> i32 {
        self.0.get()
    }

    /// Returns the complementary literal.
    #[must_use]
    pub const fn negated(self) -> Self {
        Self::new(-self.get())
    }

    /// Returns whether this encoding denotes a positive proposition.
    #[must_use]
    pub const fn is_positive(self) -> bool {
        self.get() < 0
    }

    /// Returns the unsigned literal magnitude.
    #[must_use]
    pub const fn magnitude(self) -> u32 {
        self.get().unsigned_abs()
    }
}

impl TryFrom<i32> for Lit {
    type Error = LitError;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        Self::try_new(value)
    }
}

impl From<Lit> for i32 {
    fn from(value: Lit) -> Self {
        value.get()
    }
}

impl Serialize for Lit {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_i32(self.get())
    }
}

impl<'de> Deserialize<'de> for Lit {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::try_new(i32::deserialize(deserializer)?).map_err(de::Error::custom)
    }
}

/// Compact literal storage optimized for the common unit/binary row.
pub type LitVec = SmallVec<[Lit; 2]>;

/// Shared mutable storage for a classical matrix.
///
/// A missing row is semantically neutral: true in a CNF and false in a DNF.
/// Tombstones preserve row indices during proof construction. Normalization
/// removes them together with duplicate literals and rows.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
struct Matrix(Vec<Option<LitVec>>);

/// A conjunction of disjunctive literal rows.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct Cnf(Matrix);

/// A disjunction of conjunctive literal rows.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct Dnf(Matrix);

macro_rules! semantic_matrix {
    ($name:ident) => {
        impl $name {
            /// Constructs a matrix without imposing a normalization requirement.
            #[must_use]
            pub fn new(rows: impl IntoIterator<Item = LitVec>) -> Self {
                Self(Matrix(rows.into_iter().map(Some).collect()))
            }

            /// Returns every live matrix row in insertion order.
            pub fn rows(&self) -> impl Iterator<Item = &[Lit]> {
                self.0.0.iter().filter_map(Option::as_deref)
            }

            /// Clones the live rows, omitting semantically neutral tombstones.
            #[must_use]
            pub fn to_rows(&self) -> Vec<LitVec> {
                self.0.0.iter().flatten().cloned().collect()
            }

            /// Sorts and deduplicates every row and the matrix, removing tombstones.
            pub fn normalize(&mut self) {
                let mut rows = self.0.0.drain(..).flatten().collect::<Vec<_>>();
                for row in &mut rows {
                    row.sort_unstable();
                    row.dedup();
                }
                rows.sort_unstable();
                rows.dedup();
                self.0.0 = rows.into_iter().map(Some).collect();
            }
        }

        impl<const N: usize> From<[LitVec; N]> for $name {
            fn from(value: [LitVec; N]) -> Self {
                Self::new(value)
            }
        }
    };
}

semantic_matrix!(Cnf);
semantic_matrix!(Dnf);

impl Cnf {
    fn row(&self, id: CnfId) -> Result<&LitVec, Error> {
        self.0
            .0
            .get(id.position())
            .and_then(Option::as_ref)
            .ok_or(Error::MissingCnf { id: id.get() })
    }

    fn append(&mut self, row: LitVec) -> Result<CnfId, Error> {
        let id = self
            .0
            .0
            .len()
            .checked_add(1)
            .and_then(|value| i32::try_from(value).ok())
            .and_then(CnfId::new)
            .ok_or(Error::ArenaFull)?;
        self.0.0.push(Some(row));
        Ok(id)
    }

    fn remove(&mut self, id: CnfId) -> Result<LitVec, Error> {
        self.0
            .0
            .get_mut(id.position())
            .and_then(Option::take)
            .ok_or(Error::MissingCnf { id: id.get() })
    }

    fn contains_empty_row(&self) -> bool {
        self.rows().any(<[Lit]>::is_empty)
    }
}

/// Private owned storage for one matrix sequent.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ThmRow(Cnf, Dnf);

/// A borrowed CNF view independent of the arena's owned representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CnfRef<'a>(&'a [Option<LitVec>]);

/// A borrowed DNF view independent of the arena's owned representation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DnfRef<'a>(&'a [Option<LitVec>]);

macro_rules! matrix_ref {
    ($name:ident, $owned:ident) => {
        impl<'a> $name<'a> {
            /// Iterates over live rows, skipping semantic tombstones.
            pub fn rows(self) -> impl Iterator<Item = &'a [Lit]> {
                self.0.iter().filter_map(Option::as_deref)
            }

            /// Copies live rows into compact owned storage.
            #[must_use]
            pub fn to_rows(self) -> Vec<LitVec> {
                self.0.iter().flatten().cloned().collect()
            }

            /// Copies this borrowed matrix into owned construction storage.
            #[must_use]
            pub fn to_owned(self) -> $owned {
                $owned::new(self.to_rows())
            }
        }
    };
}

matrix_ref!(CnfRef, Cnf);
matrix_ref!(DnfRef, Dnf);

/// A borrowed classical theorem, interpreted as `CNF ⊢ DNF`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ThmRef<'a> {
    /// Conjunctive left-hand side.
    pub lhs: CnfRef<'a>,
    /// Disjunctive right-hand side.
    pub rhs: DnfRef<'a>,
}

impl ThmRow {
    fn view(&self) -> ThmRef<'_> {
        ThmRef {
            lhs: CnfRef(&self.0.0.0),
            rhs: DnfRef(&self.1.0.0),
        }
    }
}

impl Serialize for ThmRow {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut theorem = self.clone();
        theorem.normalize();
        let mut tuple = serializer.serialize_tuple(2)?;
        tuple.serialize_element(&theorem.0)?;
        tuple.serialize_element(&theorem.1)?;
        tuple.end()
    }
}

impl<'de> Deserialize<'de> for ThmRow {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let theorem = <(Cnf, Dnf)>::deserialize(deserializer)?;
        let theorem = Self(theorem.0, theorem.1);
        let mut normalized = theorem.clone();
        normalized.normalize();
        if theorem == normalized {
            Ok(theorem)
        } else {
            Err(de::Error::custom(
                "classical theorem matrix is not normalized",
            ))
        }
    }
}

impl ThmRow {
    const fn new(left: Cnf, right: Dnf) -> Self {
        Self(left, right)
    }

    #[cfg(test)]
    const fn left(&self) -> &Cnf {
        &self.0
    }

    #[cfg(test)]
    const fn right(&self) -> &Dnf {
        &self.1
    }

    /// Sorts and deduplicates rows and matrices on both sides.
    pub fn normalize(&mut self) {
        self.0.normalize();
        self.1.normalize();
    }
}

macro_rules! one_based_id {
    ($name:ident, $summary:literal) => {
        #[doc = $summary]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        #[repr(transparent)]
        pub struct $name(NonZeroI32);

        impl $name {
            /// Constructs a positive, one-based index.
            #[must_use]
            pub const fn new(value: i32) -> Option<Self> {
                if value <= 0 {
                    return None;
                }
                match NonZeroI32::new(value) {
                    Some(value) => Some(Self(value)),
                    None => None,
                }
            }

            /// Returns the positive, one-based index.
            #[must_use]
            pub const fn get(self) -> i32 {
                self.0.get()
            }

            fn position(self) -> usize {
                usize::try_from(self.get() - 1)
                    .expect("a positive i32 index is representable as usize")
            }
        }
    };
}

one_based_id!(
    ThmId,
    "An ephemeral one-based theorem slot identifier backed by `NonZeroI32`."
);
one_based_id!(
    CnfId,
    "A one-based CNF-row identifier backed by `NonZeroI32`."
);
one_based_id!(
    DnfId,
    "A one-based DNF-row identifier backed by `NonZeroI32`."
);

/// A classical arena operation failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// The theorem slot is absent or deleted.
    #[snafu(display("theorem {id} is absent"))]
    MissingTheorem {
        /// Missing one-based slot.
        id: i32,
    },
    /// The indexed CNF row is absent.
    #[snafu(display("CNF row {index} is absent from theorem {id}"))]
    MissingCnfRow {
        /// The theorem slot.
        id: i32,
        /// Missing one-based CNF row index.
        index: i32,
    },
    /// The indexed DNF row is absent.
    #[snafu(display("DNF row {index} is absent from theorem {id}"))]
    MissingDnfRow {
        /// The theorem slot.
        id: i32,
        /// Missing one-based DNF row index.
        index: i32,
    },
    /// A unit literal needed by a rule is absent.
    #[snafu(display("required unit literal {literal} is absent"))]
    MissingUnit {
        /// Required signed literal.
        literal: i32,
    },
    /// No further theorem slot can be represented.
    #[snafu(display("theorem arena is full"))]
    ArenaFull,
    /// A refutation hint names no live CNF row.
    #[snafu(display("CNF row {id} is absent"))]
    MissingCnf { id: i32 },
    /// A propagation hint is neither unit nor conflicting under the trail.
    #[snafu(display("CNF row {id} is not unit under the propagation trail"))]
    UselessHint { id: i32 },
    /// Reverse unit propagation did not reach a conflict.
    #[snafu(display("reverse unit propagation did not reach a conflict"))]
    NoConflict,
    /// The declared RAT pivot is not the learned row's first literal.
    #[snafu(display("the declared RAT pivot is not the row's first literal"))]
    BadPivot,
    /// A RAT group names a row without the complementary pivot.
    #[snafu(display("CNF row {id} does not contain the complementary RAT pivot"))]
    WrongOpposingCnf { id: i32 },
    /// Two RAT groups name the same opposing row.
    #[snafu(display("CNF row {id} has more than one RAT group"))]
    DuplicateRatGroup { id: i32 },
    /// A live opposing row has no RAT group.
    #[snafu(display("CNF row {id} has no RAT group"))]
    IncompleteRat { id: i32 },
    /// The refuter has not derived an empty row.
    #[snafu(display("the current CNF state has not been refuted"))]
    NoRefutation,
}

/// Mutable theorem-row storage with one-at-a-time deletion and slot reuse.
#[derive(Clone, Debug, Default)]
pub struct ClassicalArena {
    slots: Vec<Option<ThmRow>>,
    free: Vec<ThmId>,
}

/// The sound, target-independent classical inference surface.
///
/// Implementations may store sequents with different ambient meanings. Every
/// operation here preserves validity provided its resident input sequents are
/// valid; arbitrary insertion remains available only on [`ClassicalArena`].
#[allow(clippy::missing_errors_doc)]
pub trait ClassicalRules {
    /// Borrows a resident sequent.
    fn get(&self, id: ThmId) -> Option<ThmRef<'_>>;
    /// Introduces identity.
    fn identity(&mut self, literal: Lit) -> Result<ThmId, Error>;
    /// Weakens a resident sequent in place.
    fn weaken(&mut self, id: ThmId, cnf: &[LitVec], dnf: &[LitVec]) -> Result<(), Error>;
    /// Cuts a unit literal between two resident sequents.
    fn cut(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error>;
    /// Resolves complementary unit conclusions.
    fn resolve(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error>;
    /// Copies a resident sequent.
    fn copy(&mut self, source: ThmId) -> Result<ThmId, Error>;
    /// Removes one resident sequent.
    fn remove(&mut self, id: ThmId) -> bool;
    /// Moves an indexed CNF row across the turnstile.
    fn move_cnf_right(&mut self, id: ThmId, row: CnfId) -> Result<(), Error>;
    /// Moves an indexed DNF row across the turnstile.
    fn move_dnf_left(&mut self, id: ThmId, row: DnfId) -> Result<(), Error>;
    /// Normalizes a resident sequent.
    fn normalize(&mut self, id: ThmId) -> Result<(), Error>;
    /// Normalizes one CNF row.
    fn normalize_cnf(&mut self, id: ThmId, row: CnfId) -> Result<(), Error>;
    /// Normalizes one DNF row.
    fn normalize_dnf(&mut self, id: ThmId, row: DnfId) -> Result<(), Error>;
}

/// A capability view exposing only sound mutations of a classical arena.
pub struct CheckedArena<'a> {
    arena: &'a mut ClassicalArena,
}

impl<'a> CheckedArena<'a> {
    /// Restricts a mutable arena borrow to sound inference operations.
    #[must_use]
    pub const fn new(arena: &'a mut ClassicalArena) -> Self {
        Self { arena }
    }

    /// Borrows a resident sequent.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent or deleted.
    #[must_use]
    pub fn get(&self, id: ThmId) -> Option<ThmRef<'_>> {
        self.arena.get(id)
    }

    /// Iterates over live resident sequents in slot order.
    pub fn live_theorems(&self) -> impl Iterator<Item = ThmRef<'_>> {
        self.arena.live_theorems()
    }

    /// Copies a universally valid sequent from a classical kernel.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent or target storage is exhausted.
    pub fn copy_from(&mut self, source: &ClassicalKernel, id: ThmId) -> Result<ThmId, Error> {
        let theorem = source
            .get(id)
            .ok_or(Error::MissingTheorem { id: id.get() })?;
        self.arena.store_row(ThmRow::new(
            Cnf::new(theorem.lhs.to_rows()),
            Dnf::new(theorem.rhs.to_rows()),
        ))
    }

    /// Inserts the universal consequence certified by a completed refutation.
    ///
    /// # Errors
    ///
    /// Returns an error if target storage is exhausted.
    pub fn copy_refutation(&mut self, refutation: &Refutation) -> Result<ThmId, Error> {
        self.arena.store_row(refutation.theorem.clone())
    }
}

impl ClassicalRules for CheckedArena<'_> {
    fn get(&self, id: ThmId) -> Option<ThmRef<'_>> {
        self.arena.get(id)
    }
    fn identity(&mut self, literal: Lit) -> Result<ThmId, Error> {
        self.arena.identity(literal)
    }
    fn weaken(&mut self, id: ThmId, cnf: &[LitVec], dnf: &[LitVec]) -> Result<(), Error> {
        self.arena.weaken(id, cnf, dnf)
    }
    fn cut(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        self.arena.cut(left, right, literal)
    }
    fn resolve(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        self.arena.resolve(left, right, literal)
    }
    fn copy(&mut self, source: ThmId) -> Result<ThmId, Error> {
        self.arena.copy(source)
    }
    fn remove(&mut self, id: ThmId) -> bool {
        self.arena.remove(id)
    }
    fn move_cnf_right(&mut self, id: ThmId, row: CnfId) -> Result<(), Error> {
        self.arena.move_cnf_right(id, row)
    }
    fn move_dnf_left(&mut self, id: ThmId, row: DnfId) -> Result<(), Error> {
        self.arena.move_dnf_left(id, row)
    }
    fn normalize(&mut self, id: ThmId) -> Result<(), Error> {
        self.arena.normalize(id)
    }
    fn normalize_cnf(&mut self, id: ThmId, row: CnfId) -> Result<(), Error> {
        self.arena.normalize_cnf(id, row)
    }
    fn normalize_dnf(&mut self, id: ThmId, row: DnfId) -> Result<(), Error> {
        self.arena.normalize_dnf(id, row)
    }
}

impl Serialize for ClassicalArena {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.live_theorems().count()))?;
        for theorem in self.slots.iter().flatten() {
            sequence.serialize_element(theorem)?;
        }
        sequence.end()
    }
}

impl<'de> Deserialize<'de> for ClassicalArena {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_rows(Vec::<ThmRow>::deserialize(deserializer)?).map_err(de::Error::custom)
    }
}

impl ClassicalArena {
    /// Constructs an empty arena.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: Vec::new(),
            free: Vec::new(),
        }
    }

    /// Builds dense theorem storage from rows in iteration order.
    ///
    /// # Errors
    ///
    /// Returns [`Error::ArenaFull`] if the iterator contains more rows than
    /// positive `i32` theorem identifiers can address.
    fn from_rows(theorems: impl IntoIterator<Item = ThmRow>) -> Result<Self, Error> {
        let mut arena = Self::new();
        for theorem in theorems {
            arena.store_row(theorem)?;
        }
        Ok(arena)
    }

    /// Iterates over live theorem rows in slot order, skipping deleted slots.
    pub fn live_theorems(&self) -> impl Iterator<Item = ThmRef<'_>> {
        self.slots.iter().flatten().map(ThmRow::view)
    }

    /// Borrows a stored theorem when its slot is live.
    #[must_use]
    pub fn get(&self, id: ThmId) -> Option<ThmRef<'_>> {
        self.theorem_row(id).ok().map(ThmRow::view)
    }

    fn theorem_row(&self, id: ThmId) -> Result<&ThmRow, Error> {
        self.slots
            .get(Self::position(id))
            .and_then(Option::as_ref)
            .ok_or(Error::MissingTheorem { id: id.get() })
    }

    #[cfg(test)]
    fn theorem(&self, id: ThmId) -> Result<&ThmRow, Error> {
        self.theorem_row(id)
    }

    /// Stores an untrusted row.
    ///
    /// This is a storage operation, not an inference rule. Checked wrappers
    /// must ensure only sound rows enter their private arena.
    ///
    /// # Errors
    ///
    /// Returns an error if no further slot identifier can be represented.
    fn store_row(&mut self, theorem: ThmRow) -> Result<ThmId, Error> {
        if let Some(id) = self.free.pop() {
            self.slots[Self::position(id)] = Some(theorem);
            return Ok(id);
        }
        let next = self
            .slots
            .len()
            .checked_add(1)
            .and_then(|value| i32::try_from(value).ok())
            .and_then(ThmId::new)
            .ok_or(Error::ArenaFull)?;
        self.slots.push(Some(theorem));
        Ok(next)
    }

    #[cfg(test)]
    fn store(&mut self, theorem: ThmRow) -> Result<ThmId, Error> {
        self.store_row(theorem)
    }

    /// Inserts an untrusted sequent into storage.
    ///
    /// # Errors
    ///
    /// Returns an error if no further slot identifier can be represented.
    pub fn insert(&mut self, premises: Cnf, conclusions: Dnf) -> Result<ThmId, Error> {
        self.store_row(ThmRow::new(premises, conclusions))
    }

    /// Copies one stored theorem into a newly allocated slot.
    ///
    /// # Errors
    ///
    /// Returns an error if `source` is absent or no slot is available.
    pub fn copy(&mut self, source: ThmId) -> Result<ThmId, Error> {
        let theorem = self.theorem_row(source)?.clone();
        self.store_row(theorem)
    }

    /// Removes exactly one theorem and makes its slot reusable.
    pub fn remove(&mut self, id: ThmId) -> bool {
        let Some(theorem) = self
            .slots
            .get_mut(Self::position(id))
            .and_then(Option::take)
        else {
            return false;
        };
        self.free.push(id);
        drop(theorem);
        true
    }

    /// Introduces the identity sequent `[[p]] ⊢ [[p]]`.
    ///
    /// # Errors
    ///
    /// Returns an error if no theorem slot is available.
    pub fn identity(&mut self, literal: Lit) -> Result<ThmId, Error> {
        self.store_row(ThmRow::new(
            Cnf::new([std::iter::once(literal).collect()]),
            Dnf::new([std::iter::once(literal).collect()]),
        ))
    }

    /// Weakens a theorem by adding left clauses and right cubes.
    ///
    /// Adding a left clause strengthens the antecedent; adding a right cube
    /// weakens the consequent.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent.
    pub fn weaken(&mut self, id: ThmId, left: &[LitVec], right: &[LitVec]) -> Result<(), Error> {
        let mut replacement = self.theorem_row(id)?.clone();
        replacement.0.0.0.extend(left.iter().cloned().map(Some));
        replacement.1.0.0.extend(right.iter().cloned().map(Some));
        self.replace_row(id, replacement)
    }

    /// Cuts a singleton literal from a right cube and a left clause.
    ///
    /// From `F ⊢ G ∨ p` and `p ∧ H ⊢ K`, derives `F ∧ H ⊢ G ∨ K`.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent theorem or required unit row.
    pub fn cut(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        let mut first = self.theorem_row(left)?.clone();
        let mut second = self.theorem_row(right)?.clone();
        let right_position = first
            .1
            .0
            .0
            .iter()
            .position(|row| row.as_deref() == Some(&[literal]))
            .ok_or(Error::MissingUnit {
                literal: literal.get(),
            })?;
        let left_position = second
            .0
            .0
            .0
            .iter()
            .position(|row| row.as_deref() == Some(&[literal]))
            .ok_or(Error::MissingUnit {
                literal: literal.get(),
            })?;
        first.1.0.0.remove(right_position);
        second.0.0.0.remove(left_position);
        first.0.0.0.extend(second.0.0.0);
        first.1.0.0.extend(second.1.0.0);
        self.store_row(first)
    }

    /// Resolves complementary singleton cubes on two theorem right sides.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent theorem or required unit cube.
    pub fn resolve(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        let mut first = self.theorem_row(left)?.clone();
        let mut second = self.theorem_row(right)?.clone();
        let first_position = first
            .1
            .0
            .0
            .iter()
            .position(|row| row.as_deref() == Some(&[literal]))
            .ok_or(Error::MissingUnit {
                literal: literal.get(),
            })?;
        let complement = literal.negated();
        let second_position = second
            .1
            .0
            .0
            .iter()
            .position(|row| row.as_deref() == Some(&[complement]))
            .ok_or(Error::MissingUnit {
                literal: complement.get(),
            })?;
        first.1.0.0.remove(first_position);
        second.1.0.0.remove(second_position);
        first.0.0.0.extend(second.0.0.0);
        first.1.0.0.extend(second.1.0.0);
        self.store_row(first)
    }

    /// Moves one indexed CNF row to a pointwise-negated DNF row.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or indexed clause is absent.
    pub fn move_cnf_right(&mut self, id: ThmId, row: CnfId) -> Result<(), Error> {
        let mut replacement = self.theorem_row(id)?.clone();
        let index = row.position();
        let source = replacement
            .0
            .0
            .0
            .get_mut(index)
            .and_then(Option::take)
            .ok_or(Error::MissingCnfRow {
                id: id.get(),
                index: row.get(),
            })?;
        replacement
            .1
            .0
            .0
            .push(Some(source.into_iter().map(Lit::negated).collect()));
        self.replace_row(id, replacement)
    }

    /// Moves one indexed DNF row to a pointwise-negated CNF row.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or indexed cube is absent.
    pub fn move_dnf_left(&mut self, id: ThmId, row: DnfId) -> Result<(), Error> {
        let mut replacement = self.theorem_row(id)?.clone();
        let index = row.position();
        let source = replacement
            .1
            .0
            .0
            .get_mut(index)
            .and_then(Option::take)
            .ok_or(Error::MissingDnfRow {
                id: id.get(),
                index: row.get(),
            })?;
        replacement
            .0
            .0
            .0
            .push(Some(source.into_iter().map(Lit::negated).collect()));
        self.replace_row(id, replacement)
    }

    /// Normalizes both matrices of one theorem in place.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent.
    pub fn normalize(&mut self, id: ThmId) -> Result<(), Error> {
        self.theorem_mut(id)?.normalize();
        Ok(())
    }

    /// Normalizes one indexed CNF row in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or indexed clause is absent.
    pub fn normalize_cnf(&mut self, id: ThmId, row: CnfId) -> Result<(), Error> {
        let index = row.get();
        let theorem = self.theorem_mut(id)?;
        let row = theorem
            .0
            .0
            .0
            .get_mut(row.position())
            .and_then(Option::as_mut)
            .ok_or(Error::MissingCnfRow {
                id: id.get(),
                index,
            })?;
        row.sort_unstable();
        row.dedup();
        Ok(())
    }

    /// Normalizes one indexed DNF row in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or indexed cube is absent.
    pub fn normalize_dnf(&mut self, id: ThmId, row: DnfId) -> Result<(), Error> {
        let index = row.get();
        let theorem = self.theorem_mut(id)?;
        let row = theorem
            .1
            .0
            .0
            .get_mut(row.position())
            .and_then(Option::as_mut)
            .ok_or(Error::MissingDnfRow {
                id: id.get(),
                index,
            })?;
        row.sort_unstable();
        row.dedup();
        Ok(())
    }

    fn position(id: ThmId) -> usize {
        id.position()
    }

    fn theorem_mut(&mut self, id: ThmId) -> Result<&mut ThmRow, Error> {
        self.slots
            .get_mut(Self::position(id))
            .and_then(Option::as_mut)
            .ok_or(Error::MissingTheorem { id: id.get() })
    }

    /// Replaces an existing slot with an untrusted sequent.
    ///
    /// This is a storage operation, not an inference rule.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent or deleted.
    pub fn replace(&mut self, id: ThmId, premises: Cnf, conclusions: Dnf) -> Result<(), Error> {
        self.replace_row(id, ThmRow::new(premises, conclusions))
    }

    fn replace_row(&mut self, id: ThmId, theorem: ThmRow) -> Result<(), Error> {
        *self.theorem_mut(id)? = theorem;
        Ok(())
    }
}

/// An LCF wrapper whose resident sequents are universally valid.
///
/// Unlike [`ClassicalArena`], this type has no arbitrary insertion or
/// replacement operation. Its private arena can only be extended through
/// sound syllogism rules and completed refutations.
#[derive(Clone, Debug, Default)]
pub struct ClassicalKernel {
    arena: ClassicalArena,
}

impl ClassicalKernel {
    /// Constructs an empty classical kernel.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            arena: ClassicalArena::new(),
        }
    }

    /// Borrows one universally valid resident theorem.
    #[must_use]
    pub fn get(&self, id: ThmId) -> Option<ThmRef<'_>> {
        self.arena.get(id)
    }

    /// Restricts mutation to the sound classical inference surface.
    pub fn rules(&mut self) -> CheckedArena<'_> {
        CheckedArena::new(&mut self.arena)
    }

    /// Introduces identity.
    ///
    /// # Errors
    ///
    /// Returns an error if theorem storage is exhausted.
    pub fn identity(&mut self, literal: Lit) -> Result<ThmId, Error> {
        self.rules().identity(literal)
    }

    /// Weakens a resident theorem in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem is absent.
    pub fn weaken(&mut self, id: ThmId, cnf: &[LitVec], dnf: &[LitVec]) -> Result<(), Error> {
        self.rules().weaken(id, cnf, dnf)
    }

    /// Cuts a unit literal between two resident theorems.
    ///
    /// # Errors
    ///
    /// Returns an error unless both theorems contain the required unit row.
    pub fn cut(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        self.rules().cut(left, right, literal)
    }

    /// Resolves complementary unit DNF rows.
    ///
    /// # Errors
    ///
    /// Returns an error unless both theorems contain the required unit row.
    pub fn resolve(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        self.rules().resolve(left, right, literal)
    }

    /// Copies a universally valid theorem into a fresh slot.
    ///
    /// # Errors
    ///
    /// Returns an error if the source is absent or storage is exhausted.
    pub fn copy(&mut self, source: ThmId) -> Result<ThmId, Error> {
        self.rules().copy(source)
    }

    /// Removes one theorem, returning whether it was live.
    pub fn remove(&mut self, id: ThmId) -> bool {
        self.rules().remove(id)
    }
}

/// An LCF certificate that one CNF is universally unsatisfiable.
#[derive(Clone, Debug)]
pub struct Refutation {
    theorem: ThmRow,
}

impl Refutation {
    /// Borrows the certified sequent `goal |- []`.
    #[must_use]
    pub fn theorem(&self) -> ThmRef<'_> {
        self.theorem.view()
    }
}

/// One explicitly delimited RAT resolvent check over dense CNF row IDs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RatGroup {
    /// Live row containing the complementary pivot.
    pub opposing: CnfId,
    /// Ordered RUP hints for its resolvent.
    pub hints: Vec<CnfId>,
}

/// A stateful CNF refutation preserving `Unsat(state) -> Unsat(goal)`.
#[derive(Debug)]
pub struct Refuter {
    goal: Cnf,
    state: Cnf,
    derived_empty: bool,
}

impl Refuter {
    /// Opens a stateful refutation whose initial state is `goal`.
    #[must_use]
    pub fn new(goal: Cnf) -> Self {
        Self {
            derived_empty: goal.contains_empty_row(),
            state: goal.clone(),
            goal,
        }
    }

    /// Borrows the original CNF being refuted.
    #[must_use]
    pub const fn goal(&self) -> &Cnf {
        &self.goal
    }

    /// Borrows the current CNF state.
    #[must_use]
    pub const fn state(&self) -> &Cnf {
        &self.state
    }

    /// Borrows one live current-state row.
    ///
    /// # Errors
    ///
    /// Returns an error if the row is absent or deleted.
    pub fn row(&self, id: CnfId) -> Result<&[Lit], Error> {
        self.state.row(id).map(LitVec::as_slice)
    }

    /// Learns a row by ordered reverse unit propagation.
    ///
    /// # Errors
    ///
    /// Returns an error if a hint is absent or the trail does not conflict.
    pub fn learn_rup(&mut self, row: LitVec, hints: &[CnfId]) -> Result<CnfId, Error> {
        let mut trail = falsifying_trail(&row);
        if !trail_conflicts(&trail) && !propagate(&self.state, &mut trail, hints)? {
            return Err(Error::NoConflict);
        }
        self.derived_empty |= row.is_empty();
        self.state.append(row)
    }

    /// Deletes one live row while retaining its stable tombstoned index.
    ///
    /// # Errors
    ///
    /// Returns an error if the row is absent or already deleted.
    pub fn remove(&mut self, id: CnfId) -> Result<(), Error> {
        self.state.remove(id).map(drop)
    }

    /// Finishes after deriving an empty row.
    ///
    /// Deriving the empty row permanently certifies the goal, so deleting that
    /// row afterward does not discard the certificate.
    ///
    /// # Errors
    ///
    /// Returns an error unless an empty row has been derived.
    pub fn done(self) -> Result<Refutation, Error> {
        if !self.derived_empty {
            return Err(Error::NoRefutation);
        }
        Ok(Refutation {
            theorem: ThmRow::new(self.goal, Dnf::default()),
        })
    }
    /// Learns a row by RUP or complete explicit RAT groups.
    ///
    /// # Errors
    ///
    /// Returns an error if the pivot, propagation, or opposing-row coverage is invalid.
    pub fn learn_rat(
        &mut self,
        row: LitVec,
        pivot: Lit,
        prefix_hints: &[CnfId],
        groups: &[RatGroup],
    ) -> Result<CnfId, Error> {
        if row.first().copied() != Some(pivot) {
            return Err(Error::BadPivot);
        }
        let mut prefix = falsifying_trail(&row);
        if trail_conflicts(&prefix) || propagate(&self.state, &mut prefix, prefix_hints)? {
            self.derived_empty |= row.is_empty();
            return self.state.append(row);
        }
        check_rat(&self.state, pivot, &prefix, groups)?;
        self.derived_empty |= row.is_empty();
        self.state.append(row)
    }
}

fn falsifying_trail(row: &[Lit]) -> BTreeSet<Lit> {
    row.iter().copied().map(Lit::negated).collect()
}

fn trail_conflicts(trail: &BTreeSet<Lit>) -> bool {
    trail
        .iter()
        .any(|literal| trail.contains(&literal.negated()))
}

fn propagate(state: &Cnf, trail: &mut BTreeSet<Lit>, hints: &[CnfId]) -> Result<bool, Error> {
    for id in hints {
        let row = state.row(*id)?;
        if row.iter().any(|literal| trail.contains(literal)) {
            return Err(Error::UselessHint { id: id.get() });
        }
        let mut open = row
            .iter()
            .copied()
            .filter(|literal| !trail.contains(&literal.negated()));
        match (open.next(), open.next()) {
            (None, _) => return Ok(true),
            (Some(unit), None) => {
                trail.insert(unit);
            }
            _ => return Err(Error::UselessHint { id: id.get() }),
        }
    }
    Ok(false)
}

fn check_rat(
    state: &Cnf,
    pivot: Lit,
    prefix: &BTreeSet<Lit>,
    groups: &[RatGroup],
) -> Result<(), Error> {
    let complement = pivot.negated();
    let mut covered = BTreeSet::new();
    for group in groups {
        if !covered.insert(group.opposing) {
            return Err(Error::DuplicateRatGroup {
                id: group.opposing.get(),
            });
        }
        let opposing = state.row(group.opposing)?;
        if !opposing.contains(&complement) {
            return Err(Error::WrongOpposingCnf {
                id: group.opposing.get(),
            });
        }
        let mut trail = prefix.clone();
        let mut tautological = false;
        for literal in opposing
            .iter()
            .copied()
            .filter(|literal| *literal != complement)
        {
            if trail.contains(&literal) {
                tautological = true;
                break;
            }
            trail.insert(literal.negated());
        }
        if !tautological && !propagate(state, &mut trail, &group.hints)? {
            return Err(Error::NoConflict);
        }
    }
    for (position, row) in state.0.0.iter().enumerate() {
        let Some(row) = row else { continue };
        let id = CnfId::new(i32::try_from(position + 1).expect("CNF slot is i32-bounded"))
            .expect("CNF slots are one-based");
        if row.contains(&complement) && !covered.contains(&id) {
            return Err(Error::IncompleteRat { id: id.get() });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(value: i32) -> Lit {
        Lit::new(value)
    }

    fn row(values: impl IntoIterator<Item = Lit>) -> LitVec {
        values.into_iter().collect()
    }

    fn cnf_id(value: i32) -> CnfId {
        CnfId::new(value).unwrap()
    }

    fn dnf_id(value: i32) -> DnfId {
        DnfId::new(value).unwrap()
    }

    fn eval_lit(literal: Lit, valuation: usize) -> bool {
        let variable = usize::try_from(literal.get().unsigned_abs()).unwrap() - 1;
        let positive = valuation & (1 << variable) != 0;
        if literal.is_positive() {
            positive
        } else {
            !positive
        }
    }

    fn eval_cnf_row(row: &[Lit], valuation: usize) -> bool {
        row.iter().any(|&p| eval_lit(p, valuation))
    }

    fn eval_dnf_row(row: &[Lit], valuation: usize) -> bool {
        row.iter().all(|&p| eval_lit(p, valuation))
    }

    fn sound(theorem: &ThmRow, variables: usize) -> bool {
        (0..(1 << variables)).all(|valuation| {
            let left = theorem
                .left()
                .rows()
                .all(|row| eval_cnf_row(row, valuation));
            let right = theorem
                .right()
                .rows()
                .any(|row| eval_dnf_row(row, valuation));
            !left || right
        })
    }

    fn all_sound(arena: &ClassicalArena, ids: &[ThmId]) {
        for &id in ids {
            assert!(sound(arena.theorem(id).unwrap(), 3));
        }
    }

    #[test]
    fn literal_boundaries_and_involution() {
        assert!(Lit::try_new(0).is_err());
        assert!(Lit::try_new(i32::MIN).is_err());
        assert!(Lit::try_new(i32::MIN + 1).is_err());
        assert!(Lit::try_new(i32::MAX).is_err());
        for value in [i32::MIN + 2, -1, 1, i32::MAX - 1] {
            let literal = lit(value);
            assert_eq!(literal.negated().negated(), literal);
        }
    }

    #[test]
    fn resident_indices_are_positive_nonzero_i32_values() {
        assert_eq!(
            std::mem::size_of::<ThmId>(),
            std::mem::size_of::<NonZeroI32>()
        );
        assert_eq!(
            std::mem::size_of::<CnfId>(),
            std::mem::size_of::<NonZeroI32>()
        );
        assert_eq!(
            std::mem::size_of::<DnfId>(),
            std::mem::size_of::<NonZeroI32>()
        );
        for rejected in [i32::MIN, -1, 0] {
            assert!(ThmId::new(rejected).is_none());
            assert!(CnfId::new(rejected).is_none());
            assert!(DnfId::new(rejected).is_none());
        }
        assert_eq!(ThmId::new(i32::MAX).unwrap().get(), i32::MAX);
        assert_eq!(CnfId::new(i32::MAX).unwrap().get(), i32::MAX);
        assert_eq!(DnfId::new(i32::MAX).unwrap().get(), i32::MAX);
    }

    #[test]
    fn identity_weakening_and_normalization_are_sound() {
        let mut arena = ClassicalArena::new();
        let theorem = arena.identity(lit(1)).unwrap();
        arena
            .weaken(
                theorem,
                &[row([lit(2), lit(2), lit(-3)])],
                &[row([lit(2), lit(2)])],
            )
            .unwrap();
        assert!(sound(arena.theorem(theorem).unwrap(), 3));
        arena.normalize(theorem).unwrap();
        assert!(sound(arena.theorem(theorem).unwrap(), 3));
        assert!(
            arena
                .theorem(theorem)
                .unwrap()
                .left()
                .rows()
                .any(|row| row == [lit(-3), lit(2)])
        );
    }

    #[test]
    fn transfers_are_semantic_equivalences_including_empty_rows() {
        let literals = [lit(-2), lit(-1), lit(1), lit(2)];
        let cases = (0_u8..16).map(|mask| {
            row(literals
                .iter()
                .enumerate()
                .filter(|(index, _)| mask & (1 << index) != 0)
                .map(|(_, literal)| *literal))
        });
        for clause in cases {
            let original = ThmRow::new(
                Cnf::new([row([lit(2)]), clause]),
                Dnf::new([row([lit(-3)])]),
            );
            let mut arena = ClassicalArena::new();
            let id = arena.store(original.clone()).unwrap();
            arena.move_cnf_right(id, cnf_id(2)).unwrap();
            for valuation in 0..8 {
                assert_eq!(
                    sequent_value(&original, valuation),
                    sequent_value(arena.theorem(id).unwrap(), valuation)
                );
            }
            arena.move_dnf_left(id, dnf_id(2)).unwrap();
            for valuation in 0..8 {
                assert_eq!(
                    sequent_value(&original, valuation),
                    sequent_value(arena.theorem(id).unwrap(), valuation)
                );
            }
        }
    }

    fn sequent_value(theorem: &ThmRow, valuation: usize) -> bool {
        let left = theorem
            .left()
            .rows()
            .all(|row| eval_cnf_row(row, valuation));
        let right = theorem
            .right()
            .rows()
            .any(|row| eval_dnf_row(row, valuation));
        !left || right
    }

    #[test]
    fn cut_and_resolution_preserve_soundness_exhaustively() {
        let mut arena = ClassicalArena::new();
        let p = lit(1);
        let q = lit(2);
        let r = lit(3);
        let cut_left = arena
            .store(ThmRow::new(
                Cnf::from([row([q])]),
                Dnf::new([row([p]), row([q])]),
            ))
            .unwrap();
        let cut_right = arena
            .store(ThmRow::new(
                Cnf::new([row([p]), row([r])]),
                Dnf::from([row([r])]),
            ))
            .unwrap();
        let cut = arena.cut(cut_left, cut_right, p).unwrap();

        let resolution_left = arena
            .store(ThmRow::new(
                Cnf::from([row([q])]),
                Dnf::new([row([p]), row([q])]),
            ))
            .unwrap();
        let resolution_right = arena
            .store(ThmRow::new(
                Cnf::from([row([r])]),
                Dnf::new([row([p.negated()]), row([r])]),
            ))
            .unwrap();
        let resolved = arena.resolve(resolution_left, resolution_right, p).unwrap();
        all_sound(
            &arena,
            &[
                cut_left,
                cut_right,
                cut,
                resolution_left,
                resolution_right,
                resolved,
            ],
        );
    }

    #[test]
    fn failed_mutations_are_atomic_and_do_not_allocate() {
        let mut arena = ClassicalArena::new();
        let id = arena.identity(lit(1)).unwrap();
        let original = arena.theorem(id).unwrap().clone();
        assert!(arena.move_cnf_right(id, cnf_id(8)).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);
        assert!(arena.move_dnf_left(id, dnf_id(8)).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);
        assert!(arena.cut(id, id, lit(2)).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);
        assert!(arena.resolve(id, id, lit(2)).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);
        assert!(arena.normalize_cnf(id, cnf_id(8)).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);
        assert!(arena.normalize_dnf(id, dnf_id(8)).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);

        let next = arena.identity(lit(2)).unwrap();
        assert_eq!(next.get(), id.get() + 1);
    }

    #[test]
    fn cut_and_resolution_require_exact_unit_rows_and_fail_atomically() {
        let mut arena = ClassicalArena::new();
        let p = lit(1);
        let q = lit(2);
        let left = arena
            .store(ThmRow::new(Cnf::from([row([q])]), Dnf::from([row([p])])))
            .unwrap();
        let right = arena
            .store(ThmRow::new(
                Cnf::from([row([p, q])]),
                Dnf::from([row([p.negated(), q])]),
            ))
            .unwrap();
        let left_before = arena.theorem(left).unwrap().clone();
        let right_before = arena.theorem(right).unwrap().clone();

        assert_eq!(
            arena.cut(left, right, p),
            Err(Error::MissingUnit { literal: p.get() })
        );
        assert_eq!(arena.theorem(left).unwrap(), &left_before);
        assert_eq!(arena.theorem(right).unwrap(), &right_before);
        assert_eq!(
            arena.resolve(left, right, p),
            Err(Error::MissingUnit {
                literal: p.negated().get()
            })
        );
        assert_eq!(arena.theorem(left).unwrap(), &left_before);
        assert_eq!(arena.theorem(right).unwrap(), &right_before);

        let next = arena.identity(q).unwrap();
        assert_eq!(next.get(), right.get() + 1);
    }

    #[test]
    fn copy_delete_and_free_list_reuse_one_slot() {
        let mut arena = ClassicalArena::new();
        let first = arena.identity(lit(1)).unwrap();
        let copied = arena.copy(first).unwrap();
        assert_ne!(first, copied);
        let removed = arena.theorem(first).unwrap().clone();
        assert!(arena.remove(first));
        assert_eq!(
            arena.theorem(first),
            Err(Error::MissingTheorem { id: first.get() })
        );
        assert!(!arena.remove(first));
        let reused = arena.store(removed).unwrap();
        assert_eq!(reused, first);
        assert_eq!(arena.theorem(reused), arena.theorem(copied));
    }

    #[test]
    fn theorem_wire_format_is_canonical_and_has_golden_cbor_bytes() {
        let theorem = ThmRow::new(
            Cnf::new([row([lit(2), lit(-1)])]),
            Dnf::new([row([]), row([lit(3)])]),
        );
        let mut bytes = Vec::new();
        covalence_lib_cbor::into_writer(&theorem, &mut bytes).unwrap();
        assert_eq!(
            bytes,
            [0x82, 0x81, 0x82, 0x20, 0x02, 0x82, 0x80, 0x81, 0x03]
        );

        let decoded: ThmRow = covalence_lib_cbor::from_reader(bytes.as_slice()).unwrap();
        let mut normalized = theorem.clone();
        normalized.normalize();
        assert_eq!(decoded, normalized);
        let value: covalence_lib_cbor::Value =
            covalence_lib_cbor::from_reader(bytes.as_slice()).unwrap();
        assert!(matches!(value, covalence_lib_cbor::Value::Array(parts) if parts.len() == 2));

        for rejected in [0_i32, i32::MIN, -(i32::MAX), i32::MAX] {
            let mut encoded = Vec::new();
            covalence_lib_cbor::into_writer(&rejected, &mut encoded).unwrap();
            assert!(
                covalence_lib_cbor::from_reader::<Lit, _>(encoded.as_slice()).is_err(),
                "accepted invalid literal {rejected}"
            );
        }
    }

    #[test]
    fn arena_wire_format_omits_holes_and_rebuilds_dense_slots() {
        let mut arena = ClassicalArena::new();
        let removed = arena.identity(lit(3)).unwrap();
        let retained = arena
            .store(ThmRow::new(
                Cnf::new([row([lit(2), lit(-1)])]),
                Dnf::new([row([]), row([lit(3)])]),
            ))
            .unwrap();
        assert!(arena.remove(removed));

        let mut bytes = Vec::new();
        covalence_lib_cbor::into_writer(&arena, &mut bytes).unwrap();
        assert_eq!(
            bytes,
            [0x81, 0x82, 0x81, 0x82, 0x20, 0x02, 0x82, 0x80, 0x81, 0x03]
        );

        let mut decoded: ClassicalArena =
            covalence_lib_cbor::from_reader(bytes.as_slice()).unwrap();
        let dense = ThmId::new(1).unwrap();
        let mut retained_theorem = arena.theorem(retained).unwrap().clone();
        retained_theorem.normalize();
        assert_eq!(decoded.theorem(dense).unwrap(), &retained_theorem);
        assert_eq!(decoded.identity(lit(2)).unwrap(), ThmId::new(2).unwrap());
    }

    #[test]
    fn wire_decode_rejects_noncanonical_theorems() {
        // [[2, -1]] is not in the canonical literal order.
        let noncanonical = [0x82, 0x81, 0x82, 0x02, 0x20, 0x80];
        assert!(covalence_lib_cbor::from_reader::<ThmRow, _>(&noncanonical[..]).is_err());
    }

    #[test]
    fn normalization_preserves_tautologies_contradictions_and_empty_rows() {
        let mut theorem = ThmRow::new(
            Cnf::new([row([lit(1), lit(-1), lit(1)]), row([]), row([])]),
            Dnf::new([row([lit(2), lit(-2), lit(2)]), row([]), row([])]),
        );
        let before: Vec<_> = (0..4)
            .map(|valuation| sequent_value(&theorem, valuation))
            .collect();
        theorem.normalize();
        let after: Vec<_> = (0..4)
            .map(|valuation| sequent_value(&theorem, valuation))
            .collect();
        assert_eq!(before, after);
        assert_eq!(theorem.left().rows().count(), 2);
        assert_eq!(theorem.right().rows().count(), 2);
        assert!(theorem.left().rows().any(|row| row == [lit(-1), lit(1)]));
        assert!(theorem.right().rows().any(|row| row == [lit(-2), lit(2)]));
    }

    #[test]
    fn two_atom_rule_universe_is_exhaustively_sound() {
        let literals = [lit(-2), lit(-1), lit(1), lit(2)];
        let clauses: Vec<_> = (0_u8..16)
            .map(|mask| {
                row(literals
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| mask & (1 << index) != 0)
                    .map(|(_, literal)| *literal))
            })
            .collect();
        let cubes: Vec<_> = clauses
            .iter()
            .map(|values| row(values.iter().copied()))
            .collect();

        for (clause, cube) in clauses.iter().zip(&cubes) {
            let mut theorem = ThmRow::new(
                Cnf::new([row(clause.iter().chain(clause).copied())]),
                Dnf::new([row(cube.iter().chain(cube).copied())]),
            );
            let before: Vec<_> = (0..4)
                .map(|valuation| sequent_value(&theorem, valuation))
                .collect();
            theorem.normalize();
            let after: Vec<_> = (0..4)
                .map(|valuation| sequent_value(&theorem, valuation))
                .collect();
            assert_eq!(before, after);
        }

        let mut cnfs = vec![Cnf::default()];
        cnfs.extend(clauses.iter().cloned().map(|clause| Cnf::new([clause])));
        let mut dnfs = vec![Dnf::default()];
        dnfs.extend(cubes.iter().cloned().map(|cube| Dnf::new([cube])));
        let sound_theorems: Vec<_> = cnfs
            .iter()
            .flat_map(|cnf| {
                dnfs.iter()
                    .map(move |dnf| ThmRow::new(cnf.clone(), dnf.clone()))
            })
            .filter(|theorem| sound(theorem, 2))
            .collect();

        for theorem in &sound_theorems {
            for clause in &clauses {
                let mut arena = ClassicalArena::new();
                let id = arena.store(theorem.clone()).unwrap();
                arena.weaken(id, std::slice::from_ref(clause), &[]).unwrap();
                assert!(sound(arena.theorem(id).unwrap(), 2));
            }
            for cube in &cubes {
                let mut arena = ClassicalArena::new();
                let id = arena.store(theorem.clone()).unwrap();
                arena.weaken(id, &[], std::slice::from_ref(cube)).unwrap();
                assert!(sound(arena.theorem(id).unwrap(), 2));
            }
        }

        for left in &sound_theorems {
            for right in &sound_theorems {
                for pivot in [lit(-1), lit(-2), lit(1), lit(2)] {
                    let cut_applies = left.right().rows().any(|row| row == [pivot])
                        && right.left().rows().any(|row| row == [pivot]);
                    if cut_applies {
                        let mut arena = ClassicalArena::new();
                        let left = arena.store(left.clone()).unwrap();
                        let right = arena.store(right.clone()).unwrap();
                        let result = arena.cut(left, right, pivot).unwrap();
                        assert!(sound(arena.theorem(result).unwrap(), 2));
                    }

                    let resolution_applies = left.right().rows().any(|row| row == [pivot])
                        && right.right().rows().any(|row| row == [pivot.negated()]);
                    if resolution_applies {
                        let mut arena = ClassicalArena::new();
                        let left = arena.store(left.clone()).unwrap();
                        let right = arena.store(right.clone()).unwrap();
                        let result = arena.resolve(left, right, pivot).unwrap();
                        assert!(sound(arena.theorem(result).unwrap(), 2));
                    }
                }
            }
        }
    }

    #[test]
    fn rat_checks_exact_live_coverage_and_is_transactional() {
        let p = lit(1);
        let q = lit(2);
        let goal = Cnf::new([row([p.negated(), q]), row([p])]);
        let mut refuter = Refuter::new(goal);
        let opposing = cnf_id(1);
        let forcing = cnf_id(2);
        let before = refuter.state().clone();

        assert_eq!(
            refuter.learn_rat(row([p]), p.negated(), &[], &[]),
            Err(Error::BadPivot)
        );
        assert_eq!(refuter.state(), &before);
        assert_eq!(
            refuter.learn_rat(row([p]), p, &[], &[]),
            Err(Error::IncompleteRat { id: opposing.get() })
        );
        assert_eq!(refuter.state(), &before);
        assert_eq!(
            refuter.learn_rat(
                row([p]),
                p,
                &[],
                &[RatGroup {
                    opposing: forcing,
                    hints: vec![],
                }],
            ),
            Err(Error::WrongOpposingCnf { id: forcing.get() })
        );
        assert_eq!(refuter.state(), &before);
        assert_eq!(
            refuter.learn_rat(
                row([p]),
                p,
                &[],
                &[
                    RatGroup {
                        opposing,
                        hints: vec![forcing],
                    },
                    RatGroup {
                        opposing,
                        hints: vec![forcing],
                    },
                ],
            ),
            Err(Error::DuplicateRatGroup { id: opposing.get() })
        );
        assert_eq!(refuter.state(), &before);

        let learned = refuter
            .learn_rat(
                row([p]),
                p,
                &[],
                &[RatGroup {
                    opposing,
                    hints: vec![forcing],
                }],
            )
            .unwrap();
        assert_eq!(refuter.row(learned).unwrap(), [p]);
    }

    #[test]
    fn rat_coverage_ignores_deleted_rows_but_rejects_deleted_hints() {
        let p = lit(1);
        let q = lit(2);
        let mut refuter = Refuter::new(Cnf::new([
            row([p.negated(), q]),
            row([p]),
            row([q.negated()]),
        ]));
        let opposing = cnf_id(1);
        let forcing = cnf_id(2);
        let deleted = cnf_id(3);
        refuter.remove(opposing).unwrap();
        refuter.remove(deleted).unwrap();
        let before = refuter.state().clone();

        // Once the sole opposing row is deleted, the RAT coverage obligation
        // is empty. Deleted rows remain tombstones and cannot be used as hints.
        let learned = refuter.learn_rat(row([p]), p, &[], &[]).unwrap();
        assert_eq!(refuter.row(learned).unwrap(), [p]);
        assert_eq!(
            refuter.learn_rup(row([p]), &[deleted]),
            Err(Error::MissingCnf { id: deleted.get() })
        );
        assert_ne!(refuter.state(), &before);
        assert_eq!(refuter.row(forcing).unwrap(), [p]);
    }

    #[test]
    fn tautological_rat_resolvent_needs_no_propagation_hints() {
        let p = lit(1);
        let q = lit(2);
        let mut refuter = Refuter::new(Cnf::new([row([p.negated(), q.negated()])]));
        let learned = refuter
            .learn_rat(
                row([p, q]),
                p,
                &[],
                &[RatGroup {
                    opposing: cnf_id(1),
                    hints: vec![],
                }],
            )
            .unwrap();
        assert_eq!(refuter.row(learned).unwrap(), [p, q]);
    }

    #[test]
    fn done_requires_a_derived_empty_row() {
        let p = lit(1);

        assert!(matches!(
            Refuter::new(Cnf::new([row([p])])).done(),
            Err(Error::NoRefutation)
        ));

        let mut derived = Refuter::new(Cnf::new([row([])]));
        derived.remove(cnf_id(1)).unwrap();
        assert!(derived.done().is_ok());
    }

    #[test]
    fn completed_refutation_copies_through_checked_arenas_and_reuses_slots() {
        let p = lit(1);
        let refutation = Refuter::new(Cnf::new([row([]), row([p])])).done().unwrap();
        let mut first = ClassicalArena::new();
        let mut second = ClassicalArena::new();
        let first_id = CheckedArena::new(&mut first)
            .copy_refutation(&refutation)
            .unwrap();
        let second_id = CheckedArena::new(&mut second)
            .copy_refutation(&refutation)
            .unwrap();
        assert_eq!(first.get(first_id), second.get(second_id));
        assert!(first.remove(first_id));
        let reused = CheckedArena::new(&mut first)
            .copy_refutation(&refutation)
            .unwrap();
        assert_eq!(reused, first_id);
        assert_eq!(first.get(reused), second.get(second_id));
    }
}
