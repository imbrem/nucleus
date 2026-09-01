//! Compatibility surface for the former matrix API.
//!
//! `Cnf` and `Dnf` are untrusted construction and projection values. Every
//! live arena slot is backed by the selected tagged runtime: raw arenas carry
//! [`tagged::Checked`] syntax, while [`ClassicalKernel`] carries sealed
//! [`tagged::Theorem`] facts. One-based IDs are only external handles.

use std::{collections::BTreeSet, num::NonZeroI32};

use covalence_lib_error::snafu::Snafu;
use serde::{
    Deserialize, Deserializer, Serialize, Serializer, de,
    ser::{SerializeSeq, SerializeTuple},
};
use smallvec::SmallVec;

use crate::tagged::{self, Formula, Sequent};

/// A signed, losslessly negatable Boolean literal.
///
/// Negative values denote positive propositions; positive values denote their
/// negations. This preserves the established Ethane-facing convention.
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
    /// Returns an error unless the magnitude is nonzero and below `i32::MAX`.
    pub const fn try_new(value: i32) -> Result<Self, LitError> {
        if value.unsigned_abs() >= i32::MAX as u32 {
            return Err(LitError { value });
        }
        match NonZeroI32::new(value) {
            Some(value) => Ok(Self(value)),
            None => Err(LitError { value }),
        }
    }

    /// Encodes a positive proposition occurrence from its magnitude.
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

    fn formula(self) -> Formula {
        Formula::Literal {
            atom: u64::from(self.magnitude()),
            negative: !self.is_positive(),
        }
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

/// Compact literal storage optimized for unit and binary rows.
pub type LitVec = SmallVec<[Lit; 2]>;

#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
struct Matrix(Vec<Option<LitVec>>);

/// An untrusted conjunction of disjunctive literal rows.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct Cnf(Matrix);

/// An untrusted disjunction of conjunctive literal rows.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct Dnf(Matrix);

macro_rules! semantic_matrix {
    ($name:ident) => {
        impl $name {
            /// Constructs the empty matrix.
            #[must_use]
            pub const fn empty() -> Self {
                Self(Matrix(Vec::new()))
            }

            /// Constructs a matrix without normalizing it.
            #[must_use]
            pub fn new(rows: impl IntoIterator<Item = LitVec>) -> Self {
                Self(Matrix(rows.into_iter().map(Some).collect()))
            }

            /// Iterates over live rows in insertion order.
            pub fn rows(&self) -> impl Iterator<Item = &[Lit]> {
                self.0.0.iter().filter_map(Option::as_deref)
            }

            /// Clones live rows, omitting neutral tombstones.
            #[must_use]
            pub fn to_rows(&self) -> Vec<LitVec> {
                self.0.0.iter().flatten().cloned().collect()
            }

            /// Sorts and deduplicates rows and literals and removes tombstones.
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

    fn formula(&self) -> Formula {
        Formula::And {
            negative: false,
            children: self
                .rows()
                .map(|row| Formula::Or {
                    negative: false,
                    children: row.iter().copied().map(Lit::formula).collect(),
                })
                .collect(),
        }
    }
}

impl Dnf {
    fn formula(&self) -> Formula {
        Formula::Or {
            negative: false,
            children: self
                .rows()
                .map(|row| Formula::And {
                    negative: false,
                    children: row.iter().copied().map(Lit::formula).collect(),
                })
                .collect(),
        }
    }
}

/// A borrowed CNF projection of tagged checked syntax.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CnfRef<'a>(&'a [Option<LitVec>]);

/// A borrowed DNF projection of tagged checked syntax.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DnfRef<'a>(&'a [Option<LitVec>]);

macro_rules! matrix_ref {
    ($name:ident, $owned:ident) => {
        impl<'a> $name<'a> {
            /// Iterates over live rows, skipping tombstones.
            pub fn rows(self) -> impl Iterator<Item = &'a [Lit]> {
                self.0.iter().filter_map(Option::as_deref)
            }

            /// Copies live rows into compact owned storage.
            #[must_use]
            pub fn to_rows(self) -> Vec<LitVec> {
                self.0.iter().flatten().cloned().collect()
            }

            /// Copies this projection into an untrusted builder.
            #[must_use]
            pub fn to_owned(self) -> $owned {
                $owned::new(self.to_rows())
            }
        }
    };
}

matrix_ref!(CnfRef, Cnf);
matrix_ref!(DnfRef, Dnf);

/// A borrowed compatibility projection interpreted as `CNF |- DNF`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ThmRef<'a> {
    /// Conjunctive left-hand side.
    pub lhs: CnfRef<'a>,
    /// Disjunctive right-hand side.
    pub rhs: DnfRef<'a>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Projection(Cnf, Dnf);

impl Projection {
    const fn new(left: Cnf, right: Dnf) -> Self {
        Self(left, right)
    }

    fn view(&self) -> ThmRef<'_> {
        ThmRef {
            lhs: CnfRef(&self.0.0.0),
            rhs: DnfRef(&self.1.0.0),
        }
    }

    fn sequent(&self) -> Sequent {
        Sequent {
            premise: self.0.formula(),
            conclusion: self.1.formula(),
        }
    }
}

impl Serialize for Projection {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut tuple = serializer.serialize_tuple(2)?;
        tuple.serialize_element(&self.0)?;
        tuple.serialize_element(&self.1)?;
        tuple.end()
    }
}

impl<'de> Deserialize<'de> for Projection {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let (left, right) = <(Cnf, Dnf)>::deserialize(deserializer)?;
        Ok(Self(left, right))
    }
}

macro_rules! one_based_id {
    ($name:ident, $summary:literal) => {
        #[doc = $summary]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        #[repr(transparent)]
        pub struct $name(NonZeroI32);

        impl $name {
            /// Constructs a positive one-based index.
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

            /// Returns the positive one-based index.
            #[must_use]
            pub const fn get(self) -> i32 {
                self.0.get()
            }

            fn position(self) -> usize {
                usize::try_from(self.get() - 1).expect("positive i32 fits usize")
            }
        }
    };
}

one_based_id!(ThmId, "An ephemeral one-based theorem handle.");
one_based_id!(CnfId, "A one-based CNF-row identifier.");
one_based_id!(DnfId, "A one-based DNF-row identifier.");

/// A classical compatibility operation failure.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// The theorem handle is absent or deleted.
    #[snafu(display("theorem {id} is absent"))]
    MissingTheorem {
        /// Missing handle.
        id: i32,
    },
    /// The indexed CNF row is absent.
    #[snafu(display("CNF row {index} is absent from theorem {id}"))]
    MissingCnfRow {
        /// The theorem handle.
        id: i32,
        /// Missing row.
        index: i32,
    },
    /// The indexed DNF row is absent.
    #[snafu(display("DNF row {index} is absent from theorem {id}"))]
    MissingDnfRow {
        /// The theorem handle.
        id: i32,
        /// Missing row.
        index: i32,
    },
    /// A required unit literal is absent.
    #[snafu(display("required unit literal {literal} is absent"))]
    MissingUnit {
        /// Required signed literal.
        literal: i32,
    },
    /// No further handle can be represented.
    #[snafu(display("theorem arena is full"))]
    ArenaFull,
    /// A refutation hint names no live CNF row.
    #[snafu(display("CNF row {id} is absent"))]
    MissingCnf {
        /// Missing row.
        id: i32,
    },
    /// A propagation hint is not unit or conflicting.
    #[snafu(display("CNF row {id} is not unit under the propagation trail"))]
    UselessHint {
        /// Rejected row.
        id: i32,
    },
    /// Reverse unit propagation did not reach a conflict.
    #[snafu(display("reverse unit propagation did not reach a conflict"))]
    NoConflict,
    /// The declared RAT pivot is not first.
    #[snafu(display("the declared RAT pivot is not the row's first literal"))]
    BadPivot,
    /// A RAT group lacks the complementary pivot.
    #[snafu(display("CNF row {id} does not contain the complementary RAT pivot"))]
    WrongOpposingCnf {
        /// Rejected row.
        id: i32,
    },
    /// Two RAT groups name the same row.
    #[snafu(display("CNF row {id} has more than one RAT group"))]
    DuplicateRatGroup {
        /// Duplicate row.
        id: i32,
    },
    /// A live opposing row has no RAT group.
    #[snafu(display("CNF row {id} has no RAT group"))]
    IncompleteRat {
        /// Missing row.
        id: i32,
    },
    /// The refuter has not derived an empty row.
    #[snafu(display("the current CNF state has not been refuted"))]
    NoRefutation,
    /// Canonical tagged packing rejected a compatibility projection.
    #[snafu(transparent)]
    Tagged {
        /// Tagged runtime failure.
        source: tagged::RuntimeError,
    },
    /// A sealed tagged matrix operation rejected its structural inputs.
    #[snafu(transparent)]
    TaggedEdit {
        /// Tagged theorem-rule failure.
        source: tagged::EditError,
    },
}

#[derive(Clone, Debug)]
struct SyntaxSlot {
    checked: tagged::Checked,
    projection: Projection,
}

impl SyntaxSlot {
    fn pack(projection: Projection) -> Result<Self, Error> {
        let checked = tagged::pack(&[projection.sequent()])?;
        Ok(Self {
            checked,
            projection,
        })
    }

    fn view(&self) -> ThmRef<'_> {
        debug_assert_eq!(self.checked.sequents(), &[self.projection.sequent()]);
        self.projection.view()
    }
}

impl PartialEq for SyntaxSlot {
    fn eq(&self, other: &Self) -> bool {
        self.checked == other.checked
    }
}

impl Eq for SyntaxSlot {}

/// Mutable checked-syntax storage with stable external handles and LIFO reuse.
///
/// The projection cached beside each [`tagged::Checked`] value is untrusted and
/// used only to preserve borrowed matrix views. Every insertion and mutation
/// is repacked and checked before its slot changes.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ClassicalArena {
    slots: Vec<Option<SyntaxSlot>>,
    free: Vec<ThmId>,
}

// This compatibility representation is deliberately the historical sequence
// of matrix projections. It is embedded in the current HOL wire format and is
// not the versioned tagged-arena leaf. Standalone canonical DRISL encoding
// lives in `covalence-data-classical`; migrating HOL is a separate wire change.
impl Serialize for ClassicalArena {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.live_theorems().count()))?;
        for slot in self.slots.iter().flatten() {
            sequence.serialize_element(&slot.projection)?;
        }
        sequence.end()
    }
}

impl<'de> Deserialize<'de> for ClassicalArena {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let rows = Vec::<Projection>::deserialize(deserializer)?;
        let mut arena = Self::new();
        for row in rows {
            arena.store_projection(row).map_err(de::Error::custom)?;
        }
        Ok(arena)
    }
}

impl ClassicalArena {
    /// Constructs empty checked-syntax storage.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: Vec::new(),
            free: Vec::new(),
        }
    }

    /// Iterates over live projections in handle order.
    pub fn live_theorems(&self) -> impl Iterator<Item = ThmRef<'_>> {
        self.slots.iter().flatten().map(SyntaxSlot::view)
    }

    /// Iterates over validated, non-theorem syntax in handle order.
    pub fn live_checked(&self) -> impl Iterator<Item = &tagged::Checked> {
        self.slots.iter().flatten().map(|slot| &slot.checked)
    }

    /// Borrows a live compatibility projection.
    #[must_use]
    pub fn get(&self, id: ThmId) -> Option<ThmRef<'_>> {
        self.slot(id).ok().map(SyntaxSlot::view)
    }

    /// Borrows the selected-runtime syntax behind one live external handle.
    #[must_use]
    pub fn checked(&self, id: ThmId) -> Option<&tagged::Checked> {
        self.slot(id).ok().map(|slot| &slot.checked)
    }

    fn slot(&self, id: ThmId) -> Result<&SyntaxSlot, Error> {
        self.slots
            .get(id.position())
            .and_then(Option::as_ref)
            .ok_or(Error::MissingTheorem { id: id.get() })
    }

    fn projection(&self, id: ThmId) -> Result<&Projection, Error> {
        Ok(&self.slot(id)?.projection)
    }

    fn allocate(&mut self, slot: SyntaxSlot) -> Result<ThmId, Error> {
        if let Some(id) = self.free.pop() {
            self.slots[id.position()] = Some(slot);
            return Ok(id);
        }
        let id = self
            .slots
            .len()
            .checked_add(1)
            .and_then(|value| i32::try_from(value).ok())
            .and_then(ThmId::new)
            .ok_or(Error::ArenaFull)?;
        self.slots.push(Some(slot));
        Ok(id)
    }

    fn store_projection(&mut self, projection: Projection) -> Result<ThmId, Error> {
        let slot = SyntaxSlot::pack(projection)?;
        self.allocate(slot)
    }

    fn replace_projection(&mut self, id: ThmId, projection: Projection) -> Result<(), Error> {
        let replacement = SyntaxSlot::pack(projection)?;
        let slot = self
            .slots
            .get_mut(id.position())
            .and_then(Option::as_mut)
            .ok_or(Error::MissingTheorem { id: id.get() })?;
        *slot = replacement;
        Ok(())
    }

    /// Inserts untrusted matrix syntax after canonical tagged validation.
    ///
    /// # Errors
    ///
    /// Returns an error if packing fails or no handle is available.
    pub fn insert(&mut self, premises: Cnf, conclusions: Dnf) -> Result<ThmId, Error> {
        self.store_projection(Projection::new(premises, conclusions))
    }

    /// Copies checked syntax into a fresh handle.
    ///
    /// # Errors
    ///
    /// Returns an error if the source is absent, repacking fails, or storage is full.
    pub fn copy(&mut self, source: ThmId) -> Result<ThmId, Error> {
        let projection = self.projection(source)?.clone();
        self.store_projection(projection)
    }

    /// Removes one live handle and makes it the next reusable handle.
    pub fn remove(&mut self, id: ThmId) -> bool {
        let Some(slot) = self.slots.get_mut(id.position()).and_then(Option::take) else {
            return false;
        };
        self.free.push(id);
        drop(slot);
        true
    }

    /// Inserts identity syntax.
    ///
    /// # Errors
    ///
    /// Returns an error if packing fails or storage is full.
    pub fn identity(&mut self, literal: Lit) -> Result<ThmId, Error> {
        self.insert(
            Cnf::new([std::iter::once(literal).collect()]),
            Dnf::new([std::iter::once(literal).collect()]),
        )
    }

    /// Weakens checked syntax transactionally.
    ///
    /// # Errors
    ///
    /// Returns an error if the handle is absent or replacement packing fails.
    pub fn weaken(&mut self, id: ThmId, left: &[LitVec], right: &[LitVec]) -> Result<(), Error> {
        let mut replacement = self.projection(id)?.clone();
        replacement.0.0.0.extend(left.iter().cloned().map(Some));
        replacement.1.0.0.extend(right.iter().cloned().map(Some));
        self.replace_projection(id, replacement)
    }

    /// Applies matrix cut to checked syntax and stores a fresh result.
    ///
    /// # Errors
    ///
    /// Returns an error for absent inputs, pivots, packing failure, or exhaustion.
    pub fn cut(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        let result = cut_projection(
            self.projection(left)?.clone(),
            self.projection(right)?.clone(),
            literal,
        )?;
        self.store_projection(result)
    }

    /// Applies matrix resolution to checked syntax and stores a fresh result.
    ///
    /// # Errors
    ///
    /// Returns an error for absent inputs, pivots, packing failure, or exhaustion.
    pub fn resolve(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        let result = resolve_projection(
            self.projection(left)?.clone(),
            self.projection(right)?.clone(),
            literal,
        )?;
        self.store_projection(result)
    }

    /// Moves one CNF row right and complements every literal.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent handle or row, or packing failure.
    pub fn move_cnf_right(&mut self, id: ThmId, row: CnfId) -> Result<(), Error> {
        let mut replacement = self.projection(id)?.clone();
        let source = replacement
            .0
            .0
            .0
            .get_mut(row.position())
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
        self.replace_projection(id, replacement)
    }

    /// Moves one DNF row left and complements every literal.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent handle or row, or packing failure.
    pub fn move_dnf_left(&mut self, id: ThmId, row: DnfId) -> Result<(), Error> {
        let mut replacement = self.projection(id)?.clone();
        let source = replacement
            .1
            .0
            .0
            .get_mut(row.position())
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
        self.replace_projection(id, replacement)
    }

    /// Sorts and deduplicates one CNF row transactionally.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent handle or row, or packing failure.
    pub fn normalize_cnf(&mut self, id: ThmId, row: CnfId) -> Result<(), Error> {
        let mut replacement = self.projection(id)?.clone();
        let target = replacement
            .0
            .0
            .0
            .get_mut(row.position())
            .and_then(Option::as_mut)
            .ok_or(Error::MissingCnfRow {
                id: id.get(),
                index: row.get(),
            })?;
        target.sort_unstable();
        target.dedup();
        self.replace_projection(id, replacement)
    }

    /// Sorts and deduplicates one DNF row transactionally.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent handle or row, or packing failure.
    pub fn normalize_dnf(&mut self, id: ThmId, row: DnfId) -> Result<(), Error> {
        let mut replacement = self.projection(id)?.clone();
        let target = replacement
            .1
            .0
            .0
            .get_mut(row.position())
            .and_then(Option::as_mut)
            .ok_or(Error::MissingDnfRow {
                id: id.get(),
                index: row.get(),
            })?;
        target.sort_unstable();
        target.dedup();
        self.replace_projection(id, replacement)
    }

    /// Replaces a live handle after packing and validating the new syntax.
    ///
    /// # Errors
    ///
    /// Returns an error if the handle is absent or packing fails. On failure,
    /// the resident checked value is unchanged.
    pub fn replace(&mut self, id: ThmId, premises: Cnf, conclusions: Dnf) -> Result<(), Error> {
        self.replace_projection(id, Projection::new(premises, conclusions))
    }
}

fn remove_unit(matrix: &mut Matrix, literal: Lit) -> Result<(), Error> {
    let position = matrix
        .0
        .iter()
        .position(|row| row.as_deref() == Some(&[literal]))
        .ok_or(Error::MissingUnit {
            literal: literal.get(),
        })?;
    matrix.0.remove(position);
    Ok(())
}

fn cut_projection(
    mut left: Projection,
    mut right: Projection,
    literal: Lit,
) -> Result<Projection, Error> {
    remove_unit(&mut left.1.0, literal)?;
    remove_unit(&mut right.0.0, literal)?;
    left.0.0.0.extend(right.0.0.0);
    left.1.0.0.extend(right.1.0.0);
    Ok(left)
}

fn resolve_projection(
    mut left: Projection,
    mut right: Projection,
    literal: Lit,
) -> Result<Projection, Error> {
    remove_unit(&mut left.1.0, literal)?;
    remove_unit(&mut right.1.0, literal.negated())?;
    left.0.0.0.extend(right.0.0.0);
    left.1.0.0.extend(right.1.0.0);
    Ok(left)
}

/// The sound, target-independent compatibility inference surface.
#[allow(clippy::missing_errors_doc)]
pub trait ClassicalRules {
    /// Borrows a resident sequent projection.
    fn get(&self, id: ThmId) -> Option<ThmRef<'_>>;
    /// Introduces identity.
    fn identity(&mut self, literal: Lit) -> Result<ThmId, Error>;
    /// Weakens a resident sequent in place.
    fn weaken(&mut self, id: ThmId, cnf: &[LitVec], dnf: &[LitVec]) -> Result<(), Error>;
    /// Cuts a unit literal between two sequents.
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
    /// Normalizes one CNF row.
    fn normalize_cnf(&mut self, id: ThmId, row: CnfId) -> Result<(), Error>;
    /// Normalizes one DNF row.
    fn normalize_dnf(&mut self, id: ThmId, row: DnfId) -> Result<(), Error>;
}

/// Capability view exposing theorem-preserving mutations of checked syntax.
///
/// This does not promote syntax to a universal theorem; it preserves whatever
/// ambient validity its caller has established for the resident slots.
pub struct CheckedArena<'a> {
    arena: &'a mut ClassicalArena,
}

impl<'a> CheckedArena<'a> {
    /// Restricts a mutable arena borrow to inference-shaped operations.
    #[must_use]
    pub const fn new(arena: &'a mut ClassicalArena) -> Self {
        Self { arena }
    }

    /// Borrows a resident projection.
    #[must_use]
    pub fn get(&self, id: ThmId) -> Option<ThmRef<'_>> {
        self.arena.get(id)
    }

    /// Iterates over live projections in handle order.
    pub fn live_theorems(&self) -> impl Iterator<Item = ThmRef<'_>> {
        self.arena.live_theorems()
    }

    /// Copies a universal theorem into ambient checked syntax.
    ///
    /// # Errors
    ///
    /// Returns an error if the source is absent, packing fails, or storage is full.
    pub fn copy_from(&mut self, source: &ClassicalKernel, id: ThmId) -> Result<ThmId, Error> {
        let projection = source
            .projection(id)
            .ok_or(Error::MissingTheorem { id: id.get() })?
            .clone();
        self.arena.store_projection(projection)
    }

    /// Copies a certified refutation into ambient checked syntax.
    ///
    /// # Errors
    ///
    /// Returns an error if packing fails or storage is full.
    pub fn copy_refutation(&mut self, refutation: &Refutation) -> Result<ThmId, Error> {
        self.arena.store_projection(refutation.projection.clone())
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
    fn normalize_cnf(&mut self, id: ThmId, row: CnfId) -> Result<(), Error> {
        self.arena.normalize_cnf(id, row)
    }
    fn normalize_dnf(&mut self, id: ThmId, row: DnfId) -> Result<(), Error> {
        self.arena.normalize_dnf(id, row)
    }
}

#[derive(Clone, Debug)]
struct TheoremSlot {
    theorem: tagged::Theorem,
    projection: Projection,
}

impl TheoremSlot {
    fn new(theorem: tagged::Theorem, projection: Projection) -> Self {
        assert_eq!(theorem.checked().sequents(), &[projection.sequent()]);
        Self {
            theorem,
            projection,
        }
    }

    fn view(&self) -> ThmRef<'_> {
        self.projection.view()
    }
}

/// LCF-style universal theorem storage backed only by sealed tagged facts.
#[derive(Clone, Debug, Default)]
pub struct ClassicalKernel {
    slots: Vec<Option<TheoremSlot>>,
    free: Vec<ThmId>,
}

impl ClassicalKernel {
    /// Constructs an empty classical kernel.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            slots: Vec::new(),
            free: Vec::new(),
        }
    }

    /// Borrows one universally valid theorem projection.
    #[must_use]
    pub fn get(&self, id: ThmId) -> Option<ThmRef<'_>> {
        self.slot(id).ok().map(TheoremSlot::view)
    }

    /// Borrows the sealed selected-runtime fact behind one live handle.
    #[must_use]
    pub fn theorem_fact(&self, id: ThmId) -> Option<&tagged::Theorem> {
        self.slot(id).ok().map(|slot| &slot.theorem)
    }

    fn slot(&self, id: ThmId) -> Result<&TheoremSlot, Error> {
        self.slots
            .get(id.position())
            .and_then(Option::as_ref)
            .ok_or(Error::MissingTheorem { id: id.get() })
    }

    fn projection(&self, id: ThmId) -> Option<&Projection> {
        self.slot(id).ok().map(|slot| &slot.projection)
    }

    fn allocate(&mut self, slot: TheoremSlot) -> Result<ThmId, Error> {
        if let Some(id) = self.free.pop() {
            self.slots[id.position()] = Some(slot);
            return Ok(id);
        }
        let id = self
            .slots
            .len()
            .checked_add(1)
            .and_then(|value| i32::try_from(value).ok())
            .and_then(ThmId::new)
            .ok_or(Error::ArenaFull)?;
        self.slots.push(Some(slot));
        Ok(id)
    }

    /// Opens the sealed theorem rule surface.
    pub fn rules(&mut self) -> KernelRules<'_> {
        KernelRules { kernel: self }
    }

    /// Introduces exact matrix identity through the sealed tagged rule.
    ///
    /// # Errors
    ///
    /// Returns an error if canonical tagged packing fails or storage is full.
    pub fn identity(&mut self, literal: Lit) -> Result<ThmId, Error> {
        self.rules().identity(literal)
    }

    /// Weakens a legacy matrix through sealed tagged row pushes.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent handle or tagged edit failure.
    pub fn weaken(&mut self, id: ThmId, cnf: &[LitVec], dnf: &[LitVec]) -> Result<(), Error> {
        self.rules().weaken(id, cnf, dnf)
    }

    /// Cuts a unit matrix row through the sealed tagged rule.
    ///
    /// # Errors
    ///
    /// Returns an error for absent inputs, pivots, or tagged packing failure.
    pub fn cut(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        self.rules().cut(left, right, literal)
    }

    /// Resolves complementary unit matrix rows through the sealed tagged rule.
    ///
    /// # Errors
    ///
    /// Returns an error for absent inputs, pivots, or tagged packing failure.
    pub fn resolve(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        self.rules().resolve(left, right, literal)
    }

    /// Copies a universal theorem into a fresh handle.
    ///
    /// # Errors
    ///
    /// Returns an error if the source is absent or storage is full.
    pub fn copy(&mut self, source: ThmId) -> Result<ThmId, Error> {
        self.rules().copy(source)
    }

    /// Removes one theorem and returns whether it was live.
    pub fn remove(&mut self, id: ThmId) -> bool {
        self.rules().remove(id)
    }
}

/// Borrowed access to sealed classical theorem rules.
pub struct KernelRules<'a> {
    kernel: &'a mut ClassicalKernel,
}

impl KernelRules<'_> {
    /// Seals an opaque checked refutation into a fresh tagged theorem slot.
    ///
    /// # Errors
    ///
    /// Returns an error if tagged packing fails or theorem storage is full.
    pub fn copy_refutation(&mut self, refutation: &Refutation) -> Result<ThmId, Error> {
        let theorem = tagged::Theorem::seal_refutation(refutation)?;
        self.kernel
            .allocate(TheoremSlot::new(theorem, refutation.projection.clone()))
    }

    fn normalize_row(
        &mut self,
        id: ThmId,
        side: tagged::Side,
        position: usize,
        external_index: i32,
    ) -> Result<(), Error> {
        let resident = self.kernel.slot(id)?.clone();
        let matrix = match side {
            tagged::Side::Left => &resident.projection.0.0,
            tagged::Side::Right => &resident.projection.1.0,
        };
        let live = live_row_position(matrix, position).ok_or_else(|| match side {
            tagged::Side::Left => Error::MissingCnfRow {
                id: id.get(),
                index: external_index,
            },
            tagged::Side::Right => Error::MissingDnfRow {
                id: id.get(),
                index: external_index,
            },
        })?;
        let mut normalized = matrix.0[position].clone().expect("live row was checked");
        normalized.sort_unstable();
        let theorem = resident
            .theorem
            .matrix_permute_row(0, side, live, formulas(&normalized))?;
        normalized.dedup();
        let theorem = theorem.matrix_dedupe_row(0, side, live)?;
        let mut projection = resident.projection;
        match side {
            tagged::Side::Left => projection.0.0.0[position] = Some(normalized),
            tagged::Side::Right => projection.1.0.0[position] = Some(normalized),
        }
        self.kernel.slots[id.position()] = Some(TheoremSlot::new(theorem, projection));
        Ok(())
    }
}

impl ClassicalRules for KernelRules<'_> {
    fn get(&self, id: ThmId) -> Option<ThmRef<'_>> {
        self.kernel.get(id)
    }

    fn identity(&mut self, literal: Lit) -> Result<ThmId, Error> {
        let theorem = tagged::Theorem::matrix_identity(literal.formula())?;
        let projection = Projection::new(
            Cnf::new([std::iter::once(literal).collect()]),
            Dnf::new([std::iter::once(literal).collect()]),
        );
        self.kernel.allocate(TheoremSlot::new(theorem, projection))
    }

    fn weaken(&mut self, id: ThmId, cnf: &[LitVec], dnf: &[LitVec]) -> Result<(), Error> {
        let resident = self.kernel.slot(id)?.clone();
        let mut theorem = resident.theorem;
        for row in cnf {
            theorem = theorem.matrix_weaken_row(0, tagged::Side::Left, formulas(row))?;
        }
        for row in dnf {
            theorem = theorem.matrix_weaken_row(0, tagged::Side::Right, formulas(row))?;
        }
        let mut projection = resident.projection;
        projection.0.0.0.extend(cnf.iter().cloned().map(Some));
        projection.1.0.0.extend(dnf.iter().cloned().map(Some));
        self.kernel.slots[id.position()] = Some(TheoremSlot::new(theorem, projection));
        Ok(())
    }

    fn cut(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        let left_slot = self.kernel.slot(left)?;
        let right_slot = self.kernel.slot(right)?;
        let projection = cut_projection(
            left_slot.projection.clone(),
            right_slot.projection.clone(),
            literal,
        )?;
        let theorem =
            left_slot
                .theorem
                .matrix_unit_cut(0, &right_slot.theorem, 0, literal.formula())?;
        self.kernel.allocate(TheoremSlot::new(theorem, projection))
    }

    fn resolve(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        let left_slot = self.kernel.slot(left)?;
        let right_slot = self.kernel.slot(right)?;
        let projection = resolve_projection(
            left_slot.projection.clone(),
            right_slot.projection.clone(),
            literal,
        )?;
        let theorem =
            left_slot
                .theorem
                .matrix_unit_resolve(0, &right_slot.theorem, 0, literal.formula())?;
        self.kernel.allocate(TheoremSlot::new(theorem, projection))
    }

    fn copy(&mut self, source: ThmId) -> Result<ThmId, Error> {
        let slot = self.kernel.slot(source)?.clone();
        self.kernel.allocate(slot)
    }

    fn remove(&mut self, id: ThmId) -> bool {
        let Some(slot) = self
            .kernel
            .slots
            .get_mut(id.position())
            .and_then(Option::take)
        else {
            return false;
        };
        self.kernel.free.push(id);
        drop(slot);
        true
    }

    fn move_cnf_right(&mut self, id: ThmId, row: CnfId) -> Result<(), Error> {
        let resident = self.kernel.slot(id)?.clone();
        let live = live_row_position(&resident.projection.0.0, row.position()).ok_or(
            Error::MissingCnfRow {
                id: id.get(),
                index: row.get(),
            },
        )?;
        let theorem = resident
            .theorem
            .matrix_cross_row(0, tagged::Side::Left, live)?;
        let mut projection = resident.projection;
        let source = projection.0.0.0[row.position()]
            .take()
            .expect("live row was checked");
        projection
            .1
            .0
            .0
            .push(Some(source.into_iter().map(Lit::negated).collect()));
        self.kernel.slots[id.position()] = Some(TheoremSlot::new(theorem, projection));
        Ok(())
    }

    fn move_dnf_left(&mut self, id: ThmId, row: DnfId) -> Result<(), Error> {
        let resident = self.kernel.slot(id)?.clone();
        let live = live_row_position(&resident.projection.1.0, row.position()).ok_or(
            Error::MissingDnfRow {
                id: id.get(),
                index: row.get(),
            },
        )?;
        let theorem = resident
            .theorem
            .matrix_cross_row(0, tagged::Side::Right, live)?;
        let mut projection = resident.projection;
        let source = projection.1.0.0[row.position()]
            .take()
            .expect("live row was checked");
        projection
            .0
            .0
            .0
            .push(Some(source.into_iter().map(Lit::negated).collect()));
        self.kernel.slots[id.position()] = Some(TheoremSlot::new(theorem, projection));
        Ok(())
    }

    fn normalize_cnf(&mut self, id: ThmId, row: CnfId) -> Result<(), Error> {
        self.normalize_row(id, tagged::Side::Left, row.position(), row.get())
    }

    fn normalize_dnf(&mut self, id: ThmId, row: DnfId) -> Result<(), Error> {
        self.normalize_row(id, tagged::Side::Right, row.position(), row.get())
    }
}

fn formulas(row: &[Lit]) -> Vec<Formula> {
    row.iter().copied().map(Lit::formula).collect()
}

fn live_row_position(matrix: &Matrix, position: usize) -> Option<usize> {
    matrix.0.get(position)?.as_ref()?;
    Some(matrix.0[..position].iter().flatten().count())
}

/// An opaque certificate produced by checked RUP/RAT state transitions.
///
/// It has no public constructor or deserializer. The sealed kernel may ingest
/// it without retaining or replaying parser data.
#[derive(Clone, Debug)]
pub struct Refutation {
    projection: Projection,
}

impl Refutation {
    /// Borrows the certified compatibility sequent `goal |- []`.
    #[must_use]
    pub fn theorem(&self) -> ThmRef<'_> {
        self.projection.view()
    }

    pub(crate) fn sequent_for_sealing(&self) -> Sequent {
        self.projection.sequent()
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

/// Stateful syntax-level CNF refutation checking.
#[derive(Debug)]
pub struct Refuter {
    goal: Cnf,
    state: Cnf,
    derived_empty: bool,
}

impl Refuter {
    /// Opens a goal and initializes the live state from it.
    #[must_use]
    pub fn new(goal: Cnf) -> Self {
        let derived_empty = goal.rows().any(<[Lit]>::is_empty);
        Self {
            state: goal.clone(),
            derived_empty,
            goal,
        }
    }

    /// Borrows the original goal.
    #[must_use]
    pub const fn goal(&self) -> &Cnf {
        &self.goal
    }

    /// Borrows the current clause state.
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
        let derived_empty = row.is_empty();
        let id = self.state.append(row)?;
        self.derived_empty |= derived_empty;
        Ok(id)
    }

    /// Deletes one live row while preserving its stable row ID.
    ///
    /// # Errors
    ///
    /// Returns an error if the row is absent or already deleted.
    pub fn remove(&mut self, id: CnfId) -> Result<(), Error> {
        self.state.remove(id).map(drop)
    }

    /// Finishes after deriving an empty row.
    ///
    /// # Errors
    ///
    /// Returns an error unless an empty row has been derived.
    pub fn done(self) -> Result<Refutation, Error> {
        if !self.derived_empty {
            return Err(Error::NoRefutation);
        }
        Ok(Refutation {
            projection: Projection::new(self.goal, Dnf::default()),
        })
    }

    /// Learns a row by RUP or complete explicit RAT groups.
    ///
    /// # Errors
    ///
    /// Returns an error if pivot, propagation, or opposing-row coverage fails.
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
            let derived_empty = row.is_empty();
            let id = self.state.append(row)?;
            self.derived_empty |= derived_empty;
            return Ok(id);
        }
        check_rat(&self.state, pivot, &prefix, groups)?;
        let derived_empty = row.is_empty();
        let id = self.state.append(row)?;
        self.derived_empty |= derived_empty;
        Ok(id)
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

    fn row<const N: usize>(values: [i32; N]) -> LitVec {
        values.into_iter().map(Lit::new).collect()
    }

    #[test]
    fn raw_slots_are_tagged_checked_and_reuse_lifo_handles() {
        let mut arena = ClassicalArena::new();
        let first = arena.insert(Cnf::new([row([-1])]), Dnf::default()).unwrap();
        let second = arena.insert(Cnf::default(), Dnf::new([row([-2])])).unwrap();
        assert!(arena.remove(first));
        assert!(arena.remove(second));
        let reused_second = arena.identity(Lit::positive(3)).unwrap();
        let reused_first = arena.identity(Lit::positive(4)).unwrap();
        assert_eq!((reused_second, reused_first), (second, first));
        for slot in arena.slots.iter().flatten() {
            assert_eq!(slot.checked.sequents(), &[slot.projection.sequent()]);
        }
    }

    #[test]
    fn failed_replacement_is_transactional() {
        let mut arena = ClassicalArena::new();
        let id = arena.identity(Lit::positive(1)).unwrap();
        let before = arena.clone();
        assert!(
            arena
                .replace(id, Cnf::new([row([i32::MAX - 1])]), Dnf::default())
                .is_ok()
        );
        // Missing-handle failure cannot disturb the successfully replaced slot.
        assert!(matches!(
            arena.replace(ThmId::new(2).unwrap(), Cnf::default(), Dnf::default()),
            Err(Error::MissingTheorem { .. })
        ));
        assert_ne!(arena, before);
        assert!(arena.get(id).is_some());
    }

    #[test]
    fn opaque_refuter_certificate_seals_through_the_tagged_kernel() {
        let refutation = Refuter::new(Cnf::new([LitVec::new()])).done().unwrap();
        let mut kernel = ClassicalKernel::new();
        let id = kernel.rules().copy_refutation(&refutation).unwrap();
        assert_eq!(kernel.get(id).unwrap().lhs.to_rows(), vec![LitVec::new()]);
        assert!(kernel.get(id).unwrap().rhs.rows().next().is_none());
        assert!(kernel.theorem_fact(id).is_some());
    }

    #[test]
    fn rat_accepts_a_tautological_opposing_remainder_without_hints() {
        let mut refuter = Refuter::new(Cnf::new([row([1, -2, 2])]));
        let learned = refuter
            .learn_rat(
                row([-1]),
                Lit::positive(1),
                &[],
                &[RatGroup {
                    opposing: CnfId::new(1).unwrap(),
                    hints: Vec::new(),
                }],
            )
            .unwrap();
        assert_eq!(learned, CnfId::new(2).unwrap());
    }

    #[test]
    fn sealed_matrix_rules_keep_exact_tagged_projections() {
        let p = Lit::positive(1);
        let q = Lit::positive(2);
        let mut kernel = ClassicalKernel::new();
        let identity = kernel.identity(p).unwrap();
        kernel
            .weaken(identity, &[row([-2, -1, -2])], &[row([-2, -1, -2])])
            .unwrap();
        kernel
            .rules()
            .normalize_cnf(identity, CnfId::new(2).unwrap())
            .unwrap();
        kernel
            .rules()
            .normalize_dnf(identity, DnfId::new(2).unwrap())
            .unwrap();
        let view = kernel.get(identity).unwrap();
        assert_eq!(view.lhs.to_rows(), vec![row([-1]), row([-2, -1])]);
        assert_eq!(view.rhs.to_rows(), vec![row([-1]), row([-2, -1])]);
        assert_eq!(
            kernel.theorem_fact(identity).unwrap().checked().sequents(),
            &[Projection::new(view.lhs.to_owned(), view.rhs.to_owned()).sequent()]
        );

        let crossed = kernel.identity(q).unwrap();
        kernel
            .rules()
            .move_cnf_right(crossed, CnfId::new(1).unwrap())
            .unwrap();
        let crossed_view = kernel.get(crossed).unwrap();
        assert!(crossed_view.lhs.rows().next().is_none());
        assert_eq!(crossed_view.rhs.to_rows(), vec![row([-2]), row([2])]);

        let left = kernel.identity(p).unwrap();
        let right = kernel.identity(p).unwrap();
        let cut = kernel.cut(left, right, p).unwrap();
        assert_eq!(kernel.get(cut).unwrap().lhs.to_rows(), vec![row([-1])]);
        assert_eq!(kernel.get(cut).unwrap().rhs.to_rows(), vec![row([-1])]);

        let positive = kernel.identity(p).unwrap();
        let negative = kernel.identity(p.negated()).unwrap();
        let resolved = kernel.resolve(positive, negative, p).unwrap();
        assert_eq!(
            kernel.get(resolved).unwrap().lhs.to_rows(),
            vec![row([-1]), row([1])]
        );
        assert!(kernel.get(resolved).unwrap().rhs.rows().next().is_none());
    }

    #[test]
    fn serde_rechecks_and_canonicalizes_runtime_storage() {
        let mut arena = ClassicalArena::new();
        arena.identity(Lit::positive(1)).unwrap();
        let mut bytes = Vec::new();
        covalence_lib_cbor::into_writer(&arena, &mut bytes).unwrap();
        let decoded: ClassicalArena = covalence_lib_cbor::from_reader(bytes.as_slice()).unwrap();
        assert_eq!(decoded, arena);
        assert!(
            decoded.slots[0]
                .as_ref()
                .unwrap()
                .checked
                .free_blocks()
                .is_empty()
        );
    }
}
