//! CNF construction and checked refutation.
//!
//! [`Matrix`] is untrusted syntax. Every stored mutation passes through the
//! tagged validator. Only [`ClassicalKernel`] stores theorem facts.

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

    /// Converts a conventional signed literal into the kernel encoding.
    ///
    /// # Errors
    ///
    /// Returns an error unless the literal is nonzero and its magnitude is
    /// below `i32::MAX`.
    pub const fn try_from_signed(value: i32) -> Result<Self, LitError> {
        match Self::try_new(value) {
            Ok(value) => Ok(value.negated()),
            Err(error) => Err(error),
        }
    }

    /// Returns the signed integer representation.
    #[must_use]
    pub const fn get(self) -> i32 {
        self.0.get()
    }

    /// Returns the conventional signed-literal representation.
    #[must_use]
    pub const fn signed(self) -> i32 {
        -self.get()
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
            atom: self.magnitude(),
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

/// An untrusted matrix of literal rows with positional tombstones.
///
/// A left matrix is a conjunction of disjunctive rows. A right matrix is a
/// disjunction of conjunctive rows.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct Matrix(Vec<Option<LitVec>>);

impl Matrix {
    /// Constructs the empty matrix.
    #[must_use]
    pub const fn empty() -> Self {
        Self(Vec::new())
    }

    /// Constructs a matrix without normalizing it.
    #[must_use]
    pub fn new(rows: impl IntoIterator<Item = LitVec>) -> Self {
        Self(rows.into_iter().map(Some).collect())
    }

    /// Iterates over live rows in insertion order.
    pub fn rows(&self) -> impl Iterator<Item = &[Lit]> {
        self.0.iter().filter_map(Option::as_deref)
    }

    /// Clones live rows, omitting neutral tombstones.
    #[must_use]
    pub fn to_rows(&self) -> Vec<LitVec> {
        self.0.iter().flatten().cloned().collect()
    }

    /// Sorts and deduplicates rows and literals and removes tombstones.
    pub fn normalize(&mut self) {
        let mut rows = self.0.drain(..).flatten().collect::<Vec<_>>();
        for row in &mut rows {
            row.sort_unstable_by_key(|literal| literal.signed());
            row.dedup();
        }
        rows.sort_unstable_by(|left, right| {
            left.iter()
                .map(|literal| literal.signed())
                .cmp(right.iter().map(|literal| literal.signed()))
        });
        rows.dedup();
        self.0 = rows.into_iter().map(Some).collect();
    }

    fn row(&self, id: RowId) -> Result<&LitVec, Error> {
        self.0
            .get(id.position())
            .and_then(Option::as_ref)
            .ok_or(Error::MissingCnf { id: id.get() })
    }

    fn append(&mut self, row: LitVec) -> Result<RowId, Error> {
        let id = self
            .0
            .len()
            .checked_add(1)
            .and_then(|value| i32::try_from(value).ok())
            .and_then(RowId::new)
            .ok_or(Error::ArenaFull)?;
        self.0.push(Some(row));
        Ok(id)
    }

    fn remove(&mut self, id: RowId) -> Result<LitVec, Error> {
        self.0
            .get_mut(id.position())
            .and_then(Option::take)
            .ok_or(Error::MissingCnf { id: id.get() })
    }

    /// Denotes this matrix as the formula on one side of the turnstile.
    fn formula(&self, side: tagged::Side) -> Formula {
        junction(
            side,
            self.rows()
                .map(|row| {
                    junction(
                        opposite(side),
                        row.iter().copied().map(Lit::formula).collect(),
                    )
                })
                .collect(),
        )
    }
}

impl<const N: usize> From<[LitVec; N]> for Matrix {
    fn from(value: [LitVec; N]) -> Self {
        Self::new(value)
    }
}

const fn opposite(side: tagged::Side) -> tagged::Side {
    match side {
        tagged::Side::Left => tagged::Side::Right,
        tagged::Side::Right => tagged::Side::Left,
    }
}

fn missing_row(id: ThmId, side: tagged::Side, row: RowId) -> Error {
    match side {
        tagged::Side::Left => Error::MissingCnfRow {
            id: id.get(),
            index: row.get(),
        },
        tagged::Side::Right => Error::MissingDnfRow {
            id: id.get(),
            index: row.get(),
        },
    }
}

fn junction(side: tagged::Side, children: Vec<Formula>) -> Formula {
    match side {
        tagged::Side::Left => Formula::And {
            negative: false,
            children,
        },
        tagged::Side::Right => Formula::Or {
            negative: false,
            children,
        },
    }
}

/// An owned matrix sequent interpreted as `CNF |- DNF`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ThmRef {
    /// Conjunctive left-hand side.
    pub lhs: Matrix,
    /// Disjunctive right-hand side.
    pub rhs: Matrix,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Projection(Matrix, Matrix);

impl Projection {
    const fn new(left: Matrix, right: Matrix) -> Self {
        Self(left, right)
    }

    fn view(&self) -> ThmRef {
        ThmRef {
            lhs: Matrix::new(self.0.to_rows()),
            rhs: Matrix::new(self.1.to_rows()),
        }
    }

    fn side_mut(&mut self, side: tagged::Side) -> &mut Matrix {
        match side {
            tagged::Side::Left => &mut self.0,
            tagged::Side::Right => &mut self.1,
        }
    }

    fn sequent(&self) -> Sequent {
        Sequent {
            premise: self.0.formula(tagged::Side::Left),
            conclusion: self.1.formula(tagged::Side::Right),
        }
    }

    fn from_sequent(sequent: &Sequent) -> Result<Self, Error> {
        Ok(Self(
            matrix_from_formula(&sequent.premise, tagged::Side::Left)?,
            matrix_from_formula(&sequent.conclusion, tagged::Side::Right)?,
        ))
    }
}

#[allow(clippy::manual_let_else)]
fn matrix_from_formula(formula: &Formula, side: tagged::Side) -> Result<Matrix, Error> {
    let children = match (side, formula) {
        (
            tagged::Side::Left,
            Formula::And {
                negative: false,
                children,
            },
        )
        | (
            tagged::Side::Right,
            Formula::Or {
                negative: false,
                children,
            },
        ) => children,
        _ => {
            return Err(Error::Tagged {
                source: tagged::RuntimeError::InvalidArena,
            });
        }
    };
    let mut rows = Vec::with_capacity(children.len());
    for child in children {
        let literals = match (side, child) {
            (
                tagged::Side::Left,
                Formula::Or {
                    negative: false,
                    children,
                },
            )
            | (
                tagged::Side::Right,
                Formula::And {
                    negative: false,
                    children,
                },
            ) => children,
            _ => {
                return Err(Error::Tagged {
                    source: tagged::RuntimeError::InvalidArena,
                });
            }
        };
        let mut row = LitVec::with_capacity(literals.len());
        for literal in literals {
            let Formula::Literal { atom, negative } = literal else {
                return Err(Error::Tagged {
                    source: tagged::RuntimeError::InvalidArena,
                });
            };
            let magnitude = i32::try_from(*atom).map_err(|_| Error::ArenaFull)?;
            row.push(Lit::new(if *negative { magnitude } else { -magnitude }));
        }
        rows.push(row);
    }
    Ok(Matrix::new(rows))
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
        let (left, right) = <(Matrix, Matrix)>::deserialize(deserializer)?;
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
one_based_id!(RowId, "A one-based matrix-row identifier.");

/// A classical operation failure.
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
    /// Canonical tagged packing rejected a matrix sequent.
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

/// One resident matrix sequent.
#[derive(Clone, Debug)]
struct SyntaxSlot {
    checked: tagged::Checked,
}

impl SyntaxSlot {
    /// Validates and packs untrusted syntax.
    fn pack(projection: &Projection) -> Result<Self, Error> {
        Ok(Self {
            checked: tagged::pack(&[projection.sequent()])?,
        })
    }

    fn projection(&self) -> Result<Projection, Error> {
        let sequent = self.checked.decode_sequents()?.pop().ok_or(Error::Tagged {
            source: tagged::RuntimeError::InvalidArena,
        })?;
        Projection::from_sequent(&sequent)
    }

    fn view(&self) -> Result<ThmRef, Error> {
        Ok(self.projection()?.view())
    }
}

impl PartialEq for SyntaxSlot {
    fn eq(&self, other: &Self) -> bool {
        self.checked == other.checked
    }
}

impl Eq for SyntaxSlot {}

/// Mutable checked syntax with stable handles and LIFO reuse.
///
/// Universal facts live in [`ClassicalKernel`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ClassicalArena {
    slots: Vec<Option<SyntaxSlot>>,
    free: Vec<ThmId>,
}

impl Serialize for ClassicalArena {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut sequence = serializer.serialize_seq(Some(self.live_theorems().count()))?;
        for slot in self.slots.iter().flatten() {
            sequence.serialize_element(&slot.projection().map_err(serde::ser::Error::custom)?)?;
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
            arena.store_projection(&row).map_err(de::Error::custom)?;
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
    pub fn live_theorems(&self) -> impl Iterator<Item = ThmRef> + '_ {
        self.slots
            .iter()
            .flatten()
            .filter_map(|slot| slot.view().ok())
    }

    /// Borrows a live matrix sequent.
    #[must_use]
    pub fn get(&self, id: ThmId) -> Option<ThmRef> {
        self.slot(id).ok()?.view().ok()
    }

    fn slot(&self, id: ThmId) -> Result<&SyntaxSlot, Error> {
        self.slots
            .get(id.position())
            .and_then(Option::as_ref)
            .ok_or(Error::MissingTheorem { id: id.get() })
    }

    fn projection(&self, id: ThmId) -> Result<Projection, Error> {
        self.slot(id)?.projection()
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

    fn store_projection(&mut self, projection: &Projection) -> Result<ThmId, Error> {
        let slot = SyntaxSlot::pack(projection)?;
        self.allocate(slot)
    }

    fn replace_projection(&mut self, id: ThmId, projection: &Projection) -> Result<(), Error> {
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
    pub fn insert(&mut self, premises: Matrix, conclusions: Matrix) -> Result<ThmId, Error> {
        self.store_projection(&Projection::new(premises, conclusions))
    }

    /// Copies checked syntax into a fresh handle.
    ///
    /// # Errors
    ///
    /// Returns an error if the source is absent, repacking fails, or storage is full.
    pub fn copy(&mut self, source: ThmId) -> Result<ThmId, Error> {
        let projection = self.projection(source)?;
        self.store_projection(&projection)
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

    /// Moves one indexed row across the turnstile, complementing its literals.
    ///
    /// The source row leaves a tombstone so that later row identifiers on that
    /// side stay stable.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent handle or row, or packing failure.
    pub fn cross_row(&mut self, id: ThmId, side: tagged::Side, row: RowId) -> Result<(), Error> {
        let slot = self
            .slots
            .get_mut(id.position())
            .and_then(Option::as_mut)
            .ok_or(Error::MissingTheorem { id: id.get() })?;
        if slot.checked.cross_matrix_row(side, row.position()) {
            return Ok(());
        }
        let mut replacement = self.projection(id)?;
        let source = replacement
            .side_mut(side)
            .0
            .get_mut(row.position())
            .and_then(Option::take)
            .ok_or_else(|| missing_row(id, side, row))?;
        replacement
            .side_mut(opposite(side))
            .0
            .push(Some(source.into_iter().map(Lit::negated).collect()));
        self.replace_projection(id, &replacement)
    }

    /// Sorts and deduplicates one indexed row transactionally.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent handle or row, or packing failure.
    pub fn normalize_row(
        &mut self,
        id: ThmId,
        side: tagged::Side,
        row: RowId,
    ) -> Result<(), Error> {
        let slot = self
            .slots
            .get_mut(id.position())
            .and_then(Option::as_mut)
            .ok_or(Error::MissingTheorem { id: id.get() })?;
        if slot.checked.normalize_matrix_row(side, row.position()) {
            Ok(())
        } else {
            Err(missing_row(id, side, row))
        }
    }

    /// Replaces a live handle after packing and validating the new syntax.
    ///
    /// # Errors
    ///
    /// Returns an error if the handle is absent or packing fails. On failure,
    /// the resident checked value is unchanged.
    pub fn replace(
        &mut self,
        id: ThmId,
        premises: Matrix,
        conclusions: Matrix,
    ) -> Result<(), Error> {
        self.replace_projection(id, &Projection::new(premises, conclusions))
    }
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

    /// Copies a certified refutation into ambient checked syntax.
    ///
    /// # Errors
    ///
    /// Returns an error if packing fails or storage is full.
    pub fn copy_refutation(&mut self, refutation: &Refutation) -> Result<ThmId, Error> {
        self.arena.store_projection(&refutation.projection)
    }
}

#[derive(Clone, Debug)]
struct TheoremSlot {
    theorem: tagged::Theorem,
}

impl TheoremSlot {
    const fn new(theorem: tagged::Theorem) -> Self {
        Self { theorem }
    }

    fn view(&self) -> Result<ThmRef, Error> {
        let sequent = self
            .theorem
            .checked()
            .decode_sequents()?
            .pop()
            .ok_or(Error::Tagged {
                source: tagged::RuntimeError::InvalidArena,
            })?;
        Ok(Projection::from_sequent(&sequent)?.view())
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
    pub fn get(&self, id: ThmId) -> Option<ThmRef> {
        self.slot(id).ok()?.view().ok()
    }

    /// Borrows the theorem fact behind a live handle.
    #[must_use]
    pub fn theorem_fact(&self, id: ThmId) -> Option<&tagged::Theorem> {
        self.slot(id).ok().map(|slot| &slot.theorem)
    }

    /// Derives the universal matrix refutation represented by a sealed
    /// negative-`SAT` theorem.
    #[must_use]
    pub fn refutation(&self, id: ThmId) -> Option<ThmRef> {
        let theorem = self.theorem_fact(id)?.refutation_to_false(0).ok()?;
        TheoremSlot::new(theorem).view().ok()
    }

    fn slot(&self, id: ThmId) -> Result<&TheoremSlot, Error> {
        self.slots
            .get(id.position())
            .and_then(Option::as_ref)
            .ok_or(Error::MissingTheorem { id: id.get() })
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

    /// Stores a checked refutation as a theorem fact.
    ///
    /// # Errors
    ///
    /// Returns an error if tagged packing fails or theorem storage is full.
    pub fn copy_refutation(&mut self, refutation: &Refutation) -> Result<ThmId, Error> {
        let theorem = tagged::Theorem::seal_refutation(refutation)?;
        self.allocate(TheoremSlot::new(theorem))
    }
}

/// A certificate produced by checked RUP/RAT transitions.
///
/// It has no public constructor or deserializer.
#[derive(Clone, Debug)]
pub struct Refutation {
    projection: Projection,
}

impl Refutation {
    /// Borrows the certified sequent `goal |- []`.
    #[must_use]
    pub fn theorem(&self) -> ThmRef {
        self.projection.view()
    }

    pub(crate) fn sequent_for_sealing(&self) -> Sequent {
        let clauses = self
            .projection
            .0
            .rows()
            .map(|clause| {
                junction(
                    tagged::Side::Right,
                    clause.iter().copied().map(Lit::formula).collect(),
                )
            })
            .collect();
        Sequent {
            premise: Formula::And {
                negative: false,
                children: Vec::new(),
            },
            conclusion: Formula::Sat {
                negative: true,
                children: clauses,
            },
        }
    }
}

/// One explicitly delimited RAT resolvent check over dense CNF row IDs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RatGroup {
    /// Live row containing the complementary pivot.
    pub opposing: RowId,
    /// Ordered RUP hints for its resolvent.
    pub hints: Vec<RowId>,
}

/// Stateful syntax-level CNF refutation checking.
#[derive(Debug)]
pub struct Refuter {
    goal: Matrix,
    state: Matrix,
    derived_empty: bool,
}

impl Refuter {
    /// Opens a goal and initializes the live state from it.
    #[must_use]
    pub fn new(goal: Matrix) -> Self {
        let derived_empty = goal.rows().any(<[Lit]>::is_empty);
        Self {
            state: goal.clone(),
            derived_empty,
            goal,
        }
    }

    /// Borrows the current clause state.
    #[must_use]
    pub const fn state(&self) -> &Matrix {
        &self.state
    }

    /// Borrows one live current-state row.
    ///
    /// # Errors
    ///
    /// Returns an error if the row is absent or deleted.
    pub fn row(&self, id: RowId) -> Result<&[Lit], Error> {
        self.state.row(id).map(LitVec::as_slice)
    }

    /// Learns a row by ordered reverse unit propagation.
    ///
    /// # Errors
    ///
    /// Returns an error if a hint is absent or the trail does not conflict.
    pub fn learn_rup(&mut self, row: LitVec, hints: &[RowId]) -> Result<RowId, Error> {
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
    pub fn remove(&mut self, id: RowId) -> Result<(), Error> {
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
            projection: Projection::new(self.goal, Matrix::default()),
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
        prefix_hints: &[RowId],
        groups: &[RatGroup],
    ) -> Result<RowId, Error> {
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

fn propagate(state: &Matrix, trail: &mut BTreeSet<Lit>, hints: &[RowId]) -> Result<bool, Error> {
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
    state: &Matrix,
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
    for (position, row) in state.0.iter().enumerate() {
        let Some(row) = row else { continue };
        let id = RowId::new(i32::try_from(position + 1).expect("CNF slot is i32-bounded"))
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

    fn identity(arena: &mut ClassicalArena, literal: Lit) -> Result<ThmId, Error> {
        arena.insert(
            Matrix::new([std::iter::once(literal).collect()]),
            Matrix::new([std::iter::once(literal).collect()]),
        )
    }

    #[test]
    fn checked_slots_reuse_lifo_handles() {
        let mut arena = ClassicalArena::new();
        let first = arena
            .insert(Matrix::new([row([-1])]), Matrix::default())
            .unwrap();
        let second = arena
            .insert(Matrix::default(), Matrix::new([row([-2])]))
            .unwrap();
        assert!(arena.remove(first));
        assert!(arena.remove(second));
        let reused_second = identity(&mut arena, Lit::positive(3)).unwrap();
        let reused_first = identity(&mut arena, Lit::positive(4)).unwrap();
        assert_eq!((reused_second, reused_first), (second, first));
        for slot in arena.slots.iter().flatten() {
            let sequent = slot.projection().unwrap().sequent();
            let packed = tagged::pack(std::slice::from_ref(&sequent)).unwrap();
            assert_eq!(packed.decode_sequents().unwrap(), [sequent]);
        }
    }

    #[test]
    fn slot_equality_sees_live_rows_and_not_tombstone_layout() {
        let mut crossed = ClassicalArena::new();
        let id = crossed
            .insert(Matrix::new([row([-1]), row([-2])]), Matrix::default())
            .unwrap();
        let words = crossed.slot(id).unwrap().checked.arena().words().len();
        crossed
            .cross_row(id, tagged::Side::Left, RowId::new(1).unwrap())
            .unwrap();
        assert_eq!(
            crossed.slot(id).unwrap().checked.arena().words().len(),
            words
        );

        let mut direct = ClassicalArena::new();
        direct
            .insert(Matrix::new([row([-2])]), Matrix::new([row([1])]))
            .unwrap();

        let view = crossed.get(id).unwrap();
        assert_eq!(view.lhs.to_rows(), vec![row([-2])]);
        assert_eq!(view.rhs.to_rows(), vec![row([1])]);
        assert_eq!(crossed, direct);
    }

    #[test]
    fn failed_replacement_is_transactional() {
        let mut arena = ClassicalArena::new();
        let id = identity(&mut arena, Lit::positive(1)).unwrap();
        let before = arena.clone();
        assert!(
            arena
                .replace(id, Matrix::new([row([500_000_000])]), Matrix::default())
                .is_ok()
        );
        // Missing-handle failure cannot disturb the successfully replaced slot.
        assert!(matches!(
            arena.replace(ThmId::new(2).unwrap(), Matrix::default(), Matrix::default()),
            Err(Error::MissingTheorem { .. })
        ));
        assert_ne!(arena, before);
        assert!(arena.get(id).is_some());
    }

    #[test]
    fn checked_refutation_enters_the_tagged_kernel() {
        let refutation = Refuter::new(Matrix::new([LitVec::new()])).done().unwrap();
        let mut kernel = ClassicalKernel::new();
        let id = kernel.copy_refutation(&refutation).unwrap();
        // The generic matrix projection cannot express negative `SAT`; inspect
        // the allocation-free tagged view instead.
        assert!(kernel.get(id).is_none());
        assert_eq!(kernel.refutation(id), Some(refutation.theorem()));
        let view = kernel.theorem_fact(id).unwrap().checked().view(0).unwrap();
        assert_eq!(view.premise.tag(), 0);
        assert!(view.premise.is_empty());
        assert_eq!(view.conclusion.tag(), 2);
        assert!(view.conclusion.is_negative());
        assert_eq!(
            kernel
                .theorem_fact(id)
                .unwrap()
                .checked()
                .decode_sequents()
                .unwrap(),
            [refutation.sequent_for_sealing()]
        );
    }

    #[test]
    fn rat_accepts_a_tautological_opposing_remainder_without_hints() {
        let mut refuter = Refuter::new(Matrix::new([row([1, -2, 2])]));
        let learned = refuter
            .learn_rat(
                row([-1]),
                Lit::positive(1),
                &[],
                &[RatGroup {
                    opposing: RowId::new(1).unwrap(),
                    hints: Vec::new(),
                }],
            )
            .unwrap();
        assert_eq!(learned, RowId::new(2).unwrap());
    }

    #[test]
    fn serde_round_trips_semantic_slots() {
        let mut arena = ClassicalArena::new();
        identity(&mut arena, Lit::positive(1)).unwrap();
        let mut bytes = Vec::new();
        covalence_lib_cbor::into_writer(&arena, &mut bytes).unwrap();
        let decoded: ClassicalArena = covalence_lib_cbor::from_reader(bytes.as_slice()).unwrap();
        assert_eq!(decoded, arena);
    }
}
