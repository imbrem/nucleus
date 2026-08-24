//! Polarity-aware storage and rules for finite classical matrix sequents.
//!
//! A [`Thm`] has the semantic shape `CNF ⊢ DNF`: its left side is a
//! conjunction of disjunctive [`Clause`]s, while its right side is a
//! disjunction of conjunctive [`Cube`]s. The distinct wrappers prevent code
//! from silently confusing these polarities.
//!
//! [`ClassicalArena::store`] is intentionally an untrusted storage operation.
//! An arena alone makes no logical claim about stored rows; an LCF kernel must
//! keep the arena private and expose only checked rule methods.

use std::num::{NonZeroI64, NonZeroU64};

use covalence_lib_error::snafu::Snafu;
use serde::{Deserialize, Deserializer, Serialize, Serializer, de};
use smallvec::SmallVec;

/// A signed, losslessly negatable proposition identifier.
///
/// Negative values denote positive propositions; positive values denote their
/// negations. This is the established Ethane wire convention.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Lit(NonZeroI64);

/// A failure to construct a signed proposition identifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(display("invalid signed proposition identifier {value}"))]
pub struct LitError {
    /// Rejected signed value.
    pub value: i64,
}

impl Lit {
    /// Encodes a positive proposition occurrence from its unsigned magnitude.
    ///
    /// # Panics
    ///
    /// Panics unless `magnitude` is nonzero and strictly below `i64::MAX`.
    #[must_use]
    pub fn positive(magnitude: u64) -> Self {
        let magnitude = i64::try_from(magnitude).expect("literal magnitude fits i64");
        assert!(
            magnitude > 0 && magnitude < i64::MAX,
            "literal magnitude is signed-bounded"
        );
        Self(NonZeroI64::new(-magnitude).expect("literal magnitude is nonzero"))
    }

    /// Constructs a nonzero, losslessly negatable literal.
    ///
    /// # Errors
    ///
    /// Returns an error unless the unsigned magnitude is nonzero and strictly
    /// below `i64::MAX`.
    pub const fn new(value: i64) -> Result<Self, LitError> {
        if value == 0 || value.unsigned_abs() >= i64::MAX as u64 {
            Err(LitError { value })
        } else {
            match NonZeroI64::new(value) {
                Some(value) => Ok(Self(value)),
                None => Err(LitError { value }),
            }
        }
    }

    /// Decodes a signed wire literal.
    ///
    /// # Errors
    ///
    /// Returns an error unless the unsigned magnitude is nonzero and strictly
    /// below `i64::MAX`.
    pub const fn from_raw(value: i64) -> Result<Self, LitError> {
        Self::new(value)
    }

    /// Returns the signed integer representation.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0.get()
    }

    /// Returns the complementary literal.
    ///
    /// # Panics
    ///
    /// Panics only if a `Lit` has been created outside its private invariant.
    #[must_use]
    pub const fn negated(self) -> Self {
        Self(NonZeroI64::new(-self.get()).expect("Lit excludes zero and i64::MIN"))
    }

    /// Returns whether this encoding denotes a positive proposition.
    #[must_use]
    pub const fn is_positive(self) -> bool {
        self.get() < 0
    }

    /// Returns the unsigned proposition magnitude.
    #[must_use]
    pub const fn magnitude(self) -> u64 {
        self.get().unsigned_abs()
    }
}

impl TryFrom<i64> for Lit {
    type Error = LitError;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl From<Lit> for i64 {
    fn from(value: Lit) -> Self {
        value.get()
    }
}

impl Serialize for Lit {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_i64(self.get())
    }
}

impl<'de> Deserialize<'de> for Lit {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(i64::deserialize(deserializer)?).map_err(de::Error::custom)
    }
}

/// Compact literal storage optimized for the common unit/binary row.
pub type LitVec = SmallVec<[Lit; 2]>;

/// A disjunction of literals on the left of a sequent.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct Clause(LitVec);

/// A conjunction of literals on the right of a sequent.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(transparent)]
pub struct Cube(LitVec);

macro_rules! literal_row {
    ($name:ident) => {
        impl $name {
            /// Constructs a row without imposing a normalization requirement.
            #[must_use]
            pub fn new(literals: impl IntoIterator<Item = Lit>) -> Self {
                Self(literals.into_iter().collect())
            }

            /// Returns the literals in insertion order.
            #[must_use]
            pub fn literals(&self) -> &[Lit] {
                &self.0
            }

            /// Returns the literals in insertion order.
            #[must_use]
            pub fn as_slice(&self) -> &[Lit] {
                &self.0
            }

            /// Sorts and deduplicates this row in place.
            pub fn normalize(&mut self) {
                self.0.sort_unstable();
                self.0.dedup();
            }

            fn is_unit(&self, literal: Lit) -> bool {
                self.0.as_slice() == [literal]
            }
        }

        impl<const N: usize> From<[Lit; N]> for $name {
            fn from(value: [Lit; N]) -> Self {
                Self::new(value)
            }
        }
    };
}

literal_row!(Clause);
literal_row!(Cube);

impl Clause {
    fn negated_cube(&self) -> Cube {
        Cube::new(self.0.iter().copied().map(Lit::negated))
    }
}

impl Cube {
    fn negated_clause(&self) -> Clause {
        Clause::new(self.0.iter().copied().map(Lit::negated))
    }
}

/// A conjunction of clauses.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct Cnf(Vec<Clause>);

/// A disjunction of cubes.
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(transparent)]
pub struct Dnf(Vec<Cube>);

macro_rules! matrix {
    ($name:ident, $row:ident, $accessor:ident) => {
        impl $name {
            /// Constructs a matrix without imposing a normalization requirement.
            #[must_use]
            pub fn new(rows: impl IntoIterator<Item = $row>) -> Self {
                Self(rows.into_iter().collect())
            }

            /// Returns the matrix rows in insertion order.
            #[must_use]
            pub fn $accessor(&self) -> &[$row] {
                &self.0
            }

            /// Returns the matrix rows in insertion order.
            #[must_use]
            pub fn as_slice(&self) -> &[$row] {
                &self.0
            }

            /// Sorts and deduplicates every row and then the matrix itself.
            pub fn normalize(&mut self) {
                for row in &mut self.0 {
                    row.normalize();
                }
                self.0.sort_unstable();
                self.0.dedup();
            }
        }

        impl<const N: usize> From<[$row; N]> for $name {
            fn from(value: [$row; N]) -> Self {
                Self::new(value)
            }
        }
    };
}

matrix!(Cnf, Clause, clauses);
matrix!(Dnf, Cube, cubes);

/// One matrix sequent, interpreted as `CNF ⊢ DNF`.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Thm(Cnf, Dnf);

impl Thm {
    /// Constructs a row for untrusted storage.
    #[must_use]
    pub const fn new(left: Cnf, right: Dnf) -> Self {
        Self(left, right)
    }

    /// Returns the conjunctive left matrix.
    #[must_use]
    pub const fn left(&self) -> &Cnf {
        &self.0
    }

    /// Returns the disjunctive right matrix.
    #[must_use]
    pub const fn right(&self) -> &Dnf {
        &self.1
    }

    /// Returns the conjunctive premises.
    #[must_use]
    pub const fn premises(&self) -> &Cnf {
        &self.0
    }

    /// Returns the disjunctive conclusions.
    #[must_use]
    pub const fn conclusions(&self) -> &Dnf {
        &self.1
    }

    /// Sorts and deduplicates rows and matrices on both sides.
    pub fn normalize(&mut self) {
        self.0.normalize();
        self.1.normalize();
    }
}

/// An ephemeral one-based theorem slot identifier.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ThmId(NonZeroU64);

impl ThmId {
    /// Constructs a one-based theorem slot identifier.
    #[must_use]
    pub const fn new(value: u64) -> Option<Self> {
        match NonZeroU64::new(value) {
            Some(value) => Some(Self(value)),
            None => None,
        }
    }

    /// Returns the one-based slot number.
    #[must_use]
    pub const fn get(self) -> u64 {
        self.0.get()
    }
}

/// A classical arena operation failure.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum Error {
    /// The theorem slot is absent or deleted.
    #[snafu(display("theorem {id} is absent"))]
    MissingTheorem {
        /// Missing one-based slot.
        id: u64,
    },
    /// The indexed left clause is absent.
    #[snafu(display("left clause {index} is absent from theorem {id}"))]
    MissingClause {
        /// The theorem slot.
        id: u64,
        /// Zero-based clause index.
        index: usize,
    },
    /// The indexed right cube is absent.
    #[snafu(display("right cube {index} is absent from theorem {id}"))]
    MissingCube {
        /// The theorem slot.
        id: u64,
        /// Zero-based cube index.
        index: usize,
    },
    /// A unit literal needed by a rule is absent.
    #[snafu(display("required unit literal {literal} is absent"))]
    MissingUnit {
        /// Required signed literal.
        literal: i64,
    },
    /// No further theorem slot can be represented.
    #[snafu(display("theorem arena is full"))]
    ArenaFull,
}

/// Mutable theorem-row storage with one-at-a-time deletion and slot reuse.
#[derive(Clone, Debug, Default)]
pub struct ClassicalArena {
    slots: Vec<Option<Thm>>,
    free: Vec<ThmId>,
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

    /// Borrows a stored row.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent or deleted.
    pub fn theorem(&self, id: ThmId) -> Result<&Thm, Error> {
        self.slots
            .get(Self::position(id))
            .and_then(Option::as_ref)
            .ok_or(Error::MissingTheorem { id: id.get() })
    }

    /// Stores an untrusted row.
    ///
    /// This is a storage operation, not an inference rule. Checked wrappers
    /// must ensure only sound rows enter their private arena.
    ///
    /// # Errors
    ///
    /// Returns an error if no further slot identifier can be represented.
    pub fn store(&mut self, theorem: Thm) -> Result<ThmId, Error> {
        if let Some(id) = self.free.pop() {
            self.slots[Self::position(id)] = Some(theorem);
            return Ok(id);
        }
        let next = self
            .slots
            .len()
            .checked_add(1)
            .and_then(|value| u64::try_from(value).ok())
            .and_then(ThmId::new)
            .ok_or(Error::ArenaFull)?;
        self.slots.push(Some(theorem));
        Ok(next)
    }

    /// Inserts an untrusted row into storage.
    ///
    /// This is an alias for [`Self::store`] intended for checked wrappers.
    ///
    /// # Errors
    ///
    /// Returns an error if no further slot identifier can be represented.
    pub fn insert(&mut self, theorem: Thm) -> Result<ThmId, Error> {
        self.store(theorem)
    }

    /// Copies one stored theorem into a newly allocated slot.
    ///
    /// # Errors
    ///
    /// Returns an error if `source` is absent or no slot is available.
    pub fn copy(&mut self, source: ThmId) -> Result<ThmId, Error> {
        let theorem = self.theorem(source)?.clone();
        self.store(theorem)
    }

    /// Removes exactly one theorem and makes its slot reusable.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent or already deleted.
    pub fn remove(&mut self, id: ThmId) -> Result<Thm, Error> {
        let theorem = self
            .slots
            .get_mut(Self::position(id))
            .and_then(Option::take)
            .ok_or(Error::MissingTheorem { id: id.get() })?;
        self.free.push(id);
        Ok(theorem)
    }

    /// Introduces the identity sequent `[[p]] ⊢ [[p]]`.
    ///
    /// # Errors
    ///
    /// Returns an error if no theorem slot is available.
    pub fn identity(&mut self, literal: Lit) -> Result<ThmId, Error> {
        self.store(Thm::new(
            Cnf::from([Clause::from([literal])]),
            Dnf::from([Cube::from([literal])]),
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
    pub fn weaken(&mut self, id: ThmId, left: &[Clause], right: &[Cube]) -> Result<(), Error> {
        let mut replacement = self.theorem(id)?.clone();
        replacement.0.0.extend_from_slice(left);
        replacement.1.0.extend_from_slice(right);
        self.replace(id, replacement)
    }

    /// Cuts a singleton literal from a right cube and a left clause.
    ///
    /// From `F ⊢ G ∨ p` and `p ∧ H ⊢ K`, derives `F ∧ H ⊢ G ∨ K`.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent theorem or required unit row.
    pub fn cut(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        let mut first = self.theorem(left)?.clone();
        let mut second = self.theorem(right)?.clone();
        let right_position = first
            .1
            .0
            .iter()
            .position(|cube| cube.is_unit(literal))
            .ok_or(Error::MissingUnit {
                literal: literal.get(),
            })?;
        let left_position = second
            .0
            .0
            .iter()
            .position(|clause| clause.is_unit(literal))
            .ok_or(Error::MissingUnit {
                literal: literal.get(),
            })?;
        first.1.0.remove(right_position);
        second.0.0.remove(left_position);
        first.0.0.extend(second.0.0);
        first.1.0.extend(second.1.0);
        self.store(first)
    }

    /// Resolves complementary singleton cubes on two theorem right sides.
    ///
    /// # Errors
    ///
    /// Returns an error for an absent theorem or required unit cube.
    pub fn resolve(&mut self, left: ThmId, right: ThmId, literal: Lit) -> Result<ThmId, Error> {
        let mut first = self.theorem(left)?.clone();
        let mut second = self.theorem(right)?.clone();
        let first_position = first
            .1
            .0
            .iter()
            .position(|cube| cube.is_unit(literal))
            .ok_or(Error::MissingUnit {
                literal: literal.get(),
            })?;
        let complement = literal.negated();
        let second_position = second
            .1
            .0
            .iter()
            .position(|cube| cube.is_unit(complement))
            .ok_or(Error::MissingUnit {
                literal: complement.get(),
            })?;
        first.1.0.remove(first_position);
        second.1.0.remove(second_position);
        first.0.0.extend(second.0.0);
        first.1.0.extend(second.1.0);
        self.store(first)
    }

    /// Moves one indexed left clause to a pointwise-negated right cube.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or indexed clause is absent.
    pub fn move_clause_right(&mut self, id: ThmId, index: usize) -> Result<(), Error> {
        let mut replacement = self.theorem(id)?.clone();
        if index >= replacement.0.0.len() {
            return Err(Error::MissingClause {
                id: id.get(),
                index,
            });
        }
        let clause = replacement.0.0.remove(index);
        replacement.1.0.push(clause.negated_cube());
        self.replace(id, replacement)
    }

    /// Moves one indexed right cube to a pointwise-negated left clause.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or indexed cube is absent.
    pub fn move_cube_left(&mut self, id: ThmId, index: usize) -> Result<(), Error> {
        let mut replacement = self.theorem(id)?.clone();
        if index >= replacement.1.0.len() {
            return Err(Error::MissingCube {
                id: id.get(),
                index,
            });
        }
        let cube = replacement.1.0.remove(index);
        replacement.0.0.push(cube.negated_clause());
        self.replace(id, replacement)
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

    /// Normalizes one indexed left clause in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or indexed clause is absent.
    pub fn normalize_clause(&mut self, id: ThmId, index: usize) -> Result<(), Error> {
        let theorem = self.theorem_mut(id)?;
        theorem
            .0
            .0
            .get_mut(index)
            .ok_or(Error::MissingClause {
                id: id.get(),
                index,
            })?
            .normalize();
        Ok(())
    }

    /// Normalizes one indexed right cube in place.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem or indexed cube is absent.
    pub fn normalize_cube(&mut self, id: ThmId, index: usize) -> Result<(), Error> {
        let theorem = self.theorem_mut(id)?;
        theorem
            .1
            .0
            .get_mut(index)
            .ok_or(Error::MissingCube {
                id: id.get(),
                index,
            })?
            .normalize();
        Ok(())
    }

    fn position(id: ThmId) -> usize {
        usize::try_from(id.get() - 1).unwrap_or(usize::MAX)
    }

    fn theorem_mut(&mut self, id: ThmId) -> Result<&mut Thm, Error> {
        self.slots
            .get_mut(Self::position(id))
            .and_then(Option::as_mut)
            .ok_or(Error::MissingTheorem { id: id.get() })
    }

    /// Replaces an existing slot with an untrusted row.
    ///
    /// This is a storage operation, not an inference rule.
    ///
    /// # Errors
    ///
    /// Returns an error if `id` is absent or deleted.
    pub fn replace(&mut self, id: ThmId, theorem: Thm) -> Result<(), Error> {
        *self.theorem_mut(id)? = theorem;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(value: i64) -> Lit {
        Lit::new(value).unwrap()
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

    fn eval_clause(clause: &Clause, valuation: usize) -> bool {
        clause.literals().iter().any(|&p| eval_lit(p, valuation))
    }

    fn eval_cube(cube: &Cube, valuation: usize) -> bool {
        cube.literals().iter().all(|&p| eval_lit(p, valuation))
    }

    fn sound(theorem: &Thm, variables: usize) -> bool {
        (0..(1 << variables)).all(|valuation| {
            let left = theorem
                .left()
                .clauses()
                .iter()
                .all(|clause| eval_clause(clause, valuation));
            let right = theorem
                .right()
                .cubes()
                .iter()
                .any(|cube| eval_cube(cube, valuation));
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
        assert!(Lit::new(0).is_err());
        assert!(Lit::new(i64::MIN).is_err());
        assert!(Lit::new(i64::MIN + 1).is_err());
        assert!(Lit::new(i64::MAX).is_err());
        for value in [i64::MIN + 2, -1, 1, i64::MAX - 1] {
            let literal = lit(value);
            assert_eq!(literal.negated().negated(), literal);
        }
    }

    #[test]
    fn identity_weakening_and_normalization_are_sound() {
        let mut arena = ClassicalArena::new();
        let theorem = arena.identity(lit(1)).unwrap();
        arena
            .weaken(
                theorem,
                &[Clause::new([lit(2), lit(2), lit(-3)])],
                &[Cube::new([lit(2), lit(2)])],
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
                .clauses()
                .iter()
                .any(|clause| clause.literals() == [lit(-3), lit(2)])
        );
    }

    #[test]
    fn transfers_are_semantic_equivalences_including_empty_rows() {
        let literals = [lit(-2), lit(-1), lit(1), lit(2)];
        let cases = (0_u8..16).map(|mask| {
            Clause::new(
                literals
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| mask & (1 << index) != 0)
                    .map(|(_, literal)| *literal),
            )
        });
        for clause in cases {
            let original = Thm::new(
                Cnf::new([Clause::new([lit(2)]), clause]),
                Dnf::new([Cube::new([lit(-3)])]),
            );
            let mut arena = ClassicalArena::new();
            let id = arena.store(original.clone()).unwrap();
            arena.move_clause_right(id, 1).unwrap();
            for valuation in 0..8 {
                assert_eq!(
                    sequent_value(&original, valuation),
                    sequent_value(arena.theorem(id).unwrap(), valuation)
                );
            }
            arena.move_cube_left(id, 1).unwrap();
            for valuation in 0..8 {
                assert_eq!(
                    sequent_value(&original, valuation),
                    sequent_value(arena.theorem(id).unwrap(), valuation)
                );
            }
        }
    }

    fn sequent_value(theorem: &Thm, valuation: usize) -> bool {
        let left = theorem
            .left()
            .clauses()
            .iter()
            .all(|c| eval_clause(c, valuation));
        let right = theorem
            .right()
            .cubes()
            .iter()
            .any(|c| eval_cube(c, valuation));
        !left || right
    }

    #[test]
    fn cut_and_resolution_preserve_soundness_exhaustively() {
        let mut arena = ClassicalArena::new();
        let p = lit(1);
        let q = lit(2);
        let r = lit(3);
        let cut_left = arena
            .store(Thm::new(
                Cnf::from([Clause::from([q])]),
                Dnf::new([Cube::from([p]), Cube::from([q])]),
            ))
            .unwrap();
        let cut_right = arena
            .store(Thm::new(
                Cnf::new([Clause::from([p]), Clause::from([r])]),
                Dnf::from([Cube::from([r])]),
            ))
            .unwrap();
        let cut = arena.cut(cut_left, cut_right, p).unwrap();

        let resolution_left = arena
            .store(Thm::new(
                Cnf::from([Clause::from([q])]),
                Dnf::new([Cube::from([p]), Cube::from([q])]),
            ))
            .unwrap();
        let resolution_right = arena
            .store(Thm::new(
                Cnf::from([Clause::from([r])]),
                Dnf::new([Cube::from([p.negated()]), Cube::from([r])]),
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
    fn failed_mutations_are_atomic() {
        let mut arena = ClassicalArena::new();
        let id = arena.identity(lit(1)).unwrap();
        let original = arena.theorem(id).unwrap().clone();
        assert!(arena.move_clause_right(id, 7).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);
        assert!(arena.move_cube_left(id, 7).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);
        assert!(arena.cut(id, id, lit(2)).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);
        assert!(arena.resolve(id, id, lit(2)).is_err());
        assert_eq!(arena.theorem(id).unwrap(), &original);
    }

    #[test]
    fn copy_delete_and_free_list_reuse_one_slot() {
        let mut arena = ClassicalArena::new();
        let first = arena.identity(lit(1)).unwrap();
        let copied = arena.copy(first).unwrap();
        assert_ne!(first, copied);
        let removed = arena.remove(first).unwrap();
        assert_eq!(
            arena.theorem(first),
            Err(Error::MissingTheorem { id: first.get() })
        );
        assert!(arena.remove(first).is_err());
        let reused = arena.store(removed).unwrap();
        assert_eq!(reused, first);
        assert_eq!(arena.theorem(reused), arena.theorem(copied));
    }

    #[test]
    fn matrices_have_stable_nested_array_cbor_shape() {
        let theorem = Thm::new(
            Cnf::new([Clause::new([lit(2), lit(-1)])]),
            Dnf::new([Cube::new([]), Cube::new([lit(3)])]),
        );
        let mut bytes = Vec::new();
        covalence_lib_cbor::into_writer(&theorem, &mut bytes).unwrap();
        let decoded: Thm = covalence_lib_cbor::from_reader(bytes.as_slice()).unwrap();
        assert_eq!(decoded, theorem);
        let value: covalence_lib_cbor::Value =
            covalence_lib_cbor::from_reader(bytes.as_slice()).unwrap();
        assert!(matches!(value, covalence_lib_cbor::Value::Array(parts) if parts.len() == 2));

        for rejected in [0_i64, i64::MIN, -(i64::MAX), i64::MAX] {
            let mut encoded = Vec::new();
            covalence_lib_cbor::into_writer(&rejected, &mut encoded).unwrap();
            assert!(
                covalence_lib_cbor::from_reader::<Lit, _>(encoded.as_slice()).is_err(),
                "accepted invalid literal {rejected}"
            );
        }
    }

    #[test]
    fn normalization_preserves_tautologies_contradictions_and_empty_rows() {
        let mut theorem = Thm::new(
            Cnf::new([
                Clause::new([lit(1), lit(-1), lit(1)]),
                Clause::new([]),
                Clause::new([]),
            ]),
            Dnf::new([
                Cube::new([lit(2), lit(-2), lit(2)]),
                Cube::new([]),
                Cube::new([]),
            ]),
        );
        let before: Vec<_> = (0..4)
            .map(|valuation| sequent_value(&theorem, valuation))
            .collect();
        theorem.normalize();
        let after: Vec<_> = (0..4)
            .map(|valuation| sequent_value(&theorem, valuation))
            .collect();
        assert_eq!(before, after);
        assert_eq!(theorem.left().clauses().len(), 2);
        assert_eq!(theorem.right().cubes().len(), 2);
        assert!(
            theorem
                .left()
                .clauses()
                .iter()
                .any(|clause| { clause.literals() == [lit(-1), lit(1)] })
        );
        assert!(
            theorem
                .right()
                .cubes()
                .iter()
                .any(|cube| { cube.literals() == [lit(-2), lit(2)] })
        );
    }
}
