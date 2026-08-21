//! Typed propositional logic and SAT problems.

pub mod cnf {
    //! Conjunctive normal form formulas.

    use covalence_lib_error::snafu::{self, Snafu};

    /// A malformed CNF value.
    #[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
    #[snafu(crate_root(snafu))]
    pub enum Error {
        /// Zero and the minimum signed integer cannot represent literals.
        #[snafu(display("CNF literal must be nonzero and negatable"))]
        InvalidLiteral,
    }

    /// A signed, nonzero propositional literal.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Literal(i64);

    impl Literal {
        /// Constructs a literal from its signed DIMACS representation.
        ///
        /// # Errors
        ///
        /// Rejects zero and `i64::MIN`, whose negation is not representable.
        pub const fn new(value: i64) -> Result<Self, Error> {
            if value == 0 || value == i64::MIN {
                Err(Error::InvalidLiteral)
            } else {
                Ok(Self(value))
            }
        }

        /// Returns the signed DIMACS representation.
        #[must_use]
        pub const fn get(self) -> i64 {
            self.0
        }

        /// Returns the positive variable number.
        #[must_use]
        pub const fn variable(self) -> u64 {
            self.0.unsigned_abs()
        }
    }

    impl std::ops::Neg for Literal {
        type Output = Self;

        fn neg(self) -> Self::Output {
            Self(-self.0)
        }
    }

    impl TryFrom<i64> for Literal {
        type Error = Error;

        fn try_from(value: i64) -> Result<Self, Self::Error> {
            Self::new(value)
        }
    }

    impl From<Literal> for i64 {
        fn from(literal: Literal) -> Self {
            literal.get()
        }
    }

    /// A disjunction of literals.
    #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Clause(Box<[Literal]>);

    impl Clause {
        /// Constructs a clause from validated literals.
        #[must_use]
        pub fn new(literals: impl IntoIterator<Item = Literal>) -> Self {
            Self(literals.into_iter().collect())
        }

        /// Parses signed DIMACS literals.
        ///
        /// # Errors
        ///
        /// Rejects an invalid literal.
        pub fn from_signed(values: impl IntoIterator<Item = i64>) -> Result<Self, Error> {
            values
                .into_iter()
                .map(Literal::new)
                .collect::<Result<Box<[_]>, _>>()
                .map(Self)
        }

        /// Returns this clause's literals.
        #[must_use]
        pub fn literals(&self) -> &[Literal] {
            &self.0
        }

        #[must_use]
        pub fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        #[must_use]
        pub fn first(&self) -> Option<Literal> {
            self.0.first().copied()
        }

        pub fn iter(&self) -> impl Iterator<Item = Literal> + '_ {
            self.0.iter().copied()
        }

        #[must_use]
        pub fn contains(&self, literal: Literal) -> bool {
            self.0.contains(&literal)
        }
    }

    /// A conjunction of clauses.
    #[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct Formula(Box<[Clause]>);

    impl Formula {
        #[must_use]
        pub fn new(clauses: impl IntoIterator<Item = Clause>) -> Self {
            Self(clauses.into_iter().collect())
        }

        /// Parses a matrix of signed DIMACS literals.
        ///
        /// # Errors
        ///
        /// Rejects an invalid literal.
        pub fn from_signed(
            clauses: impl IntoIterator<Item = impl IntoIterator<Item = i64>>,
        ) -> Result<Self, Error> {
            clauses
                .into_iter()
                .map(Clause::from_signed)
                .collect::<Result<Box<[_]>, _>>()
                .map(Self)
        }

        #[must_use]
        pub fn clauses(&self) -> &[Clause] {
            &self.0
        }

        #[must_use]
        pub fn len(&self) -> usize {
            self.0.len()
        }

        #[must_use]
        pub fn is_empty(&self) -> bool {
            self.0.is_empty()
        }

        #[must_use]
        pub fn max_variable(&self) -> u64 {
            self.0
                .iter()
                .flat_map(Clause::literals)
                .map(|literal| literal.variable())
                .max()
                .unwrap_or(0)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn signed_formulas_validate_and_preserve_order() {
            let formula = Formula::from_signed([vec![1, -2], vec![]]).unwrap();
            assert_eq!(formula.max_variable(), 2);
            assert_eq!(formula.clauses()[0].literals()[1].get(), -2);
            assert!(formula.clauses()[1].is_empty());
            assert!(Formula::from_signed([vec![0]]).is_err());
        }
    }
}
