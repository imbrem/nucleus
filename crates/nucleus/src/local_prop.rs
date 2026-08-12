//! Local proposition definitions and checked theorem facts.
//!
//! Judgements are labelled `LP-DEF`, `LP-ELIM`, `LP-INTRO`, and `LP-TRANS`.
//! Queries return candidates, never authority. This module has conformance
//! tests against the adjacent fixture; it does not claim a Lean refinement.
//!
//! A later demo/host layer may name and select bitblasted SAT problems, then
//! admit checked facts through these judgement methods. Problem catalogs,
//! solver jobs, LRAT bytes, and certificate display stay outside this core;
//! binary LRAT is the expected artifact and ASCII is diagnostic rendering.

use std::num::{NonZeroU32, NonZeroU64};
use std::sync::atomic::{AtomicU64, Ordering};

use covalence_lib_hash::O256;
use covalence_neutron::sql::{Param, Transaction};

const SCHEMA: &str = include_str!("local_prop/schema.sql");
static NEXT_KERNEL: AtomicU64 = AtomicU64::new(1);

/// A public atom name. It is not a database row identity.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AtomId(NonZeroU32);

impl AtomId {
    /// Constructs a nonzero atom.
    #[must_use]
    pub const fn new(value: u32) -> Option<Self> {
        match NonZeroU32::new(value) {
            Some(value) => Some(Self(value)),
            None => None,
        }
    }

    /// Returns the numeric atom name.
    #[must_use]
    pub const fn get(self) -> u32 {
        self.0.get()
    }
}

/// A signed atom.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Literal {
    atom: AtomId,
    negative: bool,
}

impl Literal {
    /// Constructs a positive literal.
    #[must_use]
    pub const fn positive(atom: AtomId) -> Self {
        Self {
            atom,
            negative: false,
        }
    }

    /// Constructs a negative literal.
    #[must_use]
    pub const fn negative(atom: AtomId) -> Self {
        Self {
            atom,
            negative: true,
        }
    }

    /// Returns the complemented literal.
    #[must_use]
    pub const fn complement(self) -> Self {
        Self {
            negative: !self.negative,
            ..self
        }
    }

    /// Returns the atom.
    #[must_use]
    pub const fn atom(self) -> AtomId {
        self.atom
    }

    fn encoded(self) -> i64 {
        let value = i64::from(self.atom.get());
        if self.negative { -value } else { value }
    }

    fn decode(value: i64) -> Result<Self, Error> {
        let magnitude = value.unsigned_abs();
        let atom = u32::try_from(magnitude)
            .ok()
            .and_then(AtomId::new)
            .ok_or(Error::InvalidLiteral)?;
        Ok(Self {
            atom,
            negative: value < 0,
        })
    }
}

/// A stable structural identity for a literal formula.
///
/// Literal hashing is sufficient for this local core. Composite formula IDs
/// wait for a canonical structural encoding rather than inheriting row IDs.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormulaId(O256);

impl FormulaId {
    /// Identifies a literal independently of its storage row.
    #[must_use]
    pub fn literal(literal: Literal) -> Self {
        let mut bytes = b"covalence.local-prop.formula/literal/v1\0".to_vec();
        bytes.extend_from_slice(&literal.encoded().to_le_bytes());
        Self(O256::from_bytes(&bytes))
    }

    /// Returns the fixed-width identity.
    #[must_use]
    pub const fn get(self) -> O256 {
        self.0
    }
}

/// A non-authoritative query result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Candidate {
    /// Implication premise.
    pub premise: Literal,
    /// Implication conclusion.
    pub conclusion: Literal,
    /// Positive checked provenance class.
    pub reason: NonZeroU32,
}

/// The baseline source identity.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SourceId(u32);

impl SourceId {
    /// The only source accepted by this local profile.
    pub const LOCAL: Self = Self(0);
}

/// The baseline proof-context identity.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ContextId(u32);

impl ContextId {
    /// The only context accepted by this local profile.
    pub const EMPTY: Self = Self(0);
}

/// An authoritative checked implication.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fact {
    premise: Literal,
    conclusion: Literal,
    kernel: NonZeroU64,
    generation: u64,
    source: SourceId,
    context: ContextId,
}

impl Fact {
    /// Returns the proved premise.
    #[must_use]
    pub const fn premise(&self) -> Literal {
        self.premise
    }
    /// Returns the proved conclusion.
    #[must_use]
    pub const fn conclusion(&self) -> Literal {
        self.conclusion
    }
    /// Returns the opaque source identity.
    #[must_use]
    pub const fn source(&self) -> SourceId {
        self.source
    }
    /// Returns the opaque context identity.
    #[must_use]
    pub const fn context(&self) -> ContextId {
        self.context
    }
}

/// Local proposition table failure.
#[derive(Debug)]
pub enum Error {
    /// Underlying storage failed.
    Storage(covalence_lib_sqlite::Error),
    /// Underlying connection failed.
    Connection(covalence_neutron::ConnectionError),
    /// A literal was outside the public atom domain.
    InvalidLiteral,
    /// Definitions must have at least one conjunct.
    EmptyDefinition,
    /// The atom is already defined.
    AlreadyDefined,
    /// Replacement requires an existing definition.
    Undefined,
    /// The proposed definition is cyclic.
    Cycle,
    /// A reason was zero where a proved reason was required.
    InvalidReason,
    /// A fact belongs to another kernel generation.
    ForeignFact,
    /// Facts do not justify the requested inference.
    PremiseMismatch,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Error {}
impl From<covalence_lib_sqlite::Error> for Error {
    fn from(e: covalence_lib_sqlite::Error) -> Self {
        Self::Storage(e)
    }
}
impl From<covalence_neutron::ConnectionError> for Error {
    fn from(e: covalence_neutron::ConnectionError) -> Self {
        Self::Connection(e)
    }
}

/// One local, empty-context proposition kernel.
pub struct LocalPropTable {
    connection: covalence_neutron::Connection,
    kernel: NonZeroU64,
    generation: u64,
}

impl LocalPropTable {
    /// Opens a fresh local table.
    ///
    /// # Errors
    ///
    /// Returns an error when the connection or schema cannot be created.
    pub fn open_in_memory() -> Result<Self, Error> {
        let connection = covalence_neutron::Connection::open_in_memory()?;
        connection.execute_batch(SCHEMA)?;
        let raw = NEXT_KERNEL.fetch_add(1, Ordering::Relaxed);
        let kernel = NonZeroU64::new(raw).ok_or(Error::ForeignFact)?;
        Ok(Self {
            connection,
            kernel,
            generation: 0,
        })
    }

    /// `LP-DEF`: inserts a new grouped definition atomically.
    ///
    /// # Errors
    ///
    /// Rejects empty, duplicate, cyclic, or unstoreable definitions.
    pub fn define(&mut self, atom: AtomId, conjuncts: &[Literal]) -> Result<Vec<Fact>, Error> {
        self.write_definition(atom, conjuncts, false)
    }

    /// `LP-DEF`: atomically replaces one complete existing definition.
    ///
    /// # Errors
    ///
    /// Rejects missing, empty, cyclic, or unstoreable definitions.
    pub fn replace_definition(
        &mut self,
        atom: AtomId,
        conjuncts: &[Literal],
    ) -> Result<Vec<Fact>, Error> {
        self.write_definition(atom, conjuncts, true)
    }

    fn write_definition(
        &mut self,
        atom: AtomId,
        conjuncts: &[Literal],
        replace: bool,
    ) -> Result<Vec<Fact>, Error> {
        if conjuncts.is_empty() {
            return Err(Error::EmptyDefinition);
        }
        let premise = Literal::positive(atom);
        let transaction = Transaction::begin(&self.connection)?;
        let existing = transaction
            .connection()
            .query_row(
                "SELECT 1 FROM prop_row WHERE premise=?1 AND source=0 AND reason=0 LIMIT 1",
                &[premise.encoded().into()],
                |_| Ok(()),
            )?
            .is_some();
        if replace != existing {
            return Err(if existing {
                Error::AlreadyDefined
            } else {
                Error::Undefined
            });
        }
        if replace {
            // Any proved edge may depend on the old definition.
            transaction
                .connection()
                .execute("DELETE FROM prop_row WHERE reason>0", &[])?;
            transaction.connection().execute(
                "DELETE FROM prop_metadata WHERE premise=?1 AND source=0 AND (premise,source,conclusion) IN (SELECT premise,source,conclusion FROM prop_row WHERE premise=?1 AND source=0 AND reason=0)",
                &[premise.encoded().into()],
            )?;
            transaction.connection().execute(
                "DELETE FROM prop_row WHERE premise=?1 AND source=0 AND reason=0",
                &[premise.encoded().into()],
            )?;
        }
        for conjunct in conjuncts {
            transaction.connection().execute(
                "INSERT INTO prop_row(premise,source,conclusion,reason) VALUES (?1,0,?2,0)",
                &[premise.encoded().into(), conjunct.encoded().into()],
            )?;
        }
        if has_cycle(transaction.connection())? {
            return Err(Error::Cycle);
        }
        transaction.commit()?;
        if replace {
            self.generation = self.generation.checked_add(1).ok_or(Error::ForeignFact)?;
        }
        Ok(conjuncts
            .iter()
            .map(|&conclusion| self.fact(premise, conclusion))
            .collect())
    }

    /// `LP-INTRO`: proves a definition from all of its conjunct facts.
    ///
    /// # Errors
    ///
    /// Rejects foreign, incomplete, mismatched, or unstoreable facts.
    pub fn introduce(
        &mut self,
        premise: Literal,
        atom: AtomId,
        facts: &[Fact],
        reason: u32,
    ) -> Result<Fact, Error> {
        let reason = NonZeroU32::new(reason).ok_or(Error::InvalidReason)?;
        let conclusion = Literal::positive(atom);
        let expected = self.definition(conclusion)?;
        if expected.is_empty() {
            return Err(Error::Undefined);
        }
        if expected.len() != facts.len() {
            return Err(Error::PremiseMismatch);
        }
        for expected_conclusion in expected {
            if !facts.iter().any(|fact| {
                self.valid_fact(fact)
                    && fact.premise == premise
                    && fact.conclusion == expected_conclusion
            }) {
                return Err(Error::PremiseMismatch);
            }
        }
        self.insert_proved(premise, conclusion, reason)?;
        Ok(self.fact(premise, conclusion))
    }

    /// `LP-TRANS`: composes two checked facts.
    ///
    /// # Errors
    ///
    /// Rejects foreign, noncomposable, or unstoreable facts.
    pub fn trans(&mut self, left: &Fact, right: &Fact, reason: u32) -> Result<Fact, Error> {
        let reason = NonZeroU32::new(reason).ok_or(Error::InvalidReason)?;
        if !self.valid_fact(left) || !self.valid_fact(right) {
            return Err(Error::ForeignFact);
        }
        if left.conclusion != right.premise {
            return Err(Error::PremiseMismatch);
        }
        self.insert_proved(left.premise, right.conclusion, reason)?;
        Ok(self.fact(left.premise, right.conclusion))
    }

    fn insert_proved(
        &self,
        premise: Literal,
        conclusion: Literal,
        reason: NonZeroU32,
    ) -> Result<(), Error> {
        self.connection.execute(
            "INSERT INTO prop_row(premise,source,conclusion,reason) VALUES (?1,0,?2,?3)",
            &[
                premise.encoded().into(),
                conclusion.encoded().into(),
                i64::from(reason.get()).into(),
            ],
        )?;
        Ok(())
    }

    fn fact(&self, premise: Literal, conclusion: Literal) -> Fact {
        Fact {
            premise,
            conclusion,
            kernel: self.kernel,
            generation: self.generation,
            source: SourceId::LOCAL,
            context: ContextId::EMPTY,
        }
    }

    fn valid_fact(&self, fact: &Fact) -> bool {
        fact.kernel == self.kernel
            && fact.generation == self.generation
            && fact.source == SourceId::LOCAL
            && fact.context == ContextId::EMPTY
    }

    /// `LP-QUERY-DEF`: returns defining conjunct candidates.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed stored rows or storage failure.
    pub fn definition(&self, premise: Literal) -> Result<Vec<Literal>, Error> {
        self.connection.query_all(
            "SELECT conclusion FROM prop_row WHERE premise=?1 AND source=0 AND reason=0 ORDER BY conclusion",
            &[premise.encoded().into()], |row| Literal::decode(row.integer(0)?).map_err(|_| covalence_lib_sqlite::Error::with_message(covalence_lib_sqlite::ResultCode::MISMATCH, "invalid proposition literal")))
            .map_err(Into::into)
    }

    /// `LP-QUERY-FWD`: returns proved implication candidates, not `Fact`s.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed stored rows or storage failure.
    pub fn implied_by(&self, premise: Literal) -> Result<Vec<Candidate>, Error> {
        self.query_candidates("premise", premise)
    }
    /// `LP-QUERY-REV`: returns proved implication candidates, not `Fact`s.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed stored rows or storage failure.
    pub fn implying(&self, conclusion: Literal) -> Result<Vec<Candidate>, Error> {
        self.query_candidates("conclusion", conclusion)
    }

    fn query_candidates(&self, column: &str, literal: Literal) -> Result<Vec<Candidate>, Error> {
        let sql = format!(
            "SELECT premise,conclusion,reason FROM prop_row WHERE {column}=?1 AND source=0 AND reason>0 ORDER BY premise,conclusion"
        );
        self.connection
            .query_all(&sql, &[literal.encoded().into()], |row| {
                let premise = Literal::decode(row.integer(0)?).map_err(|_| {
                    covalence_lib_sqlite::Error::with_message(
                        covalence_lib_sqlite::ResultCode::MISMATCH,
                        "invalid premise",
                    )
                })?;
                let conclusion = Literal::decode(row.integer(1)?).map_err(|_| {
                    covalence_lib_sqlite::Error::with_message(
                        covalence_lib_sqlite::ResultCode::MISMATCH,
                        "invalid conclusion",
                    )
                })?;
                let reason = u32::try_from(row.integer(2)?)
                    .ok()
                    .and_then(NonZeroU32::new)
                    .ok_or_else(|| {
                        covalence_lib_sqlite::Error::with_message(
                            covalence_lib_sqlite::ResultCode::MISMATCH,
                            "invalid reason",
                        )
                    })?;
                Ok(Candidate {
                    premise,
                    conclusion,
                    reason,
                })
            })
            .map_err(Into::into)
    }

    /// Adds non-authoritative metadata to an existing row.
    ///
    /// # Errors
    ///
    /// Rejects invalid metadata or a key with no authoritative row.
    pub fn add_metadata(&self, row: Candidate, kind: &str, payload: &[u8]) -> Result<(), Error> {
        self.connection.execute(
            "INSERT INTO prop_metadata(premise,source,conclusion,kind,payload) VALUES (?1,0,?2,?3,?4)",
            &[row.premise.encoded().into(), row.conclusion.encoded().into(), Param::Text(kind), Param::Blob(payload)])?;
        Ok(())
    }
}

fn has_cycle(connection: &covalence_neutron::Connection) -> Result<bool, Error> {
    Ok(connection.query_row(
        "WITH RECURSIVE edge(a,b) AS (SELECT premise,abs(conclusion) FROM prop_row WHERE source=0 AND reason=0), reach(a,b) AS (SELECT a,b FROM edge UNION SELECT reach.a,edge.b FROM reach JOIN edge ON reach.b=edge.a) SELECT 1 FROM reach WHERE a=b LIMIT 1",
        &[], |_| Ok(()))?.is_some())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(n: u32) -> AtomId {
        AtomId::new(n).expect("atom")
    }
    fn lit(n: u32) -> Literal {
        Literal::positive(atom(n))
    }

    #[test]
    fn fixture_and_checked_rules_share_the_schema() {
        let mut table = LocalPropTable::open_in_memory().expect("open");
        let eliminated = table
            .define(atom(1), &[lit(2), lit(3).complement()])
            .expect("define");
        assert_eq!(eliminated.len(), 2);
        let introduced = table
            .introduce(lit(1), atom(1), &eliminated, 7)
            .expect("introduce");
        assert_eq!(
            (introduced.premise(), introduced.conclusion()),
            (lit(1), lit(1))
        );
        assert_eq!(
            table.definition(lit(1)).expect("query"),
            vec![lit(3).complement(), lit(2)]
        );
        let fixture = include_str!("../fixtures/local_prop_v1.tsv");
        let fixture_table = LocalPropTable::open_in_memory().expect("fixture table");
        for line in fixture.lines().filter(|line| !line.starts_with('#')) {
            let fields = line
                .split_ascii_whitespace()
                .map(str::parse::<i64>)
                .collect::<Result<Vec<_>, _>>()
                .expect("fixture integers");
            fixture_table
                .connection
                .execute(
                    "INSERT INTO prop_row(premise,source,conclusion,reason) VALUES (?1,?2,?3,?4)",
                    &fields
                        .iter()
                        .copied()
                        .map(Param::Integer)
                        .collect::<Vec<_>>(),
                )
                .expect("fixture row");
        }
        assert_eq!(
            fixture_table
                .definition(lit(1))
                .expect("fixture definition")
                .len(),
            2
        );
        assert_eq!(
            fixture_table.implied_by(lit(4)).expect("fixture query")[0].reason,
            NonZeroU32::new(7).expect("reason")
        );
        assert_ne!(
            FormulaId::literal(lit(1)),
            FormulaId::literal(lit(1).complement())
        );
    }

    #[test]
    fn replacement_is_atomic_and_invalidates_facts() {
        let mut table = LocalPropTable::open_in_memory().expect("open");
        let old = table.define(atom(1), &[lit(2)]).expect("define").remove(0);
        table
            .introduce(lit(1), atom(1), std::slice::from_ref(&old), 9)
            .expect("proved row");
        let proved = table.implied_by(lit(1)).expect("proved candidates")[0];
        table
            .add_metadata(proved, "proof", b"opaque")
            .expect("metadata");
        assert!(matches!(
            table.replace_definition(atom(1), &[lit(1)]),
            Err(Error::Cycle)
        ));
        assert_eq!(table.definition(lit(1)).expect("unchanged"), vec![lit(2)]);
        assert_eq!(
            table
                .implied_by(lit(1))
                .expect("rollback kept theorem")
                .len(),
            1
        );
        table
            .replace_definition(atom(1), &[lit(3)])
            .expect("replace");
        assert!(
            table
                .implied_by(lit(1))
                .expect("proved rows cleared")
                .is_empty()
        );
        let metadata = table
            .connection
            .query_row("SELECT count(*) FROM prop_metadata", &[], |row| {
                row.integer(0)
            })
            .expect("metadata query")
            .expect("count");
        assert_eq!(metadata, 0);
        assert!(matches!(
            table.trans(&old, &old, 1),
            Err(Error::ForeignFact)
        ));
    }

    #[test]
    fn schema_rejects_foreign_sources_negative_reasons_and_reason_conflicts() {
        let table = LocalPropTable::open_in_memory().expect("open");
        for sql in [
            "INSERT INTO prop_row VALUES (1,1,2,1)",
            "INSERT INTO prop_row VALUES (1,0,2,-1)",
        ] {
            assert!(table.connection.execute_batch(sql).is_err());
        }
        table
            .connection
            .execute_batch("INSERT INTO prop_row VALUES (1,0,2,0)")
            .expect("first");
        assert!(
            table
                .connection
                .execute_batch("INSERT INTO prop_row VALUES (1,0,2,9)")
                .is_err()
        );
    }
}
