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

    /// Renames the underlying atom while preserving polarity.
    #[must_use]
    pub fn map(self, rename: impl FnOnce(AtomId) -> AtomId) -> Self {
        Self {
            atom: rename(self.atom),
            negative: self.negative,
        }
    }

    /// Fallibly renames the underlying atom while preserving polarity.
    ///
    /// # Errors
    ///
    /// Returns the renaming error unchanged.
    pub fn try_map<E>(self, rename: impl FnOnce(AtomId) -> Result<AtomId, E>) -> Result<Self, E> {
        Ok(Self {
            atom: rename(self.atom)?,
            negative: self.negative,
        })
    }

    pub(crate) fn encoded(self) -> i64 {
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
    premise: Literal,
    /// Implication conclusion.
    conclusion: Literal,
}

impl Candidate {
    /// Returns the candidate premise.
    #[must_use]
    pub const fn premise(self) -> Literal {
        self.premise
    }

    /// Returns the candidate conclusion.
    #[must_use]
    pub const fn conclusion(self) -> Literal {
        self.conclusion
    }
}

/// A structurally valid complete definition awaiting semantic admission.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    atom: AtomId,
    conjuncts: Box<[Literal]>,
}

impl Definition {
    /// Checks the local representation invariants without consulting a table.
    ///
    /// This does not admit the definition and does not establish acyclicity.
    ///
    /// # Errors
    ///
    /// Rejects empty definitions and repeated conjuncts.
    pub fn new(atom: AtomId, conjuncts: impl Into<Box<[Literal]>>) -> Result<Self, Error> {
        let conjuncts = conjuncts.into();
        if conjuncts.is_empty() {
            return Err(Error::EmptyDefinition);
        }
        for (index, conjunct) in conjuncts.iter().enumerate() {
            if conjuncts[..index].contains(conjunct) {
                return Err(Error::DuplicateConjunct);
            }
        }
        Ok(Self { atom, conjuncts })
    }

    /// Returns the atom defined by the complete group.
    #[must_use]
    pub const fn atom(&self) -> AtomId {
        self.atom
    }

    /// Returns all conjuncts in the complete group.
    #[must_use]
    pub fn conjuncts(&self) -> &[Literal] {
        &self.conjuncts
    }
}

/// Result of a grouped-definition query.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GroupedDefinition {
    /// No definition group exists; the atom is free.
    Absent,
    /// One complete, structurally and semantically valid group exists.
    Present(Definition),
}

/// The checked rule which minted a [`Fact`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Judgement {
    /// A defined atom implies one member of its complete definition.
    DefinitionElimination,
    /// All members of a complete definition imply its atom.
    DefinitionIntroduction,
    /// Two implications were composed through their common literal.
    Transitivity,
}

/// The semantics used to check a [`Fact`].
///
/// This is deliberately an enum rather than a user-supplied integer. Adding a
/// checker version is an API review point; persisted row reasons are not a
/// substitute for a checker identity.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CheckerVersion {
    /// The local, acyclic, empty-context rules in this module.
    LocalV1,
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
    judgement: Judgement,
    checker: CheckerVersion,
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
    /// Returns the rule which minted this fact.
    #[must_use]
    pub const fn judgement(&self) -> Judgement {
        self.judgement
    }
    /// Returns the semantics under which this fact was checked.
    #[must_use]
    pub const fn checker(&self) -> CheckerVersion {
        self.checker
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
    /// A complete definition named the same conjunct more than once.
    DuplicateConjunct,
    /// The atom is already defined.
    AlreadyDefined,
    /// A logical row already exists with another definition/theorem class.
    ClassificationConflict,
    /// Replacement requires an existing definition.
    Undefined,
    /// The proposed definition is cyclic.
    Cycle,
    /// Stored rows do not form a valid local proposition table.
    InvalidState,
    /// A fact belongs to another kernel generation.
    ForeignFact,
    /// Facts do not justify the requested inference.
    PremiseMismatch,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Storage(error) => write!(f, "local proposition storage failed: {error}"),
            Self::Connection(error) => write!(f, "local proposition connection failed: {error}"),
            Self::InvalidLiteral => f.write_str("literal is outside the local atom domain"),
            Self::EmptyDefinition => f.write_str("definition must contain a conjunct"),
            Self::DuplicateConjunct => f.write_str("definition contains a repeated conjunct"),
            Self::AlreadyDefined => f.write_str("atom already has a complete definition"),
            Self::ClassificationConflict => {
                f.write_str("logical row already has another classification")
            }
            Self::Undefined => f.write_str("atom has no definition to replace"),
            Self::Cycle => f.write_str("definition would create a local cycle"),
            Self::InvalidState => f.write_str("stored proposition table is invalid"),
            Self::ForeignFact => f.write_str("fact belongs to another kernel generation"),
            Self::PremiseMismatch => f.write_str("facts do not justify the requested inference"),
        }
    }
}
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Storage(error) => Some(error),
            Self::Connection(error) => Some(error),
            _ => None,
        }
    }
}
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
    pub fn define(&mut self, definition: Definition) -> Result<Vec<Fact>, Error> {
        self.write_definition(definition, false)
    }

    /// `LP-DEF`: atomically replaces one complete existing definition.
    ///
    /// # Errors
    ///
    /// Rejects missing, empty, cyclic, or unstoreable definitions.
    pub fn replace_definition(&mut self, definition: Definition) -> Result<Vec<Fact>, Error> {
        self.write_definition(definition, true)
    }

    fn write_definition(
        &mut self,
        definition: Definition,
        replace: bool,
    ) -> Result<Vec<Fact>, Error> {
        let atom = definition.atom;
        let conjuncts = definition.conjuncts;
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
        for conjunct in &conjuncts {
            let classification = transaction.connection().query_row(
                "SELECT reason FROM prop_row WHERE premise=?1 AND source=0 AND conclusion=?2",
                &[premise.encoded().into(), conjunct.encoded().into()],
                |row| row.integer(0),
            )?;
            if classification.is_some_and(|reason| reason != 0) {
                return Err(Error::ClassificationConflict);
            }
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
            .map(|&conclusion| self.fact(premise, conclusion, Judgement::DefinitionElimination))
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
    ) -> Result<Fact, Error> {
        let conclusion = Literal::positive(atom);
        let GroupedDefinition::Present(definition) = self.grouped_definition(atom)? else {
            return Err(Error::Undefined);
        };
        let expected = definition.conjuncts();
        if expected.len() != facts.len() {
            return Err(Error::PremiseMismatch);
        }
        for expected_conclusion in expected {
            if !facts.iter().any(|fact| {
                self.valid_fact(fact)
                    && fact.premise == premise
                    && fact.conclusion == *expected_conclusion
            }) {
                return Err(Error::PremiseMismatch);
            }
        }
        self.insert_proved(premise, conclusion)?;
        Ok(self.fact(premise, conclusion, Judgement::DefinitionIntroduction))
    }

    /// `LP-TRANS`: composes two checked facts.
    ///
    /// # Errors
    ///
    /// Rejects foreign, noncomposable, or unstoreable facts.
    pub fn trans(&mut self, left: &Fact, right: &Fact) -> Result<Fact, Error> {
        if !self.valid_fact(left) || !self.valid_fact(right) {
            return Err(Error::ForeignFact);
        }
        if left.conclusion != right.premise {
            return Err(Error::PremiseMismatch);
        }
        self.insert_proved(left.premise, right.conclusion)?;
        Ok(self.fact(left.premise, right.conclusion, Judgement::Transitivity))
    }

    fn insert_proved(&self, premise: Literal, conclusion: Literal) -> Result<(), Error> {
        let classification = self.connection.query_row(
            "SELECT reason FROM prop_row WHERE premise=?1 AND source=0 AND conclusion=?2",
            &[premise.encoded().into(), conclusion.encoded().into()],
            |row| row.integer(0),
        )?;
        if classification == Some(0) {
            return Err(Error::ClassificationConflict);
        }
        if classification.is_some() {
            return Ok(());
        }
        self.connection.execute(
            "INSERT INTO prop_row(premise,source,conclusion,reason) VALUES (?1,0,?2,?3)",
            &[
                premise.encoded().into(),
                conclusion.encoded().into(),
                1_i64.into(),
            ],
        )?;
        Ok(())
    }

    fn fact(&self, premise: Literal, conclusion: Literal, judgement: Judgement) -> Fact {
        Fact {
            premise,
            conclusion,
            kernel: self.kernel,
            generation: self.generation,
            source: SourceId::LOCAL,
            context: ContextId::EMPTY,
            judgement,
            checker: CheckerVersion::LocalV1,
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
    pub fn grouped_definition(&self, atom: AtomId) -> Result<GroupedDefinition, Error> {
        if has_cycle(&self.connection)? {
            return Err(Error::InvalidState);
        }
        let premise = Literal::positive(atom);
        let conjuncts = self.connection.query_all(
            "SELECT conclusion FROM prop_row WHERE premise=?1 AND source=0 AND reason=0 ORDER BY conclusion",
            &[premise.encoded().into()], |row| Literal::decode(row.integer(0)?).map_err(|_| covalence_lib_sqlite::Error::with_message(covalence_lib_sqlite::ResultCode::MISMATCH, "invalid proposition literal")))
            .map_err(Error::from)?;
        if conjuncts.is_empty() {
            Ok(GroupedDefinition::Absent)
        } else {
            Definition::new(atom, conjuncts)
                .map(GroupedDefinition::Present)
                .map_err(|_| Error::InvalidState)
        }
    }

    /// `LP-QUERY-FWD`: returns proved implication candidates, not `Fact`s.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed stored rows or storage failure.
    pub fn direct_implications_from(&self, premise: Literal) -> Result<Vec<Candidate>, Error> {
        self.query_candidates("premise", premise)
    }
    /// `LP-QUERY-REV`: returns proved implication candidates, not `Fact`s.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed stored rows or storage failure.
    pub fn direct_implications_to(&self, conclusion: Literal) -> Result<Vec<Candidate>, Error> {
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
                u32::try_from(row.integer(2)?)
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
    use std::collections::BTreeMap;

    fn atom(n: u32) -> AtomId {
        AtomId::new(n).expect("atom")
    }
    fn lit(n: u32) -> Literal {
        Literal::positive(atom(n))
    }
    fn definition(n: u32, conjuncts: &[Literal]) -> Definition {
        Definition::new(atom(n), conjuncts.to_vec()).expect("valid definition")
    }

    fn fixture_lines(fixture: &str) -> impl Iterator<Item = &str> {
        fixture
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    enum ExpectedOutcome {
        Accept,
        RejectStorage,
        RejectCycle,
        RejectEmpty,
    }

    struct FixtureCase {
        outcome: ExpectedOutcome,
        rows: Vec<[i64; 4]>,
        attempted_empty_definition: Option<u32>,
    }

    fn cases() -> BTreeMap<String, FixtureCase> {
        let mut cases = BTreeMap::<String, FixtureCase>::new();
        for line in fixture_lines(include_str!("../fixtures/local_prop_v1.tsv")) {
            let fields = line.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 6, "invalid case record: {line}");
            let outcome = match fields[1] {
                "accept" => ExpectedOutcome::Accept,
                "reject-storage" => ExpectedOutcome::RejectStorage,
                "reject-cycle" => ExpectedOutcome::RejectCycle,
                "reject-empty" => ExpectedOutcome::RejectEmpty,
                other => panic!("unknown fixture outcome: {other}"),
            };
            let case = cases.entry(fields[0].to_owned()).or_insert(FixtureCase {
                outcome,
                rows: Vec::new(),
                attempted_empty_definition: None,
            });
            assert_eq!(case.outcome, outcome, "mixed outcomes in {}", fields[0]);
            if fields[4] == "." {
                assert_eq!(fields[3], "0", "empty definition must be local");
                assert_eq!(fields[5], "0", "empty definition must have reason zero");
                let premise = fields[2].parse::<u32>().expect("empty definition premise");
                assert!(
                    case.attempted_empty_definition.is_none(),
                    "repeated empty marker"
                );
                case.attempted_empty_definition = Some(premise);
            } else {
                case.rows.push([
                    fields[2].parse().expect("premise"),
                    fields[3].parse().expect("source"),
                    fields[4].parse().expect("conclusion"),
                    fields[5].parse().expect("reason"),
                ]);
            }
        }
        cases
    }

    fn load_rows(rows: &[[i64; 4]]) -> Result<LocalPropTable, Error> {
        let table = LocalPropTable::open_in_memory()?;
        let transaction = Transaction::begin(&table.connection)?;
        for row in rows {
            transaction.connection().execute(
                "INSERT INTO prop_row(premise,source,conclusion,reason) VALUES (?1,?2,?3,?4)",
                &row.iter().copied().map(Param::Integer).collect::<Vec<_>>(),
            )?;
        }
        if has_cycle(transaction.connection())? {
            return Err(Error::Cycle);
        }
        transaction.commit()?;
        Ok(table)
    }

    #[test]
    fn checked_rules_and_conformance_cases_share_the_schema() {
        let mut table = LocalPropTable::open_in_memory().expect("open");
        let eliminated = table
            .define(definition(1, &[lit(2), lit(3).complement()]))
            .expect("define");
        assert_eq!(eliminated.len(), 2);
        let introduced = table
            .introduce(lit(1), atom(1), &eliminated)
            .expect("introduce");
        assert_eq!(
            (introduced.premise(), introduced.conclusion()),
            (lit(1), lit(1))
        );
        assert_eq!(eliminated[0].judgement(), Judgement::DefinitionElimination);
        assert_eq!(introduced.judgement(), Judgement::DefinitionIntroduction);
        assert_eq!(introduced.checker(), CheckerVersion::LocalV1);
        assert_eq!(
            table.grouped_definition(atom(1)).expect("query"),
            GroupedDefinition::Present(definition(1, &[lit(3).complement(), lit(2)]))
        );
        for (name, case) in cases() {
            let actual = if let Some(empty_atom) = case.attempted_empty_definition {
                Definition::new(atom(empty_atom), Vec::<Literal>::new()).and_then(|definition| {
                    let mut table = LocalPropTable::open_in_memory()?;
                    table.define(definition)?;
                    Ok(table)
                })
            } else {
                load_rows(&case.rows)
            };
            let error = actual.as_ref().err();
            match case.outcome {
                ExpectedOutcome::Accept => assert!(actual.is_ok(), "{name}: {error:?}"),
                ExpectedOutcome::RejectStorage => {
                    assert!(
                        matches!(&actual, Err(Error::Storage(_))),
                        "{name}: {error:?}"
                    );
                }
                ExpectedOutcome::RejectCycle => {
                    assert!(matches!(&actual, Err(Error::Cycle)), "{name}: {error:?}");
                }
                ExpectedOutcome::RejectEmpty => {
                    assert!(
                        matches!(&actual, Err(Error::EmptyDefinition)),
                        "{name}: {error:?}"
                    );
                }
            }
        }
        assert_ne!(
            FormulaId::literal(lit(1)),
            FormulaId::literal(lit(1).complement())
        );
    }

    #[test]
    fn structural_validation_and_literal_traversal_are_explicit() {
        assert!(matches!(
            Definition::new(atom(1), Vec::<Literal>::new()),
            Err(Error::EmptyDefinition)
        ));
        assert!(matches!(
            Definition::new(atom(1), vec![lit(2), lit(2)]),
            Err(Error::DuplicateConjunct)
        ));

        let negative = lit(1).complement();
        assert_eq!(negative.map(|_| atom(2)), lit(2).complement());
        assert_eq!(negative.map(|atom| atom), negative);
        assert_eq!(
            negative.try_map::<&str>(|_| Ok(atom(3))),
            Ok(lit(3).complement())
        );
        assert_eq!(negative.try_map(|_| Err::<AtomId, _>("stop")), Err("stop"));

        let table = LocalPropTable::open_in_memory().expect("open");
        assert_eq!(
            table.grouped_definition(atom(99)).expect("valid absence"),
            GroupedDefinition::Absent
        );
        table
            .connection
            .execute_batch("INSERT INTO prop_row VALUES (99,0,-99,0)")
            .expect("schema permits a semantic cycle");
        assert!(matches!(
            table.grouped_definition(atom(99)),
            Err(Error::InvalidState)
        ));
    }

    fn literal_text(literal: Literal) -> String {
        literal.encoded().to_string()
    }

    fn candidate_text(candidate: Candidate) -> String {
        format!(
            "{}>{}",
            literal_text(candidate.premise()),
            literal_text(candidate.conclusion())
        )
    }

    #[test]
    fn conformance_queries_are_classified_and_ordered() {
        let cases = cases();
        for line in fixture_lines(include_str!("../fixtures/local_prop_queries_v1.tsv")) {
            let fields = line.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 4, "invalid query record: {line}");
            let case = cases.get(fields[0]).expect("query case exists");
            assert_eq!(case.outcome, ExpectedOutcome::Accept);
            let table = load_rows(&case.rows).expect("accepted case loads");
            let query = Literal::decode(fields[2].parse().expect("query literal"))
                .expect("valid query literal");
            let actual = match fields[1] {
                "definition" => match table
                    .grouped_definition(query.atom())
                    .expect("definition query")
                {
                    GroupedDefinition::Absent => Vec::new(),
                    GroupedDefinition::Present(definition) => definition
                        .conjuncts()
                        .iter()
                        .copied()
                        .map(literal_text)
                        .collect::<Vec<_>>(),
                },
                "implied-by" => table
                    .direct_implications_from(query)
                    .expect("forward query")
                    .into_iter()
                    .map(candidate_text)
                    .collect(),
                "implying" => table
                    .direct_implications_to(query)
                    .expect("reverse query")
                    .into_iter()
                    .map(candidate_text)
                    .collect(),
                other => panic!("unknown query mode: {other}"),
            };
            let expected = if fields[3] == "." {
                Vec::new()
            } else {
                fields[3].split(',').map(str::to_owned).collect()
            };
            assert_eq!(actual, expected, "query fixture: {line}");
        }
    }

    #[test]
    fn arbitrary_definition_row_deletion_changes_meaning() {
        let fixture = include_str!("../fixtures/local_prop_deletion_v1.tsv");
        let mut rows = Vec::<(i64, i64)>::new();
        let mut deletion = None;
        let mut valuation = BTreeMap::<i64, bool>::new();
        let mut expected_complete = None;
        let mut expected_after_delete = None;
        for line in fixture_lines(fixture) {
            let fields = line.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 4, "invalid deletion record: {line}");
            match fields[0] {
                "row" => rows.push((
                    fields[1].parse().expect("row premise"),
                    fields[2].parse().expect("row conclusion"),
                )),
                "delete" => {
                    deletion = Some((
                        fields[1].parse().expect("delete premise"),
                        fields[2].parse().expect("delete conclusion"),
                    ));
                }
                "valuation" => {
                    valuation.insert(fields[1].parse().expect("valuation atom"), fields[3] == "1");
                }
                "expect-complete" => expected_complete = Some(fields[3] == "1"),
                "expect-after-delete" => expected_after_delete = Some(fields[3] == "1"),
                other => panic!("unknown deletion record: {other}"),
            }
        }
        let group_value = |group: &[(i64, i64)]| {
            group.iter().all(|(_, conclusion)| {
                let atom_value = valuation[&conclusion.abs()];
                if *conclusion < 0 {
                    !atom_value
                } else {
                    atom_value
                }
            })
        };
        assert_eq!(
            group_value(&rows),
            expected_complete.expect("complete result")
        );
        let deletion = deletion.expect("deletion row");
        rows.retain(|row| *row != deletion);
        assert_eq!(
            group_value(&rows),
            expected_after_delete.expect("partial result")
        );
        assert_ne!(expected_complete, expected_after_delete);
    }

    #[test]
    fn replacement_is_atomic_and_invalidates_facts() {
        let mut table = LocalPropTable::open_in_memory().expect("open");
        let old = table
            .define(definition(1, &[lit(2)]))
            .expect("define")
            .remove(0);
        table
            .introduce(lit(1), atom(1), std::slice::from_ref(&old))
            .expect("proved row");
        let proved = table
            .direct_implications_from(lit(1))
            .expect("proved candidates")[0];
        table
            .add_metadata(proved, "proof", b"opaque")
            .expect("metadata");
        assert!(matches!(
            table.replace_definition(definition(1, &[lit(1)])),
            Err(Error::Cycle)
        ));
        assert_eq!(
            table.grouped_definition(atom(1)).expect("unchanged"),
            GroupedDefinition::Present(definition(1, &[lit(2)]))
        );
        assert_eq!(
            table
                .direct_implications_from(lit(1))
                .expect("rollback kept theorem")
                .len(),
            1
        );
        table
            .replace_definition(definition(1, &[lit(3)]))
            .expect("replace");
        assert!(
            table
                .direct_implications_from(lit(1))
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
        assert!(matches!(table.trans(&old, &old), Err(Error::ForeignFact)));
    }

    #[test]
    fn schema_rejects_foreign_sources_negative_reasons_and_reason_conflicts() {
        let table = LocalPropTable::open_in_memory().expect("open");
        for sql in [
            "INSERT INTO prop_row VALUES (1,1,2,1)",
            "INSERT INTO prop_row VALUES (1,0,2,-1)",
            "INSERT INTO prop_row VALUES (-1,0,2,0)",
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

    #[test]
    fn checked_rules_reject_reclassification_and_allow_rederivation() {
        let mut table = LocalPropTable::open_in_memory().expect("open");
        table
            .connection
            .execute_batch("INSERT INTO prop_row VALUES (1,0,2,1)")
            .expect("theorem candidate");
        assert!(matches!(
            table.define(definition(1, &[lit(2)])),
            Err(Error::ClassificationConflict)
        ));

        let eliminated = table.define(definition(3, &[lit(4)])).expect("definition");
        assert!(matches!(
            table.introduce(lit(3), atom(4), &eliminated),
            Err(Error::Undefined)
        ));
        let first = table
            .introduce(lit(3), atom(3), &eliminated)
            .expect("first derivation");
        let second = table
            .introduce(lit(3), atom(3), &eliminated)
            .expect("idempotent rederivation");
        assert_eq!(first, second);
    }
}
