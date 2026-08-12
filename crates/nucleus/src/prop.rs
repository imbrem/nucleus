//! Propositional kernel state governed by `prop/semantics.txt`.

use std::fmt::Write as _;
use std::sync::Arc;

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::{O256, o256_path};
use covalence_lib_sqlite::Error as SqliteError;
use covalence_neutron::sql::{Param, Transaction};

use crate::Connection;

pub mod lrat;
pub mod scratch;

fn missing_result_row() -> SqliteError {
    SqliteError::with_message(
        covalence_lib_sqlite::ResultCode::MISUSE,
        "statement promised a result row but returned none",
    )
}

/// The normative semantic commitment, byte for byte.
pub const SEMANTICS: &str = include_str!("prop/semantics.txt");

/// The physical schema installed into every propositional database.
pub const SCHEMA: &str = include_str!("prop/schema.sql");

/// Operations a connection policy may authorize or refuse.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[expect(
    missing_docs,
    reason = "variants name rules specified in semantics.txt"
)]
pub enum Operation {
    RegisterWorld,
    DeclareFree,
    DeclareTheory,
    Define,
    Refl,
    Trans,
    Contra,
    Fold,
    Unfold,
    Weaken,
    Cases,
    Choose,
    SatWitness,
    ScratchImport,
    LratRefutation,
    Read,
}

/// Connection-local authorization policy for the propositional kernel.
pub trait Policy {
    /// Returns whether the operation may proceed on this connection.
    fn allows(&self, operation: Operation) -> bool;
}

/// The permissive development policy.
#[derive(Clone, Copy, Debug, Default)]
pub struct AllowAll;

impl Policy for AllowAll {
    fn allows(&self, _operation: Operation) -> bool {
        true
    }
}

/// Protocol state for a propositional kernel-state connection.
pub struct Prop<P: Policy> {
    policy: P,
}

/// Resource bounds for an untrusted SAT assignment.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ModelLimits {
    /// Maximum literals accepted from the solver.
    pub literals: usize,
    /// Bounds for reconstructing the CNF from kernel state.
    pub cnf: CnfLimits,
}

impl Default for ModelLimits {
    fn default() -> Self {
        Self {
            literals: 1_000_000,
            cnf: CnfLimits::default(),
        }
    }
}

/// Bounds for reconstructing a CNF from kernel state.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CnfLimits {
    /// Maximum distinct proposition ids.
    pub variables: usize,
    /// Maximum number of clauses.
    pub clauses: usize,
    /// Maximum literals in one clause.
    pub literals_per_clause: usize,
    /// Maximum literals across the matrix.
    pub total_literals: usize,
    /// Maximum work spent preparing the matrix and identity.
    pub work_units: usize,
}

impl Default for CnfLimits {
    fn default() -> Self {
        Self {
            variables: 1_000_000,
            clauses: 1_000_000,
            literals_per_clause: 1_000_000,
            total_literals: 16_000_000,
            work_units: 32_000_000,
        }
    }
}

/// Bounds for CNF preparation and LRAT verification.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RefutationLimits {
    /// Bounds for reconstructing the trusted initial clauses.
    pub cnf: CnfLimits,
    /// Bounds for decoding and checking the untrusted proof.
    pub proof: lrat::Limits,
}

#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CnfError {
    /// A configured bound was exceeded.
    Limit {
        /// Name of the exhausted budget.
        resource: &'static str,
        /// Configured maximum.
        limit: usize,
    },
}

/// Why an untrusted SAT assignment was rejected.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ModelError {
    /// The assignment exceeded its literal budget.
    TooLarge,
    /// The assignment mentioned a proposition outside the CNF.
    UnrelatedProposition,
    /// Both polarities of a proposition were supplied.
    ContradictoryLiterals,
    /// The assignment tried to choose a defined or theory-bound proposition.
    BoundProposition,
    /// The same literal appeared more than once.
    DuplicateLiteral,
    /// No supplied literal satisfied one of the clauses.
    UnsatisfiedClause,
}

/// A proposition id: always positive.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PropId(i64);

impl PropId {
    /// Wraps a positive proposition id.
    #[must_use]
    pub const fn new(value: i64) -> Option<Self> {
        if value > 0 { Some(Self(value)) } else { None }
    }

    /// Returns the raw id.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }

    /// The positive literal of this proposition.
    #[must_use]
    pub const fn lit(self) -> Lit {
        Lit(self.0)
    }

    /// The negative literal of this proposition.
    #[must_use]
    pub const fn negated(self) -> Lit {
        Lit(-self.0)
    }
}

/// A literal: a nonzero integer whose sign is polarity.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lit(i64);

impl Lit {
    /// Wraps a nonzero literal.
    #[must_use]
    pub const fn new(value: i64) -> Option<Self> {
        if value == 0 || value == i64::MIN {
            None
        } else {
            Some(Self(value))
        }
    }

    /// Returns the raw signed value.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }

    /// Returns the negated literal.
    #[must_use]
    pub const fn negated(self) -> Self {
        Self(-self.0)
    }

    /// Returns the underlying proposition id.
    #[must_use]
    pub const fn proposition(self) -> PropId {
        PropId(self.0.abs())
    }
}

/// An antecedent: a literal, or the truthy constant `0`.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Ant(i64);

impl Ant {
    /// The truthy constant.
    pub const TRUE: Self = Self(0);

    /// Returns the raw value (`0` is truth).
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

impl From<Lit> for Ant {
    fn from(lit: Lit) -> Self {
        Self(lit.get())
    }
}

/// A registered world (positive model number).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WorldId(i64);

impl WorldId {
    /// Returns the raw model number.
    #[must_use]
    pub const fn get(self) -> i64 {
        self.0
    }
}

/// The layer a rule derives into.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Target {
    /// The universal layer with negative caller metadata.
    Universal(i64),
    /// A registered world.
    World(WorldId),
}

impl Target {
    const fn model(self) -> i64 {
        match self {
            Self::Universal(metadata) => metadata,
            Self::World(world) => world.0,
        }
    }

    const fn world_model(self) -> i64 {
        match self {
            Self::Universal(_) => 0,
            Self::World(world) => world.0,
        }
    }
}

/// Failure of a propositional kernel operation.
#[non_exhaustive]
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu), visibility(pub(crate)))]
pub enum PropError {
    /// The connection policy refused the operation.
    #[snafu(display("policy refused {operation:?}"))]
    PolicyDenied {
        /// The refused operation.
        operation: Operation,
    },
    /// A universal target carried a non-negative metadata value.
    #[snafu(display("universal metadata {metadata} must be negative"))]
    InvalidTarget {
        /// The offending metadata value.
        metadata: i64,
    },
    /// The proposition already has non-negative rows (define-once).
    #[snafu(display("proposition {id} is already determined"))]
    AlreadyDetermined {
        /// The offending proposition id.
        id: i64,
    },
    /// A definition would close a cycle in the definitional graph.
    #[snafu(display("defining {id} would create a definitional cycle"))]
    DefinitionCycle {
        /// The offending proposition id.
        id: i64,
    },
    /// A definition carried no conjuncts.
    #[snafu(display("definitions need at least one conjunct"))]
    EmptyDefinition,
    /// The world is not registered.
    #[snafu(display("world {world} is not registered"))]
    UnknownWorld {
        /// The offending model number.
        world: i64,
    },
    /// A choice targeted a proposition that is not free.
    #[snafu(display("proposition {id} is not free"))]
    NotFree {
        /// The offending proposition id.
        id: i64,
    },
    /// A choice contradicts an existing fact usable in the same world.
    #[snafu(display("the opposite literal already holds in this world"))]
    ContradictoryChoice,
    /// A SAT assignment does not certify the formula.
    #[snafu(display("SAT model rejected: {reason:?}"))]
    InvalidModel {
        /// Typed reason for the rejection.
        reason: ModelError,
    },
    /// An LRAT proof was rejected.
    #[snafu(display("LRAT proof rejected: {reason:?}"))]
    LratRejected {
        /// The checker's verdict.
        reason: lrat::LratError,
    },
    /// The formula does not match the ordered clause list.
    #[snafu(display("formula shape does not match the supplied clauses"))]
    MalformedFormula,
    /// Reconstructing the CNF exceeded a resource bound.
    #[snafu(display("CNF rejected: {reason:?}"))]
    InvalidCnf {
        /// Typed reason for rejection.
        reason: CnfError,
    },
    /// Scratch import metadata was empty or too large.
    #[snafu(display("scratch meaning must contain 1..={limit} UTF-8 bytes"))]
    InvalidScratchMeaning {
        /// Maximum encoded length.
        limit: usize,
    },
    /// The implication pair is already held by a different world.
    #[snafu(display("{lhs} => {rhs} is already held with model {model}"))]
    PairClaimed {
        /// Antecedent of the claimed pair.
        lhs: i64,
        /// Consequent of the claimed pair.
        rhs: i64,
        /// The stored model that owns the pair.
        model: i64,
    },
    /// A required premise row is not usable for the target layer.
    #[snafu(display("premise {lhs} => {rhs} is not usable for this target"))]
    MissingPremise {
        /// Required antecedent.
        lhs: i64,
        /// Required consequent.
        rhs: i64,
    },
    /// The underlying connection could not be created.
    #[snafu(display("cannot open the propositional connection"), context(false))]
    Connection {
        /// Underlying connection failure.
        source: covalence_neutron::ConnectionError,
    },
    /// The underlying storage failed.
    #[snafu(display("propositional storage failure"))]
    Storage {
        /// Underlying `SQLite` failure.
        source: SqliteError,
    },
    /// Serializing a database snapshot failed.
    #[snafu(display("propositional snapshot failure"))]
    Snapshot {
        /// Underlying image failure.
        source: covalence_neutron::ImageError,
    },
}

impl<P: Policy> Connection<Prop<P>> {
    /// Opens a fresh in-memory propositional database under `policy`.
    ///
    /// # Errors
    ///
    /// Returns an error if the connection cannot be opened or the schema
    /// cannot be installed.
    pub fn open_prop_in_memory(policy: P) -> Result<Self, PropError> {
        let neutron = covalence_neutron::Connection::open_in_memory()?;
        neutron.execute_batch(SCHEMA).context(StorageSnafu)?;
        Ok(Self::from_neutron(neutron, Prop { policy }))
    }

    /// Opens a borrowing kernel view.
    #[must_use]
    pub fn view(&self) -> PropView<'_, P> {
        PropView { connection: self }
    }

    /// Prepares one canonical problem for an untrusted SAT solver.
    ///
    /// The returned continuation owns this connection so it remains valid
    /// across an asynchronous host call.  Completing it re-runs the bounded
    /// state checks before admitting anything.
    ///
    /// # Errors
    ///
    /// Returns an error if the formula is malformed, policy denies reading,
    /// or preparation exceeds a configured bound.
    pub fn prepare_sat(
        self: &Arc<Self>,
        formula: PropId,
        clauses: &[PropId],
        cnf_limits: CnfLimits,
        model_literals: usize,
        proof_limits: lrat::Limits,
    ) -> Result<PreparedSat<P>, PropError> {
        let view = self.view();
        view.authorize(Operation::Read)?;
        let _operation = self.lock_operation();
        let prepared = view.prepare_cnf(formula, clauses, cnf_limits)?;
        let max_variable = prepared
            .matrix
            .iter()
            .flatten()
            .map(|literal| literal.unsigned_abs())
            .max()
            .unwrap_or(0);
        let mut dimacs = String::new();
        writeln!(dimacs, "p cnf {max_variable} {}", prepared.matrix.len())
            .expect("writing to a String cannot fail");
        for clause in &prepared.matrix {
            for literal in clause {
                write!(dimacs, "{literal} ").expect("writing to a String cannot fail");
            }
            dimacs.push_str("0\n");
        }
        Ok(PreparedSat {
            connection: Arc::clone(self),
            formula,
            clauses: clauses.to_vec(),
            id: prepared.id,
            dimacs: dimacs.into_bytes(),
            cnf_limits,
            model_literals,
            proof_limits,
        })
    }

    /// Returns the composite schema identity of this connection's database.
    ///
    /// # Errors
    ///
    /// Returns an error if the physical manifest cannot be read.
    pub fn schema_id(&self) -> Result<O256, PropError> {
        let _operation = self.lock_operation();
        let physical = crate::manifest::schema_manifest_id(self.parts().0).context(StorageSnafu)?;
        Ok(prop_schema_id(physical))
    }

    /// Serializes a read-authorized, operation-boundary snapshot.
    ///
    /// # Errors
    ///
    /// Returns an error when policy denies reading or `SQLite` cannot serialize.
    pub fn snapshot(&self) -> Result<Vec<u8>, PropError> {
        self.view().authorize(Operation::Read)?;
        let _operation = self.lock_operation();
        self.parts()
            .0
            .serialize()
            .map(|bytes| bytes.as_ref().to_vec())
            .map_err(|source| PropError::Snapshot { source })
    }
}

/// Returns the identity of the current semantic commitment.
#[must_use]
pub fn prop_semantics_id() -> O256 {
    o256_path!(::nucleus.prop.kernel_state.semantics.v1).tag(SEMANTICS.as_bytes())
}

/// Returns the composite semantic + physical schema identity.
#[must_use]
pub fn prop_schema_id(physical: O256) -> O256 {
    let mut bytes = [0_u8; 64];
    bytes[..32].copy_from_slice(prop_semantics_id().as_bytes());
    bytes[32..].copy_from_slice(physical.as_bytes());
    o256_path!(::nucleus.prop.kernel_state.sqlite_schema.v1).tag(bytes)
}

/// A borrowing view over a propositional kernel-state connection.
pub struct PropView<'v, P: Policy> {
    connection: &'v Connection<Prop<P>>,
}

pub(crate) struct PreparedCnf {
    pub(crate) id: O256,
    pub(crate) matrix: Vec<Vec<i64>>,
    variables: std::collections::BTreeSet<i64>,
    pub(crate) total_literals: usize,
}

/// One canonical SAT problem retained while an untrusted solver runs.
///
/// The solver receives only [`Self::dimacs`].  Formula identity, clause order,
/// limits, and the connection which may admit a checked result remain here.
pub struct PreparedSat<P: Policy> {
    connection: Arc<Connection<Prop<P>>>,
    formula: PropId,
    clauses: Vec<PropId>,
    id: O256,
    dimacs: Vec<u8>,
    cnf_limits: CnfLimits,
    model_literals: usize,
    proof_limits: lrat::Limits,
}

impl<P: Policy> PreparedSat<P> {
    /// Identity of the ordered canonical clause matrix.
    #[must_use]
    pub const fn id(&self) -> O256 {
        self.id
    }

    /// Canonical DIMACS bytes to give an untrusted solver.
    #[must_use]
    pub fn dimacs(&self) -> &[u8] {
        &self.dimacs
    }

    /// Largest proof response accepted by the trusted checker.
    #[must_use]
    pub const fn max_proof_bytes(&self) -> usize {
        self.proof_limits.proof_bytes
    }

    /// Largest model response accepted by the trusted checker.
    #[must_use]
    pub const fn max_model_literals(&self) -> usize {
        self.model_literals
    }

    /// Checks a solver model and admits its world atomically.
    ///
    /// Consuming the continuation makes retry policy explicit at the caller.
    /// The kernel reconstructs the CNF before committing, so the retained
    /// identity cannot be detached from the state it described.
    ///
    /// # Errors
    ///
    /// Returns an error if the model is malformed, exceeds its bound, no
    /// longer describes this kernel state, or cannot be committed atomically.
    pub fn certify_model(self, model: &[Lit]) -> Result<WorldId, PropError> {
        self.connection.view().certify_model_bounded(
            self.formula,
            &self.clauses,
            model,
            ModelLimits {
                literals: self.model_literals,
                cnf: self.cnf_limits,
            },
        )
    }

    /// Checks an ASCII or binary LRAT proof and admits UNSAT atomically.
    ///
    /// `metadata` remains caller-selected provenance and must be negative.
    ///
    /// # Errors
    ///
    /// Returns an error if the proof is malformed, exceeds a bound, fails
    /// verification, or cannot be committed.
    pub fn certify_lrat(self, proof: &[u8], metadata: i64) -> Result<(), PropError> {
        self.connection.view().certify_lrat(
            self.formula,
            &self.clauses,
            proof,
            RefutationLimits {
                cnf: self.cnf_limits,
                proof: self.proof_limits,
            },
            metadata,
        )
    }
}

impl<P: Policy> PropView<'_, P> {
    pub(crate) fn storage(&self) -> &covalence_neutron::Connection {
        self.connection.parts().0
    }

    pub(crate) fn authorize(&self, operation: Operation) -> Result<(), PropError> {
        if self.connection.parts().1.policy.allows(operation) {
            Ok(())
        } else {
            PolicyDeniedSnafu { operation }.fail()
        }
    }

    /// Upserts one implication row under the subsumption order: a stored
    /// world row is upgraded in place by a universal or definitional
    /// insert; otherwise the stored reason wins. Returns the stored model
    /// so callers can check it serves their target.
    fn insert_row(&self, lhs: i64, rhs: i64, model: i64) -> Result<i64, PropError> {
        self.storage()
            .query_row(
                "INSERT INTO prop_row(lhs, rhs, model) VALUES (?1, ?2, ?3)
                 ON CONFLICT(lhs, rhs) DO UPDATE SET model = CASE
                     WHEN excluded.model <= 0 AND prop_row.model > 0
                     THEN excluded.model
                     ELSE prop_row.model
                 END
                 RETURNING model",
                &[lhs.into(), rhs.into(), model.into()],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?
            .ok_or_else(missing_result_row)
            .context(StorageSnafu)
    }

    pub(crate) fn insert_for_target(
        &self,
        lhs: i64,
        rhs: i64,
        target: Target,
    ) -> Result<(), PropError> {
        let stored = self.insert_row(lhs, rhs, target.model())?;
        match target {
            Target::Universal(_) => Ok(()),
            Target::World(world) if stored <= 0 || stored == world.get() => Ok(()),
            Target::World(_) => PairClaimedSnafu {
                lhs,
                rhs,
                model: stored,
            }
            .fail(),
        }
    }

    /// A premise is usable for a target when it is definitional,
    /// universal, or belongs to the target's own world.
    fn usable(&self, lhs: i64, rhs: i64, target: Target) -> Result<bool, PropError> {
        self.storage()
            .query_row(
                "SELECT 1 FROM prop_row
                 WHERE lhs = ?1 AND rhs = ?2 AND (model <= 0 OR model = ?3)
                 LIMIT 1",
                &[lhs.into(), rhs.into(), target.world_model().into()],
                |_| Ok(()),
            )
            .context(StorageSnafu)
            .map(|found| found.is_some())
    }

    fn require_usable(&self, lhs: i64, rhs: i64, target: Target) -> Result<(), PropError> {
        if self.usable(lhs, rhs, target)? {
            Ok(())
        } else {
            MissingPremiseSnafu { lhs, rhs }.fail()
        }
    }

    fn require_target(&self, target: Target) -> Result<(), PropError> {
        match target {
            Target::Universal(metadata) if metadata >= 0 => InvalidTargetSnafu { metadata }.fail(),
            Target::Universal(_) => Ok(()),
            Target::World(world) => self.require_world(world),
        }
    }

    fn require_world(&self, world: WorldId) -> Result<(), PropError> {
        let present = self
            .storage()
            .query_row(
                "SELECT world_id FROM prop_world WHERE world_id = ?1",
                &[world.get().into()],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?;
        if present.is_some() {
            Ok(())
        } else {
            UnknownWorldSnafu { world: world.get() }.fail()
        }
    }

    /// Binding gate: neither polarity may be bound or used by a world.
    fn require_undetermined(&self, id: PropId) -> Result<(), PropError> {
        let touched = self
            .storage()
            .query_row(
                "SELECT lhs FROM prop_row
                 WHERE lhs = ?1 OR lhs = ?2
                    OR (model > 0 AND (rhs = ?1 OR rhs = ?2))
                 LIMIT 1",
                &[id.get().into(), (-id.get()).into()],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?;
        if touched.is_some() {
            AlreadyDeterminedSnafu { id: id.get() }.fail()
        } else {
            Ok(())
        }
    }

    fn is_free(&self, id: PropId) -> Result<bool, PropError> {
        // Free: declared free, or entirely undetermined; never defined or
        // theory-bound.
        let binding = self
            .storage()
            .query_row(
                "SELECT rhs, model FROM prop_row
                 WHERE lhs = ?1 AND model >= 0 AND (model = 0 OR rhs = 0)
                 ORDER BY rhs != 0
                 LIMIT 1",
                &[id.get().into()],
                |row| Ok((row.integer(0)?, row.integer(1)?)),
            )
            .context(StorageSnafu)?;
        Ok(match binding {
            None => true,
            Some((rhs, model)) => rhs == 0 && model == 0,
        })
    }

    // ------------------------------------------------------------------
    // Worlds and declarations.
    // ------------------------------------------------------------------

    /// Registers a fresh world; `meaning` labels externally interpreted
    /// worlds and is absent for scratch worlds.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses or storage fails.
    pub fn world(&self, meaning: Option<&str>) -> Result<WorldId, PropError> {
        self.authorize(Operation::RegisterWorld)?;
        let _operation = self.connection.lock_operation();
        self.storage()
            .query_row(
                "INSERT INTO prop_world(meaning) VALUES (?1) RETURNING world_id",
                &[Param::from(meaning)],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?
            .map(WorldId)
            .ok_or_else(missing_result_row)
            .context(StorageSnafu)
    }

    /// Declares a free (substitutable) variable.
    ///
    /// # Errors
    ///
    /// Fails if `a` is already determined.
    pub fn declare_free(&self, id: PropId) -> Result<(), PropError> {
        self.authorize(Operation::DeclareFree)?;
        let _operation = self.connection.lock_operation();
        self.require_undetermined(id)?;
        self.insert_row(id.get(), 0, 0).map(|_| ())
    }

    /// Declares a theory variable bound to a registered world's
    /// interpretation.
    ///
    /// # Errors
    ///
    /// Fails if `a` is already determined or the world is unregistered.
    pub fn declare_theory(&self, id: PropId, world: WorldId) -> Result<(), PropError> {
        self.authorize(Operation::DeclareTheory)?;
        let _operation = self.connection.lock_operation();
        self.require_world(world)?;
        self.require_undetermined(id)?;
        self.insert_row(id.get(), 0, world.get()).map(|_| ())
    }

    /// Defines `a` as the conjunction of `conjuncts`, atomically.
    ///
    /// # Errors
    ///
    /// Fails if `a` is already determined, the definition is empty, or it
    /// would create a definitional cycle.
    pub fn define(&self, id: PropId, conjuncts: &[Lit]) -> Result<(), PropError> {
        self.authorize(Operation::Define)?;
        let _operation = self.connection.lock_operation();
        if conjuncts.is_empty() {
            return EmptyDefinitionSnafu.fail();
        }
        self.require_undetermined(id)?;
        // Reject any conjunct whose definition (transitively) reaches `a`.
        for conjunct in conjuncts {
            if conjunct.proposition() == id {
                return DefinitionCycleSnafu { id: id.get() }.fail();
            }
            let reaches = self
                .storage()
                .query_row(
                    "WITH RECURSIVE reach(x) AS (
                         VALUES (?1)
                         UNION
                         SELECT abs(rhs) FROM prop_row JOIN reach ON lhs = reach.x
                         WHERE model = 0 AND rhs != 0
                     )
                     SELECT x FROM reach WHERE x = ?2 LIMIT 1",
                    &[conjunct.proposition().get().into(), id.get().into()],
                    |row| row.integer(0),
                )
                .context(StorageSnafu)?;
            if reaches.is_some() {
                return DefinitionCycleSnafu { id: id.get() }.fail();
            }
        }
        let transaction = Transaction::begin(self.storage()).context(StorageSnafu)?;
        for conjunct in conjuncts {
            transaction
                .connection()
                .execute(
                    "INSERT INTO prop_row(lhs, rhs, model) VALUES (?1, ?2, 0)
                     ON CONFLICT(lhs, rhs) DO NOTHING",
                    &[id.get().into(), conjunct.get().into()],
                )
                .context(StorageSnafu)?;
        }
        transaction.commit().context(StorageSnafu)
    }

    // ------------------------------------------------------------------
    // Rules.
    // ------------------------------------------------------------------

    /// `REFL`: inserts `p => p` at a non-definitional layer.
    ///
    /// # Errors
    ///
    /// Fails on an invalid target.
    pub fn refl(&self, target: Target, p: Lit) -> Result<(), PropError> {
        self.authorize(Operation::Refl)?;
        let _operation = self.connection.lock_operation();
        self.require_target(target)?;
        self.insert_for_target(p.get(), p.get(), target)
    }

    /// `TRANS`: from usable `a => b` and `b => c`, inserts `a => c`.
    ///
    /// # Errors
    ///
    /// Fails if a premise is not usable for the target.
    pub fn trans(&self, target: Target, a: Ant, b: Lit, c: Lit) -> Result<(), PropError> {
        self.authorize(Operation::Trans)?;
        let _operation = self.connection.lock_operation();
        self.require_target(target)?;
        self.require_usable(a.get(), b.get(), target)?;
        self.require_usable(b.get(), c.get(), target)?;
        self.insert_for_target(a.get(), c.get(), target)
    }

    /// `CONTRA`: from usable `a => b`, inserts `-b => -a`.
    ///
    /// # Errors
    ///
    /// Fails if the premise is not usable for the target.
    pub fn contra(&self, target: Target, a: Lit, b: Lit) -> Result<(), PropError> {
        self.authorize(Operation::Contra)?;
        let _operation = self.connection.lock_operation();
        self.require_target(target)?;
        self.require_usable(a.get(), b.get(), target)?;
        self.insert_for_target(-b.get(), -a.get(), target)
    }

    /// `FOLD`: from usable `x => r` for every conjunct `r` of the
    /// definition of `a`, inserts `x => a` (the completeness direction;
    /// with `x = 0` this is evaluation).
    ///
    /// # Errors
    ///
    /// Fails if `a` is not defined or a conjunct implication is missing.
    pub fn fold(&self, target: Target, x: Ant, a: PropId) -> Result<(), PropError> {
        self.authorize(Operation::Fold)?;
        let _operation = self.connection.lock_operation();
        self.require_target(target)?;
        let conjuncts = self
            .storage()
            .query_all(
                "SELECT rhs FROM prop_row WHERE lhs = ?1 AND model = 0 AND rhs != 0",
                &[a.get().into()],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?;
        if conjuncts.is_empty() {
            return MissingPremiseSnafu {
                lhs: a.get(),
                rhs: 0_i64,
            }
            .fail();
        }
        for conjunct in conjuncts {
            self.require_usable(x.get(), conjunct, target)?;
        }
        self.insert_for_target(x.get(), a.get(), target)
    }

    /// `CASES`: from usable `a => c` and `-a => c`, inserts `true => c`.
    ///
    /// # Errors
    ///
    /// Fails if a premise is not usable for the target.
    pub fn cases(&self, target: Target, a: Lit, c: Lit) -> Result<(), PropError> {
        self.authorize(Operation::Cases)?;
        let _operation = self.connection.lock_operation();
        self.require_target(target)?;
        self.require_usable(a.get(), c.get(), target)?;
        self.require_usable(-a.get(), c.get(), target)?;
        self.insert_for_target(0, c.get(), target)
    }

    /// `CHOOSE`: freely assigns a literal over a free variable in a
    /// registered world.
    ///
    /// # Errors
    ///
    /// Fails if the variable is not free or the opposite literal already
    /// holds in the world.
    pub fn choose(&self, world: WorldId, literal: Lit) -> Result<(), PropError> {
        self.authorize(Operation::Choose)?;
        let _operation = self.connection.lock_operation();
        self.require_world(world)?;
        if !self.is_free(literal.proposition())? {
            return NotFreeSnafu {
                id: literal.proposition().get(),
            }
            .fail();
        }
        if self.usable(0, -literal.get(), Target::World(world))? {
            return ContradictoryChoiceSnafu.fail();
        }
        self.insert_for_target(0, literal.get(), Target::World(world))
    }

    // ------------------------------------------------------------------
    // Judgements and validity.
    // ------------------------------------------------------------------

    /// Whether `p` is recorded as a tautology (universal truth row).
    ///
    /// # Errors
    ///
    /// Fails only on storage errors.
    pub fn tautology(&self, p: Lit) -> Result<bool, PropError> {
        self.authorize(Operation::Read)?;
        let _operation = self.connection.lock_operation();
        self.layer_truth(p, "model < 0")
    }

    /// Whether `p` is recorded as unsatisfiable.
    ///
    /// # Errors
    ///
    /// Fails only on storage errors.
    pub fn unsat(&self, p: Lit) -> Result<bool, PropError> {
        self.authorize(Operation::Read)?;
        let _operation = self.connection.lock_operation();
        if self.layer_truth(p.negated(), "model < 0")? {
            return Ok(true);
        }
        self.storage()
            .query_row(
                "SELECT 1 FROM prop_row
                 WHERE lhs = ?1 AND rhs = ?2 AND model < 0 LIMIT 1",
                &[p.get().into(), (-p.get()).into()],
                |_| Ok(()),
            )
            .context(StorageSnafu)
            .map(|found| found.is_some())
    }

    /// Whether `p` holds in the given world.
    ///
    /// # Errors
    ///
    /// Fails only on storage errors.
    pub fn world_holds(&self, world: WorldId, p: Lit) -> Result<bool, PropError> {
        self.authorize(Operation::Read)?;
        let _operation = self.connection.lock_operation();
        self.usable(0, p.get(), Target::World(world))
    }

    fn layer_truth(&self, p: Lit, model_filter: &str) -> Result<bool, PropError> {
        let sql =
            format!("SELECT 1 FROM prop_row WHERE lhs = 0 AND rhs = ?1 AND {model_filter} LIMIT 1");
        self.storage()
            .query_row(&sql, &[p.get().into()], |_| Ok(()))
            .context(StorageSnafu)
            .map(|found| found.is_some())
    }

    fn conjuncts_of(&self, id: i64) -> Result<Vec<i64>, PropError> {
        self.storage()
            .query_all(
                "SELECT rhs FROM prop_row
                 WHERE lhs = ?1 AND model = 0 AND rhs != 0 ORDER BY rhs",
                &[id.into()],
                |row| row.integer(0),
            )
            .context(StorageSnafu)
    }

    #[expect(
        clippy::too_many_lines,
        reason = "all allocation gates remain in one path"
    )]
    pub(crate) fn prepare_cnf(
        &self,
        formula: PropId,
        clauses: &[PropId],
        limits: CnfLimits,
    ) -> Result<PreparedCnf, PropError> {
        fn limit(resource: &'static str, limit: usize) -> PropError {
            InvalidCnfSnafu {
                reason: CnfError::Limit { resource, limit },
            }
            .build()
        }
        if clauses.len() > limits.clauses {
            return Err(limit("clauses", limits.clauses));
        }
        if clauses.len() > limits.work_units {
            return Err(limit("CNF work", limits.work_units));
        }
        if clauses.is_empty() {
            return MalformedFormulaSnafu.fail();
        }
        let formula_terms = self
            .storage()
            .query_row(
                "SELECT count(*) FROM prop_row WHERE lhs = ?1 AND model = 0 AND rhs != 0",
                &[formula.get().into()],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?
            .ok_or_else(missing_result_row)
            .context(StorageSnafu)?;
        if usize::try_from(formula_terms).ok() != Some(clauses.len()) {
            return MalformedFormulaSnafu.fail();
        }
        let actual: std::collections::BTreeSet<_> =
            self.conjuncts_of(formula.get())?.into_iter().collect();
        let expected: std::collections::BTreeSet<_> =
            clauses.iter().map(|clause| -clause.get()).collect();
        if actual != expected || clauses.len() != expected.len() {
            return MalformedFormulaSnafu.fail();
        }
        let mut counts = Vec::with_capacity(clauses.len());
        let mut total = 0usize;
        for clause in clauses {
            let count = self
                .storage()
                .query_row(
                    "SELECT count(*) FROM prop_row WHERE lhs = ?1 AND model = 0 AND rhs != 0",
                    &[clause.get().into()],
                    |row| row.integer(0),
                )
                .context(StorageSnafu)?
                .ok_or_else(missing_result_row)
                .context(StorageSnafu)?;
            let count = usize::try_from(count)
                .map_err(|_| limit("total literals", limits.total_literals))?;
            if count == 0 {
                return MalformedFormulaSnafu.fail();
            }
            if count > limits.literals_per_clause {
                return Err(limit("literals per clause", limits.literals_per_clause));
            }
            total = total
                .checked_add(count)
                .ok_or_else(|| limit("total literals", limits.total_literals))?;
            if total > limits.total_literals {
                return Err(limit("total literals", limits.total_literals));
            }
            counts.push(count);
        }
        let work = clauses
            .len()
            .checked_add(total)
            .and_then(|value| value.checked_add(total))
            // Distinct-variable tracking performs at most one tree operation
            // per literal, so charge its conservative upper bound up front.
            .and_then(|value| value.checked_add(total))
            .and_then(|value| value.checked_add(total))
            .and_then(|value| value.checked_add(clauses.len()))
            .ok_or_else(|| limit("CNF work", limits.work_units))?;
        if work > limits.work_units {
            return Err(limit("CNF work", limits.work_units));
        }

        let mut matrix = Vec::with_capacity(clauses.len());
        let mut variables = std::collections::BTreeSet::new();
        for (clause, count) in clauses.iter().zip(counts) {
            let mut literals = self.conjuncts_of(clause.get())?;
            if literals.len() != count {
                return MalformedFormulaSnafu.fail();
            }
            for literal in &mut literals {
                *literal = -*literal;
                variables.insert(literal.abs());
                if variables.len() > limits.variables {
                    return Err(limit("variables", limits.variables));
                }
            }
            matrix.push(literals);
        }
        let mut bytes = Vec::with_capacity(
            8usize
                .checked_add(
                    matrix
                        .len()
                        .checked_mul(8)
                        .ok_or_else(|| limit("CNF identity", limits.work_units))?,
                )
                .and_then(|size| size.checked_add(total.checked_mul(8)?))
                .ok_or_else(|| limit("CNF identity", limits.work_units))?,
        );
        bytes.extend_from_slice(&(matrix.len() as u64).to_le_bytes());
        for clause in &matrix {
            bytes.extend_from_slice(&(clause.len() as u64).to_le_bytes());
            for literal in clause {
                bytes.extend_from_slice(&literal.to_le_bytes());
            }
        }
        Ok(PreparedCnf {
            id: o256_path!(::nucleus.prop.cnf.v1).tag(bytes),
            matrix,
            variables,
            total_literals: total,
        })
    }

    /// Returns the identity of the canonical ordered CNF in kernel state.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed formula or storage failure.
    pub fn cnf_id(&self, formula: PropId, clauses: &[PropId]) -> Result<O256, PropError> {
        self.cnf_id_bounded(formula, clauses, CnfLimits::default())
    }

    /// Returns the CNF identity under explicit reconstruction bounds.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed or oversized formula or storage failure.
    pub fn cnf_id_bounded(
        &self,
        formula: PropId,
        clauses: &[PropId],
        limits: CnfLimits,
    ) -> Result<O256, PropError> {
        self.authorize(Operation::Read)?;
        let _operation = self.connection.lock_operation();
        Ok(self.prepare_cnf(formula, clauses, limits)?.id)
    }

    /// Checks and records a satisfying assignment atomically.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed formula, invalid model, or storage failure.
    pub fn certify_model(
        &self,
        formula: PropId,
        clauses: &[PropId],
        model: &[Lit],
    ) -> Result<WorldId, PropError> {
        self.certify_model_bounded(formula, clauses, model, ModelLimits::default())
    }

    /// Checks a satisfying assignment under an explicit size bound.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed formula, invalid model, or storage failure.
    pub fn certify_model_bounded(
        &self,
        formula: PropId,
        clauses: &[PropId],
        model: &[Lit],
        limits: ModelLimits,
    ) -> Result<WorldId, PropError> {
        self.authorize(Operation::SatWitness)?;
        let _operation = self.connection.lock_operation();
        if model.len() > limits.literals {
            return InvalidModelSnafu {
                reason: ModelError::TooLarge,
            }
            .fail();
        }
        let prepared = self.prepare_cnf(formula, clauses, limits.cnf)?;
        let mut assignment = std::collections::BTreeSet::new();
        for literal in model {
            if !prepared.variables.contains(&literal.proposition().get()) {
                return InvalidModelSnafu {
                    reason: ModelError::UnrelatedProposition,
                }
                .fail();
            }
            if assignment.contains(&-literal.get()) {
                return InvalidModelSnafu {
                    reason: ModelError::ContradictoryLiterals,
                }
                .fail();
            }
            if !self.is_free(literal.proposition())? {
                return InvalidModelSnafu {
                    reason: ModelError::BoundProposition,
                }
                .fail();
            }
            if !assignment.insert(literal.get()) {
                return InvalidModelSnafu {
                    reason: ModelError::DuplicateLiteral,
                }
                .fail();
            }
        }
        let witnesses: Vec<i64> = prepared
            .matrix
            .iter()
            .map(|clause| {
                clause
                    .iter()
                    .copied()
                    .find(|literal| assignment.contains(literal))
                    .ok_or_else(|| {
                        InvalidModelSnafu {
                            reason: ModelError::UnsatisfiedClause,
                        }
                        .build()
                    })
            })
            .collect::<Result<_, _>>()?;

        let transaction = Transaction::begin(self.storage()).context(StorageSnafu)?;
        let world = transaction
            .connection()
            .query_row(
                "INSERT INTO prop_world(meaning) VALUES (NULL) RETURNING world_id",
                &[],
                |row| row.integer(0),
            )
            .context(StorageSnafu)?
            .ok_or_else(missing_result_row)
            .context(StorageSnafu)?;
        for literal in assignment {
            transaction
                .connection()
                .execute(
                    "INSERT INTO prop_row(lhs, rhs, model) VALUES (0, ?1, ?2)",
                    &[literal.into(), world.into()],
                )
                .context(StorageSnafu)?;
        }
        for (index, witness) in witnesses.into_iter().enumerate() {
            let clause = clauses[index].get();
            for (lhs, rhs) in [(witness, -clause), (0, -clause)] {
                transaction
                    .connection()
                    .execute(
                        "INSERT INTO prop_row(lhs, rhs, model) VALUES (?1, ?2, ?3)",
                        &[lhs.into(), rhs.into(), world.into()],
                    )
                    .context(StorageSnafu)?;
            }
        }
        transaction
            .connection()
            .execute(
                "INSERT INTO prop_row(lhs, rhs, model) VALUES (0, ?1, ?2)",
                &[formula.get().into(), world.into()],
            )
            .context(StorageSnafu)?;
        transaction.commit().context(StorageSnafu)?;
        Ok(WorldId(world))
    }

    /// Checks a bounded LRAT certificate and records UNSAT atomically.
    ///
    /// # Errors
    ///
    /// Returns an error for a malformed formula, rejected proof, or storage failure.
    pub fn certify_lrat(
        &self,
        formula: PropId,
        clauses: &[PropId],
        proof: &[u8],
        limits: RefutationLimits,
        metadata: i64,
    ) -> Result<(), PropError> {
        self.authorize(Operation::LratRefutation)?;
        let _operation = self.connection.lock_operation();
        if metadata >= 0 {
            return InvalidTargetSnafu { metadata }.fail();
        }
        let prepared = self.prepare_cnf(formula, clauses, limits.cnf)?;
        let instructions = lrat::parse_bounded(proof, limits.proof)
            .map_err(|reason| LratRejectedSnafu { reason }.build())?;
        lrat::check_bounded(&prepared.matrix, &instructions, limits.proof)
            .map_err(|reason| LratRejectedSnafu { reason }.build())?;
        self.insert_row(formula.get(), -formula.get(), metadata)
            .map(|_| ())
    }

    pub(crate) fn unfold_unlocked(
        &self,
        target: Target,
        x: Ant,
        d: PropId,
        keep: Lit,
    ) -> Result<(), PropError> {
        self.require_target(target)?;
        let conjuncts = self.conjuncts_of(d.get())?;
        if !conjuncts.contains(&keep.get()) {
            return MissingPremiseSnafu {
                lhs: d.get(),
                rhs: keep.get(),
            }
            .fail();
        }
        self.require_usable(x.get(), -d.get(), target)?;
        for conjunct in conjuncts {
            if conjunct != keep.get() {
                self.require_usable(x.get(), conjunct, target)?;
            }
        }
        self.insert_for_target(x.get(), -keep.get(), target)
    }

    /// Eliminates one conjunct from a negated definition.
    ///
    /// # Errors
    ///
    /// Returns an error when a premise, target, policy, or storage operation fails.
    pub fn unfold(&self, target: Target, x: Ant, d: PropId, keep: Lit) -> Result<(), PropError> {
        self.authorize(Operation::Unfold)?;
        let _operation = self.connection.lock_operation();
        self.unfold_unlocked(target, x, d, keep)
    }

    /// Weakens a truth into an implication.
    ///
    /// # Errors
    ///
    /// Returns an error when the premise, target, policy, or storage operation fails.
    pub fn weaken(&self, target: Target, x: Lit, y: Lit) -> Result<(), PropError> {
        self.authorize(Operation::Weaken)?;
        let _operation = self.connection.lock_operation();
        self.require_target(target)?;
        self.require_usable(0, y.get(), target)?;
        self.insert_for_target(x.get(), y.get(), target)
    }

    /// Runs the decidable well-formedness assertions (W1-W4) and returns
    /// human-readable violations; empty means the definitional layer has
    /// a model. Intended both as a self-audit and as the structural check
    /// applied to untrusted images.
    ///
    /// # Errors
    ///
    /// Fails only on storage errors.
    pub fn check_validity(&self) -> Result<Vec<String>, PropError> {
        self.authorize(Operation::Read)?;
        let _operation = self.connection.lock_operation();
        let mut violations = Vec::new();
        let storage = self.storage();
        let mut collect = |sql: &str, label: &str| -> Result<(), PropError> {
            let rows = storage
                .query_all(sql, &[], |row| row.integer(0))
                .context(StorageSnafu)?;
            for row in rows {
                violations.push(format!("{label}: {row}"));
            }
            Ok(())
        };
        // W1: definitional and declaration rows need positive antecedents.
        collect(
            "SELECT DISTINCT lhs FROM prop_row
             WHERE (model = 0 AND lhs <= 0)
                OR (model > 0 AND rhs = 0 AND lhs <= 0)",
            "non-positive definiendum",
        )?;
        collect(
            "SELECT lhs FROM prop_row
             WHERE lhs = -9223372036854775808 OR rhs = -9223372036854775808",
            "unrepresentable literal",
        )?;
        // W2: at most one non-negative binding level per id.
        collect(
            "SELECT lhs FROM prop_row
             WHERE lhs > 0 AND model >= 0 AND (model = 0 OR rhs = 0)
             GROUP BY lhs HAVING count(DISTINCT model) > 1",
            "multiple non-negative binding levels",
        )?;
        // W3: definitional acyclicity.
        collect(
            "WITH RECURSIVE step(root, x) AS (
                 SELECT lhs, CASE rhs WHEN -9223372036854775808 THEN 0 ELSE abs(rhs) END
                 FROM prop_row WHERE model = 0 AND rhs != 0
                 UNION
                 SELECT step.root,
                        CASE prop_row.rhs WHEN -9223372036854775808
                        THEN 0 ELSE abs(prop_row.rhs) END
                 FROM prop_row
                 JOIN step ON prop_row.lhs = step.x
                 WHERE prop_row.model = 0 AND prop_row.rhs != 0
             )
             SELECT DISTINCT root FROM step WHERE root = x",
            "definitional cycle",
        )?;
        // W4: worlds must be registered.
        collect(
            "SELECT DISTINCT model FROM prop_row WHERE model > 0
             AND model NOT IN (SELECT world_id FROM prop_world)",
            "unregistered world",
        )?;
        Ok(violations)
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::o256;

    use super::*;

    struct ReadOnly;

    impl Policy for ReadOnly {
        #[expect(
            clippy::match_like_matches_macro,
            reason = "the wildcard documents forward-compatible policy denial"
        )]
        fn allows(&self, operation: Operation) -> bool {
            match operation {
                Operation::Read => true,
                _ => false,
            }
        }
    }

    fn open() -> Connection<Prop<AllowAll>> {
        Connection::open_prop_in_memory(AllowAll).expect("open propositional database")
    }

    fn prop(value: i64) -> PropId {
        PropId::new(value).expect("positive id")
    }

    fn lit(value: i64) -> Lit {
        Lit::new(value).expect("nonzero literal")
    }

    fn inject_row(view: &PropView<'_, AllowAll>, lhs: i64, rhs: i64, model: i64) {
        view.storage()
            .execute(
                "INSERT INTO prop_row(lhs, rhs, model) VALUES (?1, ?2, ?3)",
                &[lhs.into(), rhs.into(), model.into()],
            )
            .expect("inject malformed row");
    }

    #[test]
    fn semantics_identity_matches_fixed_vector() {
        assert_eq!(
            prop_semantics_id(),
            o256!("8a0c34309707bdb5a74bc3389eee687d80a7ca4d37390b91e956af87520d8e1e")
        );
    }

    #[test]
    fn literal_rejects_the_unrepresentable_negation() {
        assert!(Lit::new(i64::MIN).is_none());
    }

    #[test]
    fn policies_may_deny_future_extensible_operations() {
        let connection = Connection::open_prop_in_memory(ReadOnly).expect("open");
        match connection.view().declare_free(prop(1)) {
            Err(PropError::PolicyDenied {
                operation: Operation::DeclareFree,
            }) => {}
            _ => panic!("write should be denied"),
        }
    }

    #[test]
    fn concurrent_definitions_remain_define_once() {
        use std::sync::{Arc, Barrier};

        let connection = Arc::new(open());
        let barrier = Arc::new(Barrier::new(3));
        let mut threads = Vec::new();
        for literal in [1, 2] {
            let connection = Arc::clone(&connection);
            let barrier = Arc::clone(&barrier);
            threads.push(std::thread::spawn(move || {
                barrier.wait();
                connection.view().define(prop(3), &[lit(literal)])
            }));
        }
        barrier.wait();
        let results: Vec<_> = threads
            .into_iter()
            .map(|thread| thread.join().expect("definition thread"))
            .collect();
        assert_eq!(results.iter().filter(|result| result.is_ok()).count(), 1);
        assert_eq!(
            results
                .iter()
                .filter(|result| matches!(result, Err(PropError::AlreadyDetermined { .. })))
                .count(),
            1
        );
        assert!(
            connection
                .view()
                .check_validity()
                .expect("validity")
                .is_empty()
        );
    }

    #[test]
    fn define_once_rejects_redefinition_and_cycles() {
        let connection = open();
        let prop_view = connection.view();
        prop_view.declare_free(prop(1)).expect("declare 1");
        assert!(matches!(
            prop_view.declare_free(prop(1)),
            Err(PropError::AlreadyDetermined { .. })
        ));
        prop_view.define(prop(2), &[lit(1)]).expect("define 2");
        assert!(matches!(
            prop_view.define(prop(2), &[lit(1)]),
            Err(PropError::AlreadyDetermined { .. })
        ));
        prop_view.define(prop(3), &[lit(2)]).expect("define 3");
        assert!(matches!(
            prop_view.define(prop(4), &[lit(3), lit(-4)]),
            Err(PropError::DefinitionCycle { .. })
        ));
        // 4 := 3 is fine, but then 5 := ... cannot route back through 2.
        prop_view.define(prop(4), &[lit(3)]).expect("define 4");
        assert!(prop_view.check_validity().expect("validity").is_empty());
    }

    #[test]
    fn validity_detects_non_positive_definienda() {
        let connection = open();
        let prop_view = connection.view();
        inject_row(&prop_view, 0, 1, 0);
        assert_eq!(
            prop_view.check_validity().expect("validity"),
            ["non-positive definiendum: 0"]
        );
    }

    #[test]
    fn validity_reports_unrepresentable_literals_without_overflow() {
        let connection = open();
        let prop_view = connection.view();
        prop_view
            .storage()
            .execute_batch("PRAGMA ignore_check_constraints = ON")
            .expect("allow hostile fixture");
        inject_row(&prop_view, 1, i64::MIN, 0);
        assert_eq!(
            prop_view.check_validity().expect("validity"),
            ["unrepresentable literal: 1"]
        );
    }

    #[test]
    fn validity_detects_multiple_binding_levels() {
        let connection = open();
        let prop_view = connection.view();
        inject_row(&prop_view, 1, 2, 0);
        inject_row(&prop_view, 1, 0, 7);
        assert_eq!(
            prop_view.check_validity().expect("validity"),
            [
                "multiple non-negative binding levels: 1",
                "unregistered world: 7"
            ]
        );
    }

    #[test]
    fn validity_detects_definition_cycles() {
        let connection = open();
        let prop_view = connection.view();
        inject_row(&prop_view, 1, 2, 0);
        inject_row(&prop_view, 2, -1, 0);
        assert_eq!(
            prop_view.check_validity().expect("validity"),
            ["definitional cycle: 1", "definitional cycle: 2"]
        );
    }

    #[test]
    fn validity_detects_unregistered_worlds() {
        let connection = open();
        let prop_view = connection.view();
        inject_row(&prop_view, 0, 1, 9);
        assert_eq!(
            prop_view.check_validity().expect("validity"),
            ["unregistered world: 9"]
        );
    }

    #[test]
    fn contradiction_is_derivably_unsat() {
        // 6 := 1 /\ -1; CONTRA both conjunct rows, then CASES on 1.
        let connection = open();
        let prop_view = connection.view();
        let universal = Target::Universal(-1);
        prop_view.declare_free(prop(1)).expect("declare 1");
        prop_view
            .define(prop(6), &[lit(1), lit(-1)])
            .expect("define 6");
        prop_view
            .contra(universal, lit(6), lit(1))
            .expect("contra +");
        prop_view
            .contra(universal, lit(6), lit(-1))
            .expect("contra -");
        prop_view.cases(universal, lit(1), lit(-6)).expect("cases");
        assert!(prop_view.unsat(lit(6)).expect("judgement"));
        assert!(!prop_view.tautology(lit(6)).expect("not tauto"));
    }

    #[test]
    fn cnf_example_is_satisfied_in_a_scratch_world() {
        // The worked example from the design issue: clauses (1 2 3) and
        // (4 5 6); 7 and 8 are the clause negations, 9 the formula.
        let connection = open();
        let prop_view = connection.view();
        for id in 1..=6 {
            prop_view.declare_free(prop(id)).expect("declare var");
        }
        prop_view
            .define(prop(7), &[lit(-1), lit(-2), lit(-3)])
            .expect("define 7");
        prop_view
            .define(prop(8), &[lit(-4), lit(-5), lit(-6)])
            .expect("define 8");
        prop_view
            .define(prop(9), &[lit(-7), lit(-8)])
            .expect("define 9");

        let world = prop_view.world(None).expect("scratch world");
        let target = Target::World(world);
        prop_view.choose(world, lit(1)).expect("choose 1");
        prop_view.choose(world, lit(4)).expect("choose 4");
        // 7 => -1 definitionally, so 1 => -7; chain from truth.
        prop_view.contra(target, lit(7), lit(-1)).expect("1 => -7");
        prop_view
            .trans(target, Ant::TRUE, lit(1), lit(-7))
            .expect("true => -7");
        prop_view.contra(target, lit(8), lit(-4)).expect("4 => -8");
        prop_view
            .trans(target, Ant::TRUE, lit(4), lit(-8))
            .expect("true => -8");
        prop_view.fold(target, Ant::TRUE, prop(9)).expect("fold 9");
        assert!(prop_view.world_holds(world, lit(9)).expect("sat witness"));
        assert!(prop_view.check_validity().expect("validity").is_empty());
    }

    #[test]
    fn choices_are_gated_to_free_variables_and_consistency() {
        let connection = open();
        let prop_view = connection.view();
        prop_view.declare_free(prop(1)).expect("declare");
        prop_view.define(prop(2), &[lit(1)]).expect("define");
        let world = prop_view.world(None).expect("world");
        prop_view.choose(world, lit(-1)).expect("choose -1");
        assert!(matches!(
            prop_view.choose(world, lit(1)),
            Err(PropError::ContradictoryChoice)
        ));
        assert!(matches!(
            prop_view.choose(world, lit(2)),
            Err(PropError::NotFree { .. })
        ));
        // Undeclared ids are indeterminate and freely choosable.
        prop_view.choose(world, lit(42)).expect("indeterminate");
    }

    #[test]
    fn a_world_choice_prevents_later_restrictive_binding() {
        let connection = open();
        let prop_view = connection.view();
        let witness = prop_view.world(None).expect("witness world");
        prop_view.choose(witness, lit(1)).expect("choose a");

        assert!(matches!(
            prop_view.define(prop(1), &[lit(2), lit(-2)]),
            Err(PropError::AlreadyDetermined { id: 1 })
        ));
        let theory = prop_view.world(Some("theory")).expect("theory world");
        assert!(matches!(
            prop_view.declare_theory(prop(1), theory),
            Err(PropError::AlreadyDetermined { id: 1 })
        ));
        assert!(prop_view.world_holds(witness, lit(1)).expect("witness"));
    }

    #[test]
    fn premises_stay_inside_their_world() {
        let connection = open();
        let prop_view = connection.view();
        prop_view.declare_free(prop(1)).expect("declare");
        let first = prop_view.world(None).expect("first world");
        let second = prop_view.world(None).expect("second world");
        prop_view.choose(first, lit(1)).expect("choose");
        prop_view.refl(Target::World(second), lit(1)).expect("refl");
        assert!(matches!(
            prop_view.trans(Target::World(second), Ant::TRUE, lit(1), lit(1)),
            Err(PropError::MissingPremise { .. })
        ));
        assert!(matches!(
            prop_view.refl(Target::Universal(0), lit(1)),
            Err(PropError::InvalidTarget { .. })
        ));
    }

    #[test]
    fn pairs_are_owned_by_one_reason_with_universal_upgrade() {
        let connection = open();
        let prop_view = connection.view();
        prop_view.declare_free(prop(1)).expect("declare");
        let first = prop_view.world(None).expect("first");
        let second = prop_view.world(None).expect("second");
        prop_view.choose(first, lit(1)).expect("choose in first");
        // Another world may not claim the same truth pair.
        assert!(matches!(
            prop_view.choose(second, lit(1)),
            Err(PropError::PairClaimed { .. })
        ));
        // A universal derivation of an existing world pair upgrades it.
        prop_view
            .refl(Target::World(first), lit(1))
            .expect("world refl");
        prop_view
            .refl(Target::Universal(-7), lit(1))
            .expect("universal refl upgrades");
        // The upgraded row is now usable in every world.
        prop_view
            .trans(Target::World(second), Ant::from(lit(1)), lit(1), lit(1))
            .expect("universal premise serves any world");
    }

    fn unit_contradiction(view: &PropView<'_, AllowAll>) -> (PropId, [PropId; 2]) {
        view.declare_free(prop(1)).expect("declare");
        view.define(prop(2), &[lit(-1)]).expect("clause one");
        view.define(prop(3), &[lit(1)]).expect("clause two");
        view.define(prop(4), &[lit(-2), lit(-3)]).expect("formula");
        (prop(4), [prop(2), prop(3)])
    }

    #[test]
    fn cnf_identity_and_certificates_bind_to_kernel_state() {
        let connection = open();
        let view = connection.view();
        let (formula, clauses) = unit_contradiction(&view);
        let first = view.cnf_id(formula, &clauses).expect("identity");
        assert_ne!(
            first,
            view.cnf_id(formula, &[clauses[1], clauses[0]])
                .expect("reordered")
        );

        let proof = b"3 0 1 2 0\n";
        view.certify_lrat(formula, &clauses, proof, RefutationLimits::default(), -1)
            .expect("certificate");
        assert!(view.unsat(formula.lit()).expect("unsat"));
    }

    #[test]
    fn every_certificate_path_uses_prepared_cnf_bounds() {
        let connection = open();
        let view = connection.view();
        let (formula, clauses) = unit_contradiction(&view);

        for limits in [
            CnfLimits {
                clauses: 1,
                ..CnfLimits::default()
            },
            CnfLimits {
                variables: 0,
                ..CnfLimits::default()
            },
            CnfLimits {
                literals_per_clause: 0,
                ..CnfLimits::default()
            },
            CnfLimits {
                total_literals: 1,
                ..CnfLimits::default()
            },
            CnfLimits {
                work_units: 1,
                ..CnfLimits::default()
            },
        ] {
            assert!(matches!(
                view.cnf_id_bounded(formula, &clauses, limits),
                Err(PropError::InvalidCnf { .. })
            ));
        }

        let cnf = CnfLimits {
            total_literals: 1,
            ..CnfLimits::default()
        };
        let model_limits = ModelLimits { literals: 4, cnf };
        assert!(matches!(
            view.certify_model_bounded(formula, &clauses, &[lit(1)], model_limits),
            Err(PropError::InvalidCnf { .. })
        ));
        let proof_limits = RefutationLimits {
            cnf,
            ..RefutationLimits::default()
        };
        assert!(matches!(
            view.certify_lrat(formula, &clauses, b"3 0 1 2 0\n", proof_limits, -1),
            Err(PropError::InvalidCnf { .. })
        ));
        let instructions = lrat::parse_text("3 0 1 2 0\n").expect("parse");
        assert!(matches!(
            scratch::lrat_replay_scratch_bounded(
                &view,
                formula,
                &clauses,
                &instructions,
                "bounded",
                proof_limits,
            ),
            Err(PropError::InvalidCnf { .. })
        ));
        let scratch_terms = RefutationLimits {
            proof: lrat::Limits {
                total_terms: 2,
                ..lrat::Limits::default()
            },
            ..RefutationLimits::default()
        };
        assert!(matches!(
            scratch::lrat_replay_scratch_bounded(
                &view,
                formula,
                &clauses,
                &instructions,
                "initial terms count",
                scratch_terms,
            ),
            Err(PropError::LratRejected {
                reason: lrat::LratError::Limit { .. }
            })
        ));
    }

    #[test]
    fn rejected_model_leaves_no_world_or_rows() {
        let connection = open();
        let view = connection.view();
        view.declare_free(prop(1)).expect("declare");
        view.define(prop(2), &[lit(-1)]).expect("clause negation");
        view.define(prop(3), &[lit(-2)]).expect("formula");
        let before = view
            .storage()
            .query_row("SELECT count(*) FROM prop_row", &[], |row| row.integer(0))
            .expect("count")
            .expect("row");
        assert!(matches!(
            view.certify_model(prop(3), &[prop(2)], &[lit(-1)]),
            Err(PropError::InvalidModel { .. })
        ));
        let after = view
            .storage()
            .query_row("SELECT count(*) FROM prop_row", &[], |row| row.integer(0))
            .expect("count")
            .expect("row");
        let worlds = view
            .storage()
            .query_row("SELECT count(*) FROM prop_world", &[], |row| row.integer(0))
            .expect("count")
            .expect("row");
        assert_eq!((after, worlds), (before, 0));
    }

    #[test]
    fn model_certification_succeeds_or_rolls_back_as_one_unit() {
        let connection = open();
        let view = connection.view();
        view.declare_free(prop(1)).expect("declare");
        view.define(prop(2), &[lit(-1)]).expect("clause negation");
        view.define(prop(3), &[lit(-2)]).expect("formula");
        let world = view
            .certify_model(prop(3), &[prop(2)], &[lit(1)])
            .expect("model");
        assert!(view.world_holds(world, prop(3).lit()).expect("witness"));

        let worlds_before = view
            .storage()
            .query_row("SELECT count(*) FROM prop_world", &[], |row| row.integer(0))
            .expect("count")
            .expect("row");
        assert!(view.certify_model(prop(3), &[prop(2)], &[lit(1)]).is_err());
        let worlds_after = view
            .storage()
            .query_row("SELECT count(*) FROM prop_world", &[], |row| row.integer(0))
            .expect("count")
            .expect("row");
        assert_eq!(worlds_after, worlds_before);
    }

    #[test]
    fn model_commit_failure_rolls_back_and_leaves_connection_usable() {
        let connection = open();
        let view = connection.view();
        view.declare_free(prop(1)).expect("declare");
        view.define(prop(2), &[lit(-1)]).expect("clause negation");
        view.define(prop(3), &[lit(-2)]).expect("formula");
        view.storage()
            .execute_batch(
                "PRAGMA foreign_keys = ON;
                 CREATE TABLE commit_parent (id INTEGER PRIMARY KEY);
                 CREATE TABLE commit_child (
                     id INTEGER PRIMARY KEY,
                     parent_id INTEGER NOT NULL REFERENCES commit_parent(id)
                         DEFERRABLE INITIALLY DEFERRED
                 );
                 CREATE TEMP TRIGGER fail_model_commit AFTER INSERT ON prop_world
                 BEGIN INSERT INTO commit_child VALUES (NEW.world_id, -1); END;",
            )
            .expect("fault setup");
        let rows_before = view
            .storage()
            .query_row("SELECT count(*) FROM prop_row", &[], |row| row.integer(0))
            .expect("count")
            .expect("row");

        assert!(view.certify_model(prop(3), &[prop(2)], &[lit(1)]).is_err());
        let counts = view
            .storage()
            .query_row(
                "SELECT (SELECT count(*) FROM prop_row),
                        (SELECT count(*) FROM prop_world),
                        (SELECT count(*) FROM commit_child)",
                &[],
                |row| Ok((row.integer(0)?, row.integer(1)?, row.integer(2)?)),
            )
            .expect("counts")
            .expect("row");
        assert_eq!(counts, (rows_before, 0, 0));

        view.storage()
            .execute_batch("DROP TRIGGER fail_model_commit")
            .expect("usable connection");
        view.certify_model(prop(3), &[prop(2)], &[lit(1)])
            .expect("later transaction");
    }

    #[test]
    fn failed_scratch_replay_cleans_temporary_state() {
        let connection = open();
        let view = connection.view();
        let (formula, clauses) = unit_contradiction(&view);
        let bad = lrat::parse_text("3 0 1 1 0\n").expect("parse");
        assert!(
            scratch::lrat_replay_scratch(&view, formula, &clauses, &bad, "rejected proof").is_err()
        );
        let imports = view
            .storage()
            .query_row("SELECT count(*) FROM prop_import", &[], |row| {
                row.integer(0)
            })
            .expect("count")
            .expect("row");
        let temporary = view
            .storage()
            .query_row(
                "SELECT count(*) FROM sqlite_temp_schema WHERE name = 'prop_scratch'",
                &[],
                |row| row.integer(0),
            )
            .expect("count")
            .expect("row");
        assert_eq!((imports, temporary), (0, 0));
        assert!(!view.unsat(formula.lit()).expect("no judgement"));

        let valid = lrat::parse_text("3 0 1 2 0\n").expect("parse");
        assert!(scratch::lrat_replay_scratch(&view, formula, &clauses, &valid, "").is_err());
        let temporary = view
            .storage()
            .query_row(
                "SELECT count(*) FROM sqlite_temp_schema WHERE name = 'prop_scratch'",
                &[],
                |row| row.integer(0),
            )
            .expect("count")
            .expect("row");
        assert_eq!(temporary, 0);
    }

    #[test]
    fn scratch_replay_commits_only_its_checked_conclusion() {
        let connection = open();
        let view = connection.view();
        let (formula, clauses) = unit_contradiction(&view);
        let proof = lrat::parse_text("3 0 1 2 0\n").expect("parse");
        scratch::lrat_replay_scratch(&view, formula, &clauses, &proof, "checked replay")
            .expect("replay");
        assert!(view.unsat(formula.lit()).expect("unsat"));
        let imports = view
            .storage()
            .query_row("SELECT count(*) FROM prop_import", &[], |row| {
                row.integer(0)
            })
            .expect("count")
            .expect("row");
        let temporary = view
            .storage()
            .query_row(
                "SELECT count(*) FROM sqlite_temp_schema WHERE name = 'prop_scratch'",
                &[],
                |row| row.integer(0),
            )
            .expect("count")
            .expect("row");
        assert_eq!((imports, temporary), (1, 0));
    }

    #[test]
    fn scratch_conclusion_fault_rolls_back_import_and_replay() {
        let connection = open();
        let view = connection.view();
        let (formula, clauses) = unit_contradiction(&view);
        view.storage()
            .execute_batch(
                "CREATE TEMP TRIGGER fail_scratch_import
                 BEFORE INSERT ON prop_row
                 WHEN NEW.lhs = 4 AND NEW.rhs = -4
                 BEGIN SELECT RAISE(ABORT, 'injected conclusion fault'); END",
            )
            .expect("fault trigger");
        let proof = lrat::parse_text("3 0 1 2 0\n").expect("parse");
        assert!(
            scratch::lrat_replay_scratch(&view, formula, &clauses, &proof, "faulted replay")
                .is_err()
        );
        let imports = view
            .storage()
            .query_row("SELECT count(*) FROM prop_import", &[], |row| {
                row.integer(0)
            })
            .expect("count")
            .expect("row");
        let temporary = view
            .storage()
            .query_row(
                "SELECT count(*) FROM sqlite_temp_schema WHERE name = 'prop_scratch'",
                &[],
                |row| row.integer(0),
            )
            .expect("count")
            .expect("row");
        assert_eq!((imports, temporary), (0, 0));
        assert!(!view.unsat(formula.lit()).expect("no judgement"));
    }

    #[test]
    fn scratch_commit_failure_rolls_back_and_leaves_connection_usable() {
        let connection = open();
        let view = connection.view();
        let (formula, clauses) = unit_contradiction(&view);
        view.storage()
            .execute_batch(
                "PRAGMA foreign_keys = ON;
                 CREATE TABLE commit_parent (id INTEGER PRIMARY KEY);
                 CREATE TABLE commit_child (
                     id INTEGER PRIMARY KEY,
                     parent_id INTEGER NOT NULL REFERENCES commit_parent(id)
                         DEFERRABLE INITIALLY DEFERRED
                 );
                 CREATE TEMP TRIGGER fail_scratch_commit AFTER INSERT ON prop_import
                 BEGIN INSERT INTO commit_child VALUES (NEW.import_id, -1); END;",
            )
            .expect("fault setup");
        let proof = lrat::parse_text("3 0 1 2 0\n").expect("parse");
        assert!(
            scratch::lrat_replay_scratch(&view, formula, &clauses, &proof, "faulted commit")
                .is_err()
        );
        let counts = view
            .storage()
            .query_row(
                "SELECT (SELECT count(*) FROM prop_import),
                        (SELECT count(*) FROM commit_child),
                        (SELECT count(*) FROM sqlite_temp_schema
                         WHERE name = 'prop_scratch')",
                &[],
                |row| Ok((row.integer(0)?, row.integer(1)?, row.integer(2)?)),
            )
            .expect("counts")
            .expect("row");
        assert_eq!(counts, (0, 0, 0));
        assert!(!view.unsat(formula.lit()).expect("no judgement"));

        view.storage()
            .execute_batch("DROP TRIGGER fail_scratch_commit")
            .expect("usable connection");
        scratch::lrat_replay_scratch(&view, formula, &clauses, &proof, "later replay")
            .expect("later transaction");
    }

    #[test]
    fn scratch_rejects_metadata_and_large_hint_tail_before_replay() {
        let connection = open();
        let view = connection.view();
        let (formula, clauses) = unit_contradiction(&view);
        let proof = [lrat::LratInstr::Learn {
            id: 3,
            clause: Vec::new(),
            hints: vec![1; 100_000],
        }];
        let limits = RefutationLimits {
            proof: lrat::Limits {
                terms_per_instruction: 100_000,
                total_terms: 100_002,
                work_units: 2,
                ..lrat::Limits::default()
            },
            ..RefutationLimits::default()
        };
        assert!(matches!(
            scratch::lrat_replay_scratch_bounded(
                &view, formula, &clauses, &proof, "bounded", limits,
            ),
            Err(PropError::LratRejected {
                reason: lrat::LratError::Limit {
                    resource: "scratch work",
                    ..
                }
            })
        ));

        let oversized = "x".repeat(scratch::SCRATCH_MEANING_BYTES + 1);
        assert!(matches!(
            scratch::lrat_replay_scratch(&view, formula, &clauses, &[], &oversized,),
            Err(PropError::InvalidScratchMeaning { .. })
        ));
    }

    #[test]
    fn schema_identity_matches_fixed_vector() {
        assert_eq!(
            open().schema_id().expect("schema id"),
            o256!("09a2f43cdef21ee61fb1b0cc7062e42acbdde05bd6c605f223929d751133cc58")
        );
    }
}
