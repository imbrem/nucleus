//! Propositional kernel state governed by `prop/semantics.txt`.

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_lib_hash::{O256, o256_path};
use covalence_lib_sqlite::Error as SqliteError;
use covalence_neutron::sql::{Param, Transaction};

use crate::Connection;

fn missing_result_row() -> SqliteError {
    SqliteError::with_message(
        covalence_lib_sqlite::ResultCode::MISUSE,
        "statement promised a result row but returned none",
    )
}

pub mod lrat;
pub mod scratch;
pub mod transfer;

/// The normative semantic commitment, byte for byte.
pub const SEMANTICS: &str = include_str!("prop/semantics.txt");

/// The physical schema installed into every propositional database.
pub const SCHEMA: &str = include_str!("prop/schema.sql");

/// Operations a connection policy may authorize or refuse.
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
    ScratchImport,
    LratRefutation,
    Export,
    TrustSigner,
    ImportTable,
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
    /// Connection-local trusted snapshot signers; never serialized.
    pub(crate) trusted: std::cell::RefCell<std::collections::BTreeSet<O256>>,
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
        if value == 0 { None } else { Some(Self(value)) }
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
    /// An LRAT proof was rejected by the checker.
    #[snafu(display("LRAT proof rejected: {reason:?}"))]
    LratRejected {
        /// The checker's verdict.
        reason: lrat::LratError,
    },
    /// The formula's definitional shape does not match the clause list.
    #[snafu(display("formula shape does not match the supplied clauses"))]
    MalformedFormula,
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
    /// The envelope failed authentication.
    #[snafu(display("snapshot authentication failed"))]
    Snapshot {
        /// Underlying authentication failure.
        source: crate::snapshot::SnapshotAuthenticationError,
    },
    /// The envelope's signer is not in this connection's trusted set.
    #[snafu(display("signer {signer} is not trusted by this connection"))]
    UntrustedSigner {
        /// The authenticated but untrusted signer identity.
        signer: O256,
    },
    /// The envelope does not carry this protocol's schema identity.
    #[snafu(display("schema {claimed} does not match expected {expected}"))]
    SchemaMismatch {
        /// The claimed or recomputed identity.
        claimed: O256,
        /// This connection's identity.
        expected: O256,
    },
    /// The source database failed its own validity assertions.
    #[snafu(display("imported database is invalid: {violations:?}"))]
    ImportInvalid {
        /// The failing assertions.
        violations: Vec<String>,
    },
    /// The kernel could not sign the export statement.
    #[snafu(display("cannot sign the export statement"))]
    Sign {
        /// Underlying signing failure.
        source: crate::snapshot::SignError,
    },
    /// Serialization or attachment of image bytes failed.
    #[snafu(display("cannot move database image bytes"))]
    Image {
        /// Underlying image failure.
        source: covalence_neutron::ImageError,
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
        Ok(Self::from_neutron(
            neutron,
            Prop {
                policy,
                trusted: std::cell::RefCell::default(),
            },
        ))
    }

    /// Opens a borrowing kernel view.
    #[must_use]
    pub fn view(&self) -> PropView<'_, P> {
        PropView { connection: self }
    }

    /// Returns the composite schema identity of this connection's database.
    ///
    /// # Errors
    ///
    /// Returns an error if the physical manifest cannot be read.
    pub fn schema_id(&self) -> Result<O256, PropError> {
        let physical = crate::manifest::schema_manifest_id(self.parts().0).context(StorageSnafu)?;
        Ok(prop_schema_id(physical))
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

    /// Define-once gate: `a` may acquire non-negative rows only while no
    /// row mentions it (either polarity) as an antecedent.
    fn require_undetermined(&self, id: PropId) -> Result<(), PropError> {
        let touched = self
            .storage()
            .query_row(
                "SELECT lhs FROM prop_row WHERE lhs = ?1 OR lhs = ?2 LIMIT 1",
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
        self.layer_truth(p, "model < 0")
    }

    /// Whether `p` is recorded as unsatisfiable.
    ///
    /// # Errors
    ///
    /// Fails only on storage errors.
    pub fn unsat(&self, p: Lit) -> Result<bool, PropError> {
        self.authorize(Operation::Read)?;
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

    /// Whether `a => b` is established universally (definitionally or
    /// derived) — the read HOL-context layering builds on: contexts as
    /// propositions, entailment as row queries.
    ///
    /// # Errors
    ///
    /// Fails only on storage errors.
    pub fn implies(&self, a: Ant, b: Lit) -> Result<bool, PropError> {
        self.authorize(Operation::Read)?;
        self.usable(a.get(), b.get(), Target::Universal(-1))
    }

    /// Whether `p` holds in the given world.
    ///
    /// # Errors
    ///
    /// Fails only on storage errors.
    pub fn world_holds(&self, world: WorldId, p: Lit) -> Result<bool, PropError> {
        self.authorize(Operation::Read)?;
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

    /// `LRAT_REFUTATION`: checks an LRAT proof that the clause set of
    /// `formula` is unsatisfiable, and records `formula => -formula`
    /// universally.
    ///
    /// `clauses` names the clause-negation ids in solver order: the
    /// formula must be defined as the conjunction of their negations, and
    /// clause `i + 1` of the proof is read off `clauses[i]`'s definition
    /// (the negations of its conjuncts). Everything the proof is checked
    /// against is therefore kernel state; only the checker itself is
    /// trusted, and it is policy-gated.
    ///
    /// # Errors
    ///
    /// Fails if the formula/clause shape does not match, the proof is
    /// rejected, or the metadata is not negative.
    pub fn lrat_refutation(
        &self,
        formula: PropId,
        clauses: &[PropId],
        instructions: &[lrat::LratInstr],
        metadata: i64,
    ) -> Result<(), PropError> {
        self.authorize(Operation::LratRefutation)?;
        if metadata >= 0 {
            return InvalidTargetSnafu { metadata }.fail();
        }
        let initial = self.clause_matrix(formula, clauses)?;
        lrat::check(&initial, instructions)
            .map_err(|reason| LratRejectedSnafu { reason }.build())?;
        self.insert_row(formula.get(), -formula.get(), metadata)
            .map(|_| ())
    }

    /// Reads defined conjuncts of an id (its model-0 rows).
    pub(crate) fn conjuncts_of(&self, id: i64) -> Result<Vec<i64>, PropError> {
        self.storage()
            .query_all(
                "SELECT rhs FROM prop_row WHERE lhs = ?1 AND model = 0 AND rhs != 0",
                &[id.into()],
                |row| row.integer(0),
            )
            .context(StorageSnafu)
    }

    /// Verifies the formula/clause-list correspondence and returns the
    /// clause matrix: clause `i + 1` is the negation set of
    /// `clauses[i]`'s conjuncts, and `formula` must be defined as exactly
    /// the conjunction of the negated clause ids.
    pub(crate) fn clause_matrix(
        &self,
        formula: PropId,
        clauses: &[PropId],
    ) -> Result<Vec<Vec<i64>>, PropError> {
        let formula_conjuncts: std::collections::BTreeSet<i64> =
            self.conjuncts_of(formula.get())?.into_iter().collect();
        let expected: std::collections::BTreeSet<i64> =
            clauses.iter().map(|clause| -clause.get()).collect();
        if formula_conjuncts != expected || clauses.len() != expected.len() {
            return MalformedFormulaSnafu.fail();
        }
        let mut initial = Vec::new();
        for clause in clauses {
            let negated_literals = self.conjuncts_of(clause.get())?;
            if negated_literals.is_empty() {
                return MalformedFormulaSnafu.fail();
            }
            initial.push(negated_literals.into_iter().map(|lit| -lit).collect());
        }
        Ok(initial)
    }

    /// `UNFOLD`: disjunction elimination through a definition. With `d`
    /// defined as the conjunction of `r1..rk`, from usable `x => -d` and
    /// `x => ri` for every conjunct except `keep`, inserts `x => -keep`.
    ///
    /// # Errors
    ///
    /// Fails if `keep` is not a conjunct of `d` or a premise is missing.
    pub fn unfold(&self, target: Target, x: Ant, d: PropId, keep: Lit) -> Result<(), PropError> {
        self.authorize(Operation::Unfold)?;
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

    /// `WEAKEN`: from a usable truth `true => y`, inserts `x => y`.
    ///
    /// # Errors
    ///
    /// Fails if the truth premise is not usable for the target.
    pub fn weaken(&self, target: Target, x: Lit, y: Lit) -> Result<(), PropError> {
        self.authorize(Operation::Weaken)?;
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
        self.check_validity_in("main")
    }

    /// [`Self::check_validity`] against a named attached schema.
    pub(crate) fn check_validity_in(&self, schema: &str) -> Result<Vec<String>, PropError> {
        self.authorize(Operation::Read)?;
        let quoted = format!("\"{}\"", schema.replace('"', "\"\""));
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
            &format!(
                "SELECT DISTINCT lhs FROM {quoted}.prop_row
                 WHERE (model = 0 AND lhs <= 0)
                    OR (model > 0 AND rhs = 0 AND lhs <= 0)"
            ),
            "non-positive definiendum",
        )?;
        // W2: at most one non-negative binding level per id.
        collect(
            &format!(
                "SELECT lhs FROM {quoted}.prop_row
                 WHERE lhs > 0 AND model >= 0 AND (model = 0 OR rhs = 0)
                 GROUP BY lhs HAVING count(DISTINCT model) > 1"
            ),
            "multiple non-negative binding levels",
        )?;
        // W3: definitional acyclicity.
        collect(
            &format!(
                "WITH RECURSIVE step(root, x) AS (
                     SELECT lhs, abs(rhs) FROM {quoted}.prop_row
                     WHERE model = 0 AND rhs != 0
                     UNION
                     SELECT step.root, abs(source.rhs) FROM {quoted}.prop_row AS source
                     JOIN step ON source.lhs = step.x
                     WHERE source.model = 0 AND source.rhs != 0
                 )
                 SELECT DISTINCT root FROM step WHERE root = x"
            ),
            "definitional cycle",
        )?;
        // W4: worlds must be registered.
        collect(
            &format!(
                "SELECT DISTINCT model FROM {quoted}.prop_row WHERE model > 0
                 AND model NOT IN (SELECT world_id FROM {quoted}.prop_world)"
            ),
            "unregistered world",
        )?;
        Ok(violations)
    }
}

#[cfg(test)]
mod tests {
    use covalence_lib_hash::o256;

    use super::*;

    fn open() -> Connection<Prop<AllowAll>> {
        Connection::open_prop_in_memory(AllowAll).expect("open propositional database")
    }

    fn prop(value: i64) -> PropId {
        PropId::new(value).expect("positive id")
    }

    fn lit(value: i64) -> Lit {
        Lit::new(value).expect("nonzero literal")
    }

    #[test]
    fn semantics_identity_matches_fixed_vector() {
        assert_eq!(
            prop_semantics_id(),
            o256!("565806c62d1d9c53bdb58205a679f2ffddf99b8100fa323f70d79e6ee8e6c679")
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

    #[test]
    fn lrat_refutation_is_kernel_checked() {
        // Clauses (1) and (-1): 2 := {-1} is the negation of clause one,
        // 3 := {1} of clause two, F = 4 := {-2, -3}.
        let connection = open();
        let prop_view = connection.view();
        prop_view.declare_free(prop(1)).expect("declare");
        prop_view.define(prop(2), &[lit(-1)]).expect("clause one");
        prop_view.define(prop(3), &[lit(1)]).expect("clause two");
        prop_view
            .define(prop(4), &[lit(-2), lit(-3)])
            .expect("formula");
        let clauses = [prop(2), prop(3)];
        let good = lrat::parse_text("3 0 1 2 0\n").expect("parse");
        prop_view
            .lrat_refutation(prop(4), &clauses, &good, -1)
            .expect("refutation accepted");
        assert!(prop_view.unsat(lit(4)).expect("judgement"));

        // A proof over the wrong clause order or bogus hints is rejected
        // and records nothing.
        let fresh = open();
        let fresh_view = fresh.view();
        fresh_view.declare_free(prop(1)).expect("declare");
        fresh_view.define(prop(2), &[lit(-1)]).expect("clause one");
        fresh_view.define(prop(3), &[lit(1)]).expect("clause two");
        fresh_view
            .define(prop(4), &[lit(-2), lit(-3)])
            .expect("formula");
        let bad = lrat::parse_text("3 0 1 1 0\n").expect("parse");
        assert!(matches!(
            fresh_view.lrat_refutation(prop(4), &clauses, &bad, -1),
            Err(PropError::LratRejected { .. })
        ));
        assert!(!fresh_view.unsat(lit(4)).expect("nothing recorded"));
        assert!(matches!(
            fresh_view.lrat_refutation(prop(4), &[prop(2)], &good, -1),
            Err(PropError::MalformedFormula)
        ));
    }

    #[test]
    fn scratch_replay_certifies_without_the_checker() {
        // Same unit contradiction as the mini-kernel test, replayed
        // entirely through scratch-table rule applications.
        let connection = open();
        let prop_view = connection.view();
        prop_view.declare_free(prop(1)).expect("declare");
        prop_view.define(prop(2), &[lit(-1)]).expect("clause one");
        prop_view.define(prop(3), &[lit(1)]).expect("clause two");
        prop_view
            .define(prop(4), &[lit(-2), lit(-3)])
            .expect("formula");
        let instructions = lrat::parse_text("3 0 1 2 0\n").expect("parse");
        scratch::lrat_replay_scratch(
            &prop_view,
            prop(4),
            &[prop(2), prop(3)],
            &instructions,
            "unit contradiction replay",
        )
        .expect("scratch replay");
        assert!(prop_view.unsat(lit(4)).expect("judgement"));
        // The imported row names its provenance record.
        let meaning = connection
            .parts()
            .0
            .query_row(
                "SELECT i.meaning FROM prop_row r JOIN prop_import i
                 ON r.model = -i.import_id
                 WHERE r.lhs = 4 AND r.rhs = -4",
                &[],
                |row| row.text(0),
            )
            .expect("query provenance")
            .expect("import provenance");
        assert_eq!(meaning, "unit contradiction replay");
        assert!(prop_view.check_validity().expect("validity").is_empty());
    }

    #[test]
    fn unfold_and_weaken_eliminate_disjunctions() {
        // d := {1, 2}; from x => -d and x => 1 conclude x => -2.
        let connection = open();
        let prop_view = connection.view();
        prop_view.declare_free(prop(1)).expect("declare 1");
        prop_view.declare_free(prop(2)).expect("declare 2");
        prop_view
            .define(prop(3), &[lit(1), lit(2)])
            .expect("define");
        prop_view.declare_free(prop(4)).expect("declare x");
        let world = prop_view.world(None).expect("world");
        let target = Target::World(world);
        prop_view.choose(world, lit(1)).expect("choose 1");
        prop_view.choose(world, lit(-2)).expect("choose -2");
        // Derive the world truth -d from the falsified conjunct, then
        // WEAKEN the world truths into x-implications.
        prop_view
            .contra(target, lit(3), lit(2))
            .expect("contra def row");
        prop_view
            .trans(target, Ant::TRUE, lit(-2), lit(-3))
            .expect("truth chain to -d");
        prop_view
            .weaken(target, lit(4), lit(-3))
            .expect("weaken -d");
        prop_view.weaken(target, lit(4), lit(1)).expect("weaken 1");
        prop_view
            .unfold(target, Ant::from(lit(4)), prop(3), lit(2))
            .expect("unfold");
        // The conclusion (4, -2) is a usable premise now: chain it.
        prop_view.refl(target, lit(-2)).expect("refl");
        prop_view
            .trans(target, Ant::from(lit(4)), lit(-2), lit(-2))
            .expect("conclusion is present");
        // Without the excluded-conjunct premise the rule refuses.
        prop_view
            .unfold(target, Ant::from(lit(4)), prop(3), lit(1))
            .expect_err("missing (4, 2) premise");
    }

    #[test]
    fn schema_identity_is_deterministic() {
        let first = open().schema_id().expect("first");
        let second = open().schema_id().expect("second");
        assert_eq!(first, second);
    }
}
