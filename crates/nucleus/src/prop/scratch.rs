//! Transactional, rule-level RUP replay in a temporary prop table.
//!
//! Scratch definitions form a conservative extension. Success imports one
//! main-id conclusion; failure removes all temporary state.

use std::collections::{BTreeSet, HashMap};

use super::lrat::{LratError, LratInstr};
use super::{
    Ant, Lit, LratRejectedSnafu, MalformedFormulaSnafu, MissingPremiseSnafu, Operation, Policy,
    PropError, PropId, PropView, StorageSnafu, Target,
};
use covalence_lib_error::snafu::ResultExt;

/// Maximum UTF-8 byte length of persisted scratch-import metadata.
pub const SCRATCH_MEANING_BYTES: usize = 4_096;

/// A temporary prop table layered over the main one.
pub struct Scratch<'s, 'v, P: Policy> {
    view: &'s PropView<'v, P>,
    /// All ids at or above this value are scratch-local.
    base: i64,
    next: std::cell::Cell<i64>,
    import: i64,
    committed: std::cell::Cell<bool>,
}

impl<'v, P: Policy> PropView<'v, P> {
    /// Opens a scratch table (dropping any previous one on this
    /// connection) and registers its import record.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses scratch imports or storage fails.
    fn scratch<'s>(&'s self, meaning: &str) -> Result<Scratch<'s, 'v, P>, PropError> {
        self.storage()
            .execute_batch(
                "DROP TABLE IF EXISTS temp.prop_scratch;
                 CREATE TEMP TABLE prop_scratch (
                     lhs   INTEGER NOT NULL,
                     rhs   INTEGER NOT NULL,
                     model INTEGER NOT NULL DEFAULT -1,
                     PRIMARY KEY (lhs, rhs)
                 ) STRICT;",
            )
            .context(StorageSnafu)?;
        let opened = (|| {
            let base = self
                .storage()
                .query_row(
                    "SELECT COALESCE(MAX(MAX(abs(lhs), abs(rhs))), 0) + 1 FROM prop_row",
                    &[],
                    |row| row.integer(0),
                )
                .context(StorageSnafu)?
                .expect("aggregate query always returns one row");
            let import = self
                .storage()
                .query_row(
                    "INSERT INTO prop_import(meaning) VALUES (?1) RETURNING import_id",
                    &[meaning.into()],
                    |row| row.integer(0),
                )
                .context(StorageSnafu)?
                .expect("INSERT RETURNING always returns one row");
            Ok(Scratch {
                view: self,
                base,
                next: std::cell::Cell::new(base),
                import,
                committed: std::cell::Cell::new(false),
            })
        })();
        if opened.is_err() {
            let _ = self
                .storage()
                .execute_batch("DROP TABLE IF EXISTS temp.prop_scratch");
        }
        opened
    }
}

impl<P: Policy> Drop for Scratch<'_, '_, P> {
    fn drop(&mut self) {
        let _ = self
            .view
            .storage()
            .execute_batch("DROP TABLE IF EXISTS temp.prop_scratch");
        if !self.committed.get() {
            let _ = self.view.storage().execute(
                "DELETE FROM prop_import WHERE import_id = ?1",
                &[self.import.into()],
            );
        }
    }
}

impl<P: Policy> Scratch<'_, '_, P> {
    fn insert(&self, lhs: i64, rhs: i64, model: i64) -> Result<(), PropError> {
        self.view
            .storage()
            .execute(
                "INSERT INTO temp.prop_scratch(lhs, rhs, model) VALUES (?1, ?2, ?3)
                 ON CONFLICT(lhs, rhs) DO NOTHING",
                &[lhs.into(), rhs.into(), model.into()],
            )
            .context(StorageSnafu)?;
        Ok(())
    }

    /// A premise is usable when it is a scratch row or a non-world main
    /// row.
    fn usable(&self, lhs: i64, rhs: i64) -> Result<bool, PropError> {
        self.view
            .storage()
            .query_row(
                "SELECT 1 WHERE EXISTS (
                     SELECT 1 FROM temp.prop_scratch
                     WHERE lhs = ?1 AND rhs = ?2 AND model <= 0
                 ) OR EXISTS (
                     SELECT 1 FROM prop_row
                     WHERE lhs = ?1 AND rhs = ?2 AND model <= 0
                 )",
                &[lhs.into(), rhs.into()],
                |_| Ok(()),
            )
            .context(StorageSnafu)
            .map(|found| found.is_some())
    }

    fn require(&self, lhs: i64, rhs: i64) -> Result<(), PropError> {
        if self.usable(lhs, rhs)? {
            Ok(())
        } else {
            MissingPremiseSnafu { lhs, rhs }.fail()
        }
    }

    /// Conjuncts of a definition, wherever it lives (scratch ids are
    /// disjoint from main ids, so exactly one table answers).
    fn conjuncts_of(&self, id: i64) -> Result<Vec<i64>, PropError> {
        if id >= self.base {
            self.view
                .storage()
                .query_all(
                    "SELECT rhs FROM temp.prop_scratch
                     WHERE lhs = ?1 AND model = 0 AND rhs != 0",
                    &[id.into()],
                    |row| row.integer(0),
                )
                .context(StorageSnafu)
        } else {
            self.view.conjuncts_of(id)
        }
    }

    /// Defines a fresh scratch id as the conjunction of `conjuncts`.
    ///
    /// Fresh ids sit above everything either table mentions, so scratch
    /// definitions are an acyclic, conservative extension by
    /// construction.
    ///
    /// # Errors
    ///
    /// Fails if the policy refuses definitions or storage fails.
    ///
    /// # Panics
    ///
    /// Never in practice: scratch ids start above 0.
    pub fn define(&self, conjuncts: &[Lit]) -> Result<PropId, PropError> {
        let id = self.next.get();
        self.next.set(id.checked_add(1).ok_or_else(|| {
            LratRejectedSnafu {
                reason: LratError::Limit {
                    resource: "scratch ids",
                    limit: usize::MAX,
                },
            }
            .build()
        })?);
        for conjunct in conjuncts {
            self.insert(id, conjunct.get(), 0)?;
        }
        Ok(PropId::new(id).expect("scratch ids are positive"))
    }

    /// `REFL` in scratch.
    ///
    /// # Errors
    ///
    /// Fails only on policy refusal or storage failure.
    pub fn refl(&self, p: Lit) -> Result<(), PropError> {
        self.insert(p.get(), p.get(), -1)
    }

    /// `TRANS` in scratch.
    ///
    /// # Errors
    ///
    /// Fails if a premise is missing.
    pub fn trans(&self, a: Ant, b: Lit, c: Lit) -> Result<(), PropError> {
        self.require(a.get(), b.get())?;
        self.require(b.get(), c.get())?;
        self.insert(a.get(), c.get(), -1)
    }

    /// `CONTRA` in scratch.
    ///
    /// # Errors
    ///
    /// Fails if the premise is missing.
    pub fn contra(&self, a: Lit, b: Lit) -> Result<(), PropError> {
        self.require(a.get(), b.get())?;
        self.insert(-b.get(), -a.get(), -1)
    }

    /// `FOLD` in scratch.
    ///
    /// # Errors
    ///
    /// Fails if `d` is not defined or a conjunct implication is missing.
    pub fn fold(&self, x: Ant, d: PropId) -> Result<(), PropError> {
        let conjuncts = self.conjuncts_of(d.get())?;
        if conjuncts.is_empty() {
            return MissingPremiseSnafu {
                lhs: d.get(),
                rhs: 0_i64,
            }
            .fail();
        }
        for conjunct in conjuncts {
            self.require(x.get(), conjunct)?;
        }
        self.insert(x.get(), d.get(), -1)
    }

    /// `UNFOLD` in scratch.
    ///
    /// # Errors
    ///
    /// Fails if `keep` is not a conjunct of `d` or a premise is missing.
    pub fn unfold(&self, x: Ant, d: PropId, keep: Lit) -> Result<(), PropError> {
        let conjuncts = self.conjuncts_of(d.get())?;
        if !conjuncts.contains(&keep.get()) {
            return MissingPremiseSnafu {
                lhs: d.get(),
                rhs: keep.get(),
            }
            .fail();
        }
        self.require(x.get(), -d.get())?;
        for conjunct in conjuncts {
            if conjunct != keep.get() {
                self.require(x.get(), conjunct)?;
            }
        }
        self.insert(x.get(), -keep.get(), -1)
    }

    /// `CASES` in scratch.
    ///
    /// # Errors
    ///
    /// Fails if a premise is missing.
    pub fn cases(&self, a: Lit, c: Lit) -> Result<(), PropError> {
        self.require(a.get(), c.get())?;
        self.require(-a.get(), c.get())?;
        self.insert(0, c.get(), -1)
    }

    /// `WEAKEN` in scratch.
    ///
    /// # Errors
    ///
    /// Fails if the truth premise is missing.
    pub fn weaken(&self, x: Lit, y: Lit) -> Result<(), PropError> {
        self.require(0, y.get())?;
        self.insert(x.get(), y.get(), -1)
    }

    /// Copies one derived fact over main ids back into the main table,
    /// with the row's model naming this scratch derivation's import
    /// record, and drops the scratch table.
    ///
    /// Sound because scratch definitions are a conservative extension:
    /// a universal consequence mentioning only main ids is entailed by
    /// the main definitional layer alone.
    ///
    /// # Errors
    ///
    /// Fails if the fact is not a derived scratch row over main ids.
    pub fn conclude(self, lhs: Ant, rhs: Lit) -> Result<(), PropError> {
        if lhs.get().abs() >= self.base || rhs.get().abs() >= self.base {
            return MalformedFormulaSnafu.fail();
        }
        self.require(lhs.get(), rhs.get())?;
        self.view
            .insert_for_target(lhs.get(), rhs.get(), Target::Universal(-self.import))?;
        self.view
            .storage()
            .execute_batch("DROP TABLE temp.prop_scratch")
            .context(StorageSnafu)?;
        self.committed.set(true);
        Ok(())
    }
}

/// The clause bookkeeping for scratch replay.
enum ClauseForm {
    /// An initial clause: its negation id lives in the main table.
    Original {
        /// The main-table clause-negation id.
        negation: i64,
    },
    /// A learned clause: `(0, -context)` is established in scratch.
    Learned {
        /// The scratch context id `{formula, negation}`.
        context: i64,
        /// The scratch clause-negation id, absent for the empty clause.
        negation: Option<i64>,
    },
}

struct TrackedClause {
    literals: Vec<i64>,
    form: ClauseForm,
}

/// Outcome of replaying one learned clause.
enum Learned {
    /// The empty clause: the refutation is complete and concluded.
    Refuted,
    /// A clause now available for later hints.
    Clause(TrackedClause),
}

/// Replays an LRAT refutation through scratch-table rule applications
/// only — zero added TCB — and concludes `formula => -formula` into the
/// main table as an inter-table import.
///
/// # Errors
///
/// Fails if the formula/clause shape does not match or the instruction
/// stream does not certify a refutation.
pub fn lrat_replay_scratch<P: Policy>(
    view: &PropView<'_, P>,
    formula: PropId,
    clauses: &[PropId],
    instructions: &[LratInstr],
    meaning: &str,
) -> Result<(), PropError> {
    lrat_replay_scratch_bounded(
        view,
        formula,
        clauses,
        instructions,
        meaning,
        super::RefutationLimits::default(),
    )
}

/// Replays RUP-only LRAT with explicit state and work bounds.
///
/// # Errors
///
/// Returns the first failed bound, rule, or storage operation.
#[expect(
    clippy::too_many_lines,
    reason = "the replay loop keeps its cleanup scope explicit"
)]
pub fn lrat_replay_scratch_bounded<P: Policy>(
    view: &PropView<'_, P>,
    formula: PropId,
    clauses: &[PropId],
    instructions: &[LratInstr],
    meaning: &str,
    limits: super::RefutationLimits,
) -> Result<(), PropError> {
    if meaning.is_empty() || meaning.len() > SCRATCH_MEANING_BYTES {
        return Err(super::InvalidScratchMeaningSnafu {
            limit: SCRATCH_MEANING_BYTES,
        }
        .build());
    }
    super::lrat::validate_decoded(instructions, limits.proof)
        .map_err(|reason| LratRejectedSnafu { reason }.build())?;
    for operation in [
        Operation::ScratchImport,
        Operation::Define,
        Operation::Refl,
        Operation::Trans,
        Operation::Contra,
        Operation::Fold,
        Operation::Unfold,
        Operation::Cases,
        Operation::Weaken,
    ] {
        view.authorize(operation)?;
    }
    let _operation = view.connection.lock_operation();
    if instructions.len() > limits.proof.instructions || clauses.len() > limits.proof.live_clauses {
        return Err(LratRejectedSnafu {
            reason: LratError::Limit {
                resource: "scratch instructions",
                limit: limits.proof.instructions,
            },
        }
        .build());
    }
    let prepared = view.prepare_cnf(formula, clauses, limits.cnf)?;
    let transaction =
        covalence_neutron::sql::Transaction::begin(view.storage()).context(StorageSnafu)?;
    let scratch = view.scratch(meaning)?;
    let mut tracked: HashMap<u64, TrackedClause> = prepared
        .matrix
        .into_iter()
        .enumerate()
        .map(|(index, literals)| {
            (
                index as u64 + 1,
                TrackedClause {
                    literals,
                    form: ClauseForm::Original {
                        negation: clauses[index].get(),
                    },
                },
            )
        })
        .collect();
    let mut work = prepared.total_literals;
    let mut total_terms = prepared.total_literals;
    if total_terms > limits.proof.total_terms {
        return Err(LratRejectedSnafu {
            reason: LratError::Limit {
                resource: "scratch total terms",
                limit: limits.proof.total_terms,
            },
        }
        .build());
    }
    if work > limits.proof.work_units {
        return Err(LratRejectedSnafu {
            reason: LratError::Limit {
                resource: "scratch work",
                limit: limits.proof.work_units,
            },
        }
        .build());
    }
    for instruction in instructions {
        let decoded_terms = match instruction {
            LratInstr::Learn { clause, hints, .. } => {
                clause.len().checked_add(hints.len()).ok_or_else(|| {
                    LratRejectedSnafu {
                        reason: LratError::Limit {
                            resource: "scratch total terms",
                            limit: limits.proof.total_terms,
                        },
                    }
                    .build()
                })?
            }
            LratInstr::Forget { ids } => ids.len(),
        };
        total_terms = total_terms.checked_add(decoded_terms).ok_or_else(|| {
            LratRejectedSnafu {
                reason: LratError::Limit {
                    resource: "scratch total terms",
                    limit: limits.proof.total_terms,
                },
            }
            .build()
        })?;
        if total_terms > limits.proof.total_terms {
            return Err(LratRejectedSnafu {
                reason: LratError::Limit {
                    resource: "scratch total terms",
                    limit: limits.proof.total_terms,
                },
            }
            .build());
        }
        let (terms, next_work) = match instruction {
            LratInstr::Learn { clause, hints, .. } => {
                let charged = checked_scratch_work(work, clause.len(), limits.proof.work_units)?;
                hints
                    .iter()
                    .try_fold((clause.len(), charged), |(terms, charged), hint| {
                        let amount = tracked
                            .get(&hint.unsigned_abs())
                            .map_or(1, |entry| entry.literals.len());
                        let terms = terms.checked_add(amount).ok_or_else(|| {
                            LratRejectedSnafu {
                                reason: LratError::Limit {
                                    resource: "scratch terms per instruction",
                                    limit: limits.proof.terms_per_instruction,
                                },
                            }
                            .build()
                        })?;
                        let charged =
                            checked_scratch_work(charged, amount, limits.proof.work_units)?;
                        Ok::<_, PropError>((terms, charged))
                    })?
            }
            LratInstr::Forget { ids } => (
                ids.len(),
                checked_scratch_work(work, ids.len(), limits.proof.work_units)?,
            ),
        };
        if terms > limits.proof.terms_per_instruction {
            return Err(LratRejectedSnafu {
                reason: LratError::Limit {
                    resource: "scratch terms per instruction",
                    limit: limits.proof.terms_per_instruction,
                },
            }
            .build());
        }
        work = next_work;
        match instruction {
            LratInstr::Forget { ids } => {
                for id in ids {
                    tracked.remove(id);
                }
            }
            LratInstr::Learn { id, clause, hints } => {
                match replay_learn(&scratch, formula, &tracked, *id, clause, hints)? {
                    Learned::Refuted => {
                        scratch.conclude(Ant::from(formula.lit()), formula.negated())?;
                        transaction.commit().context(StorageSnafu)?;
                        return Ok(());
                    }
                    Learned::Clause(entry) => {
                        tracked.insert(*id, entry);
                        if tracked.len() > limits.proof.live_clauses {
                            return Err(LratRejectedSnafu {
                                reason: LratError::Limit {
                                    resource: "scratch live clauses",
                                    limit: limits.proof.live_clauses,
                                },
                            }
                            .build());
                        }
                    }
                }
            }
        }
    }
    Err(LratRejectedSnafu {
        reason: LratError::NoRefutation,
    }
    .build())
}

fn checked_scratch_work(total: usize, amount: usize, limit: usize) -> Result<usize, PropError> {
    let work = total.checked_add(amount).ok_or_else(|| {
        LratRejectedSnafu {
            reason: LratError::Limit {
                resource: "scratch work",
                limit,
            },
        }
        .build()
    })?;
    if work > limit {
        return Err(LratRejectedSnafu {
            reason: LratError::Limit {
                resource: "scratch work",
                limit,
            },
        }
        .build());
    }
    Ok(work)
}

/// Replays one learned clause: builds its context (formula true, clause
/// literals false), walks the hints deriving unit propagations by
/// `UNFOLD` until a hint conflicts, then establishes `(0, -context)`.
///
/// # Panics
///
/// Never in practice: literals and scratch ids are nonzero by
/// construction.
fn replay_learn<P: Policy>(
    scratch: &Scratch<'_, '_, P>,
    formula: PropId,
    tracked: &HashMap<u64, TrackedClause>,
    id: u64,
    clause: &[i64],
    hints: &[i64],
) -> Result<Learned, PropError> {
    if hints.iter().any(|hint| *hint < 0) {
        return Err(LratRejectedSnafu {
            reason: LratError::RatUnsupported { step: id },
        }
        .build());
    }
    let lit = |value: i64| Lit::new(value).expect("nonzero literal");
    let negation = if clause.is_empty() {
        None
    } else {
        let negated: Vec<Lit> = clause.iter().map(|literal| lit(-literal)).collect();
        Some(scratch.define(&negated)?)
    };
    let context_conjuncts: Vec<Lit> = match negation {
        Some(negation) => vec![formula.lit(), negation.lit()],
        None => vec![formula.lit()],
    };
    let context = scratch.define(&context_conjuncts)?;
    let x = Ant::from(context.lit());
    let mut truths: BTreeSet<i64> = BTreeSet::new();
    if let Some(negation) = negation {
        for literal in clause {
            // (ctx, negation) and (negation, -literal) chain.
            scratch.trans(x, negation.lit(), lit(-literal))?;
            truths.insert(-literal);
        }
    }
    for hint in hints {
        let hint = u64::try_from(*hint).expect("negative hints rejected above");
        let info = tracked.get(&hint).ok_or_else(|| {
            LratRejectedSnafu {
                reason: LratError::UnknownClause {
                    step: id,
                    clause: hint,
                },
            }
            .build()
        })?;
        let useless = LratRejectedSnafu {
            reason: LratError::UselessHint {
                step: id,
                clause: hint,
            },
        };
        if info.literals.iter().any(|literal| truths.contains(literal)) {
            return Err(useless.build());
        }
        // Establish (ctx, -negation_of_hint).
        let hint_negation = match &info.form {
            ClauseForm::Original { negation } => {
                scratch.trans(x, formula.lit(), lit(-negation))?;
                *negation
            }
            ClauseForm::Learned {
                context: hint_context,
                negation,
            } => {
                let negation = negation.expect("the empty clause is never a hint");
                // (0, -hint_ctx) is established; weaken it to this
                // context, then unfold {formula, negation} keeping
                // negation: (ctx, formula) is definitional here.
                scratch.weaken(context.lit(), lit(-hint_context))?;
                scratch.unfold(
                    x,
                    PropId::new(*hint_context).expect("scratch id"),
                    lit(negation),
                )?;
                negation
            }
        };
        let mut unassigned = info
            .literals
            .iter()
            .filter(|literal| !truths.contains(&-**literal));
        match (unassigned.next(), unassigned.next()) {
            (None, _) => {
                return close_conflict(scratch, formula, context, negation, hint_negation, clause);
            }
            (Some(unit), None) => {
                let negation_id = PropId::new(hint_negation).expect("clause id");
                scratch.unfold(x, negation_id, lit(-unit))?;
                truths.insert(*unit);
            }
            (Some(_), Some(_)) => return Err(useless.build()),
        }
    }
    Err(LratRejectedSnafu {
        reason: LratError::NoConflict { step: id },
    }
    .build())
}

/// Closes a conflicting hint into `(0, -context)` — fold, contradict,
/// case-split — and, for the empty clause, on to `(formula, -formula)`.
///
/// # Panics
///
/// Never in practice: clause-negation ids are positive.
fn close_conflict<P: Policy>(
    scratch: &Scratch<'_, '_, P>,
    formula: PropId,
    context: PropId,
    negation: Option<PropId>,
    hint_negation: i64,
    clause: &[i64],
) -> Result<Learned, PropError> {
    let x = Ant::from(context.lit());
    let negation_id = PropId::new(hint_negation).expect("clause id");
    scratch.fold(x, negation_id)?;
    scratch.contra(context.lit(), negation_id.lit())?;
    scratch.trans(
        x,
        Lit::new(-hint_negation).expect("nonzero literal"),
        context.negated(),
    )?;
    scratch.refl(context.negated())?;
    scratch.cases(context.lit(), context.negated())?;
    if clause.is_empty() {
        // (0, -ctx) with ctx = {formula}: weaken to the formula and
        // unfold to reach (formula, -formula).
        scratch.weaken(formula.lit(), context.negated())?;
        scratch.unfold(Ant::from(formula.lit()), context, formula.lit())?;
        return Ok(Learned::Refuted);
    }
    Ok(Learned::Clause(TrackedClause {
        literals: clause.to_vec(),
        form: ClauseForm::Learned {
            context: context.get(),
            negation: negation.map(PropId::get),
        },
    }))
}
