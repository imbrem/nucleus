//! Generic, immutable propositions over one eventful program-execution relation.
//!
//! This module is syntax and checked composition only. It does not execute a
//! program or create theorem facts. A caller supplies the versioned execution
//! relation, the allowed invocation/host policy, and the observation over a
//! trace and outcome.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref,
    builtin::{Op1, Op2},
};
use covalence_logic_hol_derived::join_same_syntax;

use crate::{ContextualObservation, Evidence};

/// Classifiers used by an eventful execution relation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunTypes {
    /// Versioned semantics/profile classifier.
    pub profile: Ref,
    /// Closed module classifier.
    pub module: Ref,
    /// Exported entry-point classifier.
    pub entry: Ref,
    /// Invocation-input classifier.
    pub inputs: Ref,
    /// Host/import-behavior classifier.
    pub host: Ref,
    /// Event-trace classifier.
    pub trace: Ref,
    /// Execution-outcome classifier.
    pub outcome: Ref,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
}

/// One checked eventful relation
/// `Runs(profile, module, entry, inputs, host, trace, outcome)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunRelation {
    types: RunTypes,
    runs: Ref,
}

impl RunRelation {
    /// Validates and packages an eventful execution predicate.
    ///
    /// # Errors
    ///
    /// Returns an error unless `runs` has the fully-curried classifier induced
    /// by `types`. `kernel` is unchanged on failure.
    pub fn new(kernel: &mut Kernel, types: RunTypes, runs: Ref) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let expected = curried_type(
            &mut staged,
            &[
                types.profile,
                types.module,
                types.entry,
                types.inputs,
                types.host,
                types.trace,
                types.outcome,
            ],
            types.bool_ty,
        )?;
        require_classifier(&mut staged, runs, expected)?;
        *kernel = staged;
        Ok(Self { types, runs })
    }

    /// Returns the execution-relation classifiers.
    #[must_use]
    pub const fn types(self) -> RunTypes {
        self.types
    }

    /// Returns the checked curried execution predicate.
    #[must_use]
    pub const fn predicate(self) -> Ref {
        self.runs
    }

    /// Validates and attaches an invocation policy.
    ///
    /// `admissible` has classifier
    /// `profile -> module -> entry -> inputs -> host -> bool`; this keeps host
    /// and input quantification explicit while allowing the policy to depend on
    /// the selected semantic profile and module.
    ///
    /// # Errors
    ///
    /// Returns an error unless the predicate has the exact required classifier.
    /// `kernel` is unchanged on failure.
    pub fn under(self, kernel: &mut Kernel, admissible: Ref) -> Result<RunDomain, KernelError> {
        let mut staged = kernel.fork();
        let admissible_ty = curried_type(
            &mut staged,
            &[
                self.types.profile,
                self.types.module,
                self.types.entry,
                self.types.inputs,
                self.types.host,
            ],
            self.types.bool_ty,
        )?;
        require_classifier(&mut staged, admissible, admissible_ty)?;
        *kernel = staged;
        Ok(RunDomain {
            relation: self,
            admissible,
        })
    }

    /// Validates and attaches an invocation policy and behavior observation.
    ///
    /// This is shorthand for `self.under(...).observe(...)` when the policy is
    /// used by one observation. Use [`Self::under`] to share it across several
    /// call, trap, return, or trace-property observations.
    ///
    /// # Errors
    ///
    /// Returns an error unless both predicates have the exact required
    /// classifiers. `kernel` is unchanged on failure.
    pub fn observe(
        self,
        kernel: &mut Kernel,
        admissible: Ref,
        observe: Ref,
    ) -> Result<RunObservation, KernelError> {
        let mut staged = kernel.fork();
        let domain = self.under(&mut staged, admissible)?;
        let observation = domain.observe(&mut staged, observe)?;
        *kernel = staged;
        Ok(observation)
    }
}

/// One eventful relation restricted by an explicit invocation and host policy.
///
/// A domain is independent of any particular observed event, so one checked
/// policy can be shared by call, trap, return, and trace-safety propositions.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunDomain {
    relation: RunRelation,
    admissible: Ref,
}

impl RunDomain {
    /// Returns the underlying versioned execution relation.
    #[must_use]
    pub const fn relation(self) -> RunRelation {
        self.relation
    }

    /// Returns the allowed invocation/host policy.
    #[must_use]
    pub const fn admissible(self) -> Ref {
        self.admissible
    }

    /// Validates and attaches a predicate over traces and outcomes.
    ///
    /// # Errors
    ///
    /// Returns an error unless `observe` has classifier
    /// `trace -> outcome -> bool`. `kernel` is unchanged on failure.
    pub fn observe(self, kernel: &mut Kernel, observe: Ref) -> Result<RunObservation, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        let observation_ty =
            curried_type(&mut staged, &[types.trace, types.outcome], types.bool_ty)?;
        require_classifier(&mut staged, observe, observation_ty)?;
        *kernel = staged;
        Ok(RunObservation {
            domain: self,
            observe,
        })
    }

    /// Adapts a predicate over traces into a behavior observation.
    ///
    /// The outcome argument is explicitly abstracted and ignored. This is the
    /// usual adapter for imported calls and trace-safety monitors.
    ///
    /// # Errors
    ///
    /// Returns an error unless `predicate` has classifier `trace -> bool`, or
    /// if checked application or abstraction fails. `kernel` is unchanged on
    /// failure.
    pub fn observe_trace(
        self,
        kernel: &mut Kernel,
        predicate: Ref,
    ) -> Result<RunObservation, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        let predicate_ty = staged.ty_arr(types.trace, types.bool_ty)?;
        require_classifier(&mut staged, predicate, predicate_ty)?;
        let first = staged.fresh_name(&[types.trace, types.outcome, types.bool_ty, predicate])?;
        let trace = staged.tm_fv(first, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 1)?, types.outcome)?;
        let body = staged.app(predicate, trace)?;
        let by_outcome_ty = staged.ty_arr(types.outcome, types.bool_ty)?;
        let by_outcome = staged.lam_at(by_outcome_ty, outcome, body)?;
        let observation_ty = staged.ty_arr(types.trace, by_outcome_ty)?;
        let observation = staged.lam_at(observation_ty, trace, by_outcome)?;
        let observation = self.observe(&mut staged, observation)?;
        *kernel = staged;
        Ok(observation)
    }

    /// Adapts a predicate over outcomes into a behavior observation.
    ///
    /// The trace argument is explicitly abstracted and ignored. This is the
    /// usual adapter for successful return, trap, divergence, and reserved
    /// failure outcomes in profiles that represent them.
    ///
    /// # Errors
    ///
    /// Returns an error unless `predicate` has classifier `outcome -> bool`,
    /// or if checked application or abstraction fails. `kernel` is unchanged
    /// on failure.
    pub fn observe_outcome(
        self,
        kernel: &mut Kernel,
        predicate: Ref,
    ) -> Result<RunObservation, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        let predicate_ty = staged.ty_arr(types.outcome, types.bool_ty)?;
        require_classifier(&mut staged, predicate, predicate_ty)?;
        let first = staged.fresh_name(&[types.trace, types.outcome, types.bool_ty, predicate])?;
        let trace = staged.tm_fv(first, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 1)?, types.outcome)?;
        let body = staged.app(predicate, outcome)?;
        let by_outcome_ty = staged.ty_arr(types.outcome, types.bool_ty)?;
        let by_outcome = staged.lam_at(by_outcome_ty, outcome, body)?;
        let observation_ty = staged.ty_arr(types.trace, by_outcome_ty)?;
        let observation = staged.lam_at(observation_ty, trace, by_outcome)?;
        let observation = self.observe(&mut staged, observation)?;
        *kernel = staged;
        Ok(observation)
    }

    /// Constructs equality of the complete allowed run graphs of two modules.
    ///
    /// The result universally quantifies entry, inputs, host behavior, trace,
    /// and outcome. It requires both modules to agree on admissibility and,
    /// when admissible, on membership in `Runs`. Consequently every predicate
    /// over traces and outcomes observes the same may, must, and never behavior.
    /// This constructs checked syntax only.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible profile/module terms, fresh-name
    /// exhaustion, or a rejected checked HOL construction. `kernel` is
    /// unchanged on failure.
    pub fn same_runs(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        self.compare_runs(kernel, profile, left, right, RunComparison::Equivalent)
    }

    /// Constructs run refinement of an implementation by a specification.
    ///
    /// `implementation refines specification` means the modules have the same
    /// admissible entry/input/host domain and every allowed implementation run
    /// is a specification run with the identical trace and outcome. The
    /// implementation may therefore remove nondeterministic alternatives. If
    /// the specification has any run for an allowed invocation, the
    /// implementation must retain at least one run, so refinement cannot hide
    /// partiality by erasing all behavior. This constructs checked syntax only.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::same_runs`].
    pub fn refines_runs(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        implementation: Ref,
        specification: Ref,
    ) -> Result<Ref, KernelError> {
        self.compare_runs(
            kernel,
            profile,
            implementation,
            specification,
            RunComparison::Refines,
        )
    }

    /// Constructs totality under this domain and one selected profile.
    ///
    /// The result says that every admissible entry/input/host choice has at
    /// least one trace and outcome related by `Runs`. Whether traps or
    /// divergence count as outcomes is determined by the supplied relation and
    /// profile; this proposition does not silently equate totality with
    /// successful return. This constructs checked syntax only.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible profile/module terms, fresh-name
    /// exhaustion, or a rejected checked HOL construction. `kernel` is
    /// unchanged on failure.
    pub fn total(self, kernel: &mut Kernel, profile: Ref, module: Ref) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        require_classifier(&mut staged, module, types.module)?;
        let first = staged.fresh_name(&[
            self.relation.runs,
            self.admissible,
            profile,
            module,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
        ])?;
        let entry = staged.tm_fv(first, types.entry)?;
        let inputs = staged.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = staged.tm_fv(checked_name(first, 2)?, types.host)?;
        let trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let allowed = apply(
            &mut staged,
            self.admissible,
            &[profile, module, entry, inputs, host],
        )?;
        let run = apply(
            &mut staged,
            self.relation.runs,
            &[profile, module, entry, inputs, host, trace, outcome],
        )?;
        let exists_run = quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], run)?;
        let total = staged.op2(Op2::Imp, allowed, exists_run)?;
        let total = quantify_forall(&mut staged, types.bool_ty, &[entry, inputs, host], total)?;
        *kernel = staged;
        Ok(total)
    }

    /// Constructs determinism under this domain and one selected profile.
    ///
    /// For each admissible entry/input/host choice, any two related runs must
    /// have equal traces and equal outcomes. Host behavior is held fixed, so a
    /// nondeterministic host policy remains explicit rather than being blamed
    /// on the module. Determinism does not imply totality.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::total`].
    #[allow(clippy::too_many_lines)]
    pub fn deterministic(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        require_classifier(&mut staged, module, types.module)?;
        let first = staged.fresh_name(&[
            self.relation.runs,
            self.admissible,
            profile,
            module,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
            types.bool_ty,
        ])?;
        let entry = staged.tm_fv(first, types.entry)?;
        let inputs = staged.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = staged.tm_fv(checked_name(first, 2)?, types.host)?;
        let left_trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let left_outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let right_trace = staged.tm_fv(checked_name(first, 5)?, types.trace)?;
        let right_outcome = staged.tm_fv(checked_name(first, 6)?, types.outcome)?;
        let allowed = apply(
            &mut staged,
            self.admissible,
            &[profile, module, entry, inputs, host],
        )?;
        let left_run = apply(
            &mut staged,
            self.relation.runs,
            &[
                profile,
                module,
                entry,
                inputs,
                host,
                left_trace,
                left_outcome,
            ],
        )?;
        let right_run = apply(
            &mut staged,
            self.relation.runs,
            &[
                profile,
                module,
                entry,
                inputs,
                host,
                right_trace,
                right_outcome,
            ],
        )?;
        let runs = staged.op2(Op2::And, left_run, right_run)?;
        let eligible_runs = staged.op2(Op2::And, allowed, runs)?;
        let same_trace = staged.eq(types.bool_ty, left_trace, right_trace)?;
        let same_outcome = staged.eq(types.bool_ty, left_outcome, right_outcome)?;
        let same_result = staged.op2(Op2::And, same_trace, same_outcome)?;
        let deterministic = staged.op2(Op2::Imp, eligible_runs, same_result)?;
        let deterministic = quantify_forall(
            &mut staged,
            types.bool_ty,
            &[
                entry,
                inputs,
                host,
                left_trace,
                left_outcome,
                right_trace,
                right_outcome,
            ],
            deterministic,
        )?;
        *kernel = staged;
        Ok(deterministic)
    }

    /// Proves that every module has the same allowed run graph as itself.
    ///
    /// The proof uses only checked equality reflexivity, propositional rules,
    /// and universal introduction. It has no premises and assumes no property
    /// of the execution relation or admissibility policy.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible profile/module terms or a rejected
    /// checked construction or theorem rule. `kernel` is unchanged on failure.
    pub fn prove_same_runs_reflexive(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
    ) -> Result<Evidence, KernelError> {
        self.prove_comparison_reflexive(kernel, profile, module, RunComparison::Equivalent)
    }

    /// Proves that every module refines itself.
    ///
    /// The proof is structural and premise-free; it assumes no determinism,
    /// totality, or semantic property of `Runs`.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`Self::prove_same_runs_reflexive`].
    pub fn prove_run_refinement_reflexive(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
    ) -> Result<Evidence, KernelError> {
        self.prove_comparison_reflexive(kernel, profile, module, RunComparison::Refines)
    }

    #[allow(clippy::too_many_lines)]
    fn prove_comparison_reflexive(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
        comparison: RunComparison,
    ) -> Result<Evidence, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        require_classifier(&mut staged, module, types.module)?;
        let first = staged.fresh_name(&[
            types.profile,
            types.module,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
            types.bool_ty,
            self.relation.runs,
            self.admissible,
            profile,
            module,
        ])?;
        let entry = staged.tm_fv(first, types.entry)?;
        let inputs = staged.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = staged.tm_fv(checked_name(first, 2)?, types.host)?;
        let trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let domain_variables = [entry, inputs, host];
        let run_variables = [entry, inputs, host, trace, outcome];
        let allowed = apply(
            &mut staged,
            self.admissible,
            &[profile, module, entry, inputs, host],
        )?;
        let same_domain = staged.eq(types.bool_ty, allowed, allowed)?;
        let same_domain_fact = staged.refl(types.bool_ty, allowed)?;
        join_same_syntax(&mut staged, same_domain_fact.equality, same_domain).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "run domain reflexivity alignment",
            }
        })?;
        staged.convert_conclusions(
            same_domain_fact.theorem,
            same_domain_fact.equality,
            same_domain,
        )?;
        let (same_domain, same_domain_theorem) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &domain_variables,
            same_domain,
            same_domain_fact.theorem,
        )?;

        let run = apply(
            &mut staged,
            self.relation.runs,
            &[profile, module, entry, inputs, host, trace, outcome],
        )?;
        let (behavior, behavior_theorem) = match comparison {
            RunComparison::Equivalent => {
                let equality = staged.eq(types.bool_ty, run, run)?;
                let reflexive = staged.refl(types.bool_ty, run)?;
                join_same_syntax(&mut staged, reflexive.equality, equality).map_err(|_| {
                    KernelError::InvalidTheoremRule {
                        rule: "run behavior reflexivity alignment",
                    }
                })?;
                staged.convert_conclusions(reflexive.theorem, reflexive.equality, equality)?;
                (equality, reflexive.theorem)
            }
            RunComparison::Refines => {
                let implication = staged.op2(Op2::Imp, run, run)?;
                let identity = staged.identity(positive(run))?;
                let theorem = staged.imp_right(identity, positive(implication))?;
                (implication, theorem)
            }
        };
        let both_allowed = staged.op2(Op2::And, allowed, allowed)?;
        staged.weaken(behavior_theorem, &[positive(both_allowed)], &[])?;
        let guarded_behavior = staged.op2(Op2::Imp, both_allowed, behavior)?;
        let guarded_theorem = staged.imp_right(behavior_theorem, positive(guarded_behavior))?;
        let (behavior, behavior_theorem) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &run_variables,
            guarded_behavior,
            guarded_theorem,
        )?;
        let (behavior, behavior_theorem) = if comparison == RunComparison::Refines {
            let exists_run = quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], run)?;
            let progress = staged.op2(Op2::Imp, exists_run, exists_run)?;
            let assumed = staged.identity(positive(exists_run))?;
            let progress_theorem = staged.imp_right(assumed, positive(progress))?;
            staged.weaken(progress_theorem, &[positive(both_allowed)], &[])?;
            let guarded_progress = staged.op2(Op2::Imp, both_allowed, progress)?;
            let guarded_progress_theorem =
                staged.imp_right(progress_theorem, positive(guarded_progress))?;
            let (progress, progress_theorem) = introduce_forall(
                &mut staged,
                types.bool_ty,
                &domain_variables,
                guarded_progress,
                guarded_progress_theorem,
            )?;
            let combined = staged.op2(Op2::And, behavior, progress)?;
            let theorem =
                staged.and_right(behavior_theorem, progress_theorem, positive(combined))?;
            (combined, theorem)
        } else {
            (behavior, behavior_theorem)
        };
        let proposition = staged.op2(Op2::And, same_domain, behavior)?;
        let theorem =
            staged.and_right(same_domain_theorem, behavior_theorem, positive(proposition))?;
        let canonical = self.compare_runs(&mut staged, profile, module, module, comparison)?;
        join_same_syntax(&mut staged, proposition, canonical).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "run comparison reflexivity alignment",
            }
        })?;
        staged.convert_conclusions(theorem, proposition, canonical)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem,
            holds: true,
        })
    }

    fn compare_runs(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        left: Ref,
        right: Ref,
        comparison: RunComparison,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        require_classifier(&mut staged, left, types.module)?;
        require_classifier(&mut staged, right, types.module)?;
        let first = staged.fresh_name(&[
            types.profile,
            types.module,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
            types.bool_ty,
            self.relation.runs,
            self.admissible,
            profile,
            left,
            right,
        ])?;
        let entry = staged.tm_fv(first, types.entry)?;
        let inputs = staged.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = staged.tm_fv(checked_name(first, 2)?, types.host)?;
        let trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let domain_variables = [entry, inputs, host];
        let run_variables = [entry, inputs, host, trace, outcome];
        let left_allowed = apply(
            &mut staged,
            self.admissible,
            &[profile, left, entry, inputs, host],
        )?;
        let right_allowed = apply(
            &mut staged,
            self.admissible,
            &[profile, right, entry, inputs, host],
        )?;
        let same_domain = staged.eq(types.bool_ty, left_allowed, right_allowed)?;
        let same_domain =
            quantify_forall(&mut staged, types.bool_ty, &domain_variables, same_domain)?;
        let left_run = apply(
            &mut staged,
            self.relation.runs,
            &[profile, left, entry, inputs, host, trace, outcome],
        )?;
        let right_run = apply(
            &mut staged,
            self.relation.runs,
            &[profile, right, entry, inputs, host, trace, outcome],
        )?;
        let both_allowed = staged.op2(Op2::And, left_allowed, right_allowed)?;
        let behavior = match comparison {
            RunComparison::Equivalent => staged.eq(types.bool_ty, left_run, right_run)?,
            RunComparison::Refines => staged.op2(Op2::Imp, left_run, right_run)?,
        };
        let behavior = staged.op2(Op2::Imp, both_allowed, behavior)?;
        let behavior = quantify_forall(&mut staged, types.bool_ty, &run_variables, behavior)?;
        let behavior = if comparison == RunComparison::Refines {
            let implementation_runs =
                quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], left_run)?;
            let specification_runs =
                quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], right_run)?;
            let progress = staged.op2(Op2::Imp, specification_runs, implementation_runs)?;
            let progress = staged.op2(Op2::Imp, both_allowed, progress)?;
            let progress =
                quantify_forall(&mut staged, types.bool_ty, &domain_variables, progress)?;
            staged.op2(Op2::And, behavior, progress)?
        } else {
            behavior
        };
        let proposition = staged.op2(Op2::And, same_domain, behavior)?;
        *kernel = staged;
        Ok(proposition)
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RunComparison {
    Equivalent,
    Refines,
}

/// Quantification mode for a behavior observation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BehaviorQuantifier {
    /// At least one allowed execution has the observed behavior.
    May,
    /// Every allowed execution has the observed behavior, without asserting
    /// that an execution exists.
    Every,
    /// Every admissible invocation has at least one execution, and every one
    /// of its executions has the observed behavior.
    Must,
    /// No allowed execution has the observed behavior.
    Never,
}

/// An observation over one eventful execution relation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunObservation {
    domain: RunDomain,
    observe: Ref,
}

/// Failure to compose behavior observations.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RunObservationError {
    /// A checked HOL construction failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Binary observations came from different execution domains.
    #[snafu(display("cannot combine observations from different run domains"))]
    DomainMismatch,
}

impl RunObservation {
    /// Returns the underlying versioned execution relation.
    #[must_use]
    pub const fn relation(self) -> RunRelation {
        self.domain.relation
    }

    /// Returns the reusable execution domain.
    #[must_use]
    pub const fn domain(self) -> RunDomain {
        self.domain
    }

    /// Returns the allowed invocation/host policy.
    #[must_use]
    pub const fn admissible(self) -> Ref {
        self.domain.admissible
    }

    /// Returns the trace/outcome predicate.
    #[must_use]
    pub const fn observation(self) -> Ref {
        self.observe
    }

    /// Constructs the pointwise negation of this observation.
    ///
    /// The result remains attached to the same run domain and can be queried
    /// with any behavior quantifier.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application, negation, or abstraction
    /// fails. `kernel` is unchanged on failure.
    pub fn negate(self, kernel: &mut Kernel) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        let (trace, outcome) = observation_variables(&mut staged, self.domain, &[self.observe])?;
        let observed = apply(&mut staged, self.observe, &[trace, outcome])?;
        let body = staged.op1(Op1::Not, observed)?;
        let observe = abstract_observation(&mut staged, types, trace, outcome, body)?;
        let observation = self.domain.observe(&mut staged, observe)?;
        *kernel = staged;
        Ok(observation)
    }

    /// Constructs pointwise conjunction with another observation.
    ///
    /// # Errors
    ///
    /// Returns [`RunObservationError::DomainMismatch`] unless both observations
    /// use the same run relation and admissibility policy, or a checked HOL
    /// construction fails. `kernel` is unchanged on failure.
    pub fn and(self, kernel: &mut Kernel, other: Self) -> Result<Self, RunObservationError> {
        self.combine(kernel, other, Op2::And)
    }

    /// Constructs pointwise disjunction with another observation.
    ///
    /// # Errors
    ///
    /// Returns under the same conditions as [`Self::and`].
    pub fn or(self, kernel: &mut Kernel, other: Self) -> Result<Self, RunObservationError> {
        self.combine(kernel, other, Op2::Or)
    }

    fn combine(
        self,
        kernel: &mut Kernel,
        other: Self,
        operation: Op2,
    ) -> Result<Self, RunObservationError> {
        if self.domain != other.domain {
            return Err(RunObservationError::DomainMismatch);
        }
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        let (trace, outcome) =
            observation_variables(&mut staged, self.domain, &[self.observe, other.observe])?;
        let left = apply(&mut staged, self.observe, &[trace, outcome])?;
        let right = apply(&mut staged, other.observe, &[trace, outcome])?;
        let body = staged.op2(operation, left, right)?;
        let observe = abstract_observation(&mut staged, types, trace, outcome, body)?;
        let observation = self.domain.observe(&mut staged, observe)?;
        *kernel = staged;
        Ok(observation)
    }

    /// Constructs a may, every, must, or never proposition for one profile and module.
    ///
    /// `Must` is deliberately non-vacuous per invocation: for every admissible
    /// entry/input/host choice, at least one matching execution must exist and
    /// every execution must satisfy the observation.
    /// `Never` is the literal HOL negation of `May`, so the duality is visible
    /// in the resulting syntax rather than encoded as frontend policy.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible profile/module terms, fresh-name
    /// exhaustion, or a rejected checked HOL construction. `kernel` is
    /// unchanged on failure.
    pub fn proposition(
        self,
        kernel: &mut Kernel,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        module: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        require_classifier(&mut staged, module, types.module)?;
        let roots = [
            types.profile,
            types.module,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
            types.bool_ty,
            self.domain.relation.runs,
            self.domain.admissible,
            self.observe,
            profile,
            module,
        ];
        let first = staged.fresh_name(&roots)?;
        let entry = staged.tm_fv(first, types.entry)?;
        let inputs = staged.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = staged.tm_fv(checked_name(first, 2)?, types.host)?;
        let trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let invocation_variables = [entry, inputs, host];
        let result_variables = [trace, outcome];
        let run_variables = [entry, inputs, host, trace, outcome];
        let allowed = apply(
            &mut staged,
            self.domain.admissible,
            &[profile, module, entry, inputs, host],
        )?;
        let runs = apply(
            &mut staged,
            self.domain.relation.runs,
            &[profile, module, entry, inputs, host, trace, outcome],
        )?;
        let observed = apply(&mut staged, self.observe, &[trace, outcome])?;
        let proposition = match quantifier {
            BehaviorQuantifier::May | BehaviorQuantifier::Never => {
                let eligible = staged.op2(Op2::And, allowed, runs)?;
                let witnessed = staged.op2(Op2::And, eligible, observed)?;
                let may = quantify_exists(&mut staged, types.bool_ty, &run_variables, witnessed)?;
                if quantifier == BehaviorQuantifier::May {
                    may
                } else {
                    staged.op1(Op1::Not, may)?
                }
            }
            BehaviorQuantifier::Every => {
                let eligible = staged.op2(Op2::And, allowed, runs)?;
                let required = staged.op2(Op2::Imp, eligible, observed)?;
                quantify_forall(&mut staged, types.bool_ty, &run_variables, required)?
            }
            BehaviorQuantifier::Must => {
                let matching = staged.op2(Op2::And, runs, observed)?;
                let exists_matching =
                    quantify_exists(&mut staged, types.bool_ty, &result_variables, matching)?;
                let run_implies_observed = staged.op2(Op2::Imp, runs, observed)?;
                let every_run = quantify_forall(
                    &mut staged,
                    types.bool_ty,
                    &result_variables,
                    run_implies_observed,
                )?;
                let required = staged.op2(Op2::And, exists_matching, every_run)?;
                let required_when_allowed = staged.op2(Op2::Imp, allowed, required)?;
                quantify_forall(
                    &mut staged,
                    types.bool_ty,
                    &invocation_variables,
                    required_when_allowed,
                )?
            }
        };
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs `module -> bool` for one profile and quantification mode.
    ///
    /// The result plugs directly into a generic contextual observation.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::proposition`], or
    /// if checked abstraction fails. `kernel` is unchanged on failure.
    pub fn predicate(
        self,
        kernel: &mut Kernel,
        quantifier: BehaviorQuantifier,
        profile: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        let name = staged.fresh_name(&[
            types.module,
            types.bool_ty,
            self.domain.relation.runs,
            self.domain.admissible,
            self.observe,
            profile,
        ])?;
        let module = staged.tm_fv(name, types.module)?;
        let body = self.proposition(&mut staged, quantifier, profile, module)?;
        let predicate_ty = staged.ty_arr(types.module, types.bool_ty)?;
        let predicate = staged.lam_at(predicate_ty, module, body)?;
        *kernel = staged;
        Ok(predicate)
    }

    /// Adapts this behavior into contextual equivalence of modules.
    ///
    /// The supplied operations describe closing/linking contexts. The chosen
    /// may, must, or never predicate becomes the observation of each resulting
    /// closed module, so the existing contextual and function-replacement
    /// theorems apply without introducing another execution semantics.
    ///
    /// # Errors
    ///
    /// Returns an error if the profile or a context operation has an
    /// incompatible classifier, or checked predicate construction fails.
    /// `kernel` is unchanged on failure.
    pub fn contextual(
        self,
        kernel: &mut Kernel,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        context_ty: Ref,
        plug: Ref,
        admissible: Ref,
    ) -> Result<ContextualObservation, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        let observe = self.predicate(&mut staged, quantifier, profile)?;
        let contextual = ContextualObservation {
            subject_ty: types.module,
            context_ty,
            observed_ty: types.module,
            bool_ty: types.bool_ty,
            plug,
            admissible,
            observe,
        }
        .checked(&mut staged)?;
        *kernel = staged;
        Ok(contextual)
    }

    /// Constructs the existential behavior proposition.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::proposition`].
    pub fn may(self, kernel: &mut Kernel, profile: Ref, module: Ref) -> Result<Ref, KernelError> {
        self.proposition(kernel, BehaviorQuantifier::May, profile, module)
    }

    /// Constructs the universal behavior proposition without asserting progress.
    ///
    /// This is the usual form for trace safety: executions that exist must
    /// satisfy the observation, while totality remains a separate explicit
    /// property.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::proposition`].
    pub fn every(self, kernel: &mut Kernel, profile: Ref, module: Ref) -> Result<Ref, KernelError> {
        self.proposition(kernel, BehaviorQuantifier::Every, profile, module)
    }

    /// Constructs the non-vacuous universal behavior proposition.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::proposition`].
    pub fn must(self, kernel: &mut Kernel, profile: Ref, module: Ref) -> Result<Ref, KernelError> {
        self.proposition(kernel, BehaviorQuantifier::Must, profile, module)
    }

    /// Constructs the negation of existential behavior.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::proposition`].
    pub fn never(self, kernel: &mut Kernel, profile: Ref, module: Ref) -> Result<Ref, KernelError> {
        self.proposition(kernel, BehaviorQuantifier::Never, profile, module)
    }
}

fn checked_name(first: u64, offset: u64) -> Result<u64, KernelError> {
    first.checked_add(offset).ok_or(KernelError::TooManyNames)
}

fn observation_variables(
    kernel: &mut Kernel,
    domain: RunDomain,
    observations: &[Ref],
) -> Result<(Ref, Ref), KernelError> {
    let types = domain.relation.types;
    let mut roots = vec![
        types.trace,
        types.outcome,
        types.bool_ty,
        domain.relation.runs,
        domain.admissible,
    ];
    roots.extend_from_slice(observations);
    let first = kernel.fresh_name(&roots)?;
    let trace = kernel.tm_fv(first, types.trace)?;
    let outcome = kernel.tm_fv(checked_name(first, 1)?, types.outcome)?;
    Ok((trace, outcome))
}

fn abstract_observation(
    kernel: &mut Kernel,
    types: RunTypes,
    trace: Ref,
    outcome: Ref,
    body: Ref,
) -> Result<Ref, KernelError> {
    let by_outcome_ty = kernel.ty_arr(types.outcome, types.bool_ty)?;
    let by_outcome = kernel.lam_at(by_outcome_ty, outcome, body)?;
    let observation_ty = kernel.ty_arr(types.trace, by_outcome_ty)?;
    kernel.lam_at(observation_ty, trace, by_outcome)
}

fn curried_type(kernel: &mut Kernel, arguments: &[Ref], result: Ref) -> Result<Ref, KernelError> {
    arguments
        .iter()
        .rev()
        .try_fold(result, |tail, &argument| kernel.ty_arr(argument, tail))
}

fn apply(kernel: &mut Kernel, function: Ref, arguments: &[Ref]) -> Result<Ref, KernelError> {
    arguments
        .iter()
        .try_fold(function, |applied, &argument| kernel.app(applied, argument))
}

fn quantify_exists(
    kernel: &mut Kernel,
    bool_ty: Ref,
    variables: &[Ref],
    body: Ref,
) -> Result<Ref, KernelError> {
    variables
        .iter()
        .rev()
        .try_fold(body, |body, &variable| kernel.exists_tm(variable, body))
        .and_then(|proposition| {
            require_classifier(kernel, proposition, bool_ty)?;
            Ok(proposition)
        })
}

fn quantify_forall(
    kernel: &mut Kernel,
    bool_ty: Ref,
    variables: &[Ref],
    body: Ref,
) -> Result<Ref, KernelError> {
    variables.iter().rev().try_fold(body, |body, &variable| {
        kernel.forall_tm(bool_ty, variable, body)
    })
}

fn introduce_forall(
    kernel: &mut Kernel,
    bool_ty: Ref,
    variables: &[Ref],
    body: Ref,
    theorem: covalence_logic_hol::ThmId,
) -> Result<(Ref, covalence_logic_hol::ThmId), KernelError> {
    variables
        .iter()
        .rev()
        .try_fold((body, theorem), |(body, theorem), &variable| {
            let universal = kernel.forall_tm(bool_ty, variable, body)?;
            let theorem = kernel.forall_intro_at(theorem, variable, universal)?;
            Ok((universal, theorem))
        })
}

fn positive(proposition: Ref) -> Lit {
    Lit::positive(proposition.get())
}

fn require_classifier(kernel: &mut Kernel, term: Ref, expected: Ref) -> Result<(), KernelError> {
    let actual = kernel.classifier(term)?;
    join_same_syntax(kernel, actual, expected)
        .map(|_| ())
        .map_err(|_| KernelError::ClassifierMismatch { expected, actual })
}

#[cfg(test)]
mod tests {
    use super::{BehaviorQuantifier, RunRelation, RunTypes};
    use crate::EvidenceScope;
    use covalence_logic_hol::{Kernel, Tag, TmTag};

    #[test]
    #[allow(clippy::too_many_lines)]
    fn eventful_run_observations_are_generic_checked_and_transactional() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let types = RunTypes {
            profile: kernel.ty_fv(1, star).unwrap(),
            module: kernel.ty_fv(2, star).unwrap(),
            entry: kernel.ty_fv(3, star).unwrap(),
            inputs: kernel.ty_fv(4, star).unwrap(),
            host: kernel.ty_fv(5, star).unwrap(),
            trace: kernel.ty_fv(6, star).unwrap(),
            outcome: kernel.ty_fv(7, star).unwrap(),
            bool_ty,
        };
        let run_ty = super::curried_type(
            &mut kernel,
            &[
                types.profile,
                types.module,
                types.entry,
                types.inputs,
                types.host,
                types.trace,
                types.outcome,
            ],
            bool_ty,
        )
        .unwrap();
        let admissible_ty = super::curried_type(
            &mut kernel,
            &[
                types.profile,
                types.module,
                types.entry,
                types.inputs,
                types.host,
            ],
            bool_ty,
        )
        .unwrap();
        let observe_ty =
            super::curried_type(&mut kernel, &[types.trace, types.outcome], bool_ty).unwrap();
        let runs = kernel.tm_fv(20, run_ty).unwrap();
        let admissible = kernel.tm_fv(21, admissible_ty).unwrap();
        let other_admissible = kernel.tm_fv(31, admissible_ty).unwrap();
        let observe = kernel.tm_fv(22, observe_ty).unwrap();
        let trace_predicate_ty = kernel.ty_arr(types.trace, bool_ty).unwrap();
        let outcome_predicate_ty = kernel.ty_arr(types.outcome, bool_ty).unwrap();
        let trace_predicate = kernel.tm_fv(29, trace_predicate_ty).unwrap();
        let outcome_predicate = kernel.tm_fv(30, outcome_predicate_ty).unwrap();
        let profile = kernel.tm_fv(23, types.profile).unwrap();
        let module = kernel.tm_fv(24, types.module).unwrap();
        let other_module = kernel.tm_fv(26, types.module).unwrap();
        let context_ty = kernel.ty_fv(8, star).unwrap();
        let plug_ty =
            super::curried_type(&mut kernel, &[context_ty, types.module], types.module).unwrap();
        let contextual_admissible_ty =
            super::curried_type(&mut kernel, &[context_ty, types.module], bool_ty).unwrap();
        let plug = kernel.tm_fv(27, plug_ty).unwrap();
        let contextual_admissible = kernel.tm_fv(28, contextual_admissible_ty).unwrap();
        let theorem_count = kernel.thm().live_theorems().count();
        let relation = RunRelation::new(&mut kernel, types, runs).unwrap();
        let domain = relation.under(&mut kernel, admissible).unwrap();
        let observation = domain.observe(&mut kernel, observe).unwrap();
        let trace_observation = domain.observe_trace(&mut kernel, trace_predicate).unwrap();
        let outcome_observation = domain
            .observe_outcome(&mut kernel, outcome_predicate)
            .unwrap();
        assert_eq!(observation.domain(), domain);
        assert_eq!(observation.relation(), relation);
        assert_eq!(trace_observation.domain(), domain);
        assert_eq!(outcome_observation.domain(), domain);
        let combined_observation = trace_observation
            .and(&mut kernel, outcome_observation)
            .unwrap();
        let alternative_observation = trace_observation
            .or(&mut kernel, outcome_observation)
            .unwrap();
        let negated_observation = trace_observation.negate(&mut kernel).unwrap();

        let may = observation.may(&mut kernel, profile, module).unwrap();
        let every = observation.every(&mut kernel, profile, module).unwrap();
        let never = observation.never(&mut kernel, profile, module).unwrap();
        let must = observation.must(&mut kernel, profile, module).unwrap();
        assert_eq!(kernel.classifier(may).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(every).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(never).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(must).unwrap(), bool_ty);
        assert_eq!(kernel.arena().tag(never), Some(Tag::Tm(TmTag::Op1)));
        assert_eq!(kernel.arena().tag(must), Some(Tag::Tm(TmTag::Eq)));
        let never_body = kernel.arena().children(never).unwrap().next().unwrap();
        covalence_logic_hol_derived::join_same_syntax(&mut kernel, never_body, may).unwrap();
        for composed in [
            combined_observation,
            alternative_observation,
            negated_observation,
        ] {
            let proposition = composed.may(&mut kernel, profile, module).unwrap();
            assert_eq!(kernel.classifier(proposition).unwrap(), bool_ty);
        }
        let same_runs = domain
            .same_runs(&mut kernel, profile, module, other_module)
            .unwrap();
        let refinement = domain
            .refines_runs(&mut kernel, profile, module, other_module)
            .unwrap();
        let total = domain.total(&mut kernel, profile, module).unwrap();
        let deterministic = domain.deterministic(&mut kernel, profile, module).unwrap();
        assert_eq!(kernel.classifier(same_runs).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(refinement).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(total).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(deterministic).unwrap(), bool_ty);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
        let equivalence_reflexive = domain
            .prove_same_runs_reflexive(&mut kernel, profile, module)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, equivalence_reflexive)
            .unwrap();
        let refinement_reflexive = domain
            .prove_run_refinement_reflexive(&mut kernel, profile, module)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, refinement_reflexive)
            .unwrap();
        let contextual = observation
            .contextual(
                &mut kernel,
                BehaviorQuantifier::May,
                profile,
                context_ty,
                plug,
                contextual_admissible,
            )
            .unwrap();
        let contextual_equivalence = contextual
            .equivalent(&mut kernel, module, other_module)
            .unwrap();
        assert_eq!(kernel.classifier(contextual_equivalence).unwrap(), bool_ty);

        for quantifier in [
            BehaviorQuantifier::May,
            BehaviorQuantifier::Every,
            BehaviorQuantifier::Must,
            BehaviorQuantifier::Never,
        ] {
            let predicate = observation
                .predicate(&mut kernel, quantifier, profile)
                .unwrap();
            let predicate_ty = kernel.ty_arr(types.module, bool_ty).unwrap();
            let actual = kernel.classifier(predicate).unwrap();
            covalence_logic_hol_derived::join_same_syntax(&mut kernel, actual, predicate_ty)
                .unwrap();
        }

        let wrong_runs = kernel.tm_fv(25, observe_ty).unwrap();
        let before = kernel.arena().clone();
        assert!(RunRelation::new(&mut kernel, types, wrong_runs).is_err());
        assert_eq!(kernel.arena(), &before);

        let before = kernel.arena().clone();
        assert!(relation.under(&mut kernel, observe).is_err());
        assert_eq!(kernel.arena(), &before);

        let before = kernel.arena().clone();
        assert!(relation.observe(&mut kernel, observe, admissible).is_err());
        assert_eq!(kernel.arena(), &before);

        let before = kernel.arena().clone();
        assert!(domain.observe(&mut kernel, admissible).is_err());
        assert_eq!(kernel.arena(), &before);

        let before = kernel.arena().clone();
        assert!(
            domain
                .observe_trace(&mut kernel, outcome_predicate)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);

        let other_domain = relation.under(&mut kernel, other_admissible).unwrap();
        let other_observation = other_domain.observe(&mut kernel, observe).unwrap();
        let before = kernel.arena().clone();
        assert!(matches!(
            observation.and(&mut kernel, other_observation),
            Err(super::RunObservationError::DomainMismatch)
        ));
        assert_eq!(kernel.arena(), &before);

        let before = kernel.arena().clone();
        assert!(
            domain
                .refines_runs(&mut kernel, profile, profile, other_module)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);

        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            domain
                .prove_same_runs_reflexive(&mut kernel, module, module)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);

        let before = kernel.arena().clone();
        assert!(
            observation
                .contextual(
                    &mut kernel,
                    BehaviorQuantifier::May,
                    profile,
                    context_ty,
                    contextual_admissible,
                    plug,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
    }
}
