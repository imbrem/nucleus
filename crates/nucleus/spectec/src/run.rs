//! Generic, immutable propositions over one eventful program-execution relation.
//!
//! This module is syntax and checked composition only. It does not execute a
//! program or create theorem facts. A caller supplies the versioned execution
//! relation, the allowed invocation/host policy, and the observation over a
//! trace and outcome.

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
    pub fn equivalent(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        self.compare_runs(kernel, profile, left, right, RunComparison::Equivalent)
    }

    /// Constructs behavioral refinement of an implementation by a specification.
    ///
    /// `implementation refines specification` means the modules have the same
    /// admissible entry/input/host domain and every allowed implementation run
    /// is a specification run with the identical trace and outcome. The
    /// implementation may therefore remove nondeterministic behaviors but may
    /// not silently reject an invocation. This constructs checked syntax only.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::equivalent`].
    pub fn refines(
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
    pub fn prove_equivalence_reflexive(
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
    /// [`Self::prove_equivalence_reflexive`].
    pub fn prove_refinement_reflexive(
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
        let proposition = staged.op2(Op2::And, same_domain, behavior)?;
        *kernel = staged;
        Ok(proposition)
    }
}

#[derive(Clone, Copy)]
enum RunComparison {
    Equivalent,
    Refines,
}

/// Quantification mode for a behavior observation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BehaviorQuantifier {
    /// At least one allowed execution has the observed behavior.
    May,
    /// At least one allowed execution exists and every allowed execution has
    /// the observed behavior.
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

    /// Constructs a may, must, or never proposition for one profile and module.
    ///
    /// `Must` is deliberately non-vacuous: it conjoins existence of an allowed
    /// execution with universal observation of every allowed execution.
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
        let variables = [entry, inputs, host, trace, outcome];
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
        let eligible = staged.op2(Op2::And, allowed, runs)?;
        let witnessed = staged.op2(Op2::And, eligible, observed)?;
        let may = quantify_exists(&mut staged, types.bool_ty, &variables, witnessed)?;
        let proposition = match quantifier {
            BehaviorQuantifier::May => may,
            BehaviorQuantifier::Never => staged.op1(Op1::Not, may)?,
            BehaviorQuantifier::Must => {
                let exists = quantify_exists(&mut staged, types.bool_ty, &variables, eligible)?;
                let implication = staged.op2(Op2::Imp, eligible, observed)?;
                let every = quantify_forall(&mut staged, types.bool_ty, &variables, implication)?;
                staged.op2(Op2::And, exists, every)?
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
        let observe = kernel.tm_fv(22, observe_ty).unwrap();
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
        assert_eq!(observation.domain(), domain);
        assert_eq!(observation.relation(), relation);

        let may = observation.may(&mut kernel, profile, module).unwrap();
        let never = observation.never(&mut kernel, profile, module).unwrap();
        let must = observation.must(&mut kernel, profile, module).unwrap();
        assert_eq!(kernel.classifier(may).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(never).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(must).unwrap(), bool_ty);
        assert_eq!(kernel.arena().tag(never), Some(Tag::Tm(TmTag::Op1)));
        assert_eq!(kernel.arena().tag(must), Some(Tag::Tm(TmTag::Op2)));
        let equivalent = domain
            .equivalent(&mut kernel, profile, module, other_module)
            .unwrap();
        let refinement = domain
            .refines(&mut kernel, profile, module, other_module)
            .unwrap();
        assert_eq!(kernel.classifier(equivalent).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(refinement).unwrap(), bool_ty);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
        let equivalence_reflexive = domain
            .prove_equivalence_reflexive(&mut kernel, profile, module)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, equivalence_reflexive)
            .unwrap();
        let refinement_reflexive = domain
            .prove_refinement_reflexive(&mut kernel, profile, module)
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
                .refines(&mut kernel, profile, profile, other_module)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);

        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            domain
                .prove_equivalence_reflexive(&mut kernel, module, module)
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
