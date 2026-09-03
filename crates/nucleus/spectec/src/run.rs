//! Generic, immutable propositions over one eventful program-execution relation.
//!
//! This module is syntax and checked composition only. It does not execute a
//! program or create theorem facts. A caller supplies the versioned execution
//! relation, the allowed invocation/host policy, and the observation over a
//! trace and outcome.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, SynRel,
    builtin::{Op1, Op2},
};
use covalence_logic_hol_derived::{
    EqualityError, ForallError, ModelError, equality_symmetry, equality_transitivity, forall_elim,
    join_alpha_equivalent, join_same_syntax, substitute,
};

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
        let domain_ty = curried_type(
            &mut staged,
            &[self.types.entry, self.types.inputs, self.types.host],
            self.types.bool_ty,
        )?;
        let run_graph_ty = curried_type(
            &mut staged,
            &[
                self.types.entry,
                self.types.inputs,
                self.types.host,
                self.types.trace,
                self.types.outcome,
            ],
            self.types.bool_ty,
        )?;
        *kernel = staged;
        Ok(RunDomain {
            relation: self,
            admissible,
            domain_ty,
            run_graph_ty,
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
    domain_ty: Ref,
    run_graph_ty: Ref,
}

/// Immutable schema for closing a module inside a linking context.
///
/// `plug(context, module)` produces the closed module whose runs are observed.
/// `admissible(context, module)` makes context well-formedness and linkability
/// explicit rather than hiding either condition in execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunContext {
    types: RunTypes,
    context_ty: Ref,
    plug: Ref,
    admissible: Ref,
}

impl RunContext {
    /// Validates a reusable context schema.
    ///
    /// # Errors
    ///
    /// Returns an error unless `plug` has classifier
    /// `context -> module -> module` and `admissible` has classifier
    /// `context -> module -> bool`. `kernel` is unchanged on failure.
    pub fn new(
        kernel: &mut Kernel,
        types: RunTypes,
        context_ty: Ref,
        plug: Ref,
        admissible: Ref,
    ) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let plug_ty = curried_type(&mut staged, &[context_ty, types.module], types.module)?;
        require_classifier(&mut staged, plug, plug_ty)?;
        let admissible_ty = curried_type(&mut staged, &[context_ty, types.module], types.bool_ty)?;
        require_classifier(&mut staged, admissible, admissible_ty)?;
        *kernel = staged;
        Ok(Self {
            types,
            context_ty,
            plug,
            admissible,
        })
    }

    /// Returns the classifier of linking contexts.
    #[must_use]
    pub const fn context_type(self) -> Ref {
        self.context_ty
    }

    /// Returns `context -> module -> module`.
    #[must_use]
    pub const fn plug(self) -> Ref {
        self.plug
    }

    /// Returns `context -> module -> bool`.
    #[must_use]
    pub const fn admissible(self) -> Ref {
        self.admissible
    }

    /// Selects one behavior observation for this reusable context schema.
    ///
    /// # Errors
    ///
    /// Returns an error if the observation uses different run types, the
    /// profile is incompatible, or checked predicate construction fails.
    /// `kernel` is unchanged on failure.
    pub fn observe(
        self,
        kernel: &mut Kernel,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        profile: Ref,
    ) -> Result<ContextualObservation, KernelError> {
        self.observe_avoiding(kernel, observation, quantifier, profile, &[])
    }

    fn observe_avoiding(
        self,
        kernel: &mut Kernel,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        avoiding: &[Ref],
    ) -> Result<ContextualObservation, KernelError> {
        let mut staged = kernel.fork();
        self.require_domain(observation.domain)?;
        let observe = observation.predicate_avoiding(&mut staged, quantifier, profile, avoiding)?;
        let contextual = ContextualObservation {
            subject_ty: self.types.module,
            context_ty: self.context_ty,
            observed_ty: self.types.module,
            bool_ty: self.types.bool_ty,
            plug: self.plug,
            admissible: self.admissible,
            observe,
        }
        .checked(&mut staged)?;
        *kernel = staged;
        Ok(contextual)
    }

    /// Constructs contextual equality of complete allowed run graphs.
    ///
    /// The proposition quantifies over every context, requires both subjects
    /// to agree on context admissibility, and requires `same_runs` whenever
    /// that context admits both subjects. It is independent of any selected
    /// trace or outcome observation.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible modules/profile/domain or a rejected
    /// checked HOL construction. `kernel` is unchanged on failure.
    pub fn equivalent_runs(
        self,
        kernel: &mut Kernel,
        domain: RunDomain,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        self.require_domain(domain)?;
        require_classifier(&mut staged, profile, self.types.profile)?;
        require_classifier(&mut staged, left, self.types.module)?;
        require_classifier(&mut staged, right, self.types.module)?;
        let context = staged.tm_fv(
            staged.fresh_name(&[
                self.context_ty,
                self.plug,
                self.admissible,
                profile,
                left,
                right,
            ])?,
            self.context_ty,
        )?;
        let at_context = self.same_runs_at(&mut staged, domain, profile, context, left, right)?;
        let proposition = staged.forall_tm(self.types.bool_ty, context, at_context)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Proves that contextual run equivalence preserves one observation.
    ///
    /// The result is the ordinary [`ContextualObservation::equivalent`]
    /// proposition for the selected behavior quantifier. Thus complete run
    /// equivalence is observation-independent, while callers can recover
    /// indistinguishability for `callsAssert`, traps, returns, or any composed
    /// trace/outcome predicate without another semantic assumption.
    ///
    /// # Errors
    ///
    /// Returns an error unless `equivalence` positively proves this schema's
    /// contextual run equivalence, or a checked specialization, propositional,
    /// congruence, or alignment step fails. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn prove_equivalent_runs_preserves(
        self,
        kernel: &mut Kernel,
        equivalence: Evidence,
        domain: RunDomain,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.require_domain(domain)?;
        self.require_domain(observation.domain)?;
        if domain != observation.domain {
            return Err(KernelError::InvalidTheoremRule {
                rule: "contextual run preservation domain mismatch",
            }
            .into());
        }
        let expected = self.equivalent_runs(&mut staged, domain, profile, left, right)?;
        let theorem = align_evidence(&mut staged, equivalence, expected)?;
        let contextual = self.observe_avoiding(
            &mut staged,
            observation,
            quantifier,
            profile,
            &[left, right],
        )?;
        let context_name = staged.fresh_name(&[
            expected,
            self.context_ty,
            self.plug,
            self.admissible,
            contextual.observe,
            profile,
            left,
            right,
        ])?;
        let context = staged.tm_fv(context_name, self.context_ty)?;
        let specialized = forall_elim(&mut staged, theorem, context)?;
        let source_at = self.same_runs_at(&mut staged, domain, profile, context, left, right)?;
        join_alpha_equivalent(&mut staged, specialized.proposition, source_at).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "contextual run equivalence specialization alignment",
            }
        })?;
        staged.convert_conclusions(specialized.theorem, specialized.proposition, source_at)?;
        let source_admissibility =
            staged.expand_conclusion(specialized.theorem, positive(source_at), Some(false))?;
        let source_preservation =
            staged.expand_conclusion(specialized.theorem, positive(source_at), Some(true))?;
        let [source_admissibility_formula, source_implication] =
            binary_children(&staged, source_at)?;
        let [source_both_admissible, source_same_runs] =
            binary_children(&staged, source_implication)?;

        let target_at = contextual.at_context(&mut staged, context, left, right)?;
        let [target_admissibility, target_implication] = binary_children(&staged, target_at)?;
        let [target_both_admissible, target_observation] =
            binary_children(&staged, target_implication)?;
        align_theorem_conclusion(
            &mut staged,
            source_admissibility,
            source_admissibility_formula,
            target_admissibility,
            "contextual admissibility preservation alignment",
        )?;

        let assumed_admissible = staged.identity(positive(target_both_admissible))?;
        join_same_syntax(&mut staged, target_both_admissible, source_both_admissible).map_err(
            |_| KernelError::InvalidTheoremRule {
                rule: "contextual run preservation antecedent alignment",
            },
        )?;
        staged.convert_conclusions(
            assumed_admissible,
            target_both_admissible,
            source_both_admissible,
        )?;
        let expanded_implication =
            staged.expand_conclusion(source_preservation, positive(source_implication), None)?;
        let same_runs_theorem = staged.resolve(
            expanded_implication,
            assumed_admissible,
            positive(source_both_admissible).negated(),
        )?;
        let left_closed = apply(&mut staged, self.plug, &[context, left])?;
        let right_closed = apply(&mut staged, self.plug, &[context, right])?;
        let observed = observation.prove_same_runs_preserves(
            &mut staged,
            Evidence {
                proposition: source_same_runs,
                theorem: same_runs_theorem,
                holds: true,
            },
            quantifier,
            profile,
            left_closed,
            right_closed,
        )?;
        let target_observation_operands = staged
            .arena()
            .children(target_observation)
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "contextual observation equality",
            })?
            .collect::<Vec<_>>();
        let [_, left_application, right_application] = target_observation_operands.as_slice()
        else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "contextual observation equality operands",
            }
            .into());
        };
        let (left_beta, left_beta_fact) = certify_beta_application(&mut staged, *left_application)?;
        let (right_beta, right_beta_fact) =
            certify_beta_application(&mut staged, *right_application)?;
        let observed_operands = staged
            .arena()
            .children(observed.proposition)
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "preserved observation equality",
            })?
            .collect::<Vec<_>>();
        let [_, observed_left, observed_right] = observed_operands.as_slice() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "preserved observation equality operands",
            }
            .into());
        };
        let left_alpha =
            join_alpha_equivalent(&mut staged, left_beta, *observed_left).map_err(|_| {
                KernelError::InvalidTheoremRule {
                    rule: "left contextual observation beta alignment",
                }
            })?;
        let right_alpha =
            join_alpha_equivalent(&mut staged, right_beta, *observed_right).map_err(|_| {
                KernelError::InvalidTheoremRule {
                    rule: "right contextual observation beta alignment",
                }
            })?;
        let observed_to_left_beta = staged.syn_symm(None, left_alpha)?;
        let left_beta_to_application = staged.syn_symm(None, left_beta_fact)?;
        let left_conversion =
            staged.syn_trans(None, observed_to_left_beta, left_beta_to_application)?;
        let observed_to_right_beta = staged.syn_symm(None, right_alpha)?;
        let right_beta_to_application = staged.syn_symm(None, right_beta_fact)?;
        let right_conversion =
            staged.syn_trans(None, observed_to_right_beta, right_beta_to_application)?;
        let observed_classifier = observed_operands[0];
        let target_classifier = target_observation_operands[0];
        let classifier_conversion =
            join_alpha_equivalent(&mut staged, observed_classifier, target_classifier).map_err(
                |_| KernelError::InvalidTheoremRule {
                    rule: "contextual observation equality classifier alignment",
                },
            )?;
        let equality_conversion = staged.syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            observed.proposition,
            target_observation,
            &[classifier_conversion, left_conversion, right_conversion],
        )?;
        staged.union_syn_fact(equality_conversion)?;
        staged.convert_conclusions(observed.theorem, observed.proposition, target_observation)?;
        let target_preservation =
            staged.imp_right(observed.theorem, positive(target_implication))?;
        let at_context = staged.and_right(
            source_admissibility,
            target_preservation,
            positive(target_at),
        )?;
        staged.contract_theorem(at_context)?;
        let universal = staged.forall_tm(self.types.bool_ty, context, target_at)?;
        let theorem = staged.forall_intro_at(at_context, context, universal)?;
        let target = contextual.equivalent(&mut staged, left, right)?;
        align_theorem_conclusion(
            &mut staged,
            theorem,
            universal,
            target,
            "contextual observation equivalence alignment",
        )?;
        *kernel = staged;
        Ok(Evidence {
            proposition: target,
            theorem,
            holds: true,
        })
    }

    fn same_runs_at(
        self,
        kernel: &mut Kernel,
        domain: RunDomain,
        profile: Ref,
        context: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        self.require_domain(domain)?;
        require_classifier(kernel, context, self.context_ty)?;
        let left_admissible = apply(kernel, self.admissible, &[context, left])?;
        let right_admissible = apply(kernel, self.admissible, &[context, right])?;
        let same_admissibility =
            kernel.eq(self.types.bool_ty, left_admissible, right_admissible)?;
        let both_admissible = kernel.op2(Op2::And, left_admissible, right_admissible)?;
        let left_closed = apply(kernel, self.plug, &[context, left])?;
        let right_closed = apply(kernel, self.plug, &[context, right])?;
        let same_runs = domain.same_runs(kernel, profile, left_closed, right_closed)?;
        let preservation = kernel.op2(Op2::Imp, both_admissible, same_runs)?;
        kernel.op2(Op2::And, same_admissibility, preservation)
    }

    fn require_domain(self, domain: RunDomain) -> Result<(), KernelError> {
        if domain.relation.types == self.types {
            Ok(())
        } else {
            Err(KernelError::InvalidTheoremRule {
                rule: "run context/domain type mismatch",
            })
        }
    }
}

/// Failure to derive a checked law about run relations.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RunProofError {
    /// A checked kernel operation rejected the derivation.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// A derived equality rule rejected one component.
    #[snafu(transparent)]
    Equality {
        /// Underlying derived equality failure.
        source: EqualityError,
    },
    /// Universal specialization rejected the contextual evidence.
    #[snafu(transparent)]
    Forall {
        /// Underlying derived universal-elimination failure.
        source: ForallError,
    },
    /// Capture-avoiding beta substitution failed.
    #[snafu(transparent)]
    Model {
        /// Underlying derived substitution failure.
        source: ModelError,
    },
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
        let mut staged = kernel.fork();
        let left = self.run_graphs(&mut staged, profile, left)?;
        let right = self.run_graphs(&mut staged, profile, right)?;
        let left_domain_ty = staged.classifier(left.domain)?;
        let right_domain_ty = staged.classifier(right.domain)?;
        join_same_syntax(&mut staged, left_domain_ty, right_domain_ty).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "same-runs domain classifier",
            }
        })?;
        let left_runs_ty = staged.classifier(left.runs)?;
        let right_runs_ty = staged.classifier(right.runs)?;
        join_same_syntax(&mut staged, left_runs_ty, right_runs_ty).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "same-runs graph classifier",
            }
        })?;
        let same_domain = staged.eq(self.relation.types.bool_ty, left.domain, right.domain)?;
        let same_behavior = staged.eq(self.relation.types.bool_ty, left.runs, right.runs)?;
        let same = staged.op2(Op2::And, same_domain, same_behavior)?;
        *kernel = staged;
        Ok(same)
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
        self.refinement(kernel, profile, implementation, specification)
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
        let mut staged = kernel.fork();
        let graph = self.run_graphs(&mut staged, profile, module)?;
        let same_domain = staged.eq(self.relation.types.bool_ty, graph.domain, graph.domain)?;
        let domain_reflexive = staged.refl(self.relation.types.bool_ty, graph.domain)?;
        join_same_syntax(&mut staged, domain_reflexive.equality, same_domain).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "run-domain function reflexivity alignment",
            }
        })?;
        staged.convert_conclusions(
            domain_reflexive.theorem,
            domain_reflexive.equality,
            same_domain,
        )?;
        let same_behavior = staged.eq(self.relation.types.bool_ty, graph.runs, graph.runs)?;
        let behavior_reflexive = staged.refl(self.relation.types.bool_ty, graph.runs)?;
        join_same_syntax(&mut staged, behavior_reflexive.equality, same_behavior).map_err(
            |_| KernelError::InvalidTheoremRule {
                rule: "run-graph function reflexivity alignment",
            },
        )?;
        staged.convert_conclusions(
            behavior_reflexive.theorem,
            behavior_reflexive.equality,
            same_behavior,
        )?;
        let proposition = staged.op2(Op2::And, same_domain, same_behavior)?;
        let theorem = staged.and_right(
            domain_reflexive.theorem,
            behavior_reflexive.theorem,
            positive(proposition),
        )?;
        let canonical = self.same_runs(&mut staged, profile, module, module)?;
        join_same_syntax(&mut staged, proposition, canonical).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "same-runs reflexivity alignment",
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

    /// Reverses checked evidence that two modules have the same runs.
    ///
    /// Every premise of `evidence` remains visible. The derivation reverses
    /// the admissibility-function and allowed-run-function equalities with the
    /// standard checked equality rule.
    ///
    /// # Errors
    ///
    /// Returns an error unless `evidence` proves `same_runs(left, right)`, or a
    /// checked equality, conjunction, alignment, or theorem operation fails.
    /// `kernel` is unchanged on failure.
    pub fn prove_same_runs_symmetric(
        self,
        kernel: &mut Kernel,
        evidence: Evidence,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let forward = self.same_runs(&mut staged, profile, left, right)?;
        let forward_theorem = align_evidence(&mut staged, evidence, forward)?;
        let domain_fact =
            staged.expand_conclusion(forward_theorem, positive(forward), Some(false))?;
        let runs_fact = staged.expand_conclusion(forward_theorem, positive(forward), Some(true))?;
        let flipped_domain =
            equality_symmetry(&mut staged, self.relation.types.bool_ty, domain_fact)?;
        let flipped_runs = equality_symmetry(&mut staged, self.relation.types.bool_ty, runs_fact)?;
        let reverse = self.same_runs(&mut staged, profile, right, left)?;
        let [reverse_domain, reverse_runs] = binary_children(&staged, reverse)?;
        align_theorem_conclusion(
            &mut staged,
            flipped_domain.theorem,
            flipped_domain.equality,
            reverse_domain,
            "same-runs symmetric domain alignment",
        )?;
        align_theorem_conclusion(
            &mut staged,
            flipped_runs.theorem,
            flipped_runs.equality,
            reverse_runs,
            "same-runs symmetric behavior alignment",
        )?;
        let theorem = staged.and_right(
            flipped_domain.theorem,
            flipped_runs.theorem,
            positive(reverse),
        )?;
        staged.contract_theorem(theorem)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: reverse,
            theorem,
            holds: true,
        })
    }

    /// Composes two checked same-runs facts.
    ///
    /// The result proves `same_runs(left, right)` from facts for
    /// `same_runs(left, middle)` and `same_runs(middle, right)`, preserving all
    /// premises of both inputs.
    ///
    /// # Errors
    ///
    /// Returns an error unless both evidence values have the displayed positive
    /// conclusions, or a checked equality, conjunction, alignment, or theorem
    /// operation fails. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_same_runs_transitive(
        self,
        kernel: &mut Kernel,
        left_middle: Evidence,
        middle_right: Evidence,
        profile: Ref,
        left: Ref,
        middle: Ref,
        right: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let expected_left_middle = self.same_runs(&mut staged, profile, left, middle)?;
        let left_middle = align_evidence(&mut staged, left_middle, expected_left_middle)?;
        let expected_middle_right = self.same_runs(&mut staged, profile, middle, right)?;
        let middle_right = align_evidence(&mut staged, middle_right, expected_middle_right)?;
        let left_domain_fact =
            staged.expand_conclusion(left_middle, positive(expected_left_middle), Some(false))?;
        let left_runs_fact =
            staged.expand_conclusion(left_middle, positive(expected_left_middle), Some(true))?;
        let right_domain_fact =
            staged.expand_conclusion(middle_right, positive(expected_middle_right), Some(false))?;
        let right_runs_fact =
            staged.expand_conclusion(middle_right, positive(expected_middle_right), Some(true))?;
        let domain = equality_transitivity(
            &mut staged,
            self.relation.types.bool_ty,
            left_domain_fact,
            right_domain_fact,
        )?;
        let runs = equality_transitivity(
            &mut staged,
            self.relation.types.bool_ty,
            left_runs_fact,
            right_runs_fact,
        )?;
        let target = self.same_runs(&mut staged, profile, left, right)?;
        let [target_domain, target_runs] = binary_children(&staged, target)?;
        align_theorem_conclusion(
            &mut staged,
            domain.theorem,
            domain.equality,
            target_domain,
            "same-runs transitive domain alignment",
        )?;
        align_theorem_conclusion(
            &mut staged,
            runs.theorem,
            runs.equality,
            target_runs,
            "same-runs transitive behavior alignment",
        )?;
        let theorem = staged.and_right(domain.theorem, runs.theorem, positive(target))?;
        staged.contract_theorem(theorem)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: target,
            theorem,
            holds: true,
        })
    }

    fn run_graphs(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
    ) -> Result<RunGraphs, KernelError> {
        let types = self.relation.types;
        require_classifier(kernel, profile, types.profile)?;
        require_classifier(kernel, module, types.module)?;
        let first = kernel.fresh_name(&[
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
        let entry = kernel.tm_fv(first, types.entry)?;
        let inputs = kernel.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = kernel.tm_fv(checked_name(first, 2)?, types.host)?;
        let trace = kernel.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = kernel.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let allowed = apply(
            kernel,
            self.admissible,
            &[profile, module, entry, inputs, host],
        )?;
        let domain =
            abstract_variables_at(kernel, &[entry, inputs, host], allowed, self.domain_ty)?;
        let run = apply(
            kernel,
            self.relation.runs,
            &[profile, module, entry, inputs, host, trace, outcome],
        )?;
        let eligible = kernel.op2(Op2::And, allowed, run)?;
        let runs = abstract_variables_at(
            kernel,
            &[entry, inputs, host, trace, outcome],
            eligible,
            self.run_graph_ty,
        )?;
        Ok(RunGraphs { domain, runs })
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
        self.prove_refinement_reflexive(kernel, profile, module)
    }

    #[allow(clippy::too_many_lines)]
    fn prove_refinement_reflexive(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
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
        let behavior = staged.op2(Op2::Imp, run, run)?;
        let identity = staged.identity(positive(run))?;
        let behavior_theorem = staged.imp_right(identity, positive(behavior))?;
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
        let behavior_theorem =
            staged.and_right(behavior_theorem, progress_theorem, positive(combined))?;
        let behavior = combined;
        let proposition = staged.op2(Op2::And, same_domain, behavior)?;
        let theorem =
            staged.and_right(same_domain_theorem, behavior_theorem, positive(proposition))?;
        let canonical = self.refinement(&mut staged, profile, module, module)?;
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

    fn refinement(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        left: Ref,
        right: Ref,
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
        let behavior = staged.op2(Op2::Imp, left_run, right_run)?;
        let behavior = staged.op2(Op2::Imp, both_allowed, behavior)?;
        let behavior = quantify_forall(&mut staged, types.bool_ty, &run_variables, behavior)?;
        let implementation_runs =
            quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], left_run)?;
        let specification_runs =
            quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], right_run)?;
        let progress = staged.op2(Op2::Imp, specification_runs, implementation_runs)?;
        let progress = staged.op2(Op2::Imp, both_allowed, progress)?;
        let progress = quantify_forall(&mut staged, types.bool_ty, &domain_variables, progress)?;
        let behavior = staged.op2(Op2::And, behavior, progress)?;
        let proposition = staged.op2(Op2::And, same_domain, behavior)?;
        *kernel = staged;
        Ok(proposition)
    }
}

#[derive(Clone, Copy)]
struct RunGraphs {
    domain: Ref,
    runs: Ref,
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
    /// `Never` is defined by literal HOL negation of `May` inside the shared
    /// characteristic-function observer, rather than by frontend policy.
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
        self.proposition_avoiding(kernel, quantifier, profile, module, &[])
    }

    fn proposition_avoiding(
        self,
        kernel: &mut Kernel,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        module: Ref,
        avoiding: &[Ref],
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        require_classifier(&mut staged, module, types.module)?;
        let graphs = self.domain.run_graphs(&mut staged, profile, module)?;
        let observer = self.graph_observer(&mut staged, quantifier, avoiding)?;
        let proposition = apply(&mut staged, observer, &[graphs.domain, graphs.runs])?;
        *kernel = staged;
        Ok(proposition)
    }

    fn graph_observer(
        self,
        kernel: &mut Kernel,
        quantifier: BehaviorQuantifier,
        avoiding: &[Ref],
    ) -> Result<Ref, KernelError> {
        let mut roots = vec![
            self.domain.domain_ty,
            self.domain.run_graph_ty,
            self.domain.relation.types.bool_ty,
            self.observe,
        ];
        roots.extend_from_slice(avoiding);
        let name = kernel.fresh_name(&roots)?;
        let domain = kernel.tm_fv(name, self.domain.domain_ty)?;
        let runs = kernel.tm_fv(checked_name(name, 1)?, self.domain.run_graph_ty)?;
        let body = self.graph_proposition(kernel, quantifier, domain, runs, avoiding)?;
        let by_runs_ty =
            kernel.ty_arr(self.domain.run_graph_ty, self.domain.relation.types.bool_ty)?;
        let by_runs = kernel.lam_at(by_runs_ty, runs, body)?;
        let observer_ty = kernel.ty_arr(self.domain.domain_ty, by_runs_ty)?;
        kernel.lam_at(observer_ty, domain, by_runs)
    }

    fn graph_proposition(
        self,
        kernel: &mut Kernel,
        quantifier: BehaviorQuantifier,
        domain: Ref,
        runs: Ref,
        avoiding: &[Ref],
    ) -> Result<Ref, KernelError> {
        let types = self.domain.relation.types;
        require_classifier(kernel, domain, self.domain.domain_ty)?;
        require_classifier(kernel, runs, self.domain.run_graph_ty)?;
        let mut roots = vec![
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
            types.bool_ty,
            domain,
            runs,
            self.observe,
        ];
        roots.extend_from_slice(avoiding);
        let first = kernel.fresh_name(&roots)?;
        let entry = kernel.tm_fv(first, types.entry)?;
        let inputs = kernel.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = kernel.tm_fv(checked_name(first, 2)?, types.host)?;
        let trace = kernel.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = kernel.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let invocation_variables = [entry, inputs, host];
        let result_variables = [trace, outcome];
        let run_variables = [entry, inputs, host, trace, outcome];
        let allowed = apply(kernel, domain, &[entry, inputs, host])?;
        let runs = apply(kernel, runs, &[entry, inputs, host, trace, outcome])?;
        let observed = apply(kernel, self.observe, &[trace, outcome])?;
        let proposition = match quantifier {
            BehaviorQuantifier::May | BehaviorQuantifier::Never => {
                let witnessed = kernel.op2(Op2::And, runs, observed)?;
                let may = quantify_exists(kernel, types.bool_ty, &run_variables, witnessed)?;
                if quantifier == BehaviorQuantifier::May {
                    may
                } else {
                    kernel.op1(Op1::Not, may)?
                }
            }
            BehaviorQuantifier::Every => {
                let required = kernel.op2(Op2::Imp, runs, observed)?;
                quantify_forall(kernel, types.bool_ty, &run_variables, required)?
            }
            BehaviorQuantifier::Must => {
                let matching = kernel.op2(Op2::And, runs, observed)?;
                let exists_matching =
                    quantify_exists(kernel, types.bool_ty, &result_variables, matching)?;
                let run_implies_observed = kernel.op2(Op2::Imp, runs, observed)?;
                let every_run = quantify_forall(
                    kernel,
                    types.bool_ty,
                    &result_variables,
                    run_implies_observed,
                )?;
                let required = kernel.op2(Op2::And, exists_matching, every_run)?;
                let required_when_allowed = kernel.op2(Op2::Imp, allowed, required)?;
                quantify_forall(
                    kernel,
                    types.bool_ty,
                    &invocation_variables,
                    required_when_allowed,
                )?
            }
        };
        Ok(proposition)
    }

    /// Proves that identical allowed run graphs have identical observations.
    ///
    /// This is the generic soundness bridge from closed run equality to any
    /// `may`, `every`, `must`, or `never` trace/outcome observation. Every
    /// premise in `same_runs` evidence remains visible in the result.
    ///
    /// # Errors
    ///
    /// Returns an error unless `same_runs` positively proves equality for the
    /// supplied modules, or a checked equality/congruence operation fails.
    /// `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_same_runs_preserves(
        self,
        kernel: &mut Kernel,
        same_runs: Evidence,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let expected = self.domain.same_runs(&mut staged, profile, left, right)?;
        let theorem = align_evidence(&mut staged, same_runs, expected)?;
        let domain_fact = staged.expand_conclusion(theorem, positive(expected), Some(false))?;
        let runs_fact = staged.expand_conclusion(theorem, positive(expected), Some(true))?;
        let left_graphs = self.domain.run_graphs(&mut staged, profile, left)?;
        let right_graphs = self.domain.run_graphs(&mut staged, profile, right)?;

        let observer = self.graph_observer(&mut staged, quantifier, &[])?;
        let by_domain_function = staged.ap_term(domain_fact, observer)?;
        let by_domain = staged.ap_thm(by_domain_function.theorem, left_graphs.runs)?;
        let right_domain_observer = staged.app(observer, right_graphs.domain)?;
        let by_runs = staged.ap_term(runs_fact, right_domain_observer)?;
        let preserved = equality_transitivity(
            &mut staged,
            self.domain.relation.types.bool_ty,
            by_domain.theorem,
            by_runs.theorem,
        )?;
        let left_observation = self.proposition(&mut staged, quantifier, profile, left)?;
        let right_observation = self.proposition(&mut staged, quantifier, profile, right)?;
        let target = staged.eq(
            self.domain.relation.types.bool_ty,
            left_observation,
            right_observation,
        )?;
        align_theorem_conclusion(
            &mut staged,
            preserved.theorem,
            preserved.equality,
            target,
            "same-runs observation preservation alignment",
        )?;
        staged.contract_theorem(preserved.theorem)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: target,
            theorem: preserved.theorem,
            holds: true,
        })
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
        self.predicate_avoiding(kernel, quantifier, profile, &[])
    }

    fn predicate_avoiding(
        self,
        kernel: &mut Kernel,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        avoiding: &[Ref],
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        let mut roots = vec![
            types.module,
            types.bool_ty,
            self.domain.relation.runs,
            self.domain.admissible,
            self.observe,
            profile,
        ];
        roots.extend_from_slice(avoiding);
        let name = staged.fresh_name(&roots)?;
        let module = staged.tm_fv(name, types.module)?;
        let mut body_avoiding = Vec::with_capacity(avoiding.len() + 1);
        body_avoiding.push(module);
        body_avoiding.extend_from_slice(avoiding);
        let body =
            self.proposition_avoiding(&mut staged, quantifier, profile, module, &body_avoiding)?;
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
        let context = RunContext::new(&mut staged, types, context_ty, plug, admissible)?;
        let contextual = context.observe(&mut staged, self, quantifier, profile)?;
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

fn abstract_variables_at(
    kernel: &mut Kernel,
    variables: &[Ref],
    body: Ref,
    classifier: Ref,
) -> Result<Ref, KernelError> {
    let mut function_types = Vec::with_capacity(variables.len());
    let mut suffix = classifier;
    for _ in variables {
        function_types.push(suffix);
        suffix = binary_children(kernel, suffix)?[1];
    }
    variables
        .iter()
        .zip(function_types)
        .rev()
        .try_fold(body, |body, (&variable, function_ty)| {
            kernel.lam_at(function_ty, variable, body)
        })
}

fn binary_children(kernel: &Kernel, proposition: Ref) -> Result<[Ref; 2], KernelError> {
    kernel
        .arena()
        .children(proposition)
        .ok_or(KernelError::InvalidTheoremRule {
            rule: "run binary proposition",
        })?
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "run binary proposition operands",
        })
}

fn align_evidence(
    kernel: &mut Kernel,
    evidence: Evidence,
    target: Ref,
) -> Result<covalence_logic_hol::ThmId, KernelError> {
    if !evidence.holds {
        return Err(KernelError::InvalidTheoremRule {
            rule: "positive run evidence",
        });
    }
    let expected = positive(evidence.proposition);
    let exact_conclusion = {
        let theorem = kernel
            .thm()
            .get(evidence.theorem)
            .ok_or(KernelError::MissingTheorem {
                id: evidence.theorem,
            })?;
        let mut conclusions = theorem.rhs.rows();
        conclusions.next().is_some_and(|row| row == [expected]) && conclusions.next().is_none()
    };
    if !exact_conclusion {
        return Err(KernelError::InvalidTheoremRule {
            rule: "run evidence conclusion",
        });
    }
    join_same_syntax(kernel, evidence.proposition, target).map_err(|_| {
        KernelError::InvalidTheoremRule {
            rule: "run evidence proposition alignment",
        }
    })?;
    let aligned = kernel.copy_theorem(evidence.theorem)?;
    kernel.convert_conclusions(aligned, evidence.proposition, target)?;
    Ok(aligned)
}

fn align_theorem_conclusion(
    kernel: &mut Kernel,
    theorem: covalence_logic_hol::ThmId,
    source: Ref,
    target: Ref,
    rule: &'static str,
) -> Result<(), KernelError> {
    join_alpha_equivalent(kernel, source, target)
        .map_err(|_| KernelError::InvalidTheoremRule { rule })?;
    kernel.convert_conclusions(theorem, source, target)
}

fn certify_beta_application(
    kernel: &mut Kernel,
    application: Ref,
) -> Result<(Ref, covalence_logic_hol::SynFactId), RunProofError> {
    let application_children = kernel
        .arena()
        .children(application)
        .ok_or(KernelError::InvalidTheoremRule {
            rule: "run observation beta application",
        })?
        .collect::<Vec<_>>();
    let [function, argument] = application_children.as_slice() else {
        return Err(KernelError::InvalidTheoremRule {
            rule: "run observation beta application operands",
        }
        .into());
    };
    let function_children = kernel
        .arena()
        .children(*function)
        .ok_or(KernelError::InvalidTheoremRule {
            rule: "run observation beta function",
        })?
        .collect::<Vec<_>>();
    let [binder, body] = function_children.as_slice() else {
        return Err(KernelError::InvalidTheoremRule {
            rule: "run observation beta function operands",
        }
        .into());
    };
    let substitution = substitute(kernel, *binder, *argument, *body)?;
    let fact = kernel.tm_beta_fact(None, application, substitution.fact)?;
    kernel.union_syn_fact(fact)?;
    Ok((substitution.output, fact))
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
    use super::{BehaviorQuantifier, RunContext, RunRelation, RunTypes};
    use crate::{Evidence, EvidenceScope};
    use covalence_logic_hol::Kernel;

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
        let third_module = kernel.tm_fv(32, types.module).unwrap();
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
        let left_middle = domain
            .same_runs(&mut kernel, profile, module, other_module)
            .unwrap();
        let left_middle_evidence = Evidence {
            proposition: left_middle,
            theorem: kernel.identity(super::positive(left_middle)).unwrap(),
            holds: true,
        };
        let symmetric = domain
            .prove_same_runs_symmetric(
                &mut kernel,
                left_middle_evidence,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle])
            .check(&kernel, symmetric)
            .unwrap();
        for quantifier in [
            BehaviorQuantifier::May,
            BehaviorQuantifier::Every,
            BehaviorQuantifier::Must,
            BehaviorQuantifier::Never,
        ] {
            let preserved = observation
                .prove_same_runs_preserves(
                    &mut kernel,
                    left_middle_evidence,
                    quantifier,
                    profile,
                    module,
                    other_module,
                )
                .unwrap();
            EvidenceScope::positive(&[left_middle])
                .check(&kernel, preserved)
                .unwrap();
            assert_eq!(kernel.classifier(preserved.proposition).unwrap(), bool_ty);
        }
        let middle_right = domain
            .same_runs(&mut kernel, profile, other_module, third_module)
            .unwrap();
        let middle_right_evidence = Evidence {
            proposition: middle_right,
            theorem: kernel.identity(super::positive(middle_right)).unwrap(),
            holds: true,
        };
        let transitive = domain
            .prove_same_runs_transitive(
                &mut kernel,
                left_middle_evidence,
                middle_right_evidence,
                profile,
                module,
                other_module,
                third_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle, middle_right])
            .check(&kernel, transitive)
            .unwrap();
        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            domain
                .prove_same_runs_symmetric(
                    &mut kernel,
                    equivalence_reflexive,
                    profile,
                    module,
                    other_module,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
        let denied_same_runs = Evidence {
            proposition: left_middle,
            theorem: kernel
                .identity(super::positive(left_middle).negated())
                .unwrap(),
            holds: false,
        };
        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            observation
                .prove_same_runs_preserves(
                    &mut kernel,
                    denied_same_runs,
                    BehaviorQuantifier::May,
                    profile,
                    module,
                    other_module,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
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
        let context =
            RunContext::new(&mut kernel, types, context_ty, plug, contextual_admissible).unwrap();
        assert_eq!(context.context_type(), context_ty);
        assert_eq!(context.plug(), plug);
        assert_eq!(context.admissible(), contextual_admissible);
        let contextual_from_schema = context
            .observe(&mut kernel, observation, BehaviorQuantifier::May, profile)
            .unwrap();
        assert_eq!(contextual_from_schema.plug, contextual.plug);
        assert_eq!(contextual_from_schema.admissible, contextual.admissible);
        covalence_logic_hol_derived::join_same_syntax(
            &mut kernel,
            contextual_from_schema.observe,
            contextual.observe,
        )
        .unwrap();
        let contextual_same_runs = context
            .equivalent_runs(&mut kernel, domain, profile, module, other_module)
            .unwrap();
        assert_eq!(kernel.classifier(contextual_same_runs).unwrap(), bool_ty);
        let contextual_same_runs_evidence = Evidence {
            proposition: contextual_same_runs,
            theorem: kernel
                .identity(super::positive(contextual_same_runs))
                .unwrap(),
            holds: true,
        };
        for quantifier in [
            BehaviorQuantifier::May,
            BehaviorQuantifier::Every,
            BehaviorQuantifier::Must,
            BehaviorQuantifier::Never,
        ] {
            let contextual_preservation = context
                .prove_equivalent_runs_preserves(
                    &mut kernel,
                    contextual_same_runs_evidence,
                    domain,
                    observation,
                    quantifier,
                    profile,
                    module,
                    other_module,
                )
                .unwrap();
            EvidenceScope::positive(&[contextual_same_runs])
                .check(&kernel, contextual_preservation)
                .unwrap();
        }
        let denied_contextual_runs = Evidence {
            proposition: contextual_same_runs,
            theorem: kernel
                .identity(super::positive(contextual_same_runs).negated())
                .unwrap(),
            holds: false,
        };
        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            context
                .prove_equivalent_runs_preserves(
                    &mut kernel,
                    denied_contextual_runs,
                    domain,
                    observation,
                    BehaviorQuantifier::May,
                    profile,
                    module,
                    other_module,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
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
