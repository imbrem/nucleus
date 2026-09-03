//! Generic, immutable propositions over one eventful program-execution relation.
//!
//! This module is syntax and checked composition only. It does not execute a
//! program or create theorem facts. A caller supplies the versioned execution
//! relation, the allowed invocation/host policy, and the observation over a
//! trace and outcome.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, SynRel, Tag, TmTag,
    builtin::{Op1, Op2},
};
use covalence_logic_hol_derived::{
    EqualityError, ExistsError, ForallError, ModelError, equality_symmetry, equality_transitivity,
    forall_elim, introduce_exists, join_alpha_equivalent, join_same_syntax, open_exists,
    substitute,
};

use crate::{ContextualObservation, Evidence, ObservationProofError};

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
    domain: RunDomain,
    context_ty: Ref,
    plug: Ref,
    admissible: Ref,
}

/// A reusable identity linking context for closed-program observations.
///
/// Plugging ignores the context token and returns the module unchanged; every
/// module is admissible. Both facts are definitions with checked beta proofs,
/// not semantic assumptions.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClosedRunContext {
    context: RunContext,
    identity_context: Ref,
}

/// An immutable module transformation interpreted under one semantic profile.
///
/// Soundness means that every input module is contextually observationally
/// equivalent to the transformed module. The transformation is a checked HOL
/// function; packaging it creates no theorem fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunTransformation {
    context: RunContext,
    profile: Ref,
    transform: Ref,
}

/// A module transformation paired with checked evidence for its exact
/// contextual-observational soundness proposition.
///
/// This wrapper adds no trust: construction rechecks an existing kernel
/// theorem and retains all of that theorem's premises.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SoundRunTransformation {
    transformation: RunTransformation,
    soundness: Evidence,
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
        domain: RunDomain,
        context_ty: Ref,
        plug: Ref,
        admissible: Ref,
    ) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let types = domain.relation.types;
        let plug_ty = curried_type(&mut staged, &[context_ty, types.module], types.module)?;
        require_classifier(&mut staged, plug, plug_ty)?;
        let admissible_ty = curried_type(&mut staged, &[context_ty, types.module], types.bool_ty)?;
        require_classifier(&mut staged, admissible, admissible_ty)?;
        *kernel = staged;
        Ok(Self {
            domain,
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

    /// Returns the execution domain closed by this context schema.
    #[must_use]
    pub const fn domain(self) -> RunDomain {
        self.domain
    }

    /// Validates and packages a module transformation for one profile.
    ///
    /// # Errors
    ///
    /// Returns an error unless `profile` has this run relation's profile
    /// classifier and `transform` has classifier `module -> module`. `kernel`
    /// is unchanged on failure.
    pub fn transformation(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        transform: Ref,
    ) -> Result<RunTransformation, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        let transform_ty = staged.ty_arr(types.module, types.module)?;
        require_classifier(&mut staged, transform, transform_ty)?;
        *kernel = staged;
        Ok(RunTransformation {
            context: self,
            profile,
            transform,
        })
    }

    /// Constructs the identity module transformation for one semantic profile.
    ///
    /// # Errors
    ///
    /// Returns an error for an incompatible profile or if checked abstraction
    /// fails. `kernel` is unchanged on failure.
    pub fn identity_transformation(
        self,
        kernel: &mut Kernel,
        profile: Ref,
    ) -> Result<RunTransformation, KernelError> {
        let mut staged = kernel.fork();
        let module_ty = self.domain.relation.types.module;
        let module = staged.tm_fv(
            staged.fresh_name(&[
                self.context_ty,
                self.plug,
                self.admissible,
                profile,
                module_ty,
            ])?,
            module_ty,
        )?;
        let transform_ty = staged.ty_arr(module_ty, module_ty)?;
        let transform = staged.lam_at(transform_ty, module, module)?;
        let transformation = self.transformation(&mut staged, profile, transform)?;
        *kernel = staged;
        Ok(transformation)
    }

    /// Derives premise-free soundness of the identity transformation.
    ///
    /// The proof uses only checked contextual-equivalence reflexivity,
    /// universal introduction, and beta conversion.
    ///
    /// # Errors
    ///
    /// Returns an error if identity construction or any checked equivalence,
    /// universal, or alignment step fails. `kernel` is unchanged on failure.
    pub fn prove_identity_transformation_sound(
        self,
        kernel: &mut Kernel,
        profile: Ref,
    ) -> Result<SoundRunTransformation, RunProofError> {
        let mut staged = kernel.fork();
        let transformation = self.identity_transformation(&mut staged, profile)?;
        let types = self.domain.relation.types;
        let module = staged.tm_fv(
            staged.fresh_name(&[
                self.context_ty,
                self.plug,
                self.admissible,
                profile,
                transformation.transform,
                types.module,
                types.bool_ty,
            ])?,
            types.module,
        )?;
        let reflexive = self.prove_reflexive(&mut staged, profile, module)?;
        let direct = staged.forall_tm(types.bool_ty, module, reflexive.proposition)?;
        let theorem = staged.forall_intro_at(reflexive.theorem, module, direct)?;
        let canonical = transformation.sound(&mut staged)?;
        align_theorem_conclusion(
            &mut staged,
            theorem,
            direct,
            canonical,
            "identity transformation soundness alignment",
        )?;
        let sound = transformation.with_soundness(
            &mut staged,
            Evidence {
                proposition: canonical,
                theorem,
                holds: true,
            },
        )?;
        *kernel = staged;
        Ok(sound)
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
        self.require_observation(observation)?;
        let property = observation.property_avoiding(&mut staged, quantifier, avoiding)?;
        let contextual =
            self.observe_property_avoiding(&mut staged, property, profile, avoiding)?;
        *kernel = staged;
        Ok(contextual)
    }

    /// Selects an arbitrary run property for this reusable context schema.
    ///
    /// # Errors
    ///
    /// Returns an error if `property` belongs to another run domain, the
    /// profile is incompatible, or checked predicate construction fails.
    /// `kernel` is unchanged on failure.
    pub fn observe_property(
        self,
        kernel: &mut Kernel,
        property: RunProperty,
        profile: Ref,
    ) -> Result<ContextualObservation, KernelError> {
        self.observe_property_avoiding(kernel, property, profile, &[])
    }

    fn observe_property_avoiding(
        self,
        kernel: &mut Kernel,
        property: RunProperty,
        profile: Ref,
        avoiding: &[Ref],
    ) -> Result<ContextualObservation, KernelError> {
        let mut staged = kernel.fork();
        self.require_property(property)?;
        let observe = property.predicate_avoiding(&mut staged, profile, avoiding)?;
        let contextual = ContextualObservation {
            subject_ty: self.domain.relation.types.module,
            context_ty: self.context_ty,
            observed_ty: self.domain.relation.types.module,
            bool_ty: self.domain.relation.types.bool_ty,
            plug: self.plug,
            admissible: self.admissible,
            observe,
        }
        .checked(&mut staged)?;
        *kernel = staged;
        Ok(contextual)
    }

    /// Constructs contextual observational equivalence.
    ///
    /// The proposition quantifies over every context, requires both subjects
    /// to agree on context admissibility, and requires `same_runs` whenever
    /// that context admits both subjects. It is independent of any selected
    /// trace or outcome observation.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible modules/profile or a rejected
    /// checked HOL construction. `kernel` is unchanged on failure.
    pub fn equivalent(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        require_classifier(&mut staged, left, types.module)?;
        require_classifier(&mut staged, right, types.module)?;
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
        let at_context = self.same_runs_at(&mut staged, profile, context, left, right)?;
        let proposition = staged.forall_tm(types.bool_ty, context, at_context)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Proves contextual run equivalence is reflexive.
    ///
    /// The theorem is premise-free: context admissibility is reflexive, and
    /// every plugged module has the same complete allowed run graph as itself.
    /// No property of the execution relation, linker, or context policy is
    /// assumed.
    ///
    /// # Errors
    ///
    /// Returns an error for an incompatible profile/module or a rejected
    /// checked equality, implication, universal, or alignment step. `kernel`
    /// is unchanged on failure.
    pub fn prove_reflexive(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
    ) -> Result<Evidence, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        require_classifier(&mut staged, module, types.module)?;
        let context_name =
            staged.fresh_name(&[self.context_ty, self.plug, self.admissible, profile, module])?;
        let context = staged.tm_fv(context_name, self.context_ty)?;
        let at_context = self.same_runs_at(&mut staged, profile, context, module, module)?;
        let [same_admissibility, preservation] = binary_children(&staged, at_context)?;
        let [both_admissible, same_runs] = binary_children(&staged, preservation)?;
        let admissibility_operands = staged
            .arena()
            .children(same_admissibility)
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "contextual run reflexivity admissibility equality",
            })?
            .collect::<Vec<_>>();
        let [_, admissible, _] = admissibility_operands.as_slice() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "contextual run reflexivity admissibility equality operands",
            });
        };
        let admissibility_reflexive = staged.refl(types.bool_ty, *admissible)?;
        align_theorem_conclusion(
            &mut staged,
            admissibility_reflexive.theorem,
            admissibility_reflexive.equality,
            same_admissibility,
            "contextual run reflexivity admissibility alignment",
        )?;
        let closed = apply(&mut staged, self.plug, &[context, module])?;
        let run_reflexive = self
            .domain
            .prove_same_runs_reflexive(&mut staged, profile, closed)?;
        align_theorem_conclusion(
            &mut staged,
            run_reflexive.theorem,
            run_reflexive.proposition,
            same_runs,
            "contextual run reflexivity graph alignment",
        )?;
        staged.weaken(run_reflexive.theorem, &[positive(both_admissible)], &[])?;
        let preservation_theorem =
            staged.imp_right(run_reflexive.theorem, positive(preservation))?;
        let body = staged.and_right(
            admissibility_reflexive.theorem,
            preservation_theorem,
            positive(at_context),
        )?;
        let universal = staged.forall_tm(types.bool_ty, context, at_context)?;
        let theorem = staged.forall_intro_at(body, context, universal)?;
        let canonical = self.equivalent(&mut staged, profile, module, module)?;
        align_theorem_conclusion(
            &mut staged,
            theorem,
            universal,
            canonical,
            "contextual run reflexivity alignment",
        )?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem,
            holds: true,
        })
    }

    /// Reverses checked contextual run equivalence evidence.
    ///
    /// All premises remain visible while both context-admissibility equality
    /// and the complete run equality are reversed with checked equality laws.
    ///
    /// # Errors
    ///
    /// Returns an error unless `equivalence` positively proves the displayed
    /// contextual run equivalence, or a checked specialization, equality,
    /// propositional, universal, or alignment step fails. `kernel` is unchanged
    /// on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn prove_symmetric(
        self,
        kernel: &mut Kernel,
        equivalence: Evidence,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let expected = self.equivalent(&mut staged, profile, left, right)?;
        let theorem = align_evidence(&mut staged, equivalence, expected)?;
        let context_name = staged.fresh_name(&[
            expected,
            self.context_ty,
            self.plug,
            self.admissible,
            profile,
            left,
            right,
        ])?;
        let context = staged.tm_fv(context_name, self.context_ty)?;
        let specialized = forall_elim(&mut staged, theorem, context)?;
        let source = self.same_runs_at(&mut staged, profile, context, left, right)?;
        align_theorem_conclusion(
            &mut staged,
            specialized.theorem,
            specialized.proposition,
            source,
            "contextual run symmetry specialization alignment",
        )?;
        let source_admissibility =
            staged.expand_conclusion(specialized.theorem, positive(source), Some(false))?;
        let source_preservation =
            staged.expand_conclusion(specialized.theorem, positive(source), Some(true))?;
        let [_source_admissibility_formula, source_implication] = binary_children(&staged, source)?;
        let [source_both, source_same_runs] = binary_children(&staged, source_implication)?;

        let target = self.same_runs_at(&mut staged, profile, context, right, left)?;
        let [target_admissibility, target_implication] = binary_children(&staged, target)?;
        let [target_both, target_same_runs] = binary_children(&staged, target_implication)?;
        let reversed_admissibility = equality_symmetry(
            &mut staged,
            self.domain.relation.types.bool_ty,
            source_admissibility,
        )?;
        align_theorem_conclusion(
            &mut staged,
            reversed_admissibility.theorem,
            reversed_admissibility.equality,
            target_admissibility,
            "contextual run symmetry admissibility alignment",
        )?;

        let assumed_target = staged.identity(positive(target_both))?;
        let right_fact =
            staged.expand_conclusion(assumed_target, positive(target_both), Some(false))?;
        let left_fact =
            staged.expand_conclusion(assumed_target, positive(target_both), Some(true))?;
        let [source_left, source_right] = binary_children(&staged, source_both)?;
        let [target_right, target_left] = binary_children(&staged, target_both)?;
        align_theorem_conclusion(
            &mut staged,
            left_fact,
            target_left,
            source_left,
            "contextual run symmetry left admissibility alignment",
        )?;
        align_theorem_conclusion(
            &mut staged,
            right_fact,
            target_right,
            source_right,
            "contextual run symmetry right admissibility alignment",
        )?;
        let source_both_theorem = staged.and_right(left_fact, right_fact, positive(source_both))?;
        let expanded_source =
            staged.expand_conclusion(source_preservation, positive(source_implication), None)?;
        let source_same_runs_theorem = staged.resolve(
            expanded_source,
            source_both_theorem,
            positive(source_both).negated(),
        )?;
        let left_closed = apply(&mut staged, self.plug, &[context, left])?;
        let right_closed = apply(&mut staged, self.plug, &[context, right])?;
        let reversed_runs = self.domain.prove_same_runs_symmetric(
            &mut staged,
            Evidence {
                proposition: source_same_runs,
                theorem: source_same_runs_theorem,
                holds: true,
            },
            profile,
            left_closed,
            right_closed,
        )?;
        align_theorem_conclusion(
            &mut staged,
            reversed_runs.theorem,
            reversed_runs.proposition,
            target_same_runs,
            "contextual run symmetry graph alignment",
        )?;
        let target_preservation =
            staged.imp_right(reversed_runs.theorem, positive(target_implication))?;
        let body = staged.and_right(
            reversed_admissibility.theorem,
            target_preservation,
            positive(target),
        )?;
        staged.contract_theorem(body)?;
        let universal = staged.forall_tm(self.domain.relation.types.bool_ty, context, target)?;
        let theorem = staged.forall_intro_at(body, context, universal)?;
        let canonical = self.equivalent(&mut staged, profile, right, left)?;
        align_theorem_conclusion(
            &mut staged,
            theorem,
            universal,
            canonical,
            "contextual run symmetry alignment",
        )?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem,
            holds: true,
        })
    }

    /// Composes two checked contextual run-equivalence facts.
    ///
    /// Context admissibility equality supplies the middle subject's
    /// admissibility. The two resulting closed-run facts then compose through
    /// [`RunDomain::prove_same_runs_transitive`]. Both input premise sets remain
    /// visible in the result.
    ///
    /// # Errors
    ///
    /// Returns an error unless the inputs positively prove equivalence from
    /// `left` to `middle` and from `middle` to `right`, or a checked
    /// specialization, equality, propositional, universal, or alignment step
    /// fails. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn prove_transitive(
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
        let expected_left_middle = self.equivalent(&mut staged, profile, left, middle)?;
        let left_middle_theorem = align_evidence(&mut staged, left_middle, expected_left_middle)?;
        let expected_middle_right = self.equivalent(&mut staged, profile, middle, right)?;
        let middle_right_theorem =
            align_evidence(&mut staged, middle_right, expected_middle_right)?;
        let context_name = staged.fresh_name(&[
            expected_left_middle,
            expected_middle_right,
            self.context_ty,
            self.plug,
            self.admissible,
            profile,
            left,
            middle,
            right,
        ])?;
        let context = staged.tm_fv(context_name, self.context_ty)?;

        let left_middle_specialized = forall_elim(&mut staged, left_middle_theorem, context)?;
        let left_middle_at = self.same_runs_at(&mut staged, profile, context, left, middle)?;
        align_theorem_conclusion(
            &mut staged,
            left_middle_specialized.theorem,
            left_middle_specialized.proposition,
            left_middle_at,
            "contextual run transitivity left specialization alignment",
        )?;
        let middle_right_specialized = forall_elim(&mut staged, middle_right_theorem, context)?;
        let middle_right_at = self.same_runs_at(&mut staged, profile, context, middle, right)?;
        align_theorem_conclusion(
            &mut staged,
            middle_right_specialized.theorem,
            middle_right_specialized.proposition,
            middle_right_at,
            "contextual run transitivity right specialization alignment",
        )?;

        let [left_middle_admissibility_formula, left_middle_implication] =
            binary_children(&staged, left_middle_at)?;
        let [left_middle_both, left_middle_runs] =
            binary_children(&staged, left_middle_implication)?;
        let left_middle_admissibility = staged.expand_conclusion(
            left_middle_specialized.theorem,
            positive(left_middle_at),
            Some(false),
        )?;
        let left_middle_preservation = staged.expand_conclusion(
            left_middle_specialized.theorem,
            positive(left_middle_at),
            Some(true),
        )?;
        let [
            _middle_right_admissibility_formula,
            middle_right_implication,
        ] = binary_children(&staged, middle_right_at)?;
        let [middle_right_both, middle_right_runs] =
            binary_children(&staged, middle_right_implication)?;
        let middle_right_admissibility = staged.expand_conclusion(
            middle_right_specialized.theorem,
            positive(middle_right_at),
            Some(false),
        )?;
        let middle_right_preservation = staged.expand_conclusion(
            middle_right_specialized.theorem,
            positive(middle_right_at),
            Some(true),
        )?;

        let target = self.same_runs_at(&mut staged, profile, context, left, right)?;
        let [target_admissibility, target_implication] = binary_children(&staged, target)?;
        let [target_both, target_runs] = binary_children(&staged, target_implication)?;
        let admissibility = equality_transitivity(
            &mut staged,
            self.domain.relation.types.bool_ty,
            left_middle_admissibility,
            middle_right_admissibility,
        )?;
        align_theorem_conclusion(
            &mut staged,
            admissibility.theorem,
            admissibility.equality,
            target_admissibility,
            "contextual run transitivity admissibility alignment",
        )?;

        let assumed_target = staged.identity(positive(target_both))?;
        let target_left =
            staged.expand_conclusion(assumed_target, positive(target_both), Some(false))?;
        let target_right =
            staged.expand_conclusion(assumed_target, positive(target_both), Some(true))?;
        let left_middle_admissibility_operands =
            equality_operands(&staged, left_middle_admissibility_formula)?;
        let target_both_children = binary_children(&staged, target_both)?;
        let left_for_middle = aligned_theorem_conclusion(
            &mut staged,
            target_left,
            target_both_children[0],
            left_middle_admissibility_operands[0],
            "contextual run transitivity left admissibility alignment",
        )?;
        let middle_fact = staged.eq_mp(left_middle_admissibility, left_for_middle)?;

        let [left_middle_left, left_middle_middle] = binary_children(&staged, left_middle_both)?;
        let [middle_right_middle, middle_right_right] =
            binary_children(&staged, middle_right_both)?;
        let left_fact = aligned_theorem_conclusion(
            &mut staged,
            target_left,
            target_both_children[0],
            left_middle_left,
            "contextual run transitivity left conjunction alignment",
        )?;
        let middle_for_left = aligned_theorem_conclusion(
            &mut staged,
            middle_fact,
            left_middle_admissibility_operands[1],
            left_middle_middle,
            "contextual run transitivity first middle alignment",
        )?;
        let middle_for_right = aligned_theorem_conclusion(
            &mut staged,
            middle_fact,
            left_middle_admissibility_operands[1],
            middle_right_middle,
            "contextual run transitivity second middle alignment",
        )?;
        let right_fact = aligned_theorem_conclusion(
            &mut staged,
            target_right,
            target_both_children[1],
            middle_right_right,
            "contextual run transitivity right conjunction alignment",
        )?;
        let left_middle_both_theorem =
            staged.and_right(left_fact, middle_for_left, positive(left_middle_both))?;
        let middle_right_both_theorem =
            staged.and_right(middle_for_right, right_fact, positive(middle_right_both))?;
        let left_middle_expanded = staged.expand_conclusion(
            left_middle_preservation,
            positive(left_middle_implication),
            None,
        )?;
        let left_middle_runs_theorem = staged.resolve(
            left_middle_expanded,
            left_middle_both_theorem,
            positive(left_middle_both).negated(),
        )?;
        let middle_right_expanded = staged.expand_conclusion(
            middle_right_preservation,
            positive(middle_right_implication),
            None,
        )?;
        let middle_right_runs_theorem = staged.resolve(
            middle_right_expanded,
            middle_right_both_theorem,
            positive(middle_right_both).negated(),
        )?;
        let left_closed = apply(&mut staged, self.plug, &[context, left])?;
        let middle_closed = apply(&mut staged, self.plug, &[context, middle])?;
        let right_closed = apply(&mut staged, self.plug, &[context, right])?;
        let runs = self.domain.prove_same_runs_transitive(
            &mut staged,
            Evidence {
                proposition: left_middle_runs,
                theorem: left_middle_runs_theorem,
                holds: true,
            },
            Evidence {
                proposition: middle_right_runs,
                theorem: middle_right_runs_theorem,
                holds: true,
            },
            profile,
            left_closed,
            middle_closed,
            right_closed,
        )?;
        align_theorem_conclusion(
            &mut staged,
            runs.theorem,
            runs.proposition,
            target_runs,
            "contextual run transitivity graph alignment",
        )?;
        let preservation = staged.imp_right(runs.theorem, positive(target_implication))?;
        let body = staged.and_right(admissibility.theorem, preservation, positive(target))?;
        staged.contract_theorem(body)?;
        let universal = staged.forall_tm(self.domain.relation.types.bool_ty, context, target)?;
        let theorem = staged.forall_intro_at(body, context, universal)?;
        let canonical = self.equivalent(&mut staged, profile, left, right)?;
        align_theorem_conclusion(
            &mut staged,
            theorem,
            universal,
            canonical,
            "contextual run transitivity alignment",
        )?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem,
            holds: true,
        })
    }

    /// Proves that contextual run equivalence preserves an arbitrary run property.
    ///
    /// The result is the ordinary [`ContextualObservation::equivalent`]
    /// proposition for `property`. Thus complete run equivalence is
    /// observation-independent, while callers can recover indistinguishability
    /// for any HOL predicate over the complete run graph without another
    /// semantic assumption.
    ///
    /// # Errors
    ///
    /// Returns an error unless `equivalence` positively proves this schema's
    /// contextual run equivalence, or a checked specialization, propositional,
    /// congruence, or alignment step fails. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn prove_property_preserves(
        self,
        kernel: &mut Kernel,
        equivalence: Evidence,
        property: RunProperty,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.require_property(property)?;
        let expected = self.equivalent(&mut staged, profile, left, right)?;
        let theorem = align_evidence(&mut staged, equivalence, expected)?;
        let contextual =
            self.observe_property_avoiding(&mut staged, property, profile, &[left, right])?;
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
        let source_at = self.same_runs_at(&mut staged, profile, context, left, right)?;
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
        let observed = property.prove_same_runs_preserves(
            &mut staged,
            Evidence {
                proposition: source_same_runs,
                theorem: same_runs_theorem,
                holds: true,
            },
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
        let universal = staged.forall_tm(self.domain.relation.types.bool_ty, context, target_at)?;
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

    /// Proves that contextual run equivalence preserves one behavior observation.
    ///
    /// This is convenience syntax for converting `observation` and `quantifier`
    /// into a [`RunProperty`] and applying [`Self::prove_property_preserves`].
    ///
    /// # Errors
    ///
    /// Returns an error unless the observation belongs to this run domain and
    /// the generic checked property-preservation derivation succeeds. `kernel`
    /// is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_preserves(
        self,
        kernel: &mut Kernel,
        equivalence: Evidence,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.require_observation(observation)?;
        let property = observation.property_avoiding(&mut staged, quantifier, &[left, right])?;
        let evidence = self.prove_property_preserves(
            &mut staged,
            equivalence,
            property,
            profile,
            left,
            right,
        )?;
        *kernel = staged;
        Ok(evidence)
    }

    /// Refutes contextual run equivalence using one distinguishing run property.
    ///
    /// This is the checked contrapositive of observational preservation. If
    /// `distinction` proves that the selected contextual observation differs,
    /// the result proves that the modules cannot have equal complete run graphs
    /// in every admissible context. All premises of `distinction` remain
    /// visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless `distinction` is negative evidence for this
    /// context's selected observation equivalence, or a checked preservation,
    /// cut, negation, or alignment step fails. `kernel` is unchanged on
    /// failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_property_distinct(
        self,
        kernel: &mut Kernel,
        distinction: Evidence,
        property: RunProperty,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.require_property(property)?;
        let contextual =
            self.observe_property_avoiding(&mut staged, property, profile, &[left, right])?;
        let observed_equivalence = contextual.equivalent(&mut staged, left, right)?;
        let distinction_theorem =
            align_signed_evidence(&mut staged, distinction, observed_equivalence, false)?;
        let run_equivalence = self.equivalent(&mut staged, profile, left, right)?;
        let assumed = staged.identity(positive(run_equivalence))?;
        let preservation = self.prove_property_preserves(
            &mut staged,
            Evidence {
                proposition: run_equivalence,
                theorem: assumed,
                holds: true,
            },
            property,
            profile,
            left,
            right,
        )?;
        let preservation_theorem = aligned_theorem_conclusion(
            &mut staged,
            preservation.theorem,
            preservation.proposition,
            observed_equivalence,
            "contextual run distinction observation alignment",
        )?;
        staged.not_left(preservation_theorem, positive(observed_equivalence))?;
        let contradiction = staged.cut(
            distinction_theorem,
            preservation_theorem,
            positive(observed_equivalence).negated(),
        )?;
        staged.not_right(contradiction, positive(run_equivalence))?;
        *kernel = staged;
        Ok(Evidence {
            proposition: run_equivalence,
            theorem: contradiction,
            holds: false,
        })
    }

    /// Refutes contextual run equivalence using one behavior observation.
    ///
    /// This is convenience syntax for converting `observation` and `quantifier`
    /// into a [`RunProperty`] and applying [`Self::prove_property_distinct`].
    ///
    /// # Errors
    ///
    /// Returns an error unless the observation belongs to this run domain and
    /// the generic checked distinction derivation succeeds. `kernel` is
    /// unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_distinct(
        self,
        kernel: &mut Kernel,
        distinction: Evidence,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.require_observation(observation)?;
        let property = observation.property_avoiding(&mut staged, quantifier, &[left, right])?;
        let evidence =
            self.prove_property_distinct(&mut staged, distinction, property, profile, left, right)?;
        *kernel = staged;
        Ok(evidence)
    }

    fn same_runs_at(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        context: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        require_classifier(kernel, context, self.context_ty)?;
        let left_admissible = apply(kernel, self.admissible, &[context, left])?;
        let right_admissible = apply(kernel, self.admissible, &[context, right])?;
        let same_admissibility = kernel.eq(
            self.domain.relation.types.bool_ty,
            left_admissible,
            right_admissible,
        )?;
        let both_admissible = kernel.op2(Op2::And, left_admissible, right_admissible)?;
        let left_closed = apply(kernel, self.plug, &[context, left])?;
        let right_closed = apply(kernel, self.plug, &[context, right])?;
        let same_runs = self
            .domain
            .same_runs(kernel, profile, left_closed, right_closed)?;
        let preservation = kernel.op2(Op2::Imp, both_admissible, same_runs)?;
        kernel.op2(Op2::And, same_admissibility, preservation)
    }

    fn require_observation(self, observation: RunObservation) -> Result<(), KernelError> {
        if observation.domain == self.domain {
            Ok(())
        } else {
            Err(KernelError::InvalidTheoremRule {
                rule: "run context/observation domain mismatch",
            })
        }
    }

    fn require_property(self, property: RunProperty) -> Result<(), KernelError> {
        if property.domain == self.domain {
            Ok(())
        } else {
            Err(KernelError::InvalidTheoremRule {
                rule: "run context/property domain mismatch",
            })
        }
    }
}

impl ClosedRunContext {
    /// Returns the underlying reusable identity context schema.
    #[must_use]
    pub const fn context(self) -> RunContext {
        self.context
    }

    /// Returns the distinguished context token.
    #[must_use]
    pub const fn identity_context(self) -> Ref {
        self.identity_context
    }

    /// Derives premise-free admissibility of one module in the identity
    /// context.
    ///
    /// # Errors
    ///
    /// Returns an error unless `module` has the configured module classifier
    /// and checked beta conversion or truth introduction succeeds. `kernel` is
    /// unchanged on failure.
    pub fn prove_admissible(
        self,
        kernel: &mut Kernel,
        module: Ref,
    ) -> Result<Evidence, KernelError> {
        let mut staged = kernel.fork();
        require_classifier(
            &mut staged,
            module,
            self.context.domain.relation.types.module,
        )?;
        let admissible = apply(
            &mut staged,
            self.context.admissible,
            &[self.identity_context, module],
        )?;
        let truth = staged.bool(self.context.domain.relation.types.bool_ty, true)?;
        let theorem = staged.true_right(positive(truth))?;
        let reduced = certify_curried_beta2(&mut staged, admissible).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "closed run context admissibility beta reduction",
            }
        })?;
        join_alpha_equivalent(&mut staged, truth, reduced).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "closed run context admissibility alignment",
            }
        })?;
        staged.convert_conclusions(theorem, truth, reduced)?;
        staged.convert_conclusions(theorem, reduced, admissible)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: admissible,
            theorem,
            holds: true,
        })
    }

    /// Derives the bare closed-program equation for an arbitrary property and
    /// one sound transformation.
    ///
    /// Identity linking and both admissibility facts are discharged by this
    /// closed context's checked definitions. The result is the canonical
    /// observation equality with definitionally identity plug applications.
    ///
    /// # Errors
    ///
    /// Returns an error unless `sound` was proved under this exact closed
    /// context, `property` belongs to its run domain, and all checked
    /// preservation, beta-conversion, or alignment steps succeed. `kernel` is
    /// unchanged on failure.
    pub fn prove_preserves_property(
        self,
        kernel: &mut Kernel,
        sound: SoundRunTransformation,
        property: RunProperty,
        module: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let transformation = sound.transformation;
        if transformation.context != self.context {
            return Err(KernelError::InvalidTheoremRule {
                rule: "closed context/transformation mismatch",
            }
            .into());
        }
        self.context.require_property(property)?;
        let transformed = transformation.sound_application(&mut staged, module)?;
        let left_admissible = self.prove_admissible(&mut staged, module)?;
        let right_admissible = self.prove_admissible(&mut staged, transformed)?;
        let preserved = sound.prove_preserves_property_in_context(
            &mut staged,
            property,
            module,
            self.identity_context,
            left_admissible,
            right_admissible,
        )?;
        *kernel = staged;
        Ok(preserved)
    }

    /// Derives the bare closed-program equation for one quantified behavior
    /// observation and sound transformation.
    ///
    /// This is the direct closed-context preservation interface when
    /// `observation` denotes assertion reachability.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`Self::prove_preserves_property`], or if `observation` belongs to a
    /// different run domain. `kernel` is unchanged on failure.
    pub fn prove_preserves(
        self,
        kernel: &mut Kernel,
        sound: SoundRunTransformation,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        module: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.context.require_observation(observation)?;
        let property = observation.property_avoiding(
            &mut staged,
            quantifier,
            &[module, sound.transformation.transform],
        )?;
        let preserved = self.prove_preserves_property(&mut staged, sound, property, module)?;
        *kernel = staged;
        Ok(preserved)
    }

    /// Transports signed evidence for an arbitrary property through one sound
    /// transformation of a closed program.
    ///
    /// Identity linking and both admissibility proofs are discharged
    /// internally. The sign and all premises of `behavior` are retained.
    ///
    /// # Errors
    ///
    /// Returns an error unless `sound` and `property` belong to this exact
    /// closed context and `behavior` proves the original program's canonical
    /// closed observation with its declared sign. `kernel` is unchanged on
    /// failure.
    pub fn transport_property(
        self,
        kernel: &mut Kernel,
        sound: SoundRunTransformation,
        property: RunProperty,
        module: Ref,
        behavior: Evidence,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let transformation = sound.transformation;
        if transformation.context != self.context {
            return Err(KernelError::InvalidTheoremRule {
                rule: "closed context/transformation mismatch",
            }
            .into());
        }
        self.context.require_property(property)?;
        let transformed = transformation.sound_application(&mut staged, module)?;
        let left_admissible = self.prove_admissible(&mut staged, module)?;
        let right_admissible = self.prove_admissible(&mut staged, transformed)?;
        let transported = sound.transport_property_in_context(
            &mut staged,
            property,
            module,
            self.identity_context,
            left_admissible,
            right_admissible,
            behavior,
        )?;
        *kernel = staged;
        Ok(transported)
    }

    /// Transports positive or negative behavior evidence through one sound
    /// transformation of a closed program.
    ///
    /// This is the shortest checked path for carrying `callsAssert` or
    /// `not callsAssert` evidence across a sound Wasm transformation.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::transport_property`],
    /// or if `observation` belongs to another run domain. `kernel` is unchanged
    /// on failure.
    pub fn transport(
        self,
        kernel: &mut Kernel,
        sound: SoundRunTransformation,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        module: Ref,
        behavior: Evidence,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.context.require_observation(observation)?;
        let property = observation.property_avoiding(
            &mut staged,
            quantifier,
            &[module, sound.transformation.transform],
        )?;
        let transported =
            self.transport_property(&mut staged, sound, property, module, behavior)?;
        *kernel = staged;
        Ok(transported)
    }
}

impl RunTransformation {
    /// Returns the contextual semantics used to judge this transformation.
    #[must_use]
    pub const fn context(self) -> RunContext {
        self.context
    }

    /// Returns the semantic profile under which soundness is stated.
    #[must_use]
    pub const fn profile(self) -> Ref {
        self.profile
    }

    /// Returns the checked `module -> module` transformation.
    #[must_use]
    pub const fn transform(self) -> Ref {
        self.transform
    }

    /// Applies this transformation to one module.
    ///
    /// # Errors
    ///
    /// Returns an error unless `module` has the configured module classifier.
    /// `kernel` is unchanged on failure.
    pub fn apply(self, kernel: &mut Kernel, module: Ref) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        require_classifier(
            &mut staged,
            module,
            self.context.domain.relation.types.module,
        )?;
        let transformed = staged.app(self.transform, module)?;
        *kernel = staged;
        Ok(transformed)
    }

    /// Constructs the semantic soundness proposition for this transformation.
    ///
    /// The result is `forall module. module ≈ transform(module)`, where `≈`
    /// is contextual observational equivalence under this exact profile and
    /// context schema. This method constructs syntax only.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application, contextual-equivalence, or
    /// universal construction fails. `kernel` is unchanged on failure.
    pub fn sound(self, kernel: &mut Kernel) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.context.domain.relation.types;
        let module = staged.tm_fv(
            staged.fresh_name(&[
                self.context.context_ty,
                self.context.plug,
                self.context.admissible,
                self.profile,
                self.transform,
                types.module,
                types.bool_ty,
            ])?,
            types.module,
        )?;
        let transformed = self.sound_application(&mut staged, module)?;
        let equivalent = self
            .context
            .equivalent(&mut staged, self.profile, module, transformed)?;
        let sound = staged.forall_tm(types.bool_ty, module, equivalent)?;
        *kernel = staged;
        Ok(sound)
    }

    /// Constructs the proposition that this transformation preserves one run
    /// property in every admissible linking context.
    ///
    /// # Errors
    ///
    /// Returns an error if `property` belongs to another run domain or checked
    /// contextual-observation construction fails. `kernel` is unchanged on
    /// failure.
    pub fn preserves_property(
        self,
        kernel: &mut Kernel,
        property: RunProperty,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        self.context.require_property(property)?;
        let types = self.context.domain.relation.types;
        let observed = self.context.observe_property_avoiding(
            &mut staged,
            property,
            self.profile,
            &[self.transform],
        )?;
        let module = staged.tm_fv(
            staged.fresh_name(&[
                observed.observe,
                self.transform,
                self.profile,
                types.module,
                types.bool_ty,
            ])?,
            types.module,
        )?;
        let transformed = self.sound_application(&mut staged, module)?;
        let preserved = observed.equivalent(&mut staged, module, transformed)?;
        let proposition = staged.forall_tm(types.bool_ty, module, preserved)?;
        *kernel = staged;
        Ok(proposition)
    }

    fn sound_application(self, kernel: &mut Kernel, module: Ref) -> Result<Ref, KernelError> {
        let mut transformed = self.apply(kernel, module)?;
        loop {
            let Some(children) = kernel.arena().children(transformed) else {
                break;
            };
            let children = children.collect::<Vec<_>>();
            let [function, _argument] = children.as_slice() else {
                break;
            };
            if kernel.arena().tag(*function) != Some(Tag::Tm(TmTag::Lam)) {
                break;
            }
            transformed = certify_beta_application(kernel, transformed)
                .map_err(|_| KernelError::InvalidTheoremRule {
                    rule: "transformation soundness beta reduction",
                })?
                .0;
        }
        Ok(transformed)
    }

    /// Pairs this transformation with checked evidence of its exact soundness
    /// proposition.
    ///
    /// All premises of `soundness` remain visible in the returned evidence.
    /// No theorem fact is created by this operation.
    ///
    /// # Errors
    ///
    /// Returns an error unless `soundness` positively proves [`Self::sound`]
    /// for this exact transformation, context schema, and semantic profile.
    /// `kernel` is unchanged on failure.
    pub fn with_soundness(
        self,
        kernel: &mut Kernel,
        soundness: Evidence,
    ) -> Result<SoundRunTransformation, RunProofError> {
        let mut staged = kernel.fork();
        let proposition = self.sound(&mut staged)?;
        let theorem = align_evidence(&mut staged, soundness, proposition)?;
        *kernel = staged;
        Ok(SoundRunTransformation {
            transformation: self,
            soundness: Evidence {
                proposition,
                theorem,
                holds: true,
            },
        })
    }

    /// Composes this transformation with `next` without mutating either one.
    ///
    /// The resulting function applies `self` first and `next` second.
    ///
    /// # Errors
    ///
    /// Returns [`RunTransformationError::ContextMismatch`] or
    /// [`RunTransformationError::ProfileMismatch`] unless both transformations
    /// use the same semantic configuration, or an error if checked application
    /// or abstraction fails. `kernel` is unchanged on failure.
    pub fn then(self, kernel: &mut Kernel, next: Self) -> Result<Self, RunTransformationError> {
        if self.context != next.context {
            return Err(RunTransformationError::ContextMismatch);
        }
        if self.profile != next.profile {
            return Err(RunTransformationError::ProfileMismatch);
        }
        let mut staged = kernel.fork();
        let module_ty = self.context.domain.relation.types.module;
        let module = staged.tm_fv(
            staged.fresh_name(&[self.transform, next.transform, module_ty])?,
            module_ty,
        )?;
        let intermediate = self.apply(&mut staged, module)?;
        let transformed = next.apply(&mut staged, intermediate)?;
        let transform_ty = staged.ty_arr(module_ty, module_ty)?;
        let transform = staged.lam_at(transform_ty, module, transformed)?;
        let composed = self
            .context
            .transformation(&mut staged, self.profile, transform)?;
        *kernel = staged;
        Ok(composed)
    }
}

impl SoundRunTransformation {
    /// Returns the underlying checked transformation schema.
    #[must_use]
    pub const fn transformation(self) -> RunTransformation {
        self.transformation
    }

    /// Returns the checked soundness evidence, including all visible premises.
    #[must_use]
    pub const fn soundness(self) -> Evidence {
        self.soundness
    }

    /// Derives that this sound transformation preserves an arbitrary run
    /// property in every admissible linking context.
    ///
    /// All premises of the transformation's soundness theorem remain visible.
    /// The property is handled parametrically; this proof does not inspect or
    /// execute it.
    ///
    /// # Errors
    ///
    /// Returns an error unless `property` belongs to the transformation's run
    /// domain and every checked soundness specialization, contextual
    /// preservation, conversion, or universal step succeeds. `kernel` is
    /// unchanged on failure.
    pub fn prove_preserves_property(
        self,
        kernel: &mut Kernel,
        property: RunProperty,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let transformation = self.transformation;
        let context = transformation.context;
        context.require_property(property)?;
        let sound = transformation.sound(&mut staged)?;
        let sound_theorem = align_evidence(&mut staged, self.soundness, sound)?;
        let types = context.domain.relation.types;
        let module = staged.tm_fv(
            staged.fresh_name(&[
                sound,
                transformation.transform,
                property.property,
                types.module,
                types.bool_ty,
            ])?,
            types.module,
        )?;
        let transformed = transformation.sound_application(&mut staged, module)?;
        let specialized = forall_elim(&mut staged, sound_theorem, module)?;
        let equivalent =
            context.equivalent(&mut staged, transformation.profile, module, transformed)?;
        join_alpha_equivalent(&mut staged, specialized.proposition, equivalent).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "transformation property soundness specialization",
            }
        })?;
        staged.convert_conclusions(specialized.theorem, specialized.proposition, equivalent)?;
        let preserved = context.prove_property_preserves(
            &mut staged,
            Evidence {
                proposition: equivalent,
                theorem: specialized.theorem,
                holds: true,
            },
            property,
            transformation.profile,
            module,
            transformed,
        )?;
        staged.contract_theorem(preserved.theorem)?;
        let direct = staged.forall_tm(types.bool_ty, module, preserved.proposition)?;
        let theorem = staged.forall_intro_at(preserved.theorem, module, direct)?;
        let canonical = transformation.preserves_property(&mut staged, property)?;
        align_theorem_conclusion(
            &mut staged,
            theorem,
            direct,
            canonical,
            "transformation property preservation alignment",
        )?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem,
            holds: true,
        })
    }

    /// Specializes generic property preservation to one concrete module.
    ///
    /// # Errors
    ///
    /// Returns an error unless `module` has the configured module classifier
    /// and the generic checked preservation theorem can be constructed and
    /// specialized. `kernel` is unchanged on failure.
    pub fn prove_preserves_property_at(
        self,
        kernel: &mut Kernel,
        property: RunProperty,
        module: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let transformation = self.transformation;
        let context = transformation.context;
        context.require_property(property)?;
        require_classifier(&mut staged, module, context.domain.relation.types.module)?;
        let universal = self.prove_preserves_property(&mut staged, property)?;
        let specialized = forall_elim(&mut staged, universal.theorem, module)?;
        let observed = context.observe_property_avoiding(
            &mut staged,
            property,
            transformation.profile,
            &[module, transformation.transform],
        )?;
        let transformed = transformation.sound_application(&mut staged, module)?;
        let canonical = observed.equivalent(&mut staged, module, transformed)?;
        join_alpha_equivalent(&mut staged, specialized.proposition, canonical).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "transformation property preservation specialization",
            }
        })?;
        staged.convert_conclusions(specialized.theorem, specialized.proposition, canonical)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem: specialized.theorem,
            holds: true,
        })
    }

    /// Eliminates property preservation at one chosen admissible linking
    /// context and concrete module.
    ///
    /// The result equates the property on the two closed modules produced by
    /// plugging the original and transformed subjects into `linking_context`.
    /// For an always-admissible identity context this is the bare
    /// `property(P) = property(transform(P))` equation.
    ///
    /// # Errors
    ///
    /// Returns an error unless both admissibility facts positively prove the
    /// exact obligations for the selected context and subjects, or the generic
    /// preservation and checked contextual-elimination steps fail. `kernel` is
    /// unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_preserves_property_in_context(
        self,
        kernel: &mut Kernel,
        property: RunProperty,
        module: Ref,
        linking_context: Ref,
        left_admissible: Evidence,
        right_admissible: Evidence,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let transformation = self.transformation;
        let context = transformation.context;
        context.require_property(property)?;
        let transformed = transformation.sound_application(&mut staged, module)?;
        let left_ok = apply(&mut staged, context.admissible, &[linking_context, module])?;
        let right_ok = apply(
            &mut staged,
            context.admissible,
            &[linking_context, transformed],
        )?;
        let left_ok_theorem = align_evidence(&mut staged, left_admissible, left_ok)?;
        let right_ok_theorem = align_evidence(&mut staged, right_admissible, right_ok)?;
        let contextual = context.observe_property_avoiding(
            &mut staged,
            property,
            transformation.profile,
            &[module, transformed, linking_context],
        )?;
        let equivalence = self.prove_preserves_property_at(&mut staged, property, module)?;
        let preserved = contextual.prove_preservation(
            &mut staged,
            equivalence.theorem,
            linking_context,
            module,
            transformed,
            left_ok_theorem,
            right_ok_theorem,
        )?;
        *kernel = staged;
        Ok(preserved)
    }

    /// Transports positive or negative property evidence from a program to its
    /// soundly transformed image in one admissible linking context.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`Self::prove_preserves_property_in_context`], or unless `behavior`
    /// proves exactly the left-hand observation with the indicated sign.
    /// `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn transport_property_in_context(
        self,
        kernel: &mut Kernel,
        property: RunProperty,
        module: Ref,
        linking_context: Ref,
        left_admissible: Evidence,
        right_admissible: Evidence,
        behavior: Evidence,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let equality = self.prove_preserves_property_in_context(
            &mut staged,
            property,
            module,
            linking_context,
            left_admissible,
            right_admissible,
        )?;
        let [left, right] = equality_operands(&staged, equality.proposition)?;
        let behavior_theorem = align_signed_evidence(&mut staged, behavior, left, behavior.holds)?;
        let theorem = if behavior.holds {
            staged.eq_mp(equality.theorem, behavior_theorem)?
        } else {
            let reversed = equality_symmetry(
                &mut staged,
                self.transformation.context.domain.relation.types.bool_ty,
                equality.theorem,
            )?;
            let assumed_right = staged.identity(positive(right))?;
            let left_fact = staged.eq_mp(reversed.theorem, assumed_right)?;
            staged.not_left(left_fact, positive(left))?;
            let contradiction =
                staged.cut(behavior_theorem, left_fact, positive(left).negated())?;
            staged.not_right(contradiction, positive(right))?;
            contradiction
        };
        staged.contract_theorem(theorem)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: right,
            theorem,
            holds: behavior.holds,
        })
    }

    /// Derives preservation of one quantified behavior observation.
    ///
    /// This is convenience syntax for constructing the observation's generic
    /// [`RunProperty`] and applying [`Self::prove_preserves_property`].
    ///
    /// # Errors
    ///
    /// Returns an error unless `observation` belongs to this transformation's
    /// run domain and the generic checked preservation derivation succeeds.
    /// `kernel` is unchanged on failure.
    pub fn prove_preserves(
        self,
        kernel: &mut Kernel,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.transformation
            .context
            .require_observation(observation)?;
        let property = observation.property_avoiding(
            &mut staged,
            quantifier,
            &[self.transformation.transform],
        )?;
        let preserved = self.prove_preserves_property(&mut staged, property)?;
        *kernel = staged;
        Ok(preserved)
    }

    /// Specializes behavior-observation preservation to one concrete module.
    ///
    /// The result is contextual equivalence of the selected observation for
    /// `P` and `transform(P)`. Use [`Self::prove_preserves_in_context`] with
    /// concrete admissibility evidence to obtain the observation equality in
    /// one selected context.
    ///
    /// # Errors
    ///
    /// Returns an error unless the observation and module belong to this
    /// transformation's semantic domain and the generic checked preservation
    /// derivation succeeds. `kernel` is unchanged on failure.
    pub fn prove_preserves_at(
        self,
        kernel: &mut Kernel,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        module: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.transformation
            .context
            .require_observation(observation)?;
        let property = observation.property_avoiding(
            &mut staged,
            quantifier,
            &[module, self.transformation.transform],
        )?;
        let preserved = self.prove_preserves_property_at(&mut staged, property, module)?;
        *kernel = staged;
        Ok(preserved)
    }

    /// Eliminates behavior-observation preservation at one chosen admissible
    /// linking context and concrete module.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`Self::prove_preserves_property_in_context`], or if the observation
    /// belongs to another run domain. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_preserves_in_context(
        self,
        kernel: &mut Kernel,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        module: Ref,
        linking_context: Ref,
        left_admissible: Evidence,
        right_admissible: Evidence,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.transformation
            .context
            .require_observation(observation)?;
        let property = observation.property_avoiding(
            &mut staged,
            quantifier,
            &[module, linking_context, self.transformation.transform],
        )?;
        let preserved = self.prove_preserves_property_in_context(
            &mut staged,
            property,
            module,
            linking_context,
            left_admissible,
            right_admissible,
        )?;
        *kernel = staged;
        Ok(preserved)
    }

    /// Transports signed evidence for one behavior observation through this
    /// sound transformation at a selected admissible context.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`Self::transport_property_in_context`], or if `observation` belongs to
    /// another run domain. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn transport_in_context(
        self,
        kernel: &mut Kernel,
        observation: RunObservation,
        quantifier: BehaviorQuantifier,
        module: Ref,
        linking_context: Ref,
        left_admissible: Evidence,
        right_admissible: Evidence,
        behavior: Evidence,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        self.transformation
            .context
            .require_observation(observation)?;
        let property = observation.property_avoiding(
            &mut staged,
            quantifier,
            &[module, linking_context, self.transformation.transform],
        )?;
        let transported = self.transport_property_in_context(
            &mut staged,
            property,
            module,
            linking_context,
            left_admissible,
            right_admissible,
            behavior,
        )?;
        *kernel = staged;
        Ok(transported)
    }

    /// Composes two proved-sound transformations and derives soundness of the
    /// result.
    ///
    /// The derivation specializes both universal soundness theorems at the
    /// relevant module, composes their contextual equivalences transitively,
    /// and universally closes the result. Every premise from both proofs is
    /// retained.
    ///
    /// # Errors
    ///
    /// Returns an error unless both transformations use the same context and
    /// profile, their stored evidence still checks, and every checked
    /// specialization, transitivity, conversion, or universal step succeeds.
    /// `kernel` is unchanged on failure.
    pub fn then(
        self,
        kernel: &mut Kernel,
        next: Self,
    ) -> Result<Self, SoundRunTransformationError> {
        let mut staged = kernel.fork();
        let composed = self.transformation.then(&mut staged, next.transformation)?;
        let left_sound = self.transformation.sound(&mut staged)?;
        let left_theorem = align_evidence(&mut staged, self.soundness, left_sound)?;
        let right_sound = next.transformation.sound(&mut staged)?;
        let right_theorem = align_evidence(&mut staged, next.soundness, right_sound)?;
        let context = self.transformation.context;
        let profile = self.transformation.profile;
        let types = context.domain.relation.types;
        let module = staged.tm_fv(
            staged.fresh_name(&[
                left_sound,
                right_sound,
                composed.transform,
                types.module,
                types.bool_ty,
            ])?,
            types.module,
        )?;
        let intermediate = self.transformation.sound_application(&mut staged, module)?;
        let final_module = next
            .transformation
            .sound_application(&mut staged, intermediate)?;

        let left = forall_elim(&mut staged, left_theorem, module)?;
        let left_at = context.equivalent(&mut staged, profile, module, intermediate)?;
        join_alpha_equivalent(&mut staged, left.proposition, left_at).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "composed transformation left soundness alignment",
            }
        })?;
        staged.convert_conclusions(left.theorem, left.proposition, left_at)?;

        let right = forall_elim(&mut staged, right_theorem, intermediate)?;
        let right_at = context.equivalent(&mut staged, profile, intermediate, final_module)?;
        join_alpha_equivalent(&mut staged, right.proposition, right_at).map_err(|_| {
            KernelError::InvalidTheoremRule {
                rule: "composed transformation right soundness alignment",
            }
        })?;
        staged.convert_conclusions(right.theorem, right.proposition, right_at)?;

        let transitive = context.prove_transitive(
            &mut staged,
            Evidence {
                proposition: left_at,
                theorem: left.theorem,
                holds: true,
            },
            Evidence {
                proposition: right_at,
                theorem: right.theorem,
                holds: true,
            },
            profile,
            module,
            intermediate,
            final_module,
        )?;
        staged.contract_theorem(transitive.theorem)?;
        let direct = staged.forall_tm(types.bool_ty, module, transitive.proposition)?;
        let theorem = staged.forall_intro_at(transitive.theorem, module, direct)?;
        let canonical = composed.sound(&mut staged)?;
        align_theorem_conclusion(
            &mut staged,
            theorem,
            direct,
            canonical,
            "composed transformation soundness alignment",
        )?;
        let sound = composed.with_soundness(
            &mut staged,
            Evidence {
                proposition: canonical,
                theorem,
                holds: true,
            },
        )?;
        *kernel = staged;
        Ok(sound)
    }
}

/// Failure to compose proof-carrying sound transformations.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum SoundRunTransformationError {
    /// The underlying transformation schemas cannot be composed.
    #[snafu(transparent)]
    Composition {
        /// Underlying immutable composition failure.
        source: RunTransformationError,
    },
    /// A checked HOL construction failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// A derived proof step failed.
    #[snafu(transparent)]
    Proof {
        /// Underlying run-proof failure.
        source: RunProofError,
    },
    /// Universal specialization failed.
    #[snafu(transparent)]
    Forall {
        /// Underlying derived universal-elimination failure.
        source: ForallError,
    },
}

/// Failure to compose checked module transformations.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RunTransformationError {
    /// Transformations use different contextual semantics.
    #[snafu(display("cannot compose transformations from different run contexts"))]
    ContextMismatch,
    /// Transformations use different semantic profiles.
    #[snafu(display("cannot compose transformations from different semantic profiles"))]
    ProfileMismatch,
    /// A checked HOL construction failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
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
    /// Existential opening or introduction rejected progress transport.
    #[snafu(transparent)]
    Exists {
        /// Underlying derived existential failure.
        source: ExistsError,
    },
    /// Capture-avoiding beta substitution failed.
    #[snafu(transparent)]
    Model {
        /// Underlying derived substitution failure.
        source: ModelError,
    },
    /// Contextual-observation elimination failed.
    #[snafu(transparent)]
    Observation {
        /// Underlying checked contextual-observation proof failure.
        source: ObservationProofError,
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

    /// Validates and attaches a reusable linking-context schema.
    ///
    /// # Errors
    ///
    /// Returns an error unless `plug` has classifier
    /// `context -> module -> module` and `admissible` has classifier
    /// `context -> module -> bool`. `kernel` is unchanged on failure.
    pub fn in_context(
        self,
        kernel: &mut Kernel,
        context_ty: Ref,
        plug: Ref,
        admissible: Ref,
    ) -> Result<RunContext, KernelError> {
        RunContext::new(kernel, self, context_ty, plug, admissible)
    }

    /// Constructs the canonical always-admissible identity context for closed
    /// program observations.
    ///
    /// # Errors
    ///
    /// Returns an error if fresh-name allocation or checked Boolean,
    /// abstraction, or context construction fails. `kernel` is unchanged on
    /// failure.
    pub fn closed_context(self, kernel: &mut Kernel) -> Result<ClosedRunContext, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        let first = staged.fresh_name(&[
            types.module,
            types.bool_ty,
            self.relation.runs,
            self.admissible,
        ])?;
        let context_token = staged.tm_fv(first, types.bool_ty)?;
        let module = staged.tm_fv(checked_name(first, 1)?, types.module)?;
        let truth = staged.bool(types.bool_ty, true)?;
        let module_map_ty = staged.ty_arr(types.module, types.module)?;
        let identity_module = staged.lam_at(module_map_ty, module, module)?;
        let plug_ty = staged.ty_arr(types.bool_ty, module_map_ty)?;
        let plug = staged.lam_at(plug_ty, context_token, identity_module)?;
        let module_predicate_ty = staged.ty_arr(types.module, types.bool_ty)?;
        let accepts_module = staged.lam_at(module_predicate_ty, module, truth)?;
        let admissible_ty = staged.ty_arr(types.bool_ty, module_predicate_ty)?;
        let admissible = staged.lam_at(admissible_ty, context_token, accepts_module)?;
        let context = self.in_context(&mut staged, types.bool_ty, plug, admissible)?;
        *kernel = staged;
        Ok(ClosedRunContext {
            context,
            identity_context: truth,
        })
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

    /// Validates and attaches an arbitrary property of this run domain.
    ///
    /// The property receives the immutable admissible-invocation and allowed-
    /// run characteristic functions. This is the generic extension point for
    /// safety, progress, resource, and temporal propositions.
    ///
    /// # Errors
    ///
    /// Returns an error unless `property` has classifier
    /// `domain-characteristic -> run-characteristic -> bool`. `kernel` is
    /// unchanged on failure.
    pub fn property(self, kernel: &mut Kernel, property: Ref) -> Result<RunProperty, KernelError> {
        let mut staged = kernel.fork();
        let by_runs_ty = staged.ty_arr(self.run_graph_ty, self.relation.types.bool_ty)?;
        let property_ty = staged.ty_arr(self.domain_ty, by_runs_ty)?;
        require_classifier(&mut staged, property, property_ty)?;
        *kernel = staged;
        Ok(RunProperty {
            domain: self,
            property,
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

    /// Constructs the reusable totality property for this run domain.
    ///
    /// The property says every admissible invocation has at least one eligible
    /// trace/outcome pair. Its meaning remains relative to the selected run
    /// profile and outcome representation when later applied to a module.
    ///
    /// # Errors
    ///
    /// Returns an error if fresh-name allocation or checked HOL construction
    /// fails. `kernel` is unchanged on failure.
    pub fn total_property(self, kernel: &mut Kernel) -> Result<RunProperty, KernelError> {
        self.total_property_avoiding(kernel, &[])
    }

    fn total_property_avoiding(
        self,
        kernel: &mut Kernel,
        avoiding: &[Ref],
    ) -> Result<RunProperty, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        let (domain, runs) = property_variables(&mut staged, self, avoiding)?;
        let mut roots = vec![
            domain,
            runs,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
        ];
        roots.extend_from_slice(avoiding);
        let first = staged.fresh_name(&roots)?;
        let entry = staged.tm_fv(first, types.entry)?;
        let inputs = staged.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = staged.tm_fv(checked_name(first, 2)?, types.host)?;
        let trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let allowed = apply(&mut staged, domain, &[entry, inputs, host])?;
        let run = apply(&mut staged, runs, &[entry, inputs, host, trace, outcome])?;
        let exists_run = quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], run)?;
        let total = staged.op2(Op2::Imp, allowed, exists_run)?;
        let total = quantify_forall(&mut staged, types.bool_ty, &[entry, inputs, host], total)?;
        let property = abstract_property(&mut staged, self, domain, runs, total)?;
        let property = self.property(&mut staged, property)?;
        *kernel = staged;
        Ok(property)
    }

    /// Constructs the reusable determinism property for this run domain.
    ///
    /// For each invocation, any two eligible runs must have equal traces and
    /// outcomes. Host behavior remains an explicit invocation argument.
    ///
    /// # Errors
    ///
    /// Returns an error if fresh-name allocation or checked HOL construction
    /// fails. `kernel` is unchanged on failure.
    pub fn deterministic_property(self, kernel: &mut Kernel) -> Result<RunProperty, KernelError> {
        self.deterministic_property_avoiding(kernel, &[])
    }

    fn deterministic_property_avoiding(
        self,
        kernel: &mut Kernel,
        avoiding: &[Ref],
    ) -> Result<RunProperty, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        let (domain, runs) = property_variables(&mut staged, self, avoiding)?;
        let mut roots = vec![
            domain,
            runs,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
        ];
        roots.extend_from_slice(avoiding);
        let first = staged.fresh_name(&roots)?;
        let entry = staged.tm_fv(first, types.entry)?;
        let inputs = staged.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = staged.tm_fv(checked_name(first, 2)?, types.host)?;
        let left_trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let left_outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let right_trace = staged.tm_fv(checked_name(first, 5)?, types.trace)?;
        let right_outcome = staged.tm_fv(checked_name(first, 6)?, types.outcome)?;
        let left_run = apply(
            &mut staged,
            runs,
            &[entry, inputs, host, left_trace, left_outcome],
        )?;
        let right_run = apply(
            &mut staged,
            runs,
            &[entry, inputs, host, right_trace, right_outcome],
        )?;
        let both_runs = staged.op2(Op2::And, left_run, right_run)?;
        let same_trace = staged.eq(types.bool_ty, left_trace, right_trace)?;
        let same_outcome = staged.eq(types.bool_ty, left_outcome, right_outcome)?;
        let same_result = staged.op2(Op2::And, same_trace, same_outcome)?;
        let deterministic = staged.op2(Op2::Imp, both_runs, same_result)?;
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
        let property = abstract_property(&mut staged, self, domain, runs, deterministic)?;
        let property = self.property(&mut staged, property)?;
        *kernel = staged;
        Ok(property)
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
        let property = self.total_property_avoiding(&mut staged, &[profile, module])?;
        let total = property.proposition(&mut staged, profile, module)?;
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
        let property = self.deterministic_property_avoiding(&mut staged, &[profile, module])?;
        let deterministic = property.proposition(&mut staged, profile, module)?;
        *kernel = staged;
        Ok(deterministic)
    }

    /// Transports totality from a specification to an implementation that
    /// refines it.
    ///
    /// Admissibility equality moves an implementation invocation to the
    /// specification. The specification's totality supplies a run, and
    /// refinement's reverse progress clause supplies a retained implementation
    /// run. Both input premises remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless `refinement` proves the displayed directional
    /// refinement, `specification_total` positively proves totality of the
    /// specification, and every checked equality, existential, universal,
    /// propositional, or alignment step succeeds. `kernel` is unchanged on
    /// failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn prove_refinement_preserves_totality(
        self,
        kernel: &mut Kernel,
        refinement: Evidence,
        specification_total: Evidence,
        profile: Ref,
        implementation: Ref,
        specification: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        let expected_refinement =
            self.refines_runs(&mut staged, profile, implementation, specification)?;
        let refinement_theorem = align_evidence(&mut staged, refinement, expected_refinement)?;
        let domain_equality = staged.expand_conclusion(
            refinement_theorem,
            positive(expected_refinement),
            Some(false),
        )?;
        let behavior = staged.expand_conclusion(
            refinement_theorem,
            positive(expected_refinement),
            Some(true),
        )?;
        let [_, behavior_formula] = binary_children(&staged, expected_refinement)?;
        binary_children(&staged, behavior_formula)?;
        let progress =
            staged.expand_conclusion(behavior, positive(behavior_formula), Some(true))?;

        let implementation_graphs = self.run_graphs(&mut staged, profile, implementation)?;
        let specification_graphs = self.run_graphs(&mut staged, profile, specification)?;
        let specification_total_proposition = self.total(&mut staged, profile, specification)?;
        let total = align_evidence(
            &mut staged,
            specification_total,
            specification_total_proposition,
        )?;
        let first = staged.fresh_name(&[
            expected_refinement,
            specification_total_proposition,
            implementation_graphs.domain,
            implementation_graphs.runs,
            specification_graphs.domain,
            specification_graphs.runs,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
        ])?;
        let invocation = [
            staged.tm_fv(first, types.entry)?,
            staged.tm_fv(checked_name(first, 1)?, types.inputs)?,
            staged.tm_fv(checked_name(first, 2)?, types.host)?,
        ];
        let trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let implementation_allowed = apply(&mut staged, implementation_graphs.domain, &invocation)?;
        let specification_allowed = apply(&mut staged, specification_graphs.domain, &invocation)?;
        let implementation_run = apply(
            &mut staged,
            implementation_graphs.runs,
            &[invocation[0], invocation[1], invocation[2], trace, outcome],
        )?;
        let specification_run = apply(
            &mut staged,
            specification_graphs.runs,
            &[invocation[0], invocation[1], invocation[2], trace, outcome],
        )?;
        let implementation_exists = quantify_exists(
            &mut staged,
            types.bool_ty,
            &[trace, outcome],
            implementation_run,
        )?;
        let specification_exists = quantify_exists(
            &mut staged,
            types.bool_ty,
            &[trace, outcome],
            specification_run,
        )?;
        let specification_implication =
            staged.op2(Op2::Imp, specification_allowed, specification_exists)?;
        let specification_direct = quantify_forall(
            &mut staged,
            types.bool_ty,
            &invocation,
            specification_implication,
        )?;
        let specification_reduced =
            certify_curried_beta2(&mut staged, specification_total_proposition)?;
        join_alpha_equivalent(&mut staged, specification_reduced, specification_direct).map_err(
            |_| KernelError::InvalidTheoremRule {
                rule: "refinement total specification reduction",
            },
        )?;
        staged.convert_conclusions(total, specification_total_proposition, specification_direct)?;
        let total = specialize_universal_to(
            &mut staged,
            total,
            &invocation,
            specification_implication,
            "refinement total specification specialization",
        )?;
        let total = staged.expand_conclusion(total, positive(specification_implication), None)?;

        let mut allowed_equality = staged.ap_thm(domain_equality, invocation[0])?;
        for &argument in &invocation[1..] {
            allowed_equality = staged.ap_thm(allowed_equality.theorem, argument)?;
        }
        let allowed_target =
            staged.eq(types.bool_ty, implementation_allowed, specification_allowed)?;
        align_theorem_conclusion(
            &mut staged,
            allowed_equality.theorem,
            allowed_equality.equality,
            allowed_target,
            "refinement total admissibility alignment",
        )?;
        let assumed = staged.identity(positive(implementation_allowed))?;
        let specification_allowed_fact = staged.eq_mp(allowed_equality.theorem, assumed)?;
        let specification_exists_fact = staged.resolve(
            specification_allowed_fact,
            total,
            positive(specification_allowed),
        )?;
        let progress_implication =
            staged.op2(Op2::Imp, specification_exists, implementation_exists)?;
        let progress = specialize_universal_to(
            &mut staged,
            progress,
            &invocation,
            progress_implication,
            "refinement total progress specialization",
        )?;
        let progress = staged.expand_conclusion(progress, positive(progress_implication), None)?;
        let implementation_exists_fact = staged.resolve(
            specification_exists_fact,
            progress,
            positive(specification_exists),
        )?;
        let implementation_implication =
            staged.op2(Op2::Imp, implementation_allowed, implementation_exists)?;
        let proof = staged.imp_right(
            implementation_exists_fact,
            positive(implementation_implication),
        )?;
        let (direct, proof) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &invocation,
            implementation_implication,
            proof,
        )?;
        let implementation_total = self.total(&mut staged, profile, implementation)?;
        let implementation_reduced = certify_curried_beta2(&mut staged, implementation_total)?;
        align_theorem_conclusion(
            &mut staged,
            proof,
            direct,
            implementation_reduced,
            "refinement total result alignment",
        )?;
        staged.convert_conclusions(proof, implementation_reduced, implementation_total)?;
        staged.contract_theorem(proof)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: implementation_total,
            theorem: proof,
            holds: true,
        })
    }

    /// Transports determinism from a specification to an implementation that
    /// refines it.
    ///
    /// Each implementation run is also a specification run, so any two
    /// implementation results are covered by the specification's determinism
    /// premise. Both input premises remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless `refinement` proves the displayed directional
    /// refinement, `specification_deterministic` positively proves determinism
    /// of the specification, and every checked specialization, propositional,
    /// or alignment step succeeds. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn prove_refinement_preserves_determinism(
        self,
        kernel: &mut Kernel,
        refinement: Evidence,
        specification_deterministic: Evidence,
        profile: Ref,
        implementation: Ref,
        specification: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        let expected_refinement =
            self.refines_runs(&mut staged, profile, implementation, specification)?;
        let refinement_theorem = align_evidence(&mut staged, refinement, expected_refinement)?;
        let behavior = staged.expand_conclusion(
            refinement_theorem,
            positive(expected_refinement),
            Some(true),
        )?;
        let [_, behavior_formula] = binary_children(&staged, expected_refinement)?;
        binary_children(&staged, behavior_formula)?;
        let inclusion =
            staged.expand_conclusion(behavior, positive(behavior_formula), Some(false))?;

        let implementation_graphs = self.run_graphs(&mut staged, profile, implementation)?;
        let specification_graphs = self.run_graphs(&mut staged, profile, specification)?;
        let specification_deterministic_proposition =
            self.deterministic(&mut staged, profile, specification)?;
        let deterministic = align_evidence(
            &mut staged,
            specification_deterministic,
            specification_deterministic_proposition,
        )?;
        let first = staged.fresh_name(&[
            expected_refinement,
            specification_deterministic_proposition,
            implementation_graphs.runs,
            specification_graphs.runs,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
        ])?;
        let variables = [
            staged.tm_fv(first, types.entry)?,
            staged.tm_fv(checked_name(first, 1)?, types.inputs)?,
            staged.tm_fv(checked_name(first, 2)?, types.host)?,
            staged.tm_fv(checked_name(first, 3)?, types.trace)?,
            staged.tm_fv(checked_name(first, 4)?, types.outcome)?,
            staged.tm_fv(checked_name(first, 5)?, types.trace)?,
            staged.tm_fv(checked_name(first, 6)?, types.outcome)?,
        ];
        let left_arguments = [
            variables[0],
            variables[1],
            variables[2],
            variables[3],
            variables[4],
        ];
        let right_arguments = [
            variables[0],
            variables[1],
            variables[2],
            variables[5],
            variables[6],
        ];
        let implementation_left = apply(&mut staged, implementation_graphs.runs, &left_arguments)?;
        let implementation_right =
            apply(&mut staged, implementation_graphs.runs, &right_arguments)?;
        let specification_left = apply(&mut staged, specification_graphs.runs, &left_arguments)?;
        let specification_right = apply(&mut staged, specification_graphs.runs, &right_arguments)?;
        let implementation_both =
            staged.op2(Op2::And, implementation_left, implementation_right)?;
        let specification_both = staged.op2(Op2::And, specification_left, specification_right)?;
        let same_trace = staged.eq(types.bool_ty, variables[3], variables[5])?;
        let same_outcome = staged.eq(types.bool_ty, variables[4], variables[6])?;
        let same_result = staged.op2(Op2::And, same_trace, same_outcome)?;
        let specification_implication = staged.op2(Op2::Imp, specification_both, same_result)?;
        let specification_direct = quantify_forall(
            &mut staged,
            types.bool_ty,
            &variables,
            specification_implication,
        )?;
        let specification_reduced =
            certify_curried_beta2(&mut staged, specification_deterministic_proposition)?;
        join_alpha_equivalent(&mut staged, specification_reduced, specification_direct).map_err(
            |_| KernelError::InvalidTheoremRule {
                rule: "refinement deterministic specification reduction",
            },
        )?;
        staged.convert_conclusions(
            deterministic,
            specification_deterministic_proposition,
            specification_direct,
        )?;
        let deterministic = specialize_universal_to(
            &mut staged,
            deterministic,
            &variables,
            specification_implication,
            "refinement deterministic specification specialization",
        )?;
        let deterministic =
            staged.expand_conclusion(deterministic, positive(specification_implication), None)?;

        let assumed = staged.identity(positive(implementation_both))?;
        let implementation_left_fact =
            staged.expand_conclusion(assumed, positive(implementation_both), Some(false))?;
        let implementation_right_fact =
            staged.expand_conclusion(assumed, positive(implementation_both), Some(true))?;
        let left_implication = staged.op2(Op2::Imp, implementation_left, specification_left)?;
        let left_inclusion = specialize_universal_to(
            &mut staged,
            inclusion,
            &left_arguments,
            left_implication,
            "refinement deterministic left inclusion specialization",
        )?;
        let left_inclusion =
            staged.expand_conclusion(left_inclusion, positive(left_implication), None)?;
        let specification_left_fact = staged.resolve(
            implementation_left_fact,
            left_inclusion,
            positive(implementation_left),
        )?;
        let right_implication = staged.op2(Op2::Imp, implementation_right, specification_right)?;
        let right_inclusion = specialize_universal_to(
            &mut staged,
            inclusion,
            &right_arguments,
            right_implication,
            "refinement deterministic right inclusion specialization",
        )?;
        let right_inclusion =
            staged.expand_conclusion(right_inclusion, positive(right_implication), None)?;
        let specification_right_fact = staged.resolve(
            implementation_right_fact,
            right_inclusion,
            positive(implementation_right),
        )?;
        let specification_both_fact = staged.and_right(
            specification_left_fact,
            specification_right_fact,
            positive(specification_both),
        )?;
        let same_result_fact = staged.resolve(
            specification_both_fact,
            deterministic,
            positive(specification_both),
        )?;
        staged.contract_theorem(same_result_fact)?;
        let implementation_implication = staged.op2(Op2::Imp, implementation_both, same_result)?;
        let proof = staged.imp_right(same_result_fact, positive(implementation_implication))?;
        staged.contract_theorem(proof)?;
        let (direct, proof) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &variables,
            implementation_implication,
            proof,
        )?;
        let implementation_deterministic =
            self.deterministic(&mut staged, profile, implementation)?;
        let implementation_reduced =
            certify_curried_beta2(&mut staged, implementation_deterministic)?;
        align_theorem_conclusion(
            &mut staged,
            proof,
            direct,
            implementation_reduced,
            "refinement deterministic result alignment",
        )?;
        staged.convert_conclusions(proof, implementation_reduced, implementation_deterministic)?;
        staged.contract_theorem(proof)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: implementation_deterministic,
            theorem: proof,
            holds: true,
        })
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

    /// Converts complete run equality into directional run refinement.
    ///
    /// Equality supplies both inclusion of every eligible run and the reverse
    /// existence transport required by progress-sensitive refinement. Every
    /// premise of `same_runs` remains visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless `same_runs` positively proves equality for the
    /// supplied modules, or checked equality, existential, universal,
    /// propositional, or alignment work fails. `kernel` is unchanged on
    /// failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn prove_same_runs_refines(
        self,
        kernel: &mut Kernel,
        same_runs: Evidence,
        profile: Ref,
        implementation: Ref,
        specification: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        let expected = self.same_runs(&mut staged, profile, implementation, specification)?;
        let theorem = align_evidence(&mut staged, same_runs, expected)?;
        let [expected_domain, _] = binary_children(&staged, expected)?;
        let domain_theorem = staged.expand_conclusion(theorem, positive(expected), Some(false))?;
        let runs_theorem = staged.expand_conclusion(theorem, positive(expected), Some(true))?;
        let implementation_graphs = self.run_graphs(&mut staged, profile, implementation)?;
        let specification_graphs = self.run_graphs(&mut staged, profile, specification)?;
        let first = staged.fresh_name(&[
            expected,
            implementation_graphs.runs,
            specification_graphs.runs,
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
        let domain_variables = [entry, inputs, host];
        let run_variables = [entry, inputs, host, trace, outcome];

        let mut pointwise = staged.ap_thm(runs_theorem, entry)?;
        for &argument in &run_variables[1..] {
            pointwise = staged.ap_thm(pointwise.theorem, argument)?;
        }
        let implementation_run = pointwise.left;
        let specification_run = pointwise.right;
        let implementation_fact = staged.identity(positive(implementation_run))?;
        let specification_fact = staged.eq_mp(pointwise.theorem, implementation_fact)?;
        let inclusion_implication = staged.op2(Op2::Imp, implementation_run, specification_run)?;
        let inclusion = staged.imp_right(specification_fact, positive(inclusion_implication))?;
        let (inclusion_formula, inclusion) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &run_variables,
            inclusion_implication,
            inclusion,
        )?;

        let implementation_exists = quantify_exists(
            &mut staged,
            types.bool_ty,
            &[trace, outcome],
            implementation_run,
        )?;
        let specification_exists = quantify_exists(
            &mut staged,
            types.bool_ty,
            &[trace, outcome],
            specification_run,
        )?;
        let assumed_specification = staged.identity(positive(specification_exists))?;
        let outer = open_exists(&mut staged, specification_exists)?;
        let opened = staged.copy_theorem(assumed_specification)?;
        staged.convert_conclusions(opened, specification_exists, outer.body)?;
        let inner = open_exists(&mut staged, outer.body)?;
        staged.convert_conclusions(opened, outer.body, inner.body)?;

        let mut witness_equality = staged.ap_thm(runs_theorem, entry)?;
        for &argument in &[inputs, host, outer.witness, inner.witness] {
            witness_equality = staged.ap_thm(witness_equality.theorem, argument)?;
        }
        align_theorem_conclusion(
            &mut staged,
            opened,
            inner.body,
            witness_equality.right,
            "same-runs refinement witness alignment",
        )?;
        let reversed = equality_symmetry(&mut staged, types.bool_ty, witness_equality.theorem)?;
        let implementation_witness = staged.eq_mp(reversed.theorem, opened)?;
        let implementation_at_trace = apply(
            &mut staged,
            implementation_graphs.runs,
            &[entry, inputs, host, outer.witness, outcome],
        )?;
        let inner_exists = introduce_exists(
            &mut staged,
            implementation_witness,
            outcome,
            implementation_at_trace,
            inner.witness,
        )?;
        let implementation_at_binders = apply(
            &mut staged,
            implementation_graphs.runs,
            &[entry, inputs, host, trace, outcome],
        )?;
        let implementation_outcomes = staged.exists_tm(outcome, implementation_at_binders)?;
        let outer_exists = introduce_exists(
            &mut staged,
            inner_exists.theorem,
            trace,
            implementation_outcomes,
            outer.witness,
        )?;
        align_theorem_conclusion(
            &mut staged,
            outer_exists.theorem,
            outer_exists.proposition,
            implementation_exists,
            "same-runs refinement progress witness alignment",
        )?;
        let progress_implication =
            staged.op2(Op2::Imp, specification_exists, implementation_exists)?;
        let progress = staged.imp_right(outer_exists.theorem, positive(progress_implication))?;
        let (progress_formula, progress) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &domain_variables,
            progress_implication,
            progress,
        )?;
        let behavior_formula = staged.op2(Op2::And, inclusion_formula, progress_formula)?;
        let behavior = staged
            .and_right(inclusion, progress, positive(behavior_formula))
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "same-runs refinement behavior conjunction",
            })?;
        let same_domain = staged.eq(
            types.bool_ty,
            implementation_graphs.domain,
            specification_graphs.domain,
        )?;
        align_theorem_conclusion(
            &mut staged,
            domain_theorem,
            expected_domain,
            same_domain,
            "same-runs refinement domain alignment",
        )?;
        let proposition = staged.op2(Op2::And, same_domain, behavior_formula)?;
        let result = staged
            .and_right(domain_theorem, behavior, positive(proposition))
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "same-runs refinement conjunction",
            })?;
        let canonical = self.refinement(&mut staged, profile, implementation, specification)?;
        align_theorem_conclusion(
            &mut staged,
            result,
            proposition,
            canonical,
            "same-runs to refinement alignment",
        )?;
        staged.contract_theorem(result)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem: result,
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
    pub fn prove_refinement_reflexive(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
    ) -> Result<Evidence, KernelError> {
        self.prove_refinement_reflexive_direct(kernel, profile, module)
    }

    /// Composes two checked run refinements.
    ///
    /// Every premise of both input proofs remains visible. Behavior inclusion
    /// composes forward, while progress composes from the final specification
    /// back through the intermediate implementation.
    ///
    /// # Errors
    ///
    /// Returns an error unless the evidence proves the two adjacent
    /// refinements, or a checked specialization, equality, propositional, or
    /// alignment operation fails. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    pub fn prove_refinement_transitive(
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
        let types = self.relation.types;
        let left_middle_refinement = self.refinement(&mut staged, profile, left, middle)?;
        let left_middle_theorem = align_evidence(&mut staged, left_middle, left_middle_refinement)?;
        let middle_right_refinement = self.refinement(&mut staged, profile, middle, right)?;
        let middle_right_theorem =
            align_evidence(&mut staged, middle_right, middle_right_refinement)?;
        let left_middle_domain = staged.expand_conclusion(
            left_middle_theorem,
            positive(left_middle_refinement),
            Some(false),
        )?;
        let left_middle_behavior = staged.expand_conclusion(
            left_middle_theorem,
            positive(left_middle_refinement),
            Some(true),
        )?;
        let middle_right_domain = staged.expand_conclusion(
            middle_right_theorem,
            positive(middle_right_refinement),
            Some(false),
        )?;
        let middle_right_behavior = staged.expand_conclusion(
            middle_right_theorem,
            positive(middle_right_refinement),
            Some(true),
        )?;
        let [_, left_middle_behavior_formula] = binary_children(&staged, left_middle_refinement)?;
        binary_children(&staged, left_middle_behavior_formula)?;
        let [_, middle_right_behavior_formula] = binary_children(&staged, middle_right_refinement)?;
        binary_children(&staged, middle_right_behavior_formula)?;
        let left_middle_subset = staged.expand_conclusion(
            left_middle_behavior,
            positive(left_middle_behavior_formula),
            Some(false),
        )?;
        let left_middle_progress = staged.expand_conclusion(
            left_middle_behavior,
            positive(left_middle_behavior_formula),
            Some(true),
        )?;
        let middle_right_subset = staged.expand_conclusion(
            middle_right_behavior,
            positive(middle_right_behavior_formula),
            Some(false),
        )?;
        let middle_right_progress = staged.expand_conclusion(
            middle_right_behavior,
            positive(middle_right_behavior_formula),
            Some(true),
        )?;

        let left_graphs = self.run_graphs(&mut staged, profile, left)?;
        let middle_graphs = self.run_graphs(&mut staged, profile, middle)?;
        let right_graphs = self.run_graphs(&mut staged, profile, right)?;
        let domain = equality_transitivity(
            &mut staged,
            types.bool_ty,
            left_middle_domain,
            middle_right_domain,
        )?;

        let first = staged.fresh_name(&[
            left_middle_refinement,
            middle_right_refinement,
            left_graphs.runs,
            middle_graphs.runs,
            right_graphs.runs,
        ])?;
        let entry = staged.tm_fv(first, types.entry)?;
        let inputs = staged.tm_fv(checked_name(first, 1)?, types.inputs)?;
        let host = staged.tm_fv(checked_name(first, 2)?, types.host)?;
        let trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let domain_variables = [entry, inputs, host];
        let run_variables = [entry, inputs, host, trace, outcome];
        let left_run = apply(&mut staged, left_graphs.runs, &run_variables)?;
        let middle_run = apply(&mut staged, middle_graphs.runs, &run_variables)?;
        let right_run = apply(&mut staged, right_graphs.runs, &run_variables)?;
        let left_middle_subset_implication = staged.op2(Op2::Imp, left_run, middle_run)?;
        let middle_right_subset_implication = staged.op2(Op2::Imp, middle_run, right_run)?;
        let left_middle_subset = specialize_universal_to(
            &mut staged,
            left_middle_subset,
            &run_variables,
            left_middle_subset_implication,
            "left-middle refinement inclusion",
        )?;
        let middle_right_subset = specialize_universal_to(
            &mut staged,
            middle_right_subset,
            &run_variables,
            middle_right_subset_implication,
            "middle-right refinement inclusion",
        )?;
        let left_middle_subset = staged.expand_conclusion(
            left_middle_subset,
            positive(left_middle_subset_implication),
            None,
        )?;
        let middle_right_subset = staged.expand_conclusion(
            middle_right_subset,
            positive(middle_right_subset_implication),
            None,
        )?;
        let assumed_left_run = staged.identity(positive(left_run))?;
        let left_to_middle = staged
            .resolve(assumed_left_run, left_middle_subset, positive(left_run))
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "run refinement inclusion application",
            })?;
        let subset_chain = staged
            .resolve(left_to_middle, middle_right_subset, positive(middle_run))
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "run refinement inclusion transitivity resolution",
            })?;
        let subset_implication = staged.op2(Op2::Imp, left_run, right_run)?;
        let subset = staged.imp_right(subset_chain, positive(subset_implication))?;
        let (subset_formula, subset) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &run_variables,
            subset_implication,
            subset,
        )?;

        let left_exists = quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], left_run)?;
        let middle_exists =
            quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], middle_run)?;
        let right_exists =
            quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], right_run)?;
        let left_middle_progress_implication = staged.op2(Op2::Imp, middle_exists, left_exists)?;
        let middle_right_progress_implication =
            staged.op2(Op2::Imp, right_exists, middle_exists)?;
        let left_middle_progress = specialize_universal_to(
            &mut staged,
            left_middle_progress,
            &domain_variables,
            left_middle_progress_implication,
            "left-middle refinement progress",
        )?;
        let middle_right_progress = specialize_universal_to(
            &mut staged,
            middle_right_progress,
            &domain_variables,
            middle_right_progress_implication,
            "middle-right refinement progress",
        )?;
        let left_middle_progress = staged.expand_conclusion(
            left_middle_progress,
            positive(left_middle_progress_implication),
            None,
        )?;
        let middle_right_progress = staged.expand_conclusion(
            middle_right_progress,
            positive(middle_right_progress_implication),
            None,
        )?;
        let assumed_right_exists = staged.identity(positive(right_exists))?;
        let right_to_middle = staged
            .resolve(
                assumed_right_exists,
                middle_right_progress,
                positive(right_exists),
            )
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "run refinement progress application",
            })?;
        let progress_chain = staged
            .resolve(
                right_to_middle,
                left_middle_progress,
                positive(middle_exists),
            )
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "run refinement progress transitivity resolution",
            })?;
        let progress_implication = staged.op2(Op2::Imp, right_exists, left_exists)?;
        let progress = staged.imp_right(progress_chain, positive(progress_implication))?;
        let (progress_formula, progress) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &domain_variables,
            progress_implication,
            progress,
        )?;
        let behavior_formula = staged.op2(Op2::And, subset_formula, progress_formula)?;
        let behavior = staged.and_right(subset, progress, positive(behavior_formula))?;
        let proposition = staged.op2(Op2::And, domain.equality, behavior_formula)?;
        let theorem = staged.and_right(domain.theorem, behavior, positive(proposition))?;
        let canonical = self.refinement(&mut staged, profile, left, right)?;
        align_theorem_conclusion(
            &mut staged,
            theorem,
            proposition,
            canonical,
            "run refinement transitivity alignment",
        )?;
        staged.contract_theorem(theorem)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem,
            holds: true,
        })
    }

    #[allow(clippy::too_many_lines)]
    fn prove_refinement_reflexive_direct(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
    ) -> Result<Evidence, KernelError> {
        let mut staged = kernel.fork();
        let types = self.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        require_classifier(&mut staged, module, types.module)?;
        let graph = self.run_graphs(&mut staged, profile, module)?;
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
        let same_domain = staged.eq(types.bool_ty, graph.domain, graph.domain)?;
        let same_domain_fact = staged.refl(types.bool_ty, graph.domain)?;
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
        let run = apply(
            &mut staged,
            graph.runs,
            &[entry, inputs, host, trace, outcome],
        )?;
        let behavior = staged.op2(Op2::Imp, run, run)?;
        let identity = staged.identity(positive(run))?;
        let behavior_theorem = staged.imp_right(identity, positive(behavior))?;
        let (behavior, behavior_theorem) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &run_variables,
            behavior,
            behavior_theorem,
        )?;
        let exists_run = quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], run)?;
        let progress = staged.op2(Op2::Imp, exists_run, exists_run)?;
        let assumed = staged.identity(positive(exists_run))?;
        let progress_theorem = staged.imp_right(assumed, positive(progress))?;
        let (progress, progress_theorem) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &domain_variables,
            progress,
            progress_theorem,
        )?;
        let combined = staged.op2(Op2::And, behavior, progress)?;
        let behavior_theorem =
            staged.and_right(behavior_theorem, progress_theorem, positive(combined))?;
        let behavior = combined;
        let proposition = staged.op2(Op2::And, same_domain, behavior)?;
        let theorem = staged.and_right(
            same_domain_fact.theorem,
            behavior_theorem,
            positive(proposition),
        )?;
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
        let left_graphs = self.run_graphs(&mut staged, profile, left)?;
        let right_graphs = self.run_graphs(&mut staged, profile, right)?;
        let same_domain = staged.eq(types.bool_ty, left_graphs.domain, right_graphs.domain)?;
        let left_run = apply(
            &mut staged,
            left_graphs.runs,
            &[entry, inputs, host, trace, outcome],
        )?;
        let right_run = apply(
            &mut staged,
            right_graphs.runs,
            &[entry, inputs, host, trace, outcome],
        )?;
        let behavior = staged.op2(Op2::Imp, left_run, right_run)?;
        let behavior = quantify_forall(&mut staged, types.bool_ty, &run_variables, behavior)?;
        let implementation_runs =
            quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], left_run)?;
        let specification_runs =
            quantify_exists(&mut staged, types.bool_ty, &[trace, outcome], right_run)?;
        let progress = staged.op2(Op2::Imp, specification_runs, implementation_runs)?;
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

/// Direction in which a behavior proposition is preserved by refinement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RefinementDirection {
    /// Evidence about the implementation yields evidence about its
    /// specification. This is the variance of existential counterexamples.
    ImplementationToSpecification,
    /// Evidence about the specification yields evidence about its refining
    /// implementation. This is the variance of safety and total correctness.
    SpecificationToImplementation,
}

impl BehaviorQuantifier {
    /// Returns which side supplies a behavior premise and which side receives
    /// the checked conclusion under run refinement.
    #[must_use]
    pub const fn refinement_direction(self) -> RefinementDirection {
        match self {
            Self::May => RefinementDirection::ImplementationToSpecification,
            Self::Every | Self::Must | Self::Never => {
                RefinementDirection::SpecificationToImplementation
            }
        }
    }
}

/// An immutable proposition schema over one complete run graph.
///
/// The checked property has shape
/// `admissible-characteristic -> run-characteristic -> bool`. Consequently
/// equality of both characteristics preserves every `RunProperty` by ordinary
/// HOL congruence, without teaching the API about each property family.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunProperty {
    domain: RunDomain,
    property: Ref,
}

impl RunProperty {
    /// Returns the execution domain consumed by this property.
    #[must_use]
    pub const fn domain(self) -> RunDomain {
        self.domain
    }

    /// Returns the checked characteristic-function observer.
    #[must_use]
    pub const fn property(self) -> Ref {
        self.property
    }

    /// Constructs the pointwise negation of this run property.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application, negation, or abstraction
    /// fails. `kernel` is unchanged on failure.
    pub fn negate(self, kernel: &mut Kernel) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let (domain, runs) = property_variables(&mut staged, self.domain, &[self.property])?;
        let value = apply(&mut staged, self.property, &[domain, runs])?;
        let body = staged.op1(Op1::Not, value)?;
        let property = abstract_property(&mut staged, self.domain, domain, runs, body)?;
        let property = self.domain.property(&mut staged, property)?;
        *kernel = staged;
        Ok(property)
    }

    /// Constructs pointwise conjunction with another run property.
    ///
    /// # Errors
    ///
    /// Returns [`RunCompositionError::DomainMismatch`] unless both properties
    /// belong to the same run domain, or if checked HOL construction fails.
    /// `kernel` is unchanged on failure.
    pub fn and(self, kernel: &mut Kernel, other: Self) -> Result<Self, RunCompositionError> {
        self.combine(kernel, other, Op2::And)
    }

    /// Constructs pointwise disjunction with another run property.
    ///
    /// # Errors
    ///
    /// Returns under the same conditions as [`Self::and`].
    pub fn or(self, kernel: &mut Kernel, other: Self) -> Result<Self, RunCompositionError> {
        self.combine(kernel, other, Op2::Or)
    }

    /// Constructs pointwise implication to another run property.
    ///
    /// This is useful for reusable semantic contracts: the resulting property
    /// says that whenever the antecedent holds of a complete run graph, the
    /// consequent does too.
    ///
    /// # Errors
    ///
    /// Returns under the same conditions as [`Self::and`].
    pub fn implies(
        self,
        kernel: &mut Kernel,
        consequent: Self,
    ) -> Result<Self, RunCompositionError> {
        self.combine(kernel, consequent, Op2::Imp)
    }

    /// Constructs pointwise logical equivalence with another run property.
    ///
    /// The encoding is the conjunction of both implications, so it requires
    /// no additional logical primitive or trusted rule.
    ///
    /// # Errors
    ///
    /// Returns under the same conditions as [`Self::and`]. `kernel` is
    /// unchanged on failure.
    pub fn iff(self, kernel: &mut Kernel, other: Self) -> Result<Self, RunCompositionError> {
        let mut staged = kernel.fork();
        let forward = self.implies(&mut staged, other)?;
        let reverse = other.implies(&mut staged, self)?;
        let equivalent = forward.and(&mut staged, reverse)?;
        *kernel = staged;
        Ok(equivalent)
    }

    fn combine(
        self,
        kernel: &mut Kernel,
        other: Self,
        operation: Op2,
    ) -> Result<Self, RunCompositionError> {
        if self.domain != other.domain {
            return Err(RunCompositionError::DomainMismatch);
        }
        let mut staged = kernel.fork();
        let (domain, runs) =
            property_variables(&mut staged, self.domain, &[self.property, other.property])?;
        let left = apply(&mut staged, self.property, &[domain, runs])?;
        let right = apply(&mut staged, other.property, &[domain, runs])?;
        let body = staged.op2(operation, left, right)?;
        let property = abstract_property(&mut staged, self.domain, domain, runs, body)?;
        let property = self.domain.property(&mut staged, property)?;
        *kernel = staged;
        Ok(property)
    }

    /// Constructs this property for one profile and module.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible profile/module terms or a rejected
    /// checked application. `kernel` is unchanged on failure.
    pub fn proposition(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
    ) -> Result<Ref, KernelError> {
        self.proposition_avoiding(kernel, profile, module, &[])
    }

    fn proposition_avoiding(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        module: Ref,
        _avoiding: &[Ref],
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let graphs = self.domain.run_graphs(&mut staged, profile, module)?;
        let proposition = apply(&mut staged, self.property, &[graphs.domain, graphs.runs])?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs `module -> bool` for one profile.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::proposition`] or
    /// if checked abstraction fails. `kernel` is unchanged on failure.
    pub fn predicate(self, kernel: &mut Kernel, profile: Ref) -> Result<Ref, KernelError> {
        self.predicate_avoiding(kernel, profile, &[])
    }

    fn predicate_avoiding(
        self,
        kernel: &mut Kernel,
        profile: Ref,
        avoiding: &[Ref],
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        let mut roots = vec![types.module, types.bool_ty, self.property, profile];
        roots.extend_from_slice(avoiding);
        let module = staged.tm_fv(staged.fresh_name(&roots)?, types.module)?;
        let body = self.proposition_avoiding(&mut staged, profile, module, avoiding)?;
        let predicate_ty = staged.ty_arr(types.module, types.bool_ty)?;
        let predicate = staged.lam_at(predicate_ty, module, body)?;
        *kernel = staged;
        Ok(predicate)
    }

    /// Proves that `same_runs` preserves this property.
    ///
    /// Every premise in `same_runs` evidence remains visible. The derivation
    /// uses checked congruence for each characteristic argument followed by
    /// equality transitivity.
    ///
    /// # Errors
    ///
    /// Returns an error unless `same_runs` positively proves equality for the
    /// supplied modules, or a checked equality/congruence operation fails.
    /// `kernel` is unchanged on failure.
    pub fn prove_same_runs_preserves(
        self,
        kernel: &mut Kernel,
        same_runs: Evidence,
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
        let by_domain_function = staged.ap_term(domain_fact, self.property)?;
        let by_domain = staged.ap_thm(by_domain_function.theorem, left_graphs.runs)?;
        let right_domain_property = staged.app(self.property, right_graphs.domain)?;
        let by_runs = staged.ap_term(runs_fact, right_domain_property)?;
        let preserved = equality_transitivity(
            &mut staged,
            self.domain.relation.types.bool_ty,
            by_domain.theorem,
            by_runs.theorem,
        )?;
        let left_property = self.proposition(&mut staged, profile, left)?;
        let right_property = self.proposition(&mut staged, profile, right)?;
        let target = staged.eq(
            self.domain.relation.types.bool_ty,
            left_property,
            right_property,
        )?;
        align_theorem_conclusion(
            &mut staged,
            preserved.theorem,
            preserved.equality,
            target,
            "same-runs property preservation alignment",
        )?;
        staged.contract_theorem(preserved.theorem)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: target,
            theorem: preserved.theorem,
            holds: true,
        })
    }
}

/// An observation over one eventful execution relation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunObservation {
    domain: RunDomain,
    observe: Ref,
}

/// Failure to compose run observations or properties.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RunCompositionError {
    /// A checked HOL construction failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Binary schemas came from different execution domains.
    #[snafu(display("cannot combine schemas from different run domains"))]
    DomainMismatch,
}

/// Backwards-compatible name for behavior-observation composition failures.
pub type RunObservationError = RunCompositionError;

impl RunObservation {
    /// Transports a behavior proposition in its sound refinement direction.
    ///
    /// `behavior` must concern the implementation for [`BehaviorQuantifier::May`]
    /// and the specification for `Every`, `Must`, and `Never`. The conclusion
    /// concerns the opposite side. [`BehaviorQuantifier::refinement_direction`]
    /// exposes that choice without requiring callers to duplicate it.
    ///
    /// # Errors
    ///
    /// Returns an error unless `refinement` proves that `implementation`
    /// refines `specification`, `behavior` proves the selected quantifier on
    /// the required side, and the corresponding checked derivation succeeds.
    /// `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_refinement_preserves(
        self,
        kernel: &mut Kernel,
        refinement: Evidence,
        behavior: Evidence,
        quantifier: BehaviorQuantifier,
        profile: Ref,
        implementation: Ref,
        specification: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let preserved = match quantifier {
            BehaviorQuantifier::May => self.prove_refinement_preserves_may(
                &mut staged,
                refinement,
                behavior,
                profile,
                implementation,
                specification,
            )?,
            BehaviorQuantifier::Every => self.prove_refinement_preserves_every(
                &mut staged,
                refinement,
                behavior,
                profile,
                implementation,
                specification,
            )?,
            BehaviorQuantifier::Must => self.prove_refinement_preserves_must(
                &mut staged,
                refinement,
                behavior,
                profile,
                implementation,
                specification,
            )?,
            BehaviorQuantifier::Never => self.prove_refinement_preserves_never(
                &mut staged,
                refinement,
                behavior,
                profile,
                implementation,
                specification,
            )?,
        };
        *kernel = staged;
        Ok(preserved)
    }

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

    /// Constructs the generic run property for one behavior quantifier.
    ///
    /// # Errors
    ///
    /// Returns an error if checked characteristic-function abstraction or
    /// property validation fails. `kernel` is unchanged on failure.
    pub fn property(
        self,
        kernel: &mut Kernel,
        quantifier: BehaviorQuantifier,
    ) -> Result<RunProperty, KernelError> {
        self.property_avoiding(kernel, quantifier, &[])
    }

    fn property_avoiding(
        self,
        kernel: &mut Kernel,
        quantifier: BehaviorQuantifier,
        avoiding: &[Ref],
    ) -> Result<RunProperty, KernelError> {
        let mut staged = kernel.fork();
        let property = self.graph_observer(&mut staged, quantifier, avoiding)?;
        let property = self.domain.property(&mut staged, property)?;
        *kernel = staged;
        Ok(property)
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
        let mut roots = Vec::with_capacity(avoiding.len() + 2);
        roots.extend_from_slice(avoiding);
        roots.extend([profile, module]);
        let property = self.property_avoiding(&mut staged, quantifier, &roots)?;
        let proposition = property.proposition(&mut staged, profile, module)?;
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
        let property = self.property(&mut staged, quantifier)?;
        let preserved =
            property.prove_same_runs_preserves(&mut staged, same_runs, profile, left, right)?;
        *kernel = staged;
        Ok(preserved)
    }

    /// Transports an existential behavior from an implementation to a
    /// specification it refines.
    ///
    /// The concrete execution witnesses are opened from `implementation_may`,
    /// transported through refinement's run inclusion, and reintroduced for
    /// the specification. Premises from both evidence values remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless `refinement` proves the displayed directional
    /// refinement, `implementation_may` proves this observation's existential
    /// behavior for the implementation, and every checked specialization,
    /// existential, propositional, or alignment step succeeds. `kernel` is
    /// unchanged on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn prove_refinement_preserves_may(
        self,
        kernel: &mut Kernel,
        refinement: Evidence,
        implementation_may: Evidence,
        profile: Ref,
        implementation: Ref,
        specification: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        let expected_refinement =
            self.domain
                .refines_runs(&mut staged, profile, implementation, specification)?;
        let refinement_theorem = align_evidence(&mut staged, refinement, expected_refinement)?;
        let refinement_behavior = staged
            .expand_conclusion(
                refinement_theorem,
                positive(expected_refinement),
                Some(true),
            )
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "refinement may behavior projection",
            })?;
        let [_, behavior_formula] = binary_children(&staged, expected_refinement)?;
        binary_children(&staged, behavior_formula)?;
        let inclusion = staged
            .expand_conclusion(refinement_behavior, positive(behavior_formula), Some(false))
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "refinement may inclusion projection",
            })?;

        let implementation_proposition = self.may(&mut staged, profile, implementation)?;
        let implementation_theorem =
            align_evidence(&mut staged, implementation_may, implementation_proposition)?;
        let implementation_graphs = self
            .domain
            .run_graphs(&mut staged, profile, implementation)?;
        let implementation_direct = self.graph_proposition(
            &mut staged,
            BehaviorQuantifier::May,
            implementation_graphs.domain,
            implementation_graphs.runs,
            &[],
        )?;
        let implementation_reduced =
            certify_curried_beta2(&mut staged, implementation_proposition)?;
        join_alpha_equivalent(&mut staged, implementation_reduced, implementation_direct).map_err(
            |_| KernelError::InvalidTheoremRule {
                rule: "refinement may property reduction",
            },
        )?;
        staged.convert_conclusions(
            implementation_theorem,
            implementation_proposition,
            implementation_direct,
        )?;
        let mut opened_formula = implementation_direct;
        let mut witnesses = Vec::with_capacity(5);
        for _ in 0..5 {
            let opened = open_exists(&mut staged, opened_formula)?;
            staged.convert_conclusions(implementation_theorem, opened_formula, opened.body)?;
            witnesses.push(opened.witness);
            opened_formula = opened.body;
        }
        let implementation_run = staged
            .arena()
            .children(opened_formula)
            .and_then(|children| children.collect::<Vec<_>>().first().copied())
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "refinement may witness conjunction",
            })?;
        let implementation_run_fact = staged
            .expand_conclusion(
                implementation_theorem,
                positive(opened_formula),
                Some(false),
            )
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "refinement may run projection",
            })?;
        let observation_fact = staged
            .expand_conclusion(implementation_theorem, positive(opened_formula), Some(true))
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "refinement may observation projection",
            })?;

        let specification_graphs = self
            .domain
            .run_graphs(&mut staged, profile, specification)?;
        let implementation_run_expected =
            apply(&mut staged, implementation_graphs.runs, &witnesses)?;
        align_theorem_conclusion(
            &mut staged,
            implementation_run_fact,
            implementation_run,
            implementation_run_expected,
            "refinement may implementation-run alignment",
        )?;
        let specification_run = apply(&mut staged, specification_graphs.runs, &witnesses)?;
        let inclusion_at_witness =
            staged.op2(Op2::Imp, implementation_run_expected, specification_run)?;
        let inclusion = specialize_universal_to(
            &mut staged,
            inclusion,
            &witnesses,
            inclusion_at_witness,
            "refinement may inclusion specialization",
        )?;
        let inclusion = staged
            .expand_conclusion(inclusion, positive(inclusion_at_witness), None)
            .map_err(|_| KernelError::InvalidTheoremRule {
                rule: "refinement may implication expansion",
            })?;
        let specification_run_fact = staged.resolve(
            implementation_run_fact,
            inclusion,
            positive(implementation_run_expected),
        )?;
        let observed = apply(&mut staged, self.observe, &[witnesses[3], witnesses[4]])?;
        let source_observed = binary_children(&staged, opened_formula)?[1];
        align_theorem_conclusion(
            &mut staged,
            observation_fact,
            source_observed,
            observed,
            "refinement may observation alignment",
        )?;
        let specification_body = staged.op2(Op2::And, specification_run, observed)?;
        let mut proof = staged.and_right(
            specification_run_fact,
            observation_fact,
            positive(specification_body),
        )?;
        let mut proved_proposition = specification_body;

        let mut binder_roots = vec![
            expected_refinement,
            implementation_proposition,
            specification_body,
            implementation_graphs.runs,
            specification_graphs.runs,
            self.observe,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
        ];
        binder_roots.extend_from_slice(&witnesses);
        let binder_name = staged.fresh_name(&binder_roots)?;
        let binders = [
            staged.tm_fv(binder_name, types.entry)?,
            staged.tm_fv(checked_name(binder_name, 1)?, types.inputs)?,
            staged.tm_fv(checked_name(binder_name, 2)?, types.host)?,
            staged.tm_fv(checked_name(binder_name, 3)?, types.trace)?,
            staged.tm_fv(checked_name(binder_name, 4)?, types.outcome)?,
        ];
        for index in (0..5).rev() {
            let arguments: [Ref; 5] = std::array::from_fn(|candidate| {
                if candidate < index {
                    witnesses[candidate]
                } else {
                    binders[candidate]
                }
            });
            let run = apply(&mut staged, specification_graphs.runs, &arguments)?;
            let observed = apply(&mut staged, self.observe, &[arguments[3], arguments[4]])?;
            let mut body = staged.op2(Op2::And, run, observed)?;
            for &later in binders[index + 1..].iter().rev() {
                body = staged.exists_tm(later, body)?;
            }
            let introduced =
                introduce_exists(&mut staged, proof, binders[index], body, witnesses[index])
                    .map_err(|_| KernelError::InvalidTheoremRule {
                        rule: [
                            "refinement may introduce entry",
                            "refinement may introduce inputs",
                            "refinement may introduce host",
                            "refinement may introduce trace",
                            "refinement may introduce outcome",
                        ][index],
                    })?;
            proof = introduced.theorem;
            proved_proposition = introduced.proposition;
        }
        let specification_proposition = self.may(&mut staged, profile, specification)?;
        let specification_reduced = certify_curried_beta2(&mut staged, specification_proposition)?;
        align_theorem_conclusion(
            &mut staged,
            proof,
            proved_proposition,
            specification_reduced,
            "refinement may final alignment",
        )?;
        staged.convert_conclusions(proof, specification_reduced, specification_proposition)?;
        staged.contract_theorem(proof)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: specification_proposition,
            theorem: proof,
            holds: true,
        })
    }

    /// Transports universal absence from a specification to an implementation.
    ///
    /// This is the checked contrapositive of
    /// [`Self::prove_refinement_preserves_may`]: an implementation witness
    /// would transport to a forbidden specification witness. Premises from
    /// both refinement and the specification's `never` proof remain visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless `refinement` proves the displayed directional
    /// refinement, `specification_never` positively proves this observation's
    /// `never` proposition for the specification, and every checked transport,
    /// negation, resolution, or alignment step succeeds. `kernel` is unchanged
    /// on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn prove_refinement_preserves_never(
        self,
        kernel: &mut Kernel,
        refinement: Evidence,
        specification_never: Evidence,
        profile: Ref,
        implementation: Ref,
        specification: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let implementation_graphs = self
            .domain
            .run_graphs(&mut staged, profile, implementation)?;
        let specification_graphs = self
            .domain
            .run_graphs(&mut staged, profile, specification)?;
        let implementation_may = self.may(&mut staged, profile, implementation)?;
        let implementation_may_direct = self.graph_proposition(
            &mut staged,
            BehaviorQuantifier::May,
            implementation_graphs.domain,
            implementation_graphs.runs,
            &[],
        )?;
        let implementation_may_reduced = certify_curried_beta2(&mut staged, implementation_may)?;
        join_alpha_equivalent(
            &mut staged,
            implementation_may_reduced,
            implementation_may_direct,
        )
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "refinement never implementation-may reduction",
        })?;
        let assumed_direct = staged.identity(positive(implementation_may_direct))?;
        staged.convert_conclusions(
            assumed_direct,
            implementation_may_direct,
            implementation_may,
        )?;
        let transported = self.prove_refinement_preserves_may(
            &mut staged,
            refinement,
            Evidence {
                proposition: implementation_may,
                theorem: assumed_direct,
                holds: true,
            },
            profile,
            implementation,
            specification,
        )?;

        let specification_may_direct = self.graph_proposition(
            &mut staged,
            BehaviorQuantifier::May,
            specification_graphs.domain,
            specification_graphs.runs,
            &[],
        )?;
        let specification_may_reduced =
            certify_curried_beta2(&mut staged, transported.proposition)?;
        join_alpha_equivalent(
            &mut staged,
            specification_may_reduced,
            specification_may_direct,
        )
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "refinement never specification-may reduction",
        })?;
        staged.convert_conclusions(
            transported.theorem,
            transported.proposition,
            specification_may_direct,
        )?;

        let specification_never_proposition = self.never(&mut staged, profile, specification)?;
        let denied = align_evidence(
            &mut staged,
            specification_never,
            specification_never_proposition,
        )?;
        let specification_never_direct = self.graph_proposition(
            &mut staged,
            BehaviorQuantifier::Never,
            specification_graphs.domain,
            specification_graphs.runs,
            &[],
        )?;
        let specification_never_reduced =
            certify_curried_beta2(&mut staged, specification_never_proposition)?;
        join_alpha_equivalent(
            &mut staged,
            specification_never_reduced,
            specification_never_direct,
        )
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "refinement never specification reduction",
        })?;
        staged.convert_conclusions(
            denied,
            specification_never_proposition,
            specification_never_direct,
        )?;
        let denied_may = staged.flatten_conclusion(denied, positive(specification_never_direct))?;
        let denied_may_formula = staged
            .arena()
            .children(specification_never_direct)
            .and_then(|mut children| children.next())
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "refinement never negation body",
            })?;
        align_theorem_conclusion(
            &mut staged,
            denied_may,
            denied_may_formula,
            specification_may_direct,
            "refinement never denied-may alignment",
        )?;
        let contradiction = staged.resolve(
            transported.theorem,
            denied_may,
            positive(specification_may_direct),
        )?;
        staged.not_right(contradiction, positive(implementation_may_direct))?;

        let implementation_never_direct = self.graph_proposition(
            &mut staged,
            BehaviorQuantifier::Never,
            implementation_graphs.domain,
            implementation_graphs.runs,
            &[],
        )?;
        let implementation_never_body = staged
            .arena()
            .children(implementation_never_direct)
            .and_then(|mut children| children.next())
            .ok_or(KernelError::InvalidTheoremRule {
                rule: "refinement never implementation negation body",
            })?;
        join_alpha_equivalent(
            &mut staged,
            implementation_never_body,
            implementation_may_direct,
        )
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "refinement never implementation-may alignment",
        })?;
        staged.convert_conclusions(
            contradiction,
            implementation_may_direct,
            implementation_never_body,
        )?;
        let proof = staged.fold_conclusion(contradiction, positive(implementation_never_direct))?;
        let implementation_never = self.never(&mut staged, profile, implementation)?;
        let implementation_never_reduced =
            certify_curried_beta2(&mut staged, implementation_never)?;
        join_alpha_equivalent(
            &mut staged,
            implementation_never_reduced,
            implementation_never_direct,
        )
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "refinement never result reduction",
        })?;
        staged.convert_conclusions(proof, implementation_never_direct, implementation_never)?;
        staged.contract_theorem(proof)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: implementation_never,
            theorem: proof,
            holds: true,
        })
    }

    /// Transports a universal behavior property from a specification to an
    /// implementation that refines it.
    ///
    /// Every implementation run is first transported through refinement's
    /// inclusion theorem and then discharged by the specification's `every`
    /// proof. This theorem is deliberately progress-neutral; use `must` when
    /// existence of executions is also required.
    ///
    /// # Errors
    ///
    /// Returns an error unless `refinement` proves the displayed directional
    /// refinement, `specification_every` positively proves this observation's
    /// `every` proposition for the specification, and every checked
    /// specialization, propositional, or alignment step succeeds. `kernel` is
    /// unchanged on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn prove_refinement_preserves_every(
        self,
        kernel: &mut Kernel,
        refinement: Evidence,
        specification_every: Evidence,
        profile: Ref,
        implementation: Ref,
        specification: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        let expected_refinement =
            self.domain
                .refines_runs(&mut staged, profile, implementation, specification)?;
        let refinement_theorem = align_evidence(&mut staged, refinement, expected_refinement)?;
        let refinement_behavior = staged.expand_conclusion(
            refinement_theorem,
            positive(expected_refinement),
            Some(true),
        )?;
        let [_, behavior_formula] = binary_children(&staged, expected_refinement)?;
        binary_children(&staged, behavior_formula)?;
        let inclusion = staged.expand_conclusion(
            refinement_behavior,
            positive(behavior_formula),
            Some(false),
        )?;

        let implementation_graphs = self
            .domain
            .run_graphs(&mut staged, profile, implementation)?;
        let specification_graphs = self
            .domain
            .run_graphs(&mut staged, profile, specification)?;
        let specification_every_proposition = self.every(&mut staged, profile, specification)?;
        let every = align_evidence(
            &mut staged,
            specification_every,
            specification_every_proposition,
        )?;
        let specification_every_direct = self.graph_proposition(
            &mut staged,
            BehaviorQuantifier::Every,
            specification_graphs.domain,
            specification_graphs.runs,
            &[],
        )?;
        let specification_every_reduced =
            certify_curried_beta2(&mut staged, specification_every_proposition)?;
        join_alpha_equivalent(
            &mut staged,
            specification_every_reduced,
            specification_every_direct,
        )
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "refinement every specification reduction",
        })?;
        staged.convert_conclusions(
            every,
            specification_every_proposition,
            specification_every_direct,
        )?;

        let first = staged.fresh_name(&[
            expected_refinement,
            specification_every_direct,
            implementation_graphs.runs,
            specification_graphs.runs,
            self.observe,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
        ])?;
        let variables = [
            staged.tm_fv(first, types.entry)?,
            staged.tm_fv(checked_name(first, 1)?, types.inputs)?,
            staged.tm_fv(checked_name(first, 2)?, types.host)?,
            staged.tm_fv(checked_name(first, 3)?, types.trace)?,
            staged.tm_fv(checked_name(first, 4)?, types.outcome)?,
        ];
        let implementation_run = apply(&mut staged, implementation_graphs.runs, &variables)?;
        let specification_run = apply(&mut staged, specification_graphs.runs, &variables)?;
        let observed = apply(&mut staged, self.observe, &[variables[3], variables[4]])?;
        let inclusion_implication = staged.op2(Op2::Imp, implementation_run, specification_run)?;
        let inclusion = specialize_universal_to(
            &mut staged,
            inclusion,
            &variables,
            inclusion_implication,
            "refinement every inclusion specialization",
        )?;
        let inclusion =
            staged.expand_conclusion(inclusion, positive(inclusion_implication), None)?;
        let every_implication = staged.op2(Op2::Imp, specification_run, observed)?;
        let every = specialize_universal_to(
            &mut staged,
            every,
            &variables,
            every_implication,
            "refinement every specification specialization",
        )?;
        let every = staged.expand_conclusion(every, positive(every_implication), None)?;
        let assumed = staged.identity(positive(implementation_run))?;
        let specification_run_fact =
            staged.resolve(assumed, inclusion, positive(implementation_run))?;
        let observed_fact =
            staged.resolve(specification_run_fact, every, positive(specification_run))?;
        let implication = staged.op2(Op2::Imp, implementation_run, observed)?;
        let proof = staged.imp_right(observed_fact, positive(implication))?;
        let (direct, proof) =
            introduce_forall(&mut staged, types.bool_ty, &variables, implication, proof)?;

        let implementation_every = self.every(&mut staged, profile, implementation)?;
        let implementation_every_reduced =
            certify_curried_beta2(&mut staged, implementation_every)?;
        align_theorem_conclusion(
            &mut staged,
            proof,
            direct,
            implementation_every_reduced,
            "refinement every result alignment",
        )?;
        staged.convert_conclusions(proof, implementation_every_reduced, implementation_every)?;
        staged.contract_theorem(proof)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: implementation_every,
            theorem: proof,
            holds: true,
        })
    }

    /// Transports a non-vacuous universal behavior property from a
    /// specification to an implementation that refines it.
    ///
    /// Refinement transports the specification's progress witness back to an
    /// implementation run and transports that run forward again to establish
    /// the observation. Run inclusion also preserves the universal part.
    /// Consequently both existence and safety are retained for every
    /// admissible invocation.
    ///
    /// # Errors
    ///
    /// Returns an error unless `refinement` proves the displayed directional
    /// refinement, `specification_must` positively proves this observation's
    /// `must` proposition for the specification, and every checked equality,
    /// existential, universal, propositional, or alignment step succeeds.
    /// `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
    fn prove_refinement_preserves_must(
        self,
        kernel: &mut Kernel,
        refinement: Evidence,
        specification_must: Evidence,
        profile: Ref,
        implementation: Ref,
        specification: Ref,
    ) -> Result<Evidence, RunProofError> {
        let mut staged = kernel.fork();
        let types = self.domain.relation.types;
        let expected_refinement =
            self.domain
                .refines_runs(&mut staged, profile, implementation, specification)?;
        let refinement_theorem = align_evidence(&mut staged, refinement, expected_refinement)?;
        let domain_equality = staged.expand_conclusion(
            refinement_theorem,
            positive(expected_refinement),
            Some(false),
        )?;
        let refinement_behavior = staged.expand_conclusion(
            refinement_theorem,
            positive(expected_refinement),
            Some(true),
        )?;
        let [_, behavior_formula] = binary_children(&staged, expected_refinement)?;
        binary_children(&staged, behavior_formula)?;
        let inclusion = staged.expand_conclusion(
            refinement_behavior,
            positive(behavior_formula),
            Some(false),
        )?;
        let progress = staged.expand_conclusion(
            refinement_behavior,
            positive(behavior_formula),
            Some(true),
        )?;

        let implementation_graphs = self
            .domain
            .run_graphs(&mut staged, profile, implementation)?;
        let specification_graphs = self
            .domain
            .run_graphs(&mut staged, profile, specification)?;
        let specification_must_proposition = self.must(&mut staged, profile, specification)?;
        let must = align_evidence(
            &mut staged,
            specification_must,
            specification_must_proposition,
        )?;
        let specification_must_direct = self.graph_proposition(
            &mut staged,
            BehaviorQuantifier::Must,
            specification_graphs.domain,
            specification_graphs.runs,
            &[],
        )?;
        let specification_must_reduced =
            certify_curried_beta2(&mut staged, specification_must_proposition)?;
        join_alpha_equivalent(
            &mut staged,
            specification_must_reduced,
            specification_must_direct,
        )
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "refinement must specification reduction",
        })?;
        staged.convert_conclusions(
            must,
            specification_must_proposition,
            specification_must_direct,
        )?;

        let first = staged.fresh_name(&[
            expected_refinement,
            specification_must_direct,
            implementation_graphs.domain,
            implementation_graphs.runs,
            specification_graphs.domain,
            specification_graphs.runs,
            self.observe,
            types.entry,
            types.inputs,
            types.host,
            types.trace,
            types.outcome,
        ])?;
        let invocation = [
            staged.tm_fv(first, types.entry)?,
            staged.tm_fv(checked_name(first, 1)?, types.inputs)?,
            staged.tm_fv(checked_name(first, 2)?, types.host)?,
        ];
        let trace = staged.tm_fv(checked_name(first, 3)?, types.trace)?;
        let outcome = staged.tm_fv(checked_name(first, 4)?, types.outcome)?;
        let run_variables = [invocation[0], invocation[1], invocation[2], trace, outcome];
        let implementation_allowed = apply(&mut staged, implementation_graphs.domain, &invocation)?;
        let specification_allowed = apply(&mut staged, specification_graphs.domain, &invocation)?;
        let mut allowed_equality = staged.ap_thm(domain_equality, invocation[0])?;
        for &argument in &invocation[1..] {
            allowed_equality = staged.ap_thm(allowed_equality.theorem, argument)?;
        }
        let allowed_target =
            staged.eq(types.bool_ty, implementation_allowed, specification_allowed)?;
        align_theorem_conclusion(
            &mut staged,
            allowed_equality.theorem,
            allowed_equality.equality,
            allowed_target,
            "refinement must admissibility alignment",
        )?;
        let assumed_allowed = staged.identity(positive(implementation_allowed))?;
        let specification_allowed_fact = staged.eq_mp(allowed_equality.theorem, assumed_allowed)?;

        let specification_run = apply(&mut staged, specification_graphs.runs, &run_variables)?;
        let implementation_run = apply(&mut staged, implementation_graphs.runs, &run_variables)?;
        let observed = apply(&mut staged, self.observe, &[trace, outcome])?;
        let specification_matching = staged.op2(Op2::And, specification_run, observed)?;
        let specification_exists_matching = quantify_exists(
            &mut staged,
            types.bool_ty,
            &[trace, outcome],
            specification_matching,
        )?;
        let specification_run_implies_observed =
            staged.op2(Op2::Imp, specification_run, observed)?;
        let specification_every = quantify_forall(
            &mut staged,
            types.bool_ty,
            &[trace, outcome],
            specification_run_implies_observed,
        )?;
        let specification_required =
            staged.op2(Op2::And, specification_exists_matching, specification_every)?;
        let specification_requirement =
            staged.op2(Op2::Imp, specification_allowed, specification_required)?;
        let must = specialize_universal_to(
            &mut staged,
            must,
            &invocation,
            specification_requirement,
            "refinement must specification specialization",
        )?;
        let must = staged.expand_conclusion(must, positive(specification_requirement), None)?;
        let required = staged.resolve(
            specification_allowed_fact,
            must,
            positive(specification_allowed),
        )?;
        let specification_matching_fact =
            staged.expand_conclusion(required, positive(specification_required), Some(false))?;
        let specification_every_fact =
            staged.expand_conclusion(required, positive(specification_required), Some(true))?;

        let outer_specification = open_exists(&mut staged, specification_exists_matching)?;
        staged.convert_conclusions(
            specification_matching_fact,
            specification_exists_matching,
            outer_specification.body,
        )?;
        let inner_specification = open_exists(&mut staged, outer_specification.body)?;
        staged.convert_conclusions(
            specification_matching_fact,
            outer_specification.body,
            inner_specification.body,
        )?;
        let specification_witness_run = apply(
            &mut staged,
            specification_graphs.runs,
            &[
                invocation[0],
                invocation[1],
                invocation[2],
                outer_specification.witness,
                inner_specification.witness,
            ],
        )?;
        let specification_witness_run_fact = staged.expand_conclusion(
            specification_matching_fact,
            positive(inner_specification.body),
            Some(false),
        )?;
        let source_specification_witness_run =
            binary_children(&staged, inner_specification.body)?[0];
        align_theorem_conclusion(
            &mut staged,
            specification_witness_run_fact,
            source_specification_witness_run,
            specification_witness_run,
            "refinement must specification witness alignment",
        )?;
        let specification_exists_run = quantify_exists(
            &mut staged,
            types.bool_ty,
            &[trace, outcome],
            specification_run,
        )?;
        let specification_at_trace = apply(
            &mut staged,
            specification_graphs.runs,
            &[
                invocation[0],
                invocation[1],
                invocation[2],
                outer_specification.witness,
                outcome,
            ],
        )?;
        let inner_exists = introduce_exists(
            &mut staged,
            specification_witness_run_fact,
            outcome,
            specification_at_trace,
            inner_specification.witness,
        )?;
        let specification_outcomes = staged.exists_tm(outcome, specification_run)?;
        let specification_exists = introduce_exists(
            &mut staged,
            inner_exists.theorem,
            trace,
            specification_outcomes,
            outer_specification.witness,
        )?;
        align_theorem_conclusion(
            &mut staged,
            specification_exists.theorem,
            specification_exists.proposition,
            specification_exists_run,
            "refinement must specification progress alignment",
        )?;

        let implementation_exists_run = quantify_exists(
            &mut staged,
            types.bool_ty,
            &[trace, outcome],
            implementation_run,
        )?;
        let progress_implication = staged.op2(
            Op2::Imp,
            specification_exists_run,
            implementation_exists_run,
        )?;
        let progress = specialize_universal_to(
            &mut staged,
            progress,
            &invocation,
            progress_implication,
            "refinement must progress specialization",
        )?;
        let progress = staged.expand_conclusion(progress, positive(progress_implication), None)?;
        let implementation_exists = staged.resolve(
            specification_exists.theorem,
            progress,
            positive(specification_exists_run),
        )?;
        let outer_implementation = open_exists(&mut staged, implementation_exists_run)?;
        staged.convert_conclusions(
            implementation_exists,
            implementation_exists_run,
            outer_implementation.body,
        )?;
        let inner_implementation = open_exists(&mut staged, outer_implementation.body)?;
        staged.convert_conclusions(
            implementation_exists,
            outer_implementation.body,
            inner_implementation.body,
        )?;
        let implementation_witness_run = apply(
            &mut staged,
            implementation_graphs.runs,
            &[
                invocation[0],
                invocation[1],
                invocation[2],
                outer_implementation.witness,
                inner_implementation.witness,
            ],
        )?;
        align_theorem_conclusion(
            &mut staged,
            implementation_exists,
            inner_implementation.body,
            implementation_witness_run,
            "refinement must implementation witness alignment",
        )?;
        let witness_variables = [
            invocation[0],
            invocation[1],
            invocation[2],
            outer_implementation.witness,
            inner_implementation.witness,
        ];
        let specification_witness_run =
            apply(&mut staged, specification_graphs.runs, &witness_variables)?;
        let inclusion_at_witness_formula = staged.op2(
            Op2::Imp,
            implementation_witness_run,
            specification_witness_run,
        )?;
        let inclusion_at_witness = specialize_universal_to(
            &mut staged,
            inclusion,
            &witness_variables,
            inclusion_at_witness_formula,
            "refinement must inclusion specialization",
        )?;
        let inclusion_at_witness = staged.expand_conclusion(
            inclusion_at_witness,
            positive(inclusion_at_witness_formula),
            None,
        )?;
        let specification_witness = staged.resolve(
            implementation_exists,
            inclusion_at_witness,
            positive(implementation_witness_run),
        )?;
        let witness_observed = apply(
            &mut staged,
            self.observe,
            &[outer_implementation.witness, inner_implementation.witness],
        )?;
        let every_at_witness_implication =
            staged.op2(Op2::Imp, specification_witness_run, witness_observed)?;
        let every_at_witness = specialize_universal_to(
            &mut staged,
            specification_every_fact,
            &[outer_implementation.witness, inner_implementation.witness],
            every_at_witness_implication,
            "refinement must observation specialization",
        )?;
        let every_at_witness = staged.expand_conclusion(
            every_at_witness,
            positive(every_at_witness_implication),
            None,
        )?;
        let witness_observed_fact = staged.resolve(
            specification_witness,
            every_at_witness,
            positive(specification_witness_run),
        )?;
        let implementation_matching =
            staged.op2(Op2::And, implementation_witness_run, witness_observed)?;
        let implementation_matching_fact = staged.and_right(
            implementation_exists,
            witness_observed_fact,
            positive(implementation_matching),
        )?;
        let implementation_at_trace = apply(
            &mut staged,
            implementation_graphs.runs,
            &[
                invocation[0],
                invocation[1],
                invocation[2],
                outer_implementation.witness,
                outcome,
            ],
        )?;
        let observed_at_trace = apply(
            &mut staged,
            self.observe,
            &[outer_implementation.witness, outcome],
        )?;
        let matching_at_trace = staged.op2(Op2::And, implementation_at_trace, observed_at_trace)?;
        let inner_matching = introduce_exists(
            &mut staged,
            implementation_matching_fact,
            outcome,
            matching_at_trace,
            inner_implementation.witness,
        )?;
        let implementation_matching_body = staged.op2(Op2::And, implementation_run, observed)?;
        let implementation_outcomes = staged.exists_tm(outcome, implementation_matching_body)?;
        let implementation_matching_exists = introduce_exists(
            &mut staged,
            inner_matching.theorem,
            trace,
            implementation_outcomes,
            outer_implementation.witness,
        )?;

        let inclusion_generic_implication =
            staged.op2(Op2::Imp, implementation_run, specification_run)?;
        let inclusion_generic = specialize_universal_to(
            &mut staged,
            inclusion,
            &run_variables,
            inclusion_generic_implication,
            "refinement must universal inclusion",
        )?;
        let inclusion_generic = staged.expand_conclusion(
            inclusion_generic,
            positive(inclusion_generic_implication),
            None,
        )?;
        let every_generic = specialize_universal_to(
            &mut staged,
            specification_every_fact,
            &[trace, outcome],
            specification_run_implies_observed,
            "refinement must universal observation",
        )?;
        let every_generic = staged.expand_conclusion(
            every_generic,
            positive(specification_run_implies_observed),
            None,
        )?;
        let assumed_run = staged.identity(positive(implementation_run))?;
        let specification_run_fact =
            staged.resolve(assumed_run, inclusion_generic, positive(implementation_run))?;
        let observed_fact = staged.resolve(
            specification_run_fact,
            every_generic,
            positive(specification_run),
        )?;
        let implementation_run_implies_observed =
            staged.op2(Op2::Imp, implementation_run, observed)?;
        let implementation_every =
            staged.imp_right(observed_fact, positive(implementation_run_implies_observed))?;
        let (implementation_every_formula, implementation_every) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &[trace, outcome],
            implementation_run_implies_observed,
            implementation_every,
        )
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "refinement must universal behavior introduction",
        })?;
        let implementation_required = staged.op2(
            Op2::And,
            implementation_matching_exists.proposition,
            implementation_every_formula,
        )?;
        let required = staged.and_right(
            implementation_matching_exists.theorem,
            implementation_every,
            positive(implementation_required),
        )?;
        staged.contract_theorem(required)?;
        let implementation_requirement =
            staged.op2(Op2::Imp, implementation_allowed, implementation_required)?;
        let requirement = staged.imp_right(required, positive(implementation_requirement))?;
        let (direct, proof) = introduce_forall(
            &mut staged,
            types.bool_ty,
            &invocation,
            implementation_requirement,
            requirement,
        )
        .map_err(|_| KernelError::InvalidTheoremRule {
            rule: "refinement must invocation introduction",
        })?;
        let implementation_must = self.must(&mut staged, profile, implementation)?;
        let implementation_must_reduced = certify_curried_beta2(&mut staged, implementation_must)?;
        align_theorem_conclusion(
            &mut staged,
            proof,
            direct,
            implementation_must_reduced,
            "refinement must result alignment",
        )?;
        staged.convert_conclusions(proof, implementation_must_reduced, implementation_must)?;
        staged.contract_theorem(proof)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: implementation_must,
            theorem: proof,
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
        let property = self.property_avoiding(&mut staged, quantifier, avoiding)?;
        let predicate = property.predicate_avoiding(&mut staged, profile, avoiding)?;
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
        let context = RunContext::new(&mut staged, self.domain, context_ty, plug, admissible)?;
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

fn property_variables(
    kernel: &mut Kernel,
    domain: RunDomain,
    properties: &[Ref],
) -> Result<(Ref, Ref), KernelError> {
    let mut roots = vec![
        domain.domain_ty,
        domain.run_graph_ty,
        domain.relation.types.bool_ty,
        domain.relation.runs,
        domain.admissible,
    ];
    roots.extend_from_slice(properties);
    let first = kernel.fresh_name(&roots)?;
    let admissible = kernel.tm_fv(first, domain.domain_ty)?;
    let runs = kernel.tm_fv(checked_name(first, 1)?, domain.run_graph_ty)?;
    Ok((admissible, runs))
}

fn abstract_property(
    kernel: &mut Kernel,
    domain: RunDomain,
    admissible: Ref,
    runs: Ref,
    body: Ref,
) -> Result<Ref, KernelError> {
    let by_runs_ty = kernel.ty_arr(domain.run_graph_ty, domain.relation.types.bool_ty)?;
    let by_runs = kernel.lam_at(by_runs_ty, runs, body)?;
    let property_ty = kernel.ty_arr(domain.domain_ty, by_runs_ty)?;
    kernel.lam_at(property_ty, admissible, by_runs)
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

fn equality_operands(kernel: &Kernel, equality: Ref) -> Result<[Ref; 2], KernelError> {
    let children = kernel
        .arena()
        .children(equality)
        .ok_or(KernelError::InvalidTheoremRule {
            rule: "run equality proposition",
        })?
        .collect::<Vec<_>>();
    let [_, left, right] = children.as_slice() else {
        return Err(KernelError::InvalidTheoremRule {
            rule: "run equality proposition operands",
        });
    };
    Ok([*left, *right])
}

fn align_evidence(
    kernel: &mut Kernel,
    evidence: Evidence,
    target: Ref,
) -> Result<covalence_logic_hol::ThmId, KernelError> {
    align_signed_evidence(kernel, evidence, target, true)
}

fn align_signed_evidence(
    kernel: &mut Kernel,
    evidence: Evidence,
    target: Ref,
    holds: bool,
) -> Result<covalence_logic_hol::ThmId, KernelError> {
    if evidence.holds != holds {
        return Err(KernelError::InvalidTheoremRule {
            rule: "signed run evidence",
        });
    }
    let expected = if holds {
        positive(evidence.proposition)
    } else {
        positive(evidence.proposition).negated()
    };
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
    join_alpha_equivalent(kernel, evidence.proposition, target).map_err(|_| {
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

fn aligned_theorem_conclusion(
    kernel: &mut Kernel,
    theorem: covalence_logic_hol::ThmId,
    source: Ref,
    target: Ref,
    rule: &'static str,
) -> Result<covalence_logic_hol::ThmId, KernelError> {
    let aligned = kernel.copy_theorem(theorem)?;
    align_theorem_conclusion(kernel, aligned, source, target, rule)?;
    Ok(aligned)
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

fn certify_curried_beta2(kernel: &mut Kernel, application: Ref) -> Result<Ref, RunProofError> {
    let children = kernel
        .arena()
        .children(application)
        .ok_or(KernelError::InvalidTheoremRule {
            rule: "curried run property application",
        })?
        .collect::<Vec<_>>();
    let [function, argument] = children.as_slice() else {
        return Err(KernelError::InvalidTheoremRule {
            rule: "curried run property application operands",
        }
        .into());
    };
    let (reduced_function, function_fact) = certify_beta_application(kernel, *function)?;
    let reduced_application = kernel.app(reduced_function, *argument)?;
    let argument_fact = kernel.syn_refl(None, SynRel::Conv, *argument)?;
    let application_fact = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        application,
        reduced_application,
        &[function_fact, argument_fact],
    )?;
    let (reduced, beta_fact) = certify_beta_application(kernel, reduced_application)?;
    let conversion = kernel.syn_trans(None, application_fact, beta_fact)?;
    kernel.union_syn_fact(conversion)?;
    Ok(reduced)
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

fn specialize_universal_to(
    kernel: &mut Kernel,
    theorem: covalence_logic_hol::ThmId,
    arguments: &[Ref],
    target: Ref,
    rule: &'static str,
) -> Result<covalence_logic_hol::ThmId, RunProofError> {
    let mut current_theorem = theorem;
    let mut current_proposition = None;
    for &argument in arguments {
        let specialized = forall_elim(kernel, current_theorem, argument)?;
        current_theorem = specialized.theorem;
        current_proposition = Some(specialized.proposition);
    }
    let proposition = current_proposition.ok_or(KernelError::InvalidTheoremRule { rule })?;
    align_theorem_conclusion(kernel, current_theorem, proposition, target, rule)?;
    Ok(current_theorem)
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
    use super::{BehaviorQuantifier, RefinementDirection, RunRelation, RunTypes};
    use crate::{Evidence, EvidenceScope};
    use covalence_logic_hol::Kernel;

    #[test]
    #[allow(clippy::too_many_lines)]
    fn eventful_run_observations_are_generic_checked_and_transactional() {
        assert_eq!(
            BehaviorQuantifier::May.refinement_direction(),
            RefinementDirection::ImplementationToSpecification
        );
        for quantifier in [
            BehaviorQuantifier::Every,
            BehaviorQuantifier::Must,
            BehaviorQuantifier::Never,
        ] {
            assert_eq!(
                quantifier.refinement_direction(),
                RefinementDirection::SpecificationToImplementation
            );
        }
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
        let may_property = observation
            .property(&mut kernel, BehaviorQuantifier::May)
            .unwrap();
        let total_property = domain.total_property(&mut kernel).unwrap();
        let deterministic_property = domain.deterministic_property(&mut kernel).unwrap();
        let well_behaved_property = total_property
            .and(&mut kernel, deterministic_property)
            .unwrap();
        assert_eq!(may_property.domain(), domain);
        let property_tail = kernel.ty_arr(domain.run_graph_ty, bool_ty).unwrap();
        let property_ty = kernel.ty_arr(domain.domain_ty, property_tail).unwrap();
        let actual_property_ty = kernel.classifier(may_property.property()).unwrap();
        covalence_logic_hol_derived::join_same_syntax(&mut kernel, actual_property_ty, property_ty)
            .unwrap();
        let custom_property_term = kernel.tm_fv(33, property_ty).unwrap();
        let custom_property = domain.property(&mut kernel, custom_property_term).unwrap();
        let combined_property = may_property.and(&mut kernel, custom_property).unwrap();
        let alternative_property = may_property.or(&mut kernel, custom_property).unwrap();
        let contract_property = may_property.implies(&mut kernel, custom_property).unwrap();
        let equivalent_property = may_property.iff(&mut kernel, custom_property).unwrap();
        let negated_property = custom_property.negate(&mut kernel).unwrap();
        let custom_proposition = custom_property
            .proposition(&mut kernel, profile, module)
            .unwrap();
        assert_eq!(kernel.classifier(custom_proposition).unwrap(), bool_ty);
        let may_from_property = may_property
            .proposition(&mut kernel, profile, module)
            .unwrap();
        covalence_logic_hol_derived::join_alpha_equivalent(&mut kernel, may_from_property, may)
            .unwrap();
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
        for composed in [
            combined_property,
            alternative_property,
            contract_property,
            equivalent_property,
            negated_property,
        ] {
            let proposition = composed.proposition(&mut kernel, profile, module).unwrap();
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
        let total_from_property = total_property
            .proposition(&mut kernel, profile, module)
            .unwrap();
        let deterministic_from_property = deterministic_property
            .proposition(&mut kernel, profile, module)
            .unwrap();
        covalence_logic_hol_derived::join_alpha_equivalent(&mut kernel, total_from_property, total)
            .unwrap();
        covalence_logic_hol_derived::join_alpha_equivalent(
            &mut kernel,
            deterministic_from_property,
            deterministic,
        )
        .unwrap();
        let well_behaved = well_behaved_property
            .proposition(&mut kernel, profile, module)
            .unwrap();
        assert_eq!(kernel.classifier(same_runs).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(refinement).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(total).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(deterministic).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(well_behaved).unwrap(), bool_ty);
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
        let equality_refines = domain
            .prove_same_runs_refines(
                &mut kernel,
                left_middle_evidence,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle])
            .check(&kernel, equality_refines)
            .unwrap();
        let equality_reverse_refines = domain
            .prove_same_runs_refines(&mut kernel, symmetric, profile, other_module, module)
            .unwrap();
        EvidenceScope::positive(&[left_middle])
            .check(&kernel, equality_reverse_refines)
            .unwrap();
        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            domain
                .prove_same_runs_refines(
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
        let property_preserved = may_property
            .prove_same_runs_preserves(
                &mut kernel,
                left_middle_evidence,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle])
            .check(&kernel, property_preserved)
            .unwrap();
        let custom_property_preserved = custom_property
            .prove_same_runs_preserves(
                &mut kernel,
                left_middle_evidence,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle])
            .check(&kernel, custom_property_preserved)
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
            .prove_refinement_reflexive(&mut kernel, profile, module)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, refinement_reflexive)
            .unwrap();
        let left_middle_refinement = domain
            .refines_runs(&mut kernel, profile, module, other_module)
            .unwrap();
        let middle_right_refinement = domain
            .refines_runs(&mut kernel, profile, other_module, third_module)
            .unwrap();
        let left_middle_refinement_evidence = Evidence {
            proposition: left_middle_refinement,
            theorem: kernel
                .identity(super::positive(left_middle_refinement))
                .unwrap(),
            holds: true,
        };
        let middle_right_refinement_evidence = Evidence {
            proposition: middle_right_refinement,
            theorem: kernel
                .identity(super::positive(middle_right_refinement))
                .unwrap(),
            holds: true,
        };
        let specification_total = domain.total(&mut kernel, profile, other_module).unwrap();
        let specification_total_evidence = Evidence {
            proposition: specification_total,
            theorem: kernel
                .identity(super::positive(specification_total))
                .unwrap(),
            holds: true,
        };
        let implementation_total = domain
            .prove_refinement_preserves_totality(
                &mut kernel,
                left_middle_refinement_evidence,
                specification_total_evidence,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle_refinement, specification_total])
            .check(&kernel, implementation_total)
            .unwrap();
        let specification_deterministic = domain
            .deterministic(&mut kernel, profile, other_module)
            .unwrap();
        let specification_deterministic_evidence = Evidence {
            proposition: specification_deterministic,
            theorem: kernel
                .identity(super::positive(specification_deterministic))
                .unwrap(),
            holds: true,
        };
        let implementation_deterministic = domain
            .prove_refinement_preserves_determinism(
                &mut kernel,
                left_middle_refinement_evidence,
                specification_deterministic_evidence,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle_refinement, specification_deterministic])
            .check(&kernel, implementation_deterministic)
            .unwrap();
        let implementation_may = observation.may(&mut kernel, profile, module).unwrap();
        let implementation_may_evidence = Evidence {
            proposition: implementation_may,
            theorem: kernel
                .identity(super::positive(implementation_may))
                .unwrap(),
            holds: true,
        };
        let specification_may = observation
            .prove_refinement_preserves(
                &mut kernel,
                left_middle_refinement_evidence,
                implementation_may_evidence,
                BehaviorQuantifier::May,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle_refinement, implementation_may])
            .check(&kernel, specification_may)
            .unwrap();
        let specification_never = observation
            .never(&mut kernel, profile, other_module)
            .unwrap();
        let specification_never_evidence = Evidence {
            proposition: specification_never,
            theorem: kernel
                .identity(super::positive(specification_never))
                .unwrap(),
            holds: true,
        };
        let implementation_never = observation
            .prove_refinement_preserves(
                &mut kernel,
                left_middle_refinement_evidence,
                specification_never_evidence,
                BehaviorQuantifier::Never,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle_refinement, specification_never])
            .check(&kernel, implementation_never)
            .unwrap();
        let specification_every = observation
            .every(&mut kernel, profile, other_module)
            .unwrap();
        let specification_every_evidence = Evidence {
            proposition: specification_every,
            theorem: kernel
                .identity(super::positive(specification_every))
                .unwrap(),
            holds: true,
        };
        let implementation_every = observation
            .prove_refinement_preserves(
                &mut kernel,
                left_middle_refinement_evidence,
                specification_every_evidence,
                BehaviorQuantifier::Every,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle_refinement, specification_every])
            .check(&kernel, implementation_every)
            .unwrap();
        let specification_must = observation
            .must(&mut kernel, profile, other_module)
            .unwrap();
        let specification_must_evidence = Evidence {
            proposition: specification_must,
            theorem: kernel
                .identity(super::positive(specification_must))
                .unwrap(),
            holds: true,
        };
        let implementation_must = observation
            .prove_refinement_preserves(
                &mut kernel,
                left_middle_refinement_evidence,
                specification_must_evidence,
                BehaviorQuantifier::Must,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle_refinement, specification_must])
            .check(&kernel, implementation_must)
            .unwrap();
        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            observation
                .prove_refinement_preserves(
                    &mut kernel,
                    left_middle_refinement_evidence,
                    implementation_may_evidence,
                    BehaviorQuantifier::Never,
                    profile,
                    module,
                    other_module,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            observation
                .prove_refinement_preserves(
                    &mut kernel,
                    equivalence_reflexive,
                    implementation_may_evidence,
                    BehaviorQuantifier::May,
                    profile,
                    module,
                    other_module,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
        let refinement_transitive = domain
            .prove_refinement_transitive(
                &mut kernel,
                left_middle_refinement_evidence,
                middle_right_refinement_evidence,
                profile,
                module,
                other_module,
                third_module,
            )
            .unwrap();
        EvidenceScope::positive(&[left_middle_refinement, middle_right_refinement])
            .check(&kernel, refinement_transitive)
            .unwrap();
        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            domain
                .prove_refinement_transitive(
                    &mut kernel,
                    left_middle_refinement_evidence,
                    left_middle_refinement_evidence,
                    profile,
                    module,
                    other_module,
                    third_module,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
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
        let context = domain
            .in_context(&mut kernel, context_ty, plug, contextual_admissible)
            .unwrap();
        assert_eq!(context.domain(), domain);
        assert_eq!(context.context_type(), context_ty);
        assert_eq!(context.plug(), plug);
        assert_eq!(context.admissible(), contextual_admissible);
        let closed_context = domain.closed_context(&mut kernel).unwrap();
        assert_eq!(closed_context.context().domain(), domain);
        assert_eq!(
            kernel
                .classifier(closed_context.identity_context())
                .unwrap(),
            bool_ty
        );
        let closed_admissible = closed_context
            .prove_admissible(&mut kernel, module)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, closed_admissible)
            .unwrap();
        let closed_sound_identity = closed_context
            .context()
            .prove_identity_transformation_sound(&mut kernel, profile)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, closed_sound_identity.soundness())
            .unwrap();
        let closed_identity_preserves_may = closed_context
            .prove_preserves(
                &mut kernel,
                closed_sound_identity,
                observation,
                BehaviorQuantifier::May,
                module,
            )
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, closed_identity_preserves_may)
            .unwrap();
        let [closed_original_behavior, _closed_transformed_behavior] =
            super::equality_operands(&kernel, closed_identity_preserves_may.proposition).unwrap();
        let closed_positive_behavior = Evidence {
            proposition: closed_original_behavior,
            theorem: kernel
                .identity(super::positive(closed_original_behavior))
                .unwrap(),
            holds: true,
        };
        let closed_positive_transport = closed_context
            .transport(
                &mut kernel,
                closed_sound_identity,
                observation,
                BehaviorQuantifier::May,
                module,
                closed_positive_behavior,
            )
            .unwrap();
        assert!(closed_positive_transport.holds);
        EvidenceScope::positive(&[closed_original_behavior])
            .check(&kernel, closed_positive_transport)
            .unwrap();
        let closed_negative_behavior = Evidence {
            proposition: closed_original_behavior,
            theorem: kernel
                .identity(super::positive(closed_original_behavior).negated())
                .unwrap(),
            holds: false,
        };
        let closed_negative_transport = closed_context
            .transport(
                &mut kernel,
                closed_sound_identity,
                observation,
                BehaviorQuantifier::May,
                module,
                closed_negative_behavior,
            )
            .unwrap();
        assert!(!closed_negative_transport.holds);
        EvidenceScope::signed(&[super::positive(closed_original_behavior).negated()])
            .check(&kernel, closed_negative_transport)
            .unwrap();
        let identity_transformation = context
            .identity_transformation(&mut kernel, profile)
            .unwrap();
        let identity_at_module = identity_transformation.apply(&mut kernel, module).unwrap();
        assert_eq!(kernel.classifier(identity_at_module).unwrap(), types.module);
        let sound_identity = context
            .prove_identity_transformation_sound(&mut kernel, profile)
            .unwrap();
        assert_eq!(
            sound_identity.transformation().context(),
            identity_transformation.context()
        );
        EvidenceScope::positive(&[])
            .check(&kernel, sound_identity.soundness())
            .unwrap();
        let identity_preserves_may = sound_identity
            .prove_preserves_property(&mut kernel, may_property)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, identity_preserves_may)
            .unwrap();
        let identity_preserves_observation = sound_identity
            .prove_preserves(&mut kernel, observation, BehaviorQuantifier::May)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, identity_preserves_observation)
            .unwrap();
        let identity_preserves_module_observation = sound_identity
            .prove_preserves_at(&mut kernel, observation, BehaviorQuantifier::May, module)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, identity_preserves_module_observation)
            .unwrap();
        let linking_context = kernel.tm_fv(37, context_ty).unwrap();
        let module_admissible = super::apply(
            &mut kernel,
            contextual_admissible,
            &[linking_context, module],
        )
        .unwrap();
        let module_admissible_evidence = Evidence {
            proposition: module_admissible,
            theorem: kernel.identity(super::positive(module_admissible)).unwrap(),
            holds: true,
        };
        let identity_preserves_in_context = sound_identity
            .prove_preserves_in_context(
                &mut kernel,
                observation,
                BehaviorQuantifier::May,
                module,
                linking_context,
                module_admissible_evidence,
                module_admissible_evidence,
            )
            .unwrap();
        EvidenceScope::positive(&[module_admissible])
            .check(&kernel, identity_preserves_in_context)
            .unwrap();
        let [original_behavior, _transformed_behavior] =
            super::equality_operands(&kernel, identity_preserves_in_context.proposition).unwrap();
        let positive_behavior = Evidence {
            proposition: original_behavior,
            theorem: kernel.identity(super::positive(original_behavior)).unwrap(),
            holds: true,
        };
        let transported_positive = sound_identity
            .transport_in_context(
                &mut kernel,
                observation,
                BehaviorQuantifier::May,
                module,
                linking_context,
                module_admissible_evidence,
                module_admissible_evidence,
                positive_behavior,
            )
            .unwrap();
        assert!(transported_positive.holds);
        EvidenceScope::positive(&[module_admissible, original_behavior])
            .check(&kernel, transported_positive)
            .unwrap();
        let negative_behavior = Evidence {
            proposition: original_behavior,
            theorem: kernel
                .identity(super::positive(original_behavior).negated())
                .unwrap(),
            holds: false,
        };
        let transported_negative = sound_identity
            .transport_in_context(
                &mut kernel,
                observation,
                BehaviorQuantifier::May,
                module,
                linking_context,
                module_admissible_evidence,
                module_admissible_evidence,
                negative_behavior,
            )
            .unwrap();
        assert!(!transported_negative.holds);
        EvidenceScope::signed(&[
            super::positive(module_admissible),
            super::positive(original_behavior).negated(),
        ])
        .check(&kernel, transported_negative)
        .unwrap();
        let sound_identity_composition = sound_identity.then(&mut kernel, sound_identity).unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, sound_identity_composition.soundness())
            .unwrap();
        let transform_ty = kernel.ty_arr(types.module, types.module).unwrap();
        let transform = kernel.tm_fv(34, transform_ty).unwrap();
        let next_transform = kernel.tm_fv(35, transform_ty).unwrap();
        let transformation = context
            .transformation(&mut kernel, profile, transform)
            .unwrap();
        let next_transformation = context
            .transformation(&mut kernel, profile, next_transform)
            .unwrap();
        assert_eq!(transformation.context(), context);
        assert_eq!(transformation.profile(), profile);
        assert_eq!(transformation.transform(), transform);
        let transformed = transformation.apply(&mut kernel, module).unwrap();
        assert_eq!(kernel.classifier(transformed).unwrap(), types.module);
        let transformation_sound = transformation.sound(&mut kernel).unwrap();
        assert_eq!(kernel.classifier(transformation_sound).unwrap(), bool_ty);
        let transformation_sound_evidence = Evidence {
            proposition: transformation_sound,
            theorem: kernel
                .identity(super::positive(transformation_sound))
                .unwrap(),
            holds: true,
        };
        let sound_transformation = transformation
            .with_soundness(&mut kernel, transformation_sound_evidence)
            .unwrap();
        assert_eq!(sound_transformation.transformation(), transformation);
        EvidenceScope::positive(&[transformation_sound])
            .check(&kernel, sound_transformation.soundness())
            .unwrap();
        let transformation_preserves_contract = sound_transformation
            .prove_preserves_property(&mut kernel, contract_property)
            .unwrap();
        EvidenceScope::positive(&[transformation_sound])
            .check(&kernel, transformation_preserves_contract)
            .unwrap();
        let transformation_preserves_module_contract = sound_transformation
            .prove_preserves_property_at(&mut kernel, contract_property, module)
            .unwrap();
        EvidenceScope::positive(&[transformation_sound])
            .check(&kernel, transformation_preserves_module_contract)
            .unwrap();
        let rejected_soundness = Evidence {
            proposition: transformation_sound,
            theorem: kernel
                .identity(super::positive(transformation_sound).negated())
                .unwrap(),
            holds: false,
        };
        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            transformation
                .with_soundness(&mut kernel, rejected_soundness)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
        let next_sound = next_transformation.sound(&mut kernel).unwrap();
        let next_sound_evidence = Evidence {
            proposition: next_sound,
            theorem: kernel.identity(super::positive(next_sound)).unwrap(),
            holds: true,
        };
        let sound_next_transformation = next_transformation
            .with_soundness(&mut kernel, next_sound_evidence)
            .unwrap();
        let sound_composition = sound_transformation
            .then(&mut kernel, sound_next_transformation)
            .unwrap();
        EvidenceScope::positive(&[transformation_sound, next_sound])
            .check(&kernel, sound_composition.soundness())
            .unwrap();
        let composed_transformation = transformation
            .then(&mut kernel, next_transformation)
            .unwrap();
        let composed_sound = composed_transformation.sound(&mut kernel).unwrap();
        assert_eq!(kernel.classifier(composed_sound).unwrap(), bool_ty);
        let other_profile = kernel.tm_fv(36, types.profile).unwrap();
        let other_profile_transformation = context
            .transformation(&mut kernel, other_profile, transform)
            .unwrap();
        let before = kernel.arena().clone();
        assert!(matches!(
            transformation.then(&mut kernel, other_profile_transformation),
            Err(super::RunTransformationError::ProfileMismatch)
        ));
        assert_eq!(kernel.arena(), &before);
        let contextual_from_schema = context
            .observe(&mut kernel, observation, BehaviorQuantifier::May, profile)
            .unwrap();
        let contextual_from_property = context
            .observe_property(&mut kernel, may_property, profile)
            .unwrap();
        let contextual_from_custom_property = context
            .observe_property(&mut kernel, custom_property, profile)
            .unwrap();
        assert_eq!(contextual_from_schema.plug, contextual.plug);
        assert_eq!(contextual_from_schema.admissible, contextual.admissible);
        covalence_logic_hol_derived::join_same_syntax(
            &mut kernel,
            contextual_from_schema.observe,
            contextual.observe,
        )
        .unwrap();
        covalence_logic_hol_derived::join_same_syntax(
            &mut kernel,
            contextual_from_property.observe,
            contextual.observe,
        )
        .unwrap();
        let contextual_same_runs = context
            .equivalent(&mut kernel, profile, module, other_module)
            .unwrap();
        assert_eq!(kernel.classifier(contextual_same_runs).unwrap(), bool_ty);
        let contextual_reflexive = context
            .prove_reflexive(&mut kernel, profile, module)
            .unwrap();
        EvidenceScope::positive(&[])
            .check(&kernel, contextual_reflexive)
            .unwrap();
        let contextual_same_runs_evidence = Evidence {
            proposition: contextual_same_runs,
            theorem: kernel
                .identity(super::positive(contextual_same_runs))
                .unwrap(),
            holds: true,
        };
        let contextual_symmetric = context
            .prove_symmetric(
                &mut kernel,
                contextual_same_runs_evidence,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[contextual_same_runs])
            .check(&kernel, contextual_symmetric)
            .unwrap();
        let contextual_middle_right = context
            .equivalent(&mut kernel, profile, other_module, third_module)
            .unwrap();
        let contextual_middle_right_evidence = Evidence {
            proposition: contextual_middle_right,
            theorem: kernel
                .identity(super::positive(contextual_middle_right))
                .unwrap(),
            holds: true,
        };
        let contextual_transitive = context
            .prove_transitive(
                &mut kernel,
                contextual_same_runs_evidence,
                contextual_middle_right_evidence,
                profile,
                module,
                other_module,
                third_module,
            )
            .unwrap();
        EvidenceScope::positive(&[contextual_same_runs, contextual_middle_right])
            .check(&kernel, contextual_transitive)
            .unwrap();
        let before = kernel.arena().clone();
        let theorem_count = kernel.thm().live_theorems().count();
        assert!(
            context
                .prove_transitive(
                    &mut kernel,
                    contextual_same_runs_evidence,
                    contextual_same_runs_evidence,
                    profile,
                    module,
                    other_module,
                    third_module,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
        for quantifier in [
            BehaviorQuantifier::May,
            BehaviorQuantifier::Every,
            BehaviorQuantifier::Must,
            BehaviorQuantifier::Never,
        ] {
            let contextual_preservation = context
                .prove_preserves(
                    &mut kernel,
                    contextual_same_runs_evidence,
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
        let custom_contextual_preservation = context
            .prove_property_preserves(
                &mut kernel,
                contextual_same_runs_evidence,
                custom_property,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[contextual_same_runs])
            .check(&kernel, custom_contextual_preservation)
            .unwrap();
        let well_behaved_contextual_preservation = context
            .prove_property_preserves(
                &mut kernel,
                contextual_same_runs_evidence,
                well_behaved_property,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[contextual_same_runs])
            .check(&kernel, well_behaved_contextual_preservation)
            .unwrap();
        let equivalent_contextual_preservation = context
            .prove_property_preserves(
                &mut kernel,
                contextual_same_runs_evidence,
                equivalent_property,
                profile,
                module,
                other_module,
            )
            .unwrap();
        EvidenceScope::positive(&[contextual_same_runs])
            .check(&kernel, equivalent_contextual_preservation)
            .unwrap();
        let custom_observed_equivalence = contextual_from_custom_property
            .equivalent(&mut kernel, module, other_module)
            .unwrap();
        let custom_observed_distinction = Evidence {
            proposition: custom_observed_equivalence,
            theorem: kernel
                .identity(super::positive(custom_observed_equivalence).negated())
                .unwrap(),
            holds: false,
        };
        let custom_run_distinction = context
            .prove_property_distinct(
                &mut kernel,
                custom_observed_distinction,
                custom_property,
                profile,
                module,
                other_module,
            )
            .unwrap();
        assert!(!custom_run_distinction.holds);
        EvidenceScope::signed(&[super::positive(custom_observed_equivalence).negated()])
            .check(&kernel, custom_run_distinction)
            .unwrap();
        let observed_equivalence = contextual_from_schema
            .equivalent(&mut kernel, module, other_module)
            .unwrap();
        let observed_distinction = Evidence {
            proposition: observed_equivalence,
            theorem: kernel
                .identity(super::positive(observed_equivalence).negated())
                .unwrap(),
            holds: false,
        };
        let run_distinction = context
            .prove_distinct(
                &mut kernel,
                observed_distinction,
                observation,
                BehaviorQuantifier::May,
                profile,
                module,
                other_module,
            )
            .unwrap();
        assert!(!run_distinction.holds);
        EvidenceScope::signed(&[super::positive(observed_equivalence).negated()])
            .check(&kernel, run_distinction)
            .unwrap();
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
                .prove_preserves(
                    &mut kernel,
                    denied_contextual_runs,
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
        let other_property = other_domain
            .property(&mut kernel, custom_property_term)
            .unwrap();
        let before = kernel.arena().clone();
        assert!(matches!(
            observation.and(&mut kernel, other_observation),
            Err(super::RunObservationError::DomainMismatch)
        ));
        assert_eq!(kernel.arena(), &before);
        let before = kernel.arena().clone();
        assert!(matches!(
            custom_property.and(&mut kernel, other_property),
            Err(super::RunCompositionError::DomainMismatch)
        ));
        assert_eq!(kernel.arena(), &before);
        let before = kernel.arena().clone();
        assert!(matches!(
            custom_property.iff(&mut kernel, other_property),
            Err(super::RunCompositionError::DomainMismatch)
        ));
        assert_eq!(kernel.arena(), &before);
        let before = kernel.arena().clone();
        assert!(
            context
                .observe(
                    &mut kernel,
                    other_observation,
                    BehaviorQuantifier::May,
                    profile,
                )
                .is_err()
        );
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
