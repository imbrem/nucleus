//! Generic, immutable propositions over one eventful program-execution relation.
//!
//! This module is syntax and checked composition only. It does not execute a
//! program or create theorem facts. A caller supplies the versioned execution
//! relation, the allowed invocation/host policy, and the observation over a
//! trace and outcome.

use covalence_logic_hol::{
    Kernel, KernelError, Ref,
    builtin::{Op1, Op2},
};
use covalence_logic_hol_derived::join_same_syntax;

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

    /// Validates and attaches an invocation policy and behavior observation.
    ///
    /// `admissible` has classifier
    /// `profile -> module -> entry -> inputs -> host -> bool`; this keeps host
    /// and input quantification explicit while allowing the policy to depend on
    /// the selected semantic profile and module. `observe` has classifier
    /// `trace -> outcome -> bool`, allowing calls, traps, returns, and compound
    /// trace properties to share the same execution relation.
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
        let observation_ty = curried_type(
            &mut staged,
            &[self.types.trace, self.types.outcome],
            self.types.bool_ty,
        )?;
        require_classifier(&mut staged, observe, observation_ty)?;
        *kernel = staged;
        Ok(RunObservation {
            relation: self,
            admissible,
            observe,
        })
    }
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
    relation: RunRelation,
    admissible: Ref,
    observe: Ref,
}

impl RunObservation {
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
        let types = self.relation.types;
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
            self.relation.runs,
            self.admissible,
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
            self.admissible,
            &[profile, module, entry, inputs, host],
        )?;
        let runs = apply(
            &mut staged,
            self.relation.runs,
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
        let types = self.relation.types;
        require_classifier(&mut staged, profile, types.profile)?;
        let name = staged.fresh_name(&[
            types.module,
            types.bool_ty,
            self.relation.runs,
            self.admissible,
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

fn require_classifier(kernel: &mut Kernel, term: Ref, expected: Ref) -> Result<(), KernelError> {
    let actual = kernel.classifier(term)?;
    join_same_syntax(kernel, actual, expected)
        .map(|_| ())
        .map_err(|_| KernelError::ClassifierMismatch { expected, actual })
}

#[cfg(test)]
mod tests {
    use super::{BehaviorQuantifier, RunRelation, RunTypes};
    use covalence_logic_hol::{Kernel, Tag, TmTag};

    #[test]
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
        let relation = RunRelation::new(&mut kernel, types, runs).unwrap();
        let observation = relation.observe(&mut kernel, admissible, observe).unwrap();

        let may = observation.may(&mut kernel, profile, module).unwrap();
        let never = observation.never(&mut kernel, profile, module).unwrap();
        let must = observation.must(&mut kernel, profile, module).unwrap();
        assert_eq!(kernel.classifier(may).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(never).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(must).unwrap(), bool_ty);
        assert_eq!(kernel.arena().tag(never), Some(Tag::Tm(TmTag::Op1)));
        assert_eq!(kernel.arena().tag(must), Some(Tag::Tm(TmTag::Op2)));

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
        assert!(relation.observe(&mut kernel, observe, admissible).is_err());
        assert_eq!(kernel.arena(), &before);
    }
}
