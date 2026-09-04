//! Typed, immutable vocabulary over the checked structural Wasm theory.
//!
//! These wrappers refine the currently erased `SpecTec` value carrier at the
//! Rust API boundary. They do not introduce distinct HOL base types, execute
//! Wasm, or create theorem authority.

use std::sync::Arc;

use covalence_logic_hol::{Kernel, KernelError, Lit, Ref, ThmId};

use crate::{
    AssertionReachability, ClosedProgramObservation, Evidence, ObservationProofError,
    ParameterizedDocument, ReachabilityProofError, WasmLogicError, empty_wasm_module,
    forwarding_wasm_module,
};

/// A checked term used as a structural Wasm module.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WasmModule(Ref);

impl WasmModule {
    /// Returns the underlying checked HOL term.
    #[must_use]
    pub const fn term(self) -> Ref {
        self.0
    }
}

/// A checked term used as a structural Wasm function.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WasmFunction(Ref);

impl WasmFunction {
    /// Returns the underlying checked HOL term.
    #[must_use]
    pub const fn term(self) -> Ref {
        self.0
    }
}

/// A checked term used as a structural Wasm execution configuration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WasmConfiguration(Ref);

impl WasmConfiguration {
    /// Returns the underlying checked HOL term.
    #[must_use]
    pub const fn term(self) -> Ref {
        self.0
    }
}

/// Immutable facade for assertion reachability and its contextual semantics.
///
/// The facade packages checked HOL predicates only. In particular,
/// [`Self::sem_eqv`] constructs an observational-equivalence proposition; it
/// does not decide equivalence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WasmTheory<'a> {
    document: &'a ParameterizedDocument,
    reachability: AssertionReachability,
    observation: ClosedProgramObservation,
    assert_function: WasmFunction,
}

/// Categorized residual assumptions of one checked Wasm theorem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WasmEvidenceReport {
    /// Proposition whose evidence was inspected.
    pub proposition: Ref,
    /// Whether the theorem proves the proposition or its negation.
    pub holds: bool,
    /// Premises originating in the complete generated `SpecTec` theory.
    pub generated_theory: Arc<[Lit]>,
    /// Explicit concrete-value representation or grounding premises.
    pub grounding: Arc<[Lit]>,
}

impl WasmEvidenceReport {
    /// Returns whether the theorem has no residual assumptions.
    #[must_use]
    pub fn is_premise_free(&self) -> bool {
        self.generated_theory.is_empty() && self.grounding.is_empty()
    }

    /// Returns a stable compact text representation of the conclusion and all
    /// categorized residual assumptions.
    #[must_use]
    pub fn summary(&self) -> String {
        fn literals(values: &[Lit]) -> String {
            values
                .iter()
                .map(|literal| literal.get().to_string())
                .collect::<Vec<_>>()
                .join(",")
        }
        format!(
            "proposition={};holds={};generated_theory=[{}];grounding=[{}]",
            self.proposition.get(),
            self.holds,
            literals(&self.generated_theory),
            literals(&self.grounding),
        )
    }
}

impl<'a> WasmTheory<'a> {
    /// Opens a typed view of one checked assertion-reachability interpretation.
    ///
    /// # Errors
    ///
    /// Returns an error unless `assert_function` is accepted by the checked
    /// reachability predicates. `kernel` is unchanged on failure.
    pub fn open(
        kernel: &mut Kernel,
        document: &'a ParameterizedDocument,
        reachability: AssertionReachability,
        assert_function: Ref,
    ) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let observation = reachability.closed_program_observation(&mut staged, assert_function)?;
        *kernel = staged;
        Ok(Self {
            document,
            reachability,
            observation,
            assert_function: WasmFunction(assert_function),
        })
    }

    /// Constructs the structural empty module from exact recorded `SpecTec`
    /// constructors.
    ///
    /// # Errors
    ///
    /// Returns an error if a required operation is absent or checked
    /// application fails. `kernel` is unchanged on failure.
    pub fn empty_module(self, kernel: &mut Kernel) -> Result<WasmModule, WasmLogicError> {
        empty_wasm_module(kernel, self.document).map(WasmModule)
    }

    /// Constructs the structural module that forwards its export to an import.
    ///
    /// The three name arguments are terms on the currently erased `SpecTec`
    /// carrier. Name decoding remains an explicit future refinement.
    ///
    /// # Errors
    ///
    /// Returns an error if a required operation is absent, an argument has an
    /// incompatible classifier, or checked application fails. `kernel` is
    /// unchanged on failure.
    pub fn forwarding_module(
        self,
        kernel: &mut Kernel,
        import_module: Ref,
        assert_name: Ref,
        export_name: Ref,
    ) -> Result<WasmModule, WasmLogicError> {
        forwarding_wasm_module(
            kernel,
            self.document,
            import_module,
            assert_name,
            export_name,
        )
        .map(WasmModule)
    }

    /// Inspects and categorizes every residual premise of checked evidence.
    ///
    /// `grounding_laws` is the explicit concrete-value boundary for this
    /// proof. Any premise outside it and the complete generated theory is
    /// rejected rather than silently categorized.
    ///
    /// # Errors
    ///
    /// Returns an error if the evidence is malformed or contains a premise
    /// outside the generated theory and supplied grounding boundary.
    pub fn inspect_evidence(
        self,
        kernel: &Kernel,
        evidence: Evidence,
        grounding_laws: &[Ref],
    ) -> Result<WasmEvidenceReport, KernelError> {
        self.document
            .evidence_scope(grounding_laws)
            .check(kernel, evidence)?;
        let premises = evidence.premises(kernel)?;
        let theory_scope = self.document.evidence_scope(&[]);
        let grounding_scope = crate::EvidenceScope::positive(grounding_laws);
        let mut generated = Vec::new();
        let mut grounding = Vec::new();
        for premise in premises.iter().copied() {
            if literal_matches_any(kernel, premise, theory_scope.allowed())? {
                generated.push(premise);
            } else if literal_matches_any(kernel, premise, grounding_scope.allowed())? {
                grounding.push(premise);
            } else {
                return Err(KernelError::InvalidTheoremRule {
                    rule: "Wasm evidence premise categorization",
                });
            }
        }
        Ok(WasmEvidenceReport {
            proposition: evidence.proposition,
            holds: evidence.holds,
            generated_theory: Arc::from(generated),
            grounding: Arc::from(grounding),
        })
    }

    /// Checks and wraps a term as a module in this theory.
    ///
    /// # Errors
    ///
    /// Returns an error unless `term` has the configured erased module
    /// classifier. `kernel` is unchanged on failure.
    pub fn module(self, kernel: &mut Kernel, term: Ref) -> Result<WasmModule, KernelError> {
        let mut staged = kernel.fork();
        self.reachability
            .calls_assert(&mut staged, term, self.assert_function.0)?;
        *kernel = staged;
        Ok(WasmModule(term))
    }

    /// Wraps a function term already checked by the structural `SpecTec` API.
    #[must_use]
    pub const fn function(self, term: Ref) -> WasmFunction {
        WasmFunction(term)
    }

    /// Wraps a configuration term already checked by the structural `SpecTec` API.
    #[must_use]
    pub const fn configuration(self, term: Ref) -> WasmConfiguration {
        WasmConfiguration(term)
    }

    /// Constructs `calls_assert(module)` as checked HOL syntax.
    ///
    /// # Errors
    ///
    /// Returns an error if checked proposition construction fails. `kernel` is
    /// unchanged on failure.
    pub fn calls_assert(self, kernel: &mut Kernel, module: WasmModule) -> Result<Ref, KernelError> {
        self.reachability
            .calls_assert(kernel, module.0, self.assert_function.0)
    }

    /// Constructs `not calls_assert(module)` as checked HOL syntax.
    ///
    /// # Errors
    ///
    /// Returns an error if checked proposition construction fails. `kernel` is
    /// unchanged on failure.
    pub fn never_calls_assert(
        self,
        kernel: &mut Kernel,
        module: WasmModule,
    ) -> Result<Ref, KernelError> {
        self.reachability
            .never_calls_assert(kernel, module.0, self.assert_function.0)
    }

    /// Constructs contextual observational equivalence for two modules.
    ///
    /// # Errors
    ///
    /// Returns an error if checked proposition construction fails. `kernel` is
    /// unchanged on failure.
    pub fn sem_eqv(
        self,
        kernel: &mut Kernel,
        left: WasmModule,
        right: WasmModule,
    ) -> Result<Ref, KernelError> {
        self.observation.equivalent(kernel, left.0, right.0)
    }

    /// Proves `calls_assert(module)` from one concrete checked execution.
    ///
    /// Every premise of the three witness facts remains visible.
    ///
    /// # Errors
    ///
    /// Returns an error if a fact has the wrong conclusion or a checked proof
    /// step fails. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_arguments)]
    pub fn prove_calls_assert(
        self,
        kernel: &mut Kernel,
        module: WasmModule,
        initial: WasmConfiguration,
        final_state: WasmConfiguration,
        starts_fact: ThmId,
        steps_fact: ThmId,
        calls_fact: ThmId,
    ) -> Result<Evidence, ReachabilityProofError> {
        self.reachability.prove_calls_assert(
            kernel,
            module.0,
            self.assert_function.0,
            initial.0,
            final_state.0,
            starts_fact,
            steps_fact,
            calls_fact,
        )
    }

    /// Proves `not calls_assert(module)` from absence of admissible starts.
    ///
    /// Every premise of `no_start_fact` remains visible.
    ///
    /// # Errors
    ///
    /// Returns an error if the fact has the wrong conclusion or a checked
    /// proof step fails. `kernel` is unchanged on failure.
    pub fn prove_never_calls_assert(
        self,
        kernel: &mut Kernel,
        module: WasmModule,
        no_start_fact: ThmId,
    ) -> Result<Evidence, ReachabilityProofError> {
        self.reachability.prove_never_calls_assert_from_no_start(
            kernel,
            module.0,
            self.assert_function.0,
            no_start_fact,
        )
    }

    /// Proves that two modules are not observationally equivalent.
    ///
    /// # Errors
    ///
    /// Returns an error unless the supplied theorems prove positive assertion
    /// reachability for `left` and negative reachability for `right`, or a
    /// checked contextual proof step fails. `kernel` is unchanged on failure.
    pub fn prove_distinct(
        self,
        kernel: &mut Kernel,
        left: WasmModule,
        right: WasmModule,
        left_calls: ThmId,
        right_does_not_call: ThmId,
    ) -> Result<Evidence, ObservationProofError> {
        self.observation
            .prove_distinct(kernel, left.0, right.0, left_calls, right_does_not_call)
    }

    /// Proves `sem_eqv(left, right) ->
    /// (calls_assert(left) = calls_assert(right))`.
    ///
    /// The result is premise-free because it follows from the contextual
    /// definition itself.
    ///
    /// # Errors
    ///
    /// Returns an error if a checked contextual, beta-conversion, equality, or
    /// implication step fails. `kernel` is unchanged on failure.
    pub fn prove_calls_assert_preserved(
        self,
        kernel: &mut Kernel,
        left: WasmModule,
        right: WasmModule,
    ) -> Result<Evidence, ObservationProofError> {
        self.observation
            .prove_calls_assert_preserved(kernel, left.0, right.0)
    }

    /// Proves `sem_eqv(module, module)` without assumptions.
    ///
    /// # Errors
    ///
    /// Returns an error if a checked contextual proof step fails. `kernel` is
    /// unchanged on failure.
    pub fn prove_reflexive(
        self,
        kernel: &mut Kernel,
        module: WasmModule,
    ) -> Result<Evidence, ObservationProofError> {
        self.observation
            .contextual()
            .prove_reflexive(kernel, module.0)
    }

    /// Reverses checked positive evidence for `sem_eqv(left, right)`.
    ///
    /// Every premise of `equivalence` remains visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorem has the expected conclusion or a
    /// checked contextual proof step fails. `kernel` is unchanged on failure.
    pub fn prove_symmetric(
        self,
        kernel: &mut Kernel,
        equivalence: ThmId,
        left: WasmModule,
        right: WasmModule,
    ) -> Result<Evidence, ObservationProofError> {
        self.observation
            .contextual()
            .prove_symmetric(kernel, equivalence, left.0, right.0)
    }

    /// Composes two checked positive observational equivalence theorems.
    ///
    /// Every premise of both inputs remains visible.
    ///
    /// # Errors
    ///
    /// Returns an error unless the theorems prove the expected adjacent
    /// equivalences or a checked contextual proof step fails. `kernel` is
    /// unchanged on failure.
    pub fn prove_transitive(
        self,
        kernel: &mut Kernel,
        left_middle: ThmId,
        middle_right: ThmId,
        left: WasmModule,
        middle: WasmModule,
        right: WasmModule,
    ) -> Result<Evidence, ObservationProofError> {
        self.observation.contextual().prove_transitive(
            kernel,
            left_middle,
            middle_right,
            left.0,
            middle.0,
            right.0,
        )
    }
}

fn literal_matches_any(
    kernel: &Kernel,
    premise: Lit,
    candidates: &[Lit],
) -> Result<bool, KernelError> {
    let premise_ref =
        Ref::new(premise.magnitude().cast_signed()).ok_or(KernelError::InvalidTheoremRule {
            rule: "Wasm evidence premise reference",
        })?;
    for candidate in candidates.iter().copied() {
        if candidate.is_positive() != premise.is_positive() {
            continue;
        }
        let candidate_ref = Ref::new(candidate.magnitude().cast_signed()).ok_or(
            KernelError::InvalidTheoremRule {
                rule: "Wasm evidence candidate reference",
            },
        )?;
        if kernel.equivalent(candidate_ref, premise_ref)? {
            return Ok(true);
        }
    }
    Ok(false)
}
