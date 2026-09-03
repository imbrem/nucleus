//! Typed, immutable vocabulary over the checked structural Wasm theory.
//!
//! These wrappers refine the currently erased `SpecTec` value carrier at the
//! Rust API boundary. They do not introduce distinct HOL base types, execute
//! Wasm, or create theorem authority.

use covalence_logic_hol::{Kernel, KernelError, Ref, ThmId};

use crate::{
    AssertionReachability, ClosedProgramObservation, Evidence, ObservationProofError,
    ReachabilityProofError,
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
pub struct WasmTheory {
    reachability: AssertionReachability,
    observation: ClosedProgramObservation,
    assert_function: WasmFunction,
}

impl WasmTheory {
    /// Opens a typed view of one checked assertion-reachability interpretation.
    ///
    /// # Errors
    ///
    /// Returns an error unless `assert_function` is accepted by the checked
    /// reachability predicates. `kernel` is unchanged on failure.
    pub fn open(
        kernel: &mut Kernel,
        reachability: AssertionReachability,
        assert_function: Ref,
    ) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let observation = reachability.closed_program_observation(&mut staged, assert_function)?;
        *kernel = staged;
        Ok(Self {
            reachability,
            observation,
            assert_function: WasmFunction(assert_function),
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
}
