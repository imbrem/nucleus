//! Adapters from the complete `SpecTec` document to program-logic predicates.

use covalence_data_basic::Symbol;
use covalence_data_spectec::IlKind;
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, SynRel, builtin::Op2};
use covalence_logic_hol_derived::{
    ExistsError, ForallError, ModelError, SyntaxError, forall_elim, introduce_exists,
    join_alpha_equivalent, open_exists, substitute,
};

use crate::{AssertionReachability, Evidence, ParameterizedDocument};

/// Immutable view for composing structural `SpecTec` values in HOL.
///
/// The builder only exposes operations recorded by the lowered document. This
/// keeps construction generic across schemas and makes missing interpretations
/// explicit instead of silently inventing meaning for a constructor.
#[derive(Clone, Copy, Debug)]
pub struct SpecTecValueBuilder<'a> {
    document: &'a ParameterizedDocument,
}

impl<'a> SpecTecValueBuilder<'a> {
    /// Creates a structural builder over one exact lowered document.
    #[must_use]
    pub const fn new(document: &'a ParameterizedDocument) -> Self {
        Self { document }
    }

    /// Returns the shared classifier of structural values.
    #[must_use]
    pub const fn value_ty(self) -> Ref {
        self.document.schema.value()
    }

    /// Constructs a list with the supplied elements.
    ///
    /// # Errors
    ///
    /// Returns an error if this list arity was not recorded by the lowering,
    /// an element has an incompatible classifier, or application fails.
    pub fn list(self, kernel: &mut Kernel, elements: &[Ref]) -> Result<Ref, WasmLogicError> {
        self.expression(kernel, "List", elements)
    }

    /// Constructs an absent or present optional value.
    ///
    /// # Errors
    ///
    /// Returns an error if this optional arity was not recorded by the
    /// lowering, the value has an incompatible classifier, or application
    /// fails.
    pub fn optional(self, kernel: &mut Kernel, value: Option<Ref>) -> Result<Ref, WasmLogicError> {
        self.expression(kernel, "Optional", value.as_slice())
    }

    /// Constructs a tuple in semantic child order.
    ///
    /// # Errors
    ///
    /// Returns an error if this tuple arity was not recorded by the lowering,
    /// a child has an incompatible classifier, or application fails.
    pub fn tuple(self, kernel: &mut Kernel, fields: &[Ref]) -> Result<Ref, WasmLogicError> {
        self.expression(kernel, "Tuple", fields)
    }

    /// Constructs a numeric literal in an exact `SpecTec` family.
    ///
    /// # Errors
    ///
    /// Returns an error if this exact spelling was not recorded by the
    /// lowering or application fails.
    pub fn number(
        self,
        kernel: &mut Kernel,
        family: &str,
        spelling: &str,
    ) -> Result<Ref, WasmLogicError> {
        let label = format!("expression:Number {{ family: {family:?}, spelling: {spelling:?} }}");
        self.construct(kernel, &label, &[])
    }

    /// Constructs a tagged case around one payload value.
    ///
    /// `notation` is the exact `SpecTec` mixfix spelling, including one `%` for
    /// every semantic field.
    ///
    /// # Errors
    ///
    /// Returns an error if the constructor was not recorded by the lowering,
    /// the payload has an incompatible classifier, or application fails.
    pub fn case(
        self,
        kernel: &mut Kernel,
        notation: &str,
        payload: Ref,
    ) -> Result<Ref, WasmLogicError> {
        let label = format!("expression:Case({notation:?})");
        self.construct(kernel, &label, &[payload])
    }

    /// Constructs a tagged case from its semantic fields.
    ///
    /// This is the usual compositional form: it first constructs the exact
    /// tuple payload and then wraps it with [`case`](Self::case).
    ///
    /// # Errors
    ///
    /// Returns an error if the tuple arity or constructor was not recorded, a
    /// field has an incompatible classifier, or application fails.
    pub fn case_fields(
        self,
        kernel: &mut Kernel,
        notation: &str,
        fields: &[Ref],
    ) -> Result<Ref, WasmLogicError> {
        let mut staged = kernel.fork();
        let payload = self.tuple(&mut staged, fields)?;
        let value = self.case(&mut staged, notation, payload)?;
        *kernel = staged;
        Ok(value)
    }

    fn expression(
        self,
        kernel: &mut Kernel,
        name: &str,
        children: &[Ref],
    ) -> Result<Ref, WasmLogicError> {
        let label = format!("expression:{name}");
        self.construct(kernel, &label, children)
    }

    fn construct(
        self,
        kernel: &mut Kernel,
        label: &str,
        children: &[Ref],
    ) -> Result<Ref, WasmLogicError> {
        let domains = children
            .iter()
            .map(|&child| {
                kernel
                    .classifier(child)
                    .map_err(|source| WasmLogicError::Kernel { source })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let constructor = operation(self.document, label, &domains, self.value_ty())?;
        let mut staged = kernel.fork();
        let value = apply(&mut staged, constructor, children)?;
        *kernel = staged;
        Ok(value)
    }
}

/// The execution predicates extracted from one lowered `SpecTec` document.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpecTecExecution {
    /// Shared erased configuration classifier.
    pub state_ty: Ref,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Curried `state -> state -> bool` view of `Steps`.
    pub steps: Ref,
    /// Exact erased pair constructor used by the `Steps` relation.
    pub pair: Ref,
    /// Exact checked classifier of `steps`.
    pub steps_ty: Ref,
    /// Exact lowered graph predicate for `$instantiate`.
    pub instantiate: Ref,
    /// Exact lowered graph predicate for `$invoke`.
    pub invoke: Ref,
    /// Exact lowered graph predicate for `$store`.
    pub store: Ref,
    /// Exact lowered graph predicate for `$moduleinst`.
    pub moduleinst: Ref,
}

/// Concrete witnesses for one admissible exported-function invocation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AdmissibleStartWitness {
    /// Module supplied to `$instantiate`.
    pub program: Ref,
    /// Configuration produced by `$invoke` and exposed as the initial state.
    pub initial: Ref,
    /// Store supplied to `$instantiate`.
    pub store: Ref,
    /// Imported external values supplied to `$instantiate`.
    pub externs: Ref,
    /// Initial instantiation configuration.
    pub instantiation_start: Ref,
    /// Completed instantiation configuration.
    pub initialized: Ref,
    /// Exported function address selected for invocation.
    pub function: Ref,
    /// Arguments supplied to the function.
    pub arguments: Ref,
    /// Store projected from the initialized configuration.
    pub initialized_store: Ref,
}

/// Checked semantic facts supporting an [`AdmissibleStartWitness`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AdmissibleStartFacts {
    /// `$instantiate store program externs instantiation_start`.
    pub instantiated: covalence_logic_hol::ThmId,
    /// `Steps instantiation_start initialized`.
    pub initialized: covalence_logic_hol::ThmId,
    /// The selected function is exported by `initialized`.
    pub exported: covalence_logic_hol::ThmId,
    /// `initialized` contains `initialized_store`.
    pub store: covalence_logic_hol::ThmId,
    /// `$invoke initialized_store function arguments initial`.
    pub invoked: covalence_logic_hol::ThmId,
}

/// Structural views needed to recognize an exported function address.
///
/// Keeping list membership explicit is essential for negative proofs: a raw
/// totalized indexing operation cannot establish that an empty export list has
/// no members.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExportedFunctionView {
    /// Shared erased value classifier.
    pub value_ty: Ref,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Graph predicate `configuration -> module-instance -> bool`.
    pub module_instance: Ref,
    /// Graph predicate `module-instance -> export-list -> bool`.
    pub exports: Ref,
    /// Predicate `export-list -> export-instance -> bool`.
    pub member: Ref,
    /// Graph predicate `export-instance -> function-address -> bool`.
    pub function_address: Ref,
}

impl ExportedFunctionView {
    /// Constructs `configuration -> function-address -> bool` by existentially
    /// joining the four structural views.
    ///
    /// # Errors
    ///
    /// Returns an error for incompatible predicates, name exhaustion, or a
    /// rejected checked HOL construction. `kernel` is unchanged on failure.
    pub fn predicate(self, kernel: &mut Kernel) -> Result<Ref, WasmLogicError> {
        let mut staged = kernel.fork();
        let roots = [
            self.value_ty,
            self.bool_ty,
            self.module_instance,
            self.exports,
            self.member,
            self.function_address,
        ];
        let first = staged
            .fresh_name(&roots)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        let mut variables = Vec::with_capacity(5);
        for offset in 0..5 {
            variables.push(
                staged
                    .tm_fv(
                        first.checked_add(offset).ok_or(WasmLogicError::Kernel {
                            source: KernelError::TooManyNames,
                        })?,
                        self.value_ty,
                    )
                    .map_err(|source| WasmLogicError::Kernel { source })?,
            );
        }
        let [
            configuration,
            function,
            module_instance,
            exports,
            export_instance,
        ] = variables.as_slice()
        else {
            unreachable!()
        };
        let has_module = apply(
            &mut staged,
            self.module_instance,
            &[*configuration, *module_instance],
        )?;
        let has_exports = apply(&mut staged, self.exports, &[*module_instance, *exports])?;
        let contains = apply(&mut staged, self.member, &[*exports, *export_instance])?;
        let has_function = apply(
            &mut staged,
            self.function_address,
            &[*export_instance, *function],
        )?;
        let mut body = staged
            .op2(Op2::And, has_module, has_exports)
            .and_then(|body| staged.op2(Op2::And, body, contains))
            .and_then(|body| staged.op2(Op2::And, body, has_function))
            .map_err(|source| WasmLogicError::Kernel { source })?;
        for &witness in [*module_instance, *exports, *export_instance].iter().rev() {
            body = staged
                .exists_tm(witness, body)
                .map_err(|source| WasmLogicError::Kernel { source })?;
        }
        let predicate_ty = staged
            .ty_arr(self.value_ty, self.bool_ty)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        let by_function = staged
            .lam_at(predicate_ty, *function, body)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        let curried_ty = staged
            .ty_arr(self.value_ty, predicate_ty)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        let predicate = staged
            .lam_at(curried_ty, *configuration, by_function)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        *kernel = staged;
        Ok(predicate)
    }
}

impl SpecTecExecution {
    /// Constructs the exact erased pair consumed by the `Steps` relation.
    ///
    /// # Errors
    ///
    /// Returns an error if either value has an incompatible classifier or a
    /// checked application fails. `kernel` is unchanged on failure.
    pub fn step_pair(
        self,
        kernel: &mut Kernel,
        before: Ref,
        after: Ref,
    ) -> Result<Ref, WasmLogicError> {
        let mut staged = kernel.fork();
        let pair = apply(&mut staged, self.pair, &[before, after])?;
        *kernel = staged;
        Ok(pair)
    }

    /// Converts a checked unary `Steps(pair(before, after))` fact to this
    /// adapter's curried `steps before after` view.
    ///
    /// The conversion beta-reduces both checked lambdas using explicit
    /// capture-avoiding substitution certificates. All theorem premises are
    /// preserved.
    ///
    /// # Errors
    ///
    /// Returns an error unless `relation_fact` proves the exact lowered
    /// relation application for `before` and `after`, or a checked
    /// substitution, syntax alignment, or theorem conversion fails. `kernel`
    /// is unchanged on failure.
    pub fn curry_steps_fact(
        self,
        kernel: &mut Kernel,
        before: Ref,
        after: Ref,
        relation_fact: Evidence,
    ) -> Result<Evidence, WasmLogicError> {
        curry_binary_fact(kernel, self.steps, before, after, relation_fact)
    }

    /// Builds the generic assertion-reachability schema from this exact
    /// `SpecTec` execution adapter and the two remaining structural views.
    ///
    /// `exported` recognizes exported function addresses in an initialized
    /// configuration. `host_call` recognizes configurations immediately before
    /// calling a particular host-function address.
    ///
    /// # Errors
    ///
    /// Returns an error when constructing the admissible-start predicate fails.
    /// `kernel` is unchanged on failure.
    pub fn assertion_reachability(
        self,
        kernel: &mut Kernel,
        exported: Ref,
        host_call: Ref,
    ) -> Result<AssertionReachability, WasmLogicError> {
        let starts = self.admissible_starts(kernel, exported)?;
        Ok(AssertionReachability {
            program_ty: self.state_ty,
            state_ty: self.state_ty,
            bool_ty: self.bool_ty,
            starts,
            steps: self.steps,
            calls: host_call,
        })
    }

    /// Constructs the curried predicate of admissible initial invocations.
    ///
    /// `exported` must classify as `state -> function-address -> bool`. The
    /// result existentially chooses a store, imports, initial and completed
    /// instantiation configurations, exported function address, arguments, and
    /// completed store. It conjoins the exact lowered `instantiate`, `Steps`,
    /// `store`, and `invoke` graph predicates with `exported`.
    ///
    /// # Errors
    ///
    /// Returns an error for an incompatible adapter, name exhaustion, or a
    /// rejected checked HOL construction. `kernel` is unchanged on failure.
    pub fn admissible_starts(
        self,
        kernel: &mut Kernel,
        exported: Ref,
    ) -> Result<Ref, WasmLogicError> {
        self.admissible_starts_avoiding(kernel, exported, &[])
    }

    fn admissible_starts_avoiding(
        self,
        kernel: &mut Kernel,
        exported: Ref,
        avoid: &[Ref],
    ) -> Result<Ref, WasmLogicError> {
        let mut staged = kernel.fork();
        let roots = [
            self.state_ty,
            self.bool_ty,
            self.instantiate,
            self.invoke,
            self.store,
            self.moduleinst,
            exported,
        ]
        .into_iter()
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
        let first = staged
            .fresh_name(&roots)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        let mut witnesses = Vec::with_capacity(7);
        for offset in 0..7 {
            let name = first.checked_add(offset).ok_or(WasmLogicError::Kernel {
                source: KernelError::TooManyNames,
            })?;
            witnesses.push(
                staged
                    .tm_fv(name, self.state_ty)
                    .map_err(|source| WasmLogicError::Kernel { source })?,
            );
        }
        let [
            store,
            externs,
            instantiation_start,
            initialized,
            function,
            arguments,
            initialized_store,
        ] = witnesses.as_slice()
        else {
            unreachable!()
        };
        let program_name = first.checked_add(7).ok_or(WasmLogicError::Kernel {
            source: KernelError::TooManyNames,
        })?;
        let initial_name = first.checked_add(8).ok_or(WasmLogicError::Kernel {
            source: KernelError::TooManyNames,
        })?;
        let program = staged
            .tm_fv(program_name, self.state_ty)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        let initial = staged
            .tm_fv(initial_name, self.state_ty)
            .map_err(|source| WasmLogicError::Kernel { source })?;

        let instantiated_by = apply(
            &mut staged,
            self.instantiate,
            &[*store, program, *externs, *instantiation_start],
        )?;
        let initialized_by = apply(
            &mut staged,
            self.steps,
            &[*instantiation_start, *initialized],
        )?;
        let is_exported = apply(&mut staged, exported, &[*initialized, *function])?;
        let has_store = apply(&mut staged, self.store, &[*initialized, *initialized_store])?;
        let invoked = apply(
            &mut staged,
            self.invoke,
            &[*initialized_store, *function, *arguments, initial],
        )?;
        let mut body = staged
            .op2(Op2::And, instantiated_by, initialized_by)
            .and_then(|body| staged.op2(Op2::And, body, is_exported))
            .and_then(|body| staged.op2(Op2::And, body, has_store))
            .and_then(|body| staged.op2(Op2::And, body, invoked))
            .map_err(|source| WasmLogicError::Kernel { source })?;
        for &witness in witnesses.iter().rev() {
            body = staged
                .exists_tm(witness, body)
                .map_err(|source| WasmLogicError::Kernel { source })?;
        }
        let predicate_ty = staged
            .ty_arr(self.state_ty, self.bool_ty)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        let initial_predicate = staged
            .lam_at(predicate_ty, initial, body)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        let starts_ty = staged
            .ty_arr(self.state_ty, predicate_ty)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        let starts = staged
            .lam_at(starts_ty, program, initial_predicate)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        *kernel = staged;
        Ok(starts)
    }

    /// Proves an admissible start from five checked semantic facts.
    ///
    /// The method constructs the same seven existential witnesses as
    /// [`Self::admissible_starts`], conjoins the supplied facts, introduces the
    /// witnesses, and beta-aligns the result with `starts program initial`.
    /// Every premise of the input facts remains visible.
    ///
    /// # Errors
    ///
    /// Returns an error if a fact has the wrong positive conclusion, a witness
    /// has an incompatible classifier, existential introduction fails, or a
    /// checked syntax/proof step is rejected. `kernel` is unchanged on failure.
    pub fn prove_admissible_start(
        self,
        kernel: &mut Kernel,
        exported: Ref,
        witness: AdmissibleStartWitness,
        facts: AdmissibleStartFacts,
    ) -> Result<Evidence, WasmLogicError> {
        let mut staged = kernel.fork();
        let witness_roots = [
            witness.program,
            witness.initial,
            witness.store,
            witness.externs,
            witness.instantiation_start,
            witness.initialized,
            witness.function,
            witness.arguments,
            witness.initialized_store,
        ];
        let starts = self.admissible_starts_avoiding(&mut staged, exported, &witness_roots)?;
        let concrete = start_body(&mut staged, self, exported, witness)?;
        let propositions = start_propositions(&mut staged, self, exported, witness)?;
        let theorems = [
            facts.instantiated,
            facts.initialized,
            facts.exported,
            facts.store,
            facts.invoked,
        ];
        let mut aligned = Vec::with_capacity(theorems.len());
        for (&theorem, &proposition) in theorems.iter().zip(&propositions) {
            aligned.push(align_positive_fact(&mut staged, theorem, proposition)?);
        }
        let mut conjunction = aligned[0];
        let mut proposition = propositions[0];
        for (&right_theorem, &right) in aligned.iter().zip(&propositions).skip(1) {
            proposition = staged.op2(Op2::And, proposition, right)?;
            conjunction = staged.and_right(conjunction, right_theorem, positive(proposition))?;
        }
        join_alpha_equivalent(&mut staged, proposition, concrete)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        staged.convert_conclusions(conjunction, proposition, concrete)?;

        let actual = start_existentials(witness);
        let first = staged.fresh_name(&[
            self.state_ty,
            self.bool_ty,
            self.instantiate,
            self.steps,
            self.store,
            self.invoke,
            exported,
            witness.program,
            witness.initial,
            starts,
        ])?;
        let mut binders = Vec::with_capacity(actual.len());
        for offset in 0..actual.len() {
            let name = first
                .checked_add(u64::try_from(offset).map_err(|_| KernelError::TooManyNames)?)
                .ok_or(KernelError::TooManyNames)?;
            binders.push(staged.tm_fv(name, self.state_ty)?);
        }
        let mut current_values = actual;
        let mut theorem = conjunction;
        let mut existential = concrete;
        for index in (0..binders.len()).rev() {
            current_values[index] = binders[index];
            let opened_witness = start_with_existentials(witness, current_values);
            let mut opened = start_body(&mut staged, self, exported, opened_witness)?;
            for &inner in binders[index + 1..].iter().rev() {
                opened = staged.exists_tm(inner, opened)?;
            }
            let introduced =
                introduce_exists(&mut staged, theorem, binders[index], opened, actual[index])
                    .map_err(|source| WasmLogicError::Exists { source })?;
            theorem = introduced.theorem;
            existential = introduced.proposition;
        }
        let result = curry_binary_fact(
            &mut staged,
            starts,
            witness.program,
            witness.initial,
            Evidence {
                proposition: existential,
                theorem,
                holds: true,
            },
        )?;
        *kernel = staged;
        Ok(result)
    }

    /// Constructs the claim that instantiating `program` cannot produce an
    /// initialized configuration with an exported function.
    ///
    /// # Errors
    ///
    /// Returns an error for fresh-name exhaustion or an ill-typed predicate.
    /// `kernel` is unchanged on failure.
    pub fn program_cannot_export(
        self,
        kernel: &mut Kernel,
        exported: Ref,
        program: Ref,
    ) -> Result<Ref, WasmLogicError> {
        program_cannot_export_avoiding(kernel, self, exported, program, &[])
    }

    /// Proves that a program has no admissible start when no initialized
    /// configuration reachable from that program exports a function.
    ///
    /// `cannot_export_fact` must prove [`Self::program_cannot_export`]. The proof
    /// opens the seven witnesses of an assumed admissible start, extracts its
    /// exported-function conjunct, specializes the universal negative fact,
    /// and closes the contradiction under the initial-state quantifier.
    ///
    /// # Errors
    ///
    /// Returns an error for a mismatched theorem, existential or universal
    /// elimination failure, or any rejected checked proof/syntax step.
    /// `kernel` is unchanged on failure.
    pub fn prove_no_admissible_start_from_no_export(
        self,
        kernel: &mut Kernel,
        exported: Ref,
        program: Ref,
        cannot_export_fact: covalence_logic_hol::ThmId,
    ) -> Result<Evidence, WasmLogicError> {
        let mut staged = kernel.fork();
        let cannot_export =
            program_cannot_export_avoiding(&mut staged, self, exported, program, &[])?;
        let cannot_export_fact =
            align_positive_fact(&mut staged, cannot_export_fact, cannot_export)?;
        let starts =
            self.admissible_starts_avoiding(&mut staged, exported, &[program, cannot_export])?;
        let initial_name = staged.fresh_name(&[program, cannot_export, starts])?;
        let initial = staged.tm_fv(initial_name, self.state_ty)?;
        let (starts_at, mut opened) =
            reduce_binary_application(&mut staged, starts, program, initial)?;
        let assumed_start = staged.identity(positive(starts_at))?;
        staged.convert_conclusions(assumed_start, starts_at, opened)?;
        let mut witnesses = Vec::with_capacity(7);
        for _ in 0..7 {
            let exists = open_exists(&mut staged, opened)
                .map_err(|source| WasmLogicError::Exists { source })?;
            staged.convert_conclusions(assumed_start, opened, exists.body)?;
            witnesses.push(exists.witness);
            opened = exists.body;
        }
        let mut prefix_fact =
            staged.expand_conclusion(assumed_start, positive(opened), Some(false))?;
        let first_four = sole_positive_conclusion_ref(&staged, prefix_fact)?;
        prefix_fact = staged.expand_conclusion(prefix_fact, positive(first_four), Some(false))?;
        let first_three = sole_positive_conclusion_ref(&staged, prefix_fact)?;

        let mut denied = Evidence {
            proposition: cannot_export,
            theorem: cannot_export_fact,
            holds: true,
        };
        for &argument in &witnesses[..5] {
            let specialized = forall_elim(&mut staged, denied.theorem, argument)
                .map_err(|source| WasmLogicError::Forall { source })?;
            denied = Evidence {
                proposition: specialized.proposition,
                theorem: specialized.theorem,
                holds: true,
            };
        }
        let denied_prefix = staged
            .arena()
            .children(denied.proposition)
            .and_then(|mut children| children.next())
            .ok_or(WasmLogicError::StartFact)?;
        join_alpha_equivalent(&mut staged, denied_prefix, first_three)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        let denied_fact =
            staged.expand_conclusion(denied.theorem, positive(denied.proposition), None)?;
        staged.convert_conclusions(denied_fact, denied_prefix, first_three)?;
        staged.not_left(prefix_fact, positive(first_three))?;
        let contradiction =
            staged.cut(denied_fact, prefix_fact, positive(first_three).negated())?;
        staged.not_right(contradiction, positive(starts_at))?;
        let does_not_start = staged.op1(covalence_logic_hol::builtin::Op1::Not, starts_at)?;
        let negative_start = staged.fold_conclusion(contradiction, positive(does_not_start))?;
        let no_start = staged.forall_tm(self.bool_ty, initial, does_not_start)?;
        let theorem = staged.forall_intro_at(negative_start, initial, no_start)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: no_start,
            theorem,
            holds: true,
        })
    }
}

fn program_cannot_export_avoiding(
    kernel: &mut Kernel,
    execution: SpecTecExecution,
    exported: Ref,
    program: Ref,
    avoid: &[Ref],
) -> Result<Ref, WasmLogicError> {
    let mut staged = kernel.fork();
    let roots = [execution.state_ty, execution.bool_ty, exported, program]
        .into_iter()
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
    let first = staged.fresh_name(&roots)?;
    let mut variables = Vec::with_capacity(5);
    for offset in 0..5 {
        let name = first
            .checked_add(u64::try_from(offset).map_err(|_| KernelError::TooManyNames)?)
            .ok_or(KernelError::TooManyNames)?;
        variables.push(staged.tm_fv(name, execution.state_ty)?);
    }
    let [store, externs, start, initialized, function] = variables.as_slice() else {
        unreachable!()
    };
    let instantiated = apply(
        &mut staged,
        execution.instantiate,
        &[*store, program, *externs, *start],
    )?;
    let stepped = apply(&mut staged, execution.steps, &[*start, *initialized])?;
    let is_exported = apply(&mut staged, exported, &[*initialized, *function])?;
    let prefix = staged.op2(Op2::And, instantiated, stepped)?;
    let prefix = staged.op2(Op2::And, prefix, is_exported)?;
    let mut proposition = staged.op1(covalence_logic_hol::builtin::Op1::Not, prefix)?;
    for &variable in variables.iter().rev() {
        proposition = staged.forall_tm(execution.bool_ty, variable, proposition)?;
    }
    *kernel = staged;
    Ok(proposition)
}

fn start_existentials(witness: AdmissibleStartWitness) -> [Ref; 7] {
    [
        witness.store,
        witness.externs,
        witness.instantiation_start,
        witness.initialized,
        witness.function,
        witness.arguments,
        witness.initialized_store,
    ]
}

fn start_with_existentials(
    witness: AdmissibleStartWitness,
    values: [Ref; 7],
) -> AdmissibleStartWitness {
    AdmissibleStartWitness {
        program: witness.program,
        initial: witness.initial,
        store: values[0],
        externs: values[1],
        instantiation_start: values[2],
        initialized: values[3],
        function: values[4],
        arguments: values[5],
        initialized_store: values[6],
    }
}

fn start_propositions(
    kernel: &mut Kernel,
    execution: SpecTecExecution,
    exported: Ref,
    witness: AdmissibleStartWitness,
) -> Result<[Ref; 5], WasmLogicError> {
    Ok([
        apply(
            kernel,
            execution.instantiate,
            &[
                witness.store,
                witness.program,
                witness.externs,
                witness.instantiation_start,
            ],
        )?,
        apply(
            kernel,
            execution.steps,
            &[witness.instantiation_start, witness.initialized],
        )?,
        apply(kernel, exported, &[witness.initialized, witness.function])?,
        apply(
            kernel,
            execution.store,
            &[witness.initialized, witness.initialized_store],
        )?,
        apply(
            kernel,
            execution.invoke,
            &[
                witness.initialized_store,
                witness.function,
                witness.arguments,
                witness.initial,
            ],
        )?,
    ])
}

fn start_body(
    kernel: &mut Kernel,
    execution: SpecTecExecution,
    exported: Ref,
    witness: AdmissibleStartWitness,
) -> Result<Ref, WasmLogicError> {
    let propositions = start_propositions(kernel, execution, exported, witness)?;
    propositions[1..]
        .iter()
        .try_fold(propositions[0], |left, &right| {
            kernel.op2(Op2::And, left, right).map_err(Into::into)
        })
}

fn curry_binary_fact(
    kernel: &mut Kernel,
    predicate: Ref,
    left: Ref,
    right: Ref,
    fact: Evidence,
) -> Result<Evidence, WasmLogicError> {
    if !fact.holds {
        return Err(WasmLogicError::StepFact);
    }
    let mut staged = kernel.fork();
    let (curried, reduced) = reduce_binary_application(&mut staged, predicate, left, right)?;
    join_alpha_equivalent(&mut staged, fact.proposition, reduced)
        .map_err(|source| WasmLogicError::Syntax { source })?;
    let theorem = staged.copy_theorem(fact.theorem)?;
    staged.convert_conclusions(theorem, fact.proposition, curried)?;
    *kernel = staged;
    Ok(Evidence {
        proposition: curried,
        theorem,
        holds: true,
    })
}

fn reduce_binary_application(
    kernel: &mut Kernel,
    predicate: Ref,
    left: Ref,
    right: Ref,
) -> Result<(Ref, Ref), WasmLogicError> {
    let mut outer_lambda = kernel
        .arena()
        .children(predicate)
        .ok_or(WasmLogicError::StepFact)?;
    let left_binder = outer_lambda.next().ok_or(WasmLogicError::StepFact)?;
    let outer_body = outer_lambda.next().ok_or(WasmLogicError::StepFact)?;
    drop(outer_lambda);
    let outer_application = kernel.app(predicate, left)?;
    let outer_reduced = substitute(kernel, left_binder, left, outer_body)
        .map_err(|source| WasmLogicError::Substitute { source })?;
    let outer_beta = kernel.tm_beta_fact(None, outer_application, outer_reduced.fact)?;
    kernel.union_syn_fact(outer_beta)?;

    let curried = kernel.app(outer_application, right)?;
    let reduced_application = kernel.app(outer_reduced.output, right)?;
    let right_refl = kernel.syn_refl(None, SynRel::Syn, right)?;
    let lifted_outer_beta = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        curried,
        reduced_application,
        &[outer_beta, right_refl],
    )?;
    kernel.union_syn_fact(lifted_outer_beta)?;
    let mut inner_lambda = kernel
        .arena()
        .children(outer_reduced.output)
        .ok_or(WasmLogicError::StepFact)?;
    let right_binder = inner_lambda.next().ok_or(WasmLogicError::StepFact)?;
    let inner_body = inner_lambda.next().ok_or(WasmLogicError::StepFact)?;
    drop(inner_lambda);
    let inner_reduced = substitute(kernel, right_binder, right, inner_body)
        .map_err(|source| WasmLogicError::Substitute { source })?;
    let inner_beta = kernel.tm_beta_fact(None, reduced_application, inner_reduced.fact)?;
    kernel.union_syn_fact(inner_beta)?;
    Ok((curried, inner_reduced.output))
}

fn align_positive_fact(
    kernel: &mut Kernel,
    theorem: covalence_logic_hol::ThmId,
    target: Ref,
) -> Result<covalence_logic_hol::ThmId, WasmLogicError> {
    let source = {
        let theorem = kernel
            .thm()
            .get(theorem)
            .ok_or(KernelError::MissingTheorem { id: theorem })?;
        let mut conclusions = theorem.rhs.rows();
        let Some([literal]) = conclusions.next() else {
            return Err(WasmLogicError::StartFact);
        };
        if conclusions.next().is_some() || !literal.is_positive() {
            return Err(WasmLogicError::StartFact);
        }
        Ref::new(literal.magnitude().cast_signed()).ok_or(WasmLogicError::StartFact)?
    };
    join_alpha_equivalent(kernel, source, target)
        .map_err(|source| WasmLogicError::Syntax { source })?;
    let aligned = kernel.copy_theorem(theorem)?;
    kernel.convert_conclusions(aligned, source, target)?;
    Ok(aligned)
}

fn sole_positive_conclusion_ref(
    kernel: &Kernel,
    theorem: covalence_logic_hol::ThmId,
) -> Result<Ref, WasmLogicError> {
    let theorem = kernel
        .thm()
        .get(theorem)
        .ok_or(KernelError::MissingTheorem { id: theorem })?;
    let mut conclusions = theorem.rhs.rows();
    let Some([literal]) = conclusions.next() else {
        return Err(WasmLogicError::StartFact);
    };
    if conclusions.next().is_some() || !literal.is_positive() {
        return Err(WasmLogicError::StartFact);
    }
    Ref::new(literal.magnitude().cast_signed()).ok_or(WasmLogicError::StartFact)
}

fn positive(reference: Ref) -> covalence_logic_hol::Lit {
    covalence_logic_hol::Lit::positive(reference.get())
}

fn apply(kernel: &mut Kernel, function: Ref, arguments: &[Ref]) -> Result<Ref, WasmLogicError> {
    arguments
        .iter()
        .try_fold(function, |function, &argument| {
            kernel.app(function, argument)
        })
        .map_err(|source| WasmLogicError::Kernel { source })
}

/// Why the WebAssembly program-logic adapter could not be constructed.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum WasmLogicError {
    /// The exact lowered document lacks one required declaration.
    #[snafu(display("expected one SpecTec {kind:?} declaration named {name:?}, found {count}"))]
    Declaration {
        /// Required declaration category.
        kind: IlKind,
        /// Required exact source name.
        name: &'static str,
        /// Number of matching declarations.
        count: usize,
    },
    /// The lowering did not use one required structural interpretation.
    #[snafu(display("missing SpecTec interpretation operation {label:?}"))]
    Operation {
        /// Required stable operation label.
        label: Symbol,
    },
    /// A supplied fact is not a positive lowered `Steps` relation fact.
    #[snafu(display("supplied SpecTec Steps fact has the wrong shape"))]
    StepFact,
    /// A supplied admissible-start theorem is not one positive fact.
    #[snafu(display("supplied SpecTec admissible-start fact has the wrong shape"))]
    StartFact,
    /// A checked HOL construction failed.
    #[snafu(display("could not construct SpecTec program-logic adapter: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Checked capture-avoiding substitution failed.
    #[snafu(display("could not beta-reduce the SpecTec Steps adapter: {source}"))]
    Substitute {
        /// Underlying derived substitution failure.
        source: ModelError,
    },
    /// Checked syntax alignment failed.
    #[snafu(display("could not align a SpecTec Steps fact: {source}"))]
    Syntax {
        /// Underlying derived syntax failure.
        source: SyntaxError,
    },
    /// Checked existential introduction failed.
    #[snafu(display("could not introduce a SpecTec admissible-start witness: {source}"))]
    Exists {
        /// Underlying derived existential failure.
        source: ExistsError,
    },
    /// Equality-encoded universal specialization failed.
    #[snafu(display("could not specialize absence of exported functions: {source}"))]
    Forall {
        /// Underlying derived universal failure.
        source: ForallError,
    },
}

impl From<KernelError> for WasmLogicError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

/// Constructs the structural HOL term for the empty WebAssembly module.
///
/// The term uses the exact empty-list, absent-optional, 11-field tuple, and
/// `MODULE%%%%%%%%%%%` constructor operations recorded by the complete
/// lowering. It is therefore a module-syntax term under that lowering's value
/// interpretation; proving its behavior still requires the corresponding
/// representation laws and complete `SpecTec` theory.
///
/// # Errors
///
/// Returns an error if a required operation is absent or a checked application
/// fails. `kernel` is unchanged on failure.
pub fn empty_wasm_module(
    kernel: &mut Kernel,
    document: &ParameterizedDocument,
) -> Result<Ref, WasmLogicError> {
    let builder = SpecTecValueBuilder::new(document);
    let mut staged = kernel.fork();
    let empty_list = builder.list(&mut staged, &[])?;
    let absent = builder.optional(&mut staged, None)?;
    let payload = builder.tuple(
        &mut staged,
        &[
            empty_list, empty_list, empty_list, empty_list, empty_list, empty_list, empty_list,
            empty_list, empty_list, absent, empty_list,
        ],
    )?;
    let result = builder.case(&mut staged, "MODULE%%%%%%%%%%%", payload)?;
    *kernel = staged;
    Ok(result)
}

/// Constructs the structural Wasm module that exports its `assert` import.
///
/// `import_module`, `assert_name`, and `export_name` are already constructed
/// `SpecTec` `name` values. Keeping name construction outside this function lets
/// callers use structural names now and substitute a checked byte decoder later
/// without changing the module-composition API.
///
/// The resulting module has one nullary function type, one function import at
/// type index zero, and one export of function index zero. Invoking that export
/// therefore invokes the imported function under the intended grounded value
/// interpretation. This function constructs syntax and creates no theorem.
///
/// # Errors
///
/// Returns an error if a required recorded constructor is absent, an input is
/// not a structural value, or a checked application fails. `kernel` is
/// unchanged on failure.
pub fn forwarding_wasm_module(
    kernel: &mut Kernel,
    document: &ParameterizedDocument,
    import_module: Ref,
    assert_name: Ref,
    export_name: Ref,
) -> Result<Ref, WasmLogicError> {
    let builder = SpecTecValueBuilder::new(document);
    let mut staged = kernel.fork();
    let empty = builder.list(&mut staged, &[])?;
    let absent = builder.optional(&mut staged, None)?;
    let zero = builder.number(&mut staged, "nat", "0")?;

    let function_type = builder.case_fields(&mut staged, "FUNC%->%", &[empty, empty])?;
    let subtype = builder.case_fields(&mut staged, "SUB%%%", &[absent, empty, function_type])?;
    let subtypes = builder.list(&mut staged, &[subtype])?;
    let recursive_type = builder.case_fields(&mut staged, "REC%", &[subtypes])?;
    let module_type = builder.case_fields(&mut staged, "TYPE%", &[recursive_type])?;
    let types = builder.list(&mut staged, &[module_type])?;

    let type_index = builder.case_fields(&mut staged, "_IDX%", &[zero])?;
    let external_type = builder.case_fields(&mut staged, "FUNC%", &[type_index])?;
    let import = builder.case_fields(
        &mut staged,
        "IMPORT%%%",
        &[import_module, assert_name, external_type],
    )?;
    let imports = builder.list(&mut staged, &[import])?;

    let function_index = builder.case_fields(&mut staged, "FUNC%", &[zero])?;
    let export = builder.case_fields(&mut staged, "EXPORT%%", &[export_name, function_index])?;
    let exports = builder.list(&mut staged, &[export])?;
    let module = builder.case_fields(
        &mut staged,
        "MODULE%%%%%%%%%%%",
        &[
            types, imports, empty, empty, empty, empty, empty, empty, empty, absent, exports,
        ],
    )?;
    *kernel = staged;
    Ok(module)
}

fn operation(
    document: &ParameterizedDocument,
    label: &str,
    domains: &[Ref],
    codomain: Ref,
) -> Result<Ref, WasmLogicError> {
    document
        .operations()
        .find(|operation| {
            operation.signature.label == label
                && operation.signature.domains.as_ref() == domains
                && operation.signature.codomain == codomain
        })
        .map(|operation| operation.reference)
        .ok_or_else(|| WasmLogicError::Operation {
            label: Symbol::new(label),
        })
}

/// Extracts a checked curried view of the WebAssembly `Steps` relation.
///
/// The `SpecTec` IL represents a multi-argument relation as a predicate over one
/// interpreted tuple. This adapter retrieves the exact lowered `Steps` slot and
/// the exact tuple constructor used by that lowering, then constructs
/// `lambda before after. Steps(tuple(before, after))`. It does not assert the
/// complete theory or create a theorem.
///
/// # Errors
///
/// Returns an error unless `Steps` is unique, the binary tuple operation was
/// used by the lowering, and all checked applications and abstractions typecheck.
/// `kernel` is unchanged on failure.
pub fn spectec_execution(
    kernel: &mut Kernel,
    document: &ParameterizedDocument,
) -> Result<SpecTecExecution, WasmLogicError> {
    let ids = document.schema.named(IlKind::Relation, "Steps");
    let [id] = ids else {
        return Err(WasmLogicError::Declaration {
            kind: IlKind::Relation,
            name: "Steps",
            count: ids.len(),
        });
    };
    let relation = document
        .schema
        .declaration(*id)
        .ok_or(WasmLogicError::Declaration {
            kind: IlKind::Relation,
            name: "Steps",
            count: 0,
        })?
        .reference();
    let instantiate = unique_definition(document, "instantiate")?;
    let invoke = unique_definition(document, "invoke")?;
    let store = unique_definition(document, "store")?;
    let moduleinst = unique_definition(document, "moduleinst")?;
    let tuple = steps_pair_operation(kernel, document, *id)?;

    let mut staged = kernel.fork();
    let roots = [
        relation,
        instantiate,
        invoke,
        store,
        moduleinst,
        tuple,
        document.schema.value(),
        document.schema.bool_ty(),
    ];
    let before_name = staged
        .fresh_name(&roots)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let after_name = before_name.checked_add(1).ok_or(WasmLogicError::Kernel {
        source: KernelError::TooManyNames,
    })?;
    let before = staged
        .tm_fv(before_name, document.schema.value())
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let after = staged
        .tm_fv(after_name, document.schema.value())
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let pair = staged
        .app(tuple, before)
        .and_then(|tuple| staged.app(tuple, after))
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let related = staged
        .app(relation, pair)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let predicate_ty = staged
        .ty_arr(document.schema.value(), document.schema.bool_ty())
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let inner = staged
        .lam_at(predicate_ty, after, related)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let curried_ty = staged
        .ty_arr(document.schema.value(), predicate_ty)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let steps = staged
        .lam_at(curried_ty, before, inner)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    *kernel = staged;
    Ok(SpecTecExecution {
        state_ty: document.schema.value(),
        bool_ty: document.schema.bool_ty(),
        steps,
        pair: tuple,
        steps_ty: curried_ty,
        instantiate,
        invoke,
        store,
        moduleinst,
    })
}

fn steps_pair_operation(
    kernel: &Kernel,
    document: &ParameterizedDocument,
    id: covalence_data_spectec::DeclarationId,
) -> Result<Ref, WasmLogicError> {
    let steps_definition =
        document
            .semantics
            .relations()
            .get(&id)
            .ok_or(WasmLogicError::Declaration {
                kind: IlKind::Relation,
                name: "Steps",
                count: 0,
            })?;
    let argument = *steps_definition
        .rule_schemas
        .first()
        .and_then(|rule| rule.conclusion.first())
        .ok_or_else(|| WasmLogicError::Operation {
            label: Symbol::new("Steps pair"),
        })?;
    let mut outer_children =
        kernel
            .arena()
            .children(argument)
            .ok_or_else(|| WasmLogicError::Operation {
                label: Symbol::new("Steps pair"),
            })?;
    let partial_pair = outer_children
        .next()
        .ok_or_else(|| WasmLogicError::Operation {
            label: Symbol::new("Steps pair"),
        })?;
    drop(outer_children);
    kernel
        .arena()
        .children(partial_pair)
        .and_then(|mut children| children.next())
        .ok_or_else(|| WasmLogicError::Operation {
            label: Symbol::new("Steps pair"),
        })
}

fn unique_definition(
    document: &ParameterizedDocument,
    name: &'static str,
) -> Result<Ref, WasmLogicError> {
    let ids = document.schema.named(IlKind::Definition, name);
    let [id] = ids else {
        return Err(WasmLogicError::Declaration {
            kind: IlKind::Definition,
            name,
            count: ids.len(),
        });
    };
    document
        .schema
        .declaration(*id)
        .map(crate::HolDeclaration::reference)
        .ok_or(WasmLogicError::Declaration {
            kind: IlKind::Definition,
            name,
            count: 0,
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn predicate(kernel: &mut Kernel, value: Ref, bool_ty: Ref, arity: usize, name: u64) -> Ref {
        let classifier = (0..arity)
            .try_fold(bool_ty, |tail, _| kernel.ty_arr(value, tail))
            .unwrap();
        kernel.tm_fv(name, classifier).unwrap()
    }

    #[test]
    fn spectec_graphs_compose_into_calls_assert_syntax() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let value = kernel.ty_fv(0, star).unwrap();
        let steps_ty = (0..2)
            .try_fold(bool_ty, |tail, _| kernel.ty_arr(value, tail))
            .unwrap();
        let pair_tail = kernel.ty_arr(value, value).unwrap();
        let pair_ty = kernel.ty_arr(value, pair_tail).unwrap();
        let pair = kernel.tm_fv(22, pair_ty).unwrap();
        let execution = SpecTecExecution {
            state_ty: value,
            bool_ty,
            steps: predicate(&mut kernel, value, bool_ty, 2, 10),
            pair,
            steps_ty,
            instantiate: predicate(&mut kernel, value, bool_ty, 4, 11),
            invoke: predicate(&mut kernel, value, bool_ty, 4, 12),
            store: predicate(&mut kernel, value, bool_ty, 2, 13),
            moduleinst: predicate(&mut kernel, value, bool_ty, 2, 18),
        };
        let before = kernel.tm_fv(23, value).unwrap();
        let after = kernel.tm_fv(24, value).unwrap();
        let paired = execution.step_pair(&mut kernel, before, after).unwrap();
        assert_eq!(kernel.classifier(paired).unwrap(), value);
        let exported = ExportedFunctionView {
            value_ty: value,
            bool_ty,
            module_instance: execution.moduleinst,
            exports: predicate(&mut kernel, value, bool_ty, 2, 19),
            member: predicate(&mut kernel, value, bool_ty, 2, 20),
            function_address: predicate(&mut kernel, value, bool_ty, 2, 21),
        }
        .predicate(&mut kernel)
        .unwrap();
        let host_call = predicate(&mut kernel, value, bool_ty, 2, 15);
        let program = kernel.tm_fv(16, value).unwrap();
        let assert_function = kernel.tm_fv(17, value).unwrap();

        let reachability = execution
            .assertion_reachability(&mut kernel, exported, host_call)
            .unwrap();
        let proposition = reachability
            .calls_assert(&mut kernel, program, assert_function)
            .unwrap();

        assert_eq!(kernel.classifier(proposition).unwrap(), bool_ty);
    }

    #[test]
    fn checked_graph_facts_prove_an_admissible_start() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let value = kernel.ty_fv(0, star).unwrap();
        let steps_ty = (0..2)
            .try_fold(bool_ty, |tail, _| kernel.ty_arr(value, tail))
            .unwrap();
        let pair_tail = kernel.ty_arr(value, value).unwrap();
        let pair_ty = kernel.ty_arr(value, pair_tail).unwrap();
        let execution = SpecTecExecution {
            state_ty: value,
            bool_ty,
            steps: predicate(&mut kernel, value, bool_ty, 2, 10),
            pair: kernel.tm_fv(11, pair_ty).unwrap(),
            steps_ty,
            instantiate: predicate(&mut kernel, value, bool_ty, 4, 12),
            invoke: predicate(&mut kernel, value, bool_ty, 4, 13),
            store: predicate(&mut kernel, value, bool_ty, 2, 14),
            moduleinst: predicate(&mut kernel, value, bool_ty, 2, 15),
        };
        let exported = predicate(&mut kernel, value, bool_ty, 2, 16);
        let values = (20..29)
            .map(|name| kernel.tm_fv(name, value).unwrap())
            .collect::<Vec<_>>();
        let witness = AdmissibleStartWitness {
            program: values[0],
            initial: values[1],
            store: values[2],
            externs: values[3],
            instantiation_start: values[4],
            initialized: values[5],
            function: values[6],
            arguments: values[7],
            initialized_store: values[8],
        };
        let propositions = start_propositions(&mut kernel, execution, exported, witness).unwrap();
        let fact =
            |kernel: &mut Kernel, proposition: Ref| kernel.identity(positive(proposition)).unwrap();
        let facts = AdmissibleStartFacts {
            instantiated: fact(&mut kernel, propositions[0]),
            initialized: fact(&mut kernel, propositions[1]),
            exported: fact(&mut kernel, propositions[2]),
            store: fact(&mut kernel, propositions[3]),
            invoked: fact(&mut kernel, propositions[4]),
        };

        let proved = execution
            .prove_admissible_start(&mut kernel, exported, witness, facts)
            .unwrap();

        crate::EvidenceScope::positive(&propositions)
            .check(&kernel, proved)
            .unwrap();
    }

    #[test]
    fn program_specific_absence_of_exports_refutes_reachability() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let value = kernel.ty_fv(0, star).unwrap();
        let steps_ty = (0..2)
            .try_fold(bool_ty, |tail, _| kernel.ty_arr(value, tail))
            .unwrap();
        let pair_tail = kernel.ty_arr(value, value).unwrap();
        let pair_ty = kernel.ty_arr(value, pair_tail).unwrap();
        let execution = SpecTecExecution {
            state_ty: value,
            bool_ty,
            steps: predicate(&mut kernel, value, bool_ty, 2, 10),
            pair: kernel.tm_fv(11, pair_ty).unwrap(),
            steps_ty,
            instantiate: predicate(&mut kernel, value, bool_ty, 4, 12),
            invoke: predicate(&mut kernel, value, bool_ty, 4, 13),
            store: predicate(&mut kernel, value, bool_ty, 2, 14),
            moduleinst: predicate(&mut kernel, value, bool_ty, 2, 15),
        };
        let exported = predicate(&mut kernel, value, bool_ty, 2, 16);
        let program = kernel.tm_fv(17, value).unwrap();
        let cannot_export = execution
            .program_cannot_export(&mut kernel, exported, program)
            .unwrap();
        let cannot_export_fact = kernel.identity(positive(cannot_export)).unwrap();

        let no_start = execution
            .prove_no_admissible_start_from_no_export(
                &mut kernel,
                exported,
                program,
                cannot_export_fact,
            )
            .unwrap();

        crate::EvidenceScope::positive(&[cannot_export])
            .check(&kernel, no_start)
            .unwrap();
        let host_call = predicate(&mut kernel, value, bool_ty, 2, 18);
        let assert_function = kernel.tm_fv(19, value).unwrap();
        let reachability = execution
            .assertion_reachability(&mut kernel, exported, host_call)
            .unwrap();
        let never_calls = reachability
            .prove_never_calls_assert_from_no_start(
                &mut kernel,
                program,
                assert_function,
                no_start.theorem,
            )
            .unwrap();
        crate::EvidenceScope::positive(&[cannot_export])
            .check(&kernel, never_calls)
            .unwrap();
    }
}
