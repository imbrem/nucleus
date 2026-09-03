//! Adapters from the complete `SpecTec` document to program-logic predicates.

use std::sync::Arc;

use covalence_data_basic::Symbol;
use covalence_data_spectec::IlKind;
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, SynRel, Tag, TmTag, builtin::Op2};
use covalence_logic_hol_derived::{
    ExistsError, ForallError, ModelError, SyntaxError, forall_elim, introduce_exists,
    join_alpha_equivalent, join_same_syntax, open_exists, substitute,
};

use crate::{
    AssertionReachability, ContextualObservation, Evidence, FiniteSequenceLaw, FunctionObservation,
    ParameterizedDocument, StructuralConstructor, StructuralConstructorLaws,
    StructuralSequenceAlgebra, StructuralValueAlgebra,
};

fn application_spine(kernel: &Kernel, mut value: Ref) -> (Ref, Vec<Ref>) {
    let mut arguments = Vec::new();
    while kernel.arena().tag(value) == Some(Tag::Tm(TmTag::App)) {
        let Some(children) = kernel.arena().children(value) else {
            break;
        };
        let children = children.collect::<Vec<_>>();
        let [function, argument] = children.as_slice() else {
            break;
        };
        arguments.push(*argument);
        value = *function;
    }
    arguments.reverse();
    (value, arguments)
}

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

    /// Returns the generic faithfulness-law schema for this erased value carrier.
    #[must_use]
    pub const fn algebra(self) -> StructuralValueAlgebra {
        StructuralValueAlgebra {
            value_ty: self.document.schema.value(),
            bool_ty: self.document.schema.bool_ty(),
        }
    }

    /// Resolves and validates one exact recorded structural constructor.
    ///
    /// `label` is the lowering's full operation label, such as
    /// `expression:Tuple` or `expression:Case("MODULE%%%%%%%%%%%")`.
    /// The returned shape can be passed to
    /// [`StructuralValueAlgebra::injective`] or
    /// [`StructuralValueAlgebra::disjoint`].
    ///
    /// # Errors
    ///
    /// Returns an error if the operation was not recorded at this arity or its
    /// classifier is incompatible. `kernel` is unchanged on failure.
    pub fn structural_constructor(
        self,
        kernel: &mut Kernel,
        label: &str,
        arity: usize,
    ) -> Result<StructuralConstructor, WasmLogicError> {
        let domains = vec![self.value_ty(); arity];
        let operation = operation(self.document, label, &domains, self.value_ty())?;
        self.algebra()
            .constructor(kernel, operation, arity)
            .map_err(|source| WasmLogicError::Kernel { source })
    }

    /// Finds the minimal recorded structural-constructor vocabulary used by
    /// the supplied value roots.
    ///
    /// Constructors are returned in deterministic first-use order. Only full
    /// application spines whose recorded domains and codomain are this erased
    /// value carrier are selected; relation predicates and partial
    /// applications are excluded.
    ///
    /// # Errors
    ///
    /// Returns an error if a root has another classifier or a selected
    /// operation cannot be validated. `kernel` is unchanged on failure.
    pub fn constructors_in(
        self,
        kernel: &mut Kernel,
        roots: &[Ref],
    ) -> Result<Arc<[StructuralConstructor]>, WasmLogicError> {
        let mut staged = kernel.fork();
        for &root in roots {
            let actual = staged
                .classifier(root)
                .map_err(|source| WasmLogicError::Kernel { source })?;
            if actual != self.value_ty() {
                return Err(WasmLogicError::Kernel {
                    source: KernelError::ClassifierMismatch {
                        expected: self.value_ty(),
                        actual,
                    },
                });
            }
        }
        let mut pending = roots.iter().rev().copied().collect::<Vec<_>>();
        let mut visited = Vec::new();
        let mut constructors = Vec::new();
        while let Some(value) = pending.pop() {
            if visited.contains(&value) {
                continue;
            }
            visited.push(value);
            let (head, arguments) = application_spine(&staged, value);
            if let Some(operation) = self.document.operations().find(|operation| {
                operation.reference == head
                    && operation.signature.codomain == self.value_ty()
                    && operation
                        .signature
                        .domains
                        .iter()
                        .all(|&domain| domain == self.value_ty())
                    && operation.signature.domains.len() == arguments.len()
            }) {
                let constructor = self
                    .algebra()
                    .constructor(
                        &mut staged,
                        operation.reference,
                        operation.signature.domains.len(),
                    )
                    .map_err(|source| WasmLogicError::Kernel { source })?;
                if !constructors.contains(&constructor) {
                    constructors.push(constructor);
                }
            }
            if let Some(children) = staged.arena().children(value) {
                let children = children.collect::<Vec<_>>();
                pending.extend(children.into_iter().rev());
            }
        }
        *kernel = staged;
        Ok(Arc::from(constructors))
    }

    /// Constructs the complete constructor-separation obligations required by
    /// the supplied structural roots.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`Self::constructors_in`]
    /// or if checked law construction fails. `kernel` is unchanged on failure.
    pub fn constructor_laws_for(
        self,
        kernel: &mut Kernel,
        roots: &[Ref],
    ) -> Result<StructuralConstructorLaws, WasmLogicError> {
        let mut staged = kernel.fork();
        let constructors = self.constructors_in(&mut staged, roots)?;
        let laws = self
            .algebra()
            .constructor_laws(&mut staged, &constructors)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        *kernel = staged;
        Ok(laws)
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

    /// Matches a value constructed by [`Self::case_fields`] and returns its fields.
    ///
    /// This inspects only the exact recorded case and tuple application spine;
    /// it creates no theorem or syntax fact. A different structural value is
    /// the expected `Ok(None)` outcome.
    ///
    /// # Errors
    ///
    /// Returns an error if the required case or tuple operation was not
    /// recorded. `kernel` is unchanged.
    pub fn match_case_fields(
        self,
        kernel: &Kernel,
        notation: &str,
        arity: usize,
        value: Ref,
    ) -> Result<Option<Vec<Ref>>, WasmLogicError> {
        let value_ty = self.value_ty();
        let case_label = format!("expression:Case({notation:?})");
        let case_constructor = operation(self.document, &case_label, &[value_ty], value_ty)?;
        let Some(case_children) = kernel.arena().children(value) else {
            return Ok(None);
        };
        let case_children = case_children.collect::<Vec<_>>();
        let [actual_case, payload] = case_children.as_slice() else {
            return Ok(None);
        };
        if *actual_case != case_constructor {
            return Ok(None);
        }
        let tuple_constructor = operation(
            self.document,
            "expression:Tuple",
            &vec![value_ty; arity],
            value_ty,
        )?;
        let mut current = *payload;
        let mut fields = Vec::with_capacity(arity);
        for _ in 0..arity {
            let Some(children) = kernel.arena().children(current) else {
                return Ok(None);
            };
            let children = children.collect::<Vec<_>>();
            let [function, argument] = children.as_slice() else {
                return Ok(None);
            };
            fields.push(*argument);
            current = *function;
        }
        if current != tuple_constructor {
            return Ok(None);
        }
        fields.reverse();
        Ok(Some(fields))
    }

    /// Selects one named record field through the exact operation recorded by
    /// the lowering.
    ///
    /// # Errors
    ///
    /// Returns an error if the field operation was not recorded, the input has
    /// an incompatible classifier, or checked application fails.
    pub fn field(
        self,
        kernel: &mut Kernel,
        record: Ref,
        name: &str,
    ) -> Result<Ref, WasmLogicError> {
        let label = format!("expression:Dot({name:?})");
        self.construct(kernel, &label, &[record])
    }

    /// Returns the exact lowered sequence-membership predicate.
    ///
    /// # Errors
    ///
    /// Returns an error unless the lowering recorded the binary structural
    /// membership operation with Boolean codomain.
    pub fn membership_predicate(self) -> Result<Ref, WasmLogicError> {
        operation(
            self.document,
            "expression:Membership",
            &[self.value_ty(), self.value_ty()],
            self.document.schema.bool_ty(),
        )
    }

    /// Returns the exact recorded sequence-membership operation as a generic
    /// checked sequence algebra.
    ///
    /// # Errors
    ///
    /// Returns an error unless the lowering recorded a compatible membership
    /// predicate. `kernel` is unchanged on failure.
    pub fn sequence_algebra(
        self,
        kernel: &mut Kernel,
    ) -> Result<StructuralSequenceAlgebra, WasmLogicError> {
        let member = self.membership_predicate()?;
        StructuralSequenceAlgebra::new(kernel, self.algebra(), member)
            .map_err(|source| WasmLogicError::Kernel { source })
    }

    /// Constructs finite membership semantics for the exact recorded
    /// `SpecTec` list constructor at `elements.len()`.
    ///
    /// # Errors
    ///
    /// Returns an error if the list constructor or membership operation is
    /// absent or incompatible, or checked law construction fails. `kernel` is
    /// unchanged on failure.
    pub fn list_membership_law(
        self,
        kernel: &mut Kernel,
        elements: &[Ref],
    ) -> Result<FiniteSequenceLaw, WasmLogicError> {
        let mut staged = kernel.fork();
        let constructor =
            self.structural_constructor(&mut staged, "expression:List", elements.len())?;
        let sequence = self.sequence_algebra(&mut staged)?;
        let law = sequence
            .membership_law(&mut staged, constructor, elements)
            .map_err(|source| WasmLogicError::Kernel { source })?;
        *kernel = staged;
        Ok(law)
    }

    /// Constructs a relational graph for one exact record-field operation.
    ///
    /// The result is `lambda record output. field(record) = output`; it creates
    /// syntax only and introduces no theorem fact.
    ///
    /// # Errors
    ///
    /// Returns an error if the operation is absent or checked name, equality,
    /// application, or abstraction construction fails. `kernel` is unchanged
    /// on failure.
    pub fn field_graph(self, kernel: &mut Kernel, name: &str) -> Result<Ref, WasmLogicError> {
        let mut staged = kernel.fork();
        let value_ty = self.value_ty();
        let bool_ty = self.document.schema.bool_ty();
        let first = staged.fresh_name(&[value_ty, bool_ty])?;
        let record = staged.tm_fv(first, value_ty)?;
        let output = staged.tm_fv(
            first.checked_add(1).ok_or(KernelError::TooManyNames)?,
            value_ty,
        )?;
        let selected = self.field(&mut staged, record, name)?;
        let equality = staged.eq(bool_ty, selected, output)?;
        let output_predicate_ty = staged.ty_arr(value_ty, bool_ty)?;
        let by_output = staged.lam_at(output_predicate_ty, output, equality)?;
        let graph_ty = staged.ty_arr(value_ty, output_predicate_ty)?;
        let graph = staged.lam_at(graph_ty, record, by_output)?;
        *kernel = staged;
        Ok(graph)
    }

    /// Constructs a relational view of one field in an exact structural record.
    ///
    /// The graph existentially reconstructs the record with the recorded
    /// `Struct` operation and equates the selected field with its output. This
    /// does not require the source document to use a `Dot` operation.
    ///
    /// # Errors
    ///
    /// Returns an error if `selected` is absent or ambiguous, the exact struct
    /// operation was not recorded, or checked construction fails. `kernel` is
    /// unchanged on failure.
    #[allow(clippy::too_many_lines)]
    pub fn struct_field_graph(
        self,
        kernel: &mut Kernel,
        fields: &[&str],
        selected: &str,
    ) -> Result<Ref, WasmLogicError> {
        let mut selected_indices = fields
            .iter()
            .enumerate()
            .filter_map(|(index, field)| (*field == selected).then_some(index));
        let selected_index = selected_indices
            .next()
            .ok_or_else(|| WasmLogicError::Operation {
                label: Symbol::new(selected),
            })?;
        if selected_indices.next().is_some() {
            return Err(WasmLogicError::Operation {
                label: Symbol::new(selected),
            });
        }
        let mut staged = kernel.fork();
        let value_ty = self.value_ty();
        let bool_ty = self.document.schema.bool_ty();
        let label = format!("expression:Struct({fields:?})");
        let domains = vec![value_ty; fields.len()];
        let constructor = operation(self.document, &label, &domains, value_ty)?;
        let first = staged.fresh_name(&[value_ty, bool_ty, constructor])?;
        let record = staged.tm_fv(first, value_ty)?;
        let output = staged.tm_fv(
            first.checked_add(1).ok_or(KernelError::TooManyNames)?,
            value_ty,
        )?;
        let field_values = (0..fields.len())
            .map(|offset| {
                let offset = u64::try_from(offset).map_err(|_| KernelError::TooManyNames)?;
                let name = first
                    .checked_add(2)
                    .and_then(|name| name.checked_add(offset))
                    .ok_or(KernelError::TooManyNames)?;
                staged.tm_fv(name, value_ty)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let constructed = apply(&mut staged, constructor, &field_values)?;
        let record_equality = staged.eq(bool_ty, record, constructed)?;
        let output_equality = staged.eq(bool_ty, field_values[selected_index], output)?;
        let mut body = staged.op2(Op2::And, record_equality, output_equality)?;
        for &field_value in field_values.iter().rev() {
            body = staged.exists_tm(field_value, body)?;
        }
        let output_predicate_ty = staged.ty_arr(value_ty, bool_ty)?;
        let by_output = staged.lam_at(output_predicate_ty, output, body)?;
        let graph_ty = staged.ty_arr(value_ty, output_predicate_ty)?;
        let graph = staged.lam_at(graph_ty, record, by_output)?;
        *kernel = staged;
        Ok(graph)
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
    /// Exact `SpecTec` predicate `export-instance -> export-list -> bool`.
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
        let contains = apply(&mut staged, self.member, &[*export_instance, *exports])?;
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

    /// Constructs the claim that no freshly instantiated export list has an entry.
    ///
    /// The result quantifies stores, imports, instantiation states, module
    /// instances, export lists, and export entries. It rules out membership in
    /// every export list exposed by the exact structural view of the
    /// configuration returned by instantiating `program`.
    ///
    /// # Errors
    ///
    /// Returns an error for a foreign execution carrier, fresh-name exhaustion,
    /// or a rejected checked application or Boolean constructor. `kernel` is
    /// unchanged on failure.
    pub fn program_has_no_export_entries(
        self,
        kernel: &mut Kernel,
        execution: SpecTecExecution,
        program: Ref,
    ) -> Result<Ref, WasmLogicError> {
        no_export_entries_avoiding(kernel, self, execution, program, &[])
            .map(|parts| parts.proposition)
    }

    /// Constructs the invariant that every reachable export-list view of a
    /// program equals `expected`.
    ///
    /// This is deliberately separate from list membership: execution
    /// semantics establish which list is exposed, while a generic list model
    /// establishes what membership in that list means.
    ///
    /// # Errors
    ///
    /// Returns an error for a foreign carrier, fresh-name exhaustion, or a
    /// rejected checked application, equality, or Boolean constructor.
    /// `kernel` is unchanged on failure.
    pub fn program_export_lists_equal(
        self,
        kernel: &mut Kernel,
        execution: SpecTecExecution,
        program: Ref,
        expected: Ref,
    ) -> Result<Ref, WasmLogicError> {
        program_export_lists_equal_avoiding(kernel, self, execution, program, expected, &[])
    }

    /// Constructs the generic representation law that `list` has no members.
    ///
    /// # Errors
    ///
    /// Returns an error for a foreign carrier, fresh-name exhaustion, or a
    /// rejected checked application or Boolean constructor. `kernel` is
    /// unchanged on failure.
    pub fn list_has_no_members(
        self,
        kernel: &mut Kernel,
        list: Ref,
    ) -> Result<Ref, WasmLogicError> {
        list_has_no_members_avoiding(kernel, self, list, &[])
    }

    /// Derives absence of export entries from an execution invariant and a
    /// generic empty-list membership law.
    ///
    /// The first theorem must prove [`Self::program_export_lists_equal`]; the
    /// second must prove [`Self::list_has_no_members`] for the same list. Both
    /// sets of premises remain visible in the resulting theorem.
    ///
    /// # Errors
    ///
    /// Returns an error when either theorem has the wrong conclusion or when
    /// checked specialization, equality substitution, or contradiction
    /// closure fails. `kernel` is unchanged on failure.
    #[allow(clippy::too_many_lines)]
    pub fn prove_no_export_entries_from_list_invariant(
        self,
        kernel: &mut Kernel,
        execution: SpecTecExecution,
        program: Ref,
        expected: Ref,
        export_lists_equal_fact: covalence_logic_hol::ThmId,
        no_members_fact: covalence_logic_hol::ThmId,
    ) -> Result<Evidence, WasmLogicError> {
        let mut staged = kernel.fork();
        let invariant = program_export_lists_equal_avoiding(
            &mut staged,
            self,
            execution,
            program,
            expected,
            &[],
        )?;
        let invariant_fact = align_positive_fact(&mut staged, export_lists_equal_fact, invariant)?;
        let no_members = list_has_no_members_avoiding(&mut staged, self, expected, &[])?;
        let no_members_fact = align_positive_fact(&mut staged, no_members_fact, no_members)?;
        let no_entry_parts = no_export_entries_avoiding(
            &mut staged,
            self,
            execution,
            program,
            &[expected, invariant, no_members],
        )?;
        let no_entries = no_entry_parts.proposition;
        let [
            store,
            externs,
            start,
            module_instance,
            exports,
            export_instance,
        ] = &no_entry_parts.variables;
        let entry = no_entry_parts.entry;
        let assumed = staged.identity(positive(entry))?;
        let export_prefix = select_conjunct(&mut staged, assumed, entry, &[false])?;
        let contains = select_conjunct(&mut staged, assumed, entry, &[true])?;

        let mut specialized_invariant = Evidence {
            proposition: invariant,
            theorem: invariant_fact,
            holds: true,
        };
        for &argument in &[*store, *externs, *start, *module_instance, *exports] {
            let specialized = forall_elim(&mut staged, specialized_invariant.theorem, argument)
                .map_err(|source| WasmLogicError::Forall { source })?;
            specialized_invariant = Evidence {
                proposition: specialized.proposition,
                theorem: specialized.theorem,
                holds: true,
            };
        }
        let implication = specialized_invariant.proposition;
        let operands = staged
            .arena()
            .children(implication)
            .ok_or(WasmLogicError::StartFact)?
            .collect::<Vec<_>>();
        let [invariant_prefix, list_equality] = operands.as_slice() else {
            return Err(WasmLogicError::StartFact);
        };
        let export_prefix = align_positive_fact(&mut staged, export_prefix, *invariant_prefix)?;
        let equality_identity = staged.identity(positive(*list_equality))?;
        let use_invariant =
            staged.imp_left(export_prefix, equality_identity, positive(implication))?;
        let list_equality_fact = staged.cut(
            specialized_invariant.theorem,
            use_invariant,
            positive(implication),
        )?;

        let list_binder_name = staged.fresh_name(&[
            no_entries,
            invariant,
            no_members,
            entry,
            expected,
            *export_instance,
        ])?;
        let list_binder = staged.tm_fv(list_binder_name, self.value_ty)?;
        let member_body = apply(&mut staged, self.member, &[*export_instance, list_binder])?;
        let member_function_ty = staged.ty_arr(self.value_ty, self.bool_ty)?;
        let member_function = staged.lam_at(member_function_ty, list_binder, member_body)?;
        let member_equality = staged.ap_term(list_equality_fact, member_function)?;
        let contains_proposition = apply(&mut staged, self.member, &[*export_instance, *exports])?;
        let contains = align_positive_fact(&mut staged, contains, contains_proposition)?;
        let left_substitution = substitute(&mut staged, list_binder, *exports, member_body)
            .map_err(|source| WasmLogicError::Substitute { source })?;
        let left_beta = staged.tm_beta_fact(None, member_equality.left, left_substitution.fact)?;
        staged.union_syn_fact(left_beta)?;
        let right_substitution = substitute(&mut staged, list_binder, expected, member_body)
            .map_err(|source| WasmLogicError::Substitute { source })?;
        let right_beta =
            staged.tm_beta_fact(None, member_equality.right, right_substitution.fact)?;
        staged.union_syn_fact(right_beta)?;
        join_same_syntax(&mut staged, left_substitution.output, contains_proposition)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        staged.convert_conclusions(contains, contains_proposition, member_equality.left)?;
        let expected_contains = staged.eq_mp(member_equality.theorem, contains)?;

        let denied = forall_elim(&mut staged, no_members_fact, *export_instance)
            .map_err(|source| WasmLogicError::Forall { source })?;
        let denied_member = staged
            .arena()
            .children(denied.proposition)
            .and_then(|mut children| children.next())
            .ok_or(WasmLogicError::StartFact)?;
        let denied_fact =
            staged.expand_conclusion(denied.theorem, positive(denied.proposition), None)?;
        let expected_member = apply(&mut staged, self.member, &[*export_instance, expected])?;
        join_same_syntax(&mut staged, right_substitution.output, expected_member)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        staged.convert_conclusions(expected_contains, member_equality.right, expected_member)?;
        join_alpha_equivalent(&mut staged, denied_member, expected_member)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        staged.convert_conclusions(denied_fact, denied_member, expected_member)?;
        staged.not_left(expected_contains, positive(expected_member))?;
        let contradiction = staged.cut(
            denied_fact,
            expected_contains,
            positive(expected_member).negated(),
        )?;
        staged.contract_theorem(contradiction)?;
        staged.not_right(contradiction, positive(entry))?;
        let flattened = staged.flatten_conclusion(contradiction, positive(entry).negated())?;
        let mut theorem = staged.fold_conclusion(flattened, positive(no_entry_parts.body))?;
        let mut proposition = no_entry_parts.body;
        for &variable in no_entry_parts.variables.iter().rev() {
            proposition = staged.forall_tm(execution.bool_ty, variable, proposition)?;
            theorem = staged.forall_intro_at(theorem, variable, proposition)?;
        }
        join_alpha_equivalent(&mut staged, proposition, no_entries)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        staged.convert_conclusions(theorem, proposition, no_entries)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: no_entries,
            theorem,
            holds: true,
        })
    }

    /// Derives `program_cannot_export` from absence of export-list entries.
    ///
    /// This opens the three witnesses in the concrete exported-function
    /// predicate and extracts its list-membership conjunct. The supplied
    /// theorem must prove [`Self::program_has_no_export_entries`]. Its premises
    /// remain visible; function-address interpretation is not needed for the
    /// contradiction.
    ///
    /// # Errors
    ///
    /// Returns an error if the theorem has the wrong conclusion or if checked
    /// beta reduction, existential/universal elimination, conjunction
    /// projection, or contradiction closure fails. `kernel` is unchanged on
    /// failure.
    #[allow(clippy::too_many_lines)]
    pub fn prove_program_cannot_export_from_no_entries(
        self,
        kernel: &mut Kernel,
        execution: SpecTecExecution,
        program: Ref,
        no_entries_fact: covalence_logic_hol::ThmId,
    ) -> Result<Evidence, WasmLogicError> {
        let mut staged = kernel.fork();
        let no_entries =
            no_export_entries_avoiding(&mut staged, self, execution, program, &[])?.proposition;
        let no_entries_fact = align_positive_fact(&mut staged, no_entries_fact, no_entries)?;
        let exported = self.predicate(&mut staged)?;
        let roots = [
            execution.state_ty,
            execution.bool_ty,
            execution.instantiate,
            exported,
            program,
            no_entries,
        ];
        let first = staged.fresh_name(&roots)?;
        let values = (0..4)
            .map(|offset| {
                staged.tm_fv(
                    first.checked_add(offset).ok_or(KernelError::TooManyNames)?,
                    execution.state_ty,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        let [store, externs, start, function] = values.as_slice() else {
            unreachable!()
        };
        let instantiated = apply(
            &mut staged,
            execution.instantiate,
            &[*store, program, *externs, *start],
        )?;
        let is_exported = apply(&mut staged, exported, &[*start, *function])?;
        let prefix = staged.op2(Op2::And, instantiated, is_exported)?;
        let assumed = staged.identity(positive(prefix))?;
        let instantiated_fact = select_conjunct(&mut staged, assumed, prefix, &[false])?;
        let exported_fact = select_conjunct(&mut staged, assumed, prefix, &[true])?;
        let exported_fact = align_positive_fact(&mut staged, exported_fact, is_exported)?;

        let (curried_exported, mut opened) =
            reduce_binary_application(&mut staged, exported, *start, *function)?;
        let opened_export = staged.copy_theorem(exported_fact)?;
        join_same_syntax(&mut staged, is_exported, curried_exported)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        staged.convert_conclusions(opened_export, is_exported, opened)?;
        let mut export_witnesses = Vec::with_capacity(3);
        for _ in 0..3 {
            let exists = open_exists(&mut staged, opened)
                .map_err(|source| WasmLogicError::Exists { source })?;
            staged.convert_conclusions(opened_export, opened, exists.body)?;
            export_witnesses.push(exists.witness);
            opened = exists.body;
        }
        let [module_instance, exports, export_instance] = export_witnesses.as_slice() else {
            unreachable!()
        };
        let has_module =
            select_conjunct(&mut staged, opened_export, opened, &[false, false, false])?;
        let has_exports =
            select_conjunct(&mut staged, opened_export, opened, &[false, false, true])?;
        let contains = select_conjunct(&mut staged, opened_export, opened, &[false, true])?;
        let has_module_proposition = apply(
            &mut staged,
            self.module_instance,
            &[*start, *module_instance],
        )?;
        let has_exports_proposition =
            apply(&mut staged, self.exports, &[*module_instance, *exports])?;
        let contains_proposition = apply(&mut staged, self.member, &[*export_instance, *exports])?;
        let has_module = align_positive_fact(&mut staged, has_module, has_module_proposition)?;
        let has_exports = align_positive_fact(&mut staged, has_exports, has_exports_proposition)?;
        let contains = align_positive_fact(&mut staged, contains, contains_proposition)?;
        let with_module = staged.op2(Op2::And, instantiated, has_module_proposition)?;
        let with_module_fact =
            staged.and_right(instantiated_fact, has_module, positive(with_module))?;
        let with_exports = staged.op2(Op2::And, with_module, has_exports_proposition)?;
        let with_exports_fact =
            staged.and_right(with_module_fact, has_exports, positive(with_exports))?;
        let entry = staged.op2(Op2::And, with_exports, contains_proposition)?;
        let entry_fact = staged.and_right(with_exports_fact, contains, positive(entry))?;

        let mut denied = Evidence {
            proposition: no_entries,
            theorem: no_entries_fact,
            holds: true,
        };
        for &argument in &[
            *store,
            *externs,
            *start,
            *module_instance,
            *exports,
            *export_instance,
        ] {
            let specialized = forall_elim(&mut staged, denied.theorem, argument)
                .map_err(|source| WasmLogicError::Forall { source })?;
            denied = Evidence {
                proposition: specialized.proposition,
                theorem: specialized.theorem,
                holds: true,
            };
        }
        let denied_fact =
            staged.expand_conclusion(denied.theorem, positive(denied.proposition), None)?;
        let denied_entry = staged
            .arena()
            .children(denied.proposition)
            .and_then(|mut children| children.next())
            .ok_or(WasmLogicError::StartFact)?;
        join_alpha_equivalent(&mut staged, denied_entry, entry)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        staged.convert_conclusions(denied_fact, denied_entry, entry)?;
        staged.not_left(entry_fact, positive(entry))?;
        let contradiction = staged.cut(denied_fact, entry_fact, positive(entry).negated())?;
        staged.contract_theorem(contradiction)?;
        staged.not_right(contradiction, positive(prefix))?;
        let does_not_export = staged.op1(covalence_logic_hol::builtin::Op1::Not, prefix)?;
        let flattened = staged.flatten_conclusion(contradiction, positive(prefix).negated())?;
        let mut theorem = staged.fold_conclusion(flattened, positive(does_not_export))?;
        let mut proposition = does_not_export;
        for &variable in values.iter().rev() {
            proposition = staged.forall_tm(execution.bool_ty, variable, proposition)?;
            theorem = staged.forall_intro_at(theorem, variable, proposition)?;
        }
        let canonical = execution.program_cannot_export(&mut staged, exported, program)?;
        join_alpha_equivalent(&mut staged, proposition, canonical)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        staged.convert_conclusions(theorem, proposition, canonical)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem,
            holds: true,
        })
    }
}

fn program_export_lists_equal_avoiding(
    kernel: &mut Kernel,
    view: ExportedFunctionView,
    execution: SpecTecExecution,
    program: Ref,
    expected: Ref,
    avoid: &[Ref],
) -> Result<Ref, WasmLogicError> {
    let mut staged = kernel.fork();
    let roots = [
        execution.state_ty,
        execution.bool_ty,
        execution.instantiate,
        view.module_instance,
        view.exports,
        program,
        expected,
    ]
    .into_iter()
    .chain(avoid.iter().copied())
    .collect::<Vec<_>>();
    let first = staged.fresh_name(&roots)?;
    let values = (0..5)
        .map(|offset| {
            staged.tm_fv(
                first.checked_add(offset).ok_or(KernelError::TooManyNames)?,
                execution.state_ty,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let [store, externs, start, module_instance, exports] = values.as_slice() else {
        unreachable!()
    };
    let instantiated = apply(
        &mut staged,
        execution.instantiate,
        &[*store, program, *externs, *start],
    )?;
    let has_module = apply(
        &mut staged,
        view.module_instance,
        &[*start, *module_instance],
    )?;
    let has_exports = apply(&mut staged, view.exports, &[*module_instance, *exports])?;
    let mut prefix = staged.op2(Op2::And, instantiated, has_module)?;
    prefix = staged.op2(Op2::And, prefix, has_exports)?;
    let equality = staged.eq(execution.bool_ty, *exports, expected)?;
    let mut proposition = staged.op2(Op2::Imp, prefix, equality)?;
    for &variable in values.iter().rev() {
        proposition = staged.forall_tm(execution.bool_ty, variable, proposition)?;
    }
    *kernel = staged;
    Ok(proposition)
}

fn list_has_no_members_avoiding(
    kernel: &mut Kernel,
    view: ExportedFunctionView,
    list: Ref,
    avoid: &[Ref],
) -> Result<Ref, WasmLogicError> {
    let mut staged = kernel.fork();
    let roots = [view.value_ty, view.bool_ty, view.member, list]
        .into_iter()
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
    let name = staged.fresh_name(&roots)?;
    let entry = staged.tm_fv(name, view.value_ty)?;
    let member = apply(&mut staged, view.member, &[entry, list])?;
    let denied = staged.op1(covalence_logic_hol::builtin::Op1::Not, member)?;
    let proposition = staged.forall_tm(view.bool_ty, entry, denied)?;
    *kernel = staged;
    Ok(proposition)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct NoExportEntriesParts {
    proposition: Ref,
    body: Ref,
    entry: Ref,
    variables: [Ref; 6],
}

fn no_export_entries_avoiding(
    kernel: &mut Kernel,
    view: ExportedFunctionView,
    execution: SpecTecExecution,
    program: Ref,
    avoid: &[Ref],
) -> Result<NoExportEntriesParts, WasmLogicError> {
    let mut staged = kernel.fork();
    let roots = [
        execution.state_ty,
        execution.bool_ty,
        execution.instantiate,
        view.module_instance,
        view.exports,
        view.member,
        program,
    ]
    .into_iter()
    .chain(avoid.iter().copied())
    .collect::<Vec<_>>();
    let first = staged.fresh_name(&roots)?;
    let values = (0..6)
        .map(|offset| {
            staged.tm_fv(
                first.checked_add(offset).ok_or(KernelError::TooManyNames)?,
                execution.state_ty,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let variables: [Ref; 6] = values.try_into().unwrap_or_else(|_| unreachable!());
    let [
        store,
        externs,
        start,
        module_instance,
        exports,
        export_instance,
    ] = variables;
    let instantiated = apply(
        &mut staged,
        execution.instantiate,
        &[store, program, externs, start],
    )?;
    let has_module = apply(&mut staged, view.module_instance, &[start, module_instance])?;
    let has_exports = apply(&mut staged, view.exports, &[module_instance, exports])?;
    let contains = apply(&mut staged, view.member, &[export_instance, exports])?;
    let mut entry = staged.op2(Op2::And, instantiated, has_module)?;
    entry = staged.op2(Op2::And, entry, has_exports)?;
    entry = staged.op2(Op2::And, entry, contains)?;
    let body = staged.op1(covalence_logic_hol::builtin::Op1::Not, entry)?;
    let mut proposition = body;
    for &variable in variables.iter().rev() {
        proposition = staged.forall_tm(execution.bool_ty, variable, proposition)?;
    }
    *kernel = staged;
    Ok(NoExportEntriesParts {
        proposition,
        body,
        entry,
        variables,
    })
}

fn select_conjunct(
    kernel: &mut Kernel,
    theorem: covalence_logic_hol::ThmId,
    proposition: Ref,
    path: &[bool],
) -> Result<covalence_logic_hol::ThmId, WasmLogicError> {
    let mut theorem = kernel.copy_theorem(theorem)?;
    let mut proposition = proposition;
    for &branch in path {
        theorem = kernel.expand_conclusion(theorem, positive(proposition), Some(branch))?;
        let children = kernel
            .arena()
            .children(proposition)
            .ok_or(WasmLogicError::StartFact)?
            .collect::<Vec<_>>();
        let [left, right] = children.as_slice() else {
            return Err(WasmLogicError::StartFact);
        };
        proposition = if branch { *right } else { *left };
    }
    Ok(theorem)
}

impl SpecTecExecution {
    /// Constructs contextual equivalence for individual erased Wasm functions.
    ///
    /// The complete `SpecTec` lowering uses `state_ty` as its shared structural
    /// value carrier. `replace` must have classifier
    /// `replacement_context_ty -> state_ty -> modules.subject_ty`. The returned
    /// schema quantifies every function-hole replacement context and then every
    /// admissible outer module observation context, so its replacement theorem
    /// preserves full observational equivalence.
    ///
    /// # Errors
    ///
    /// Returns an error unless the module carrier is this exact `SpecTec` value
    /// carrier and `replace` has the required checked classifier. No theorem
    /// fact is created, and `kernel` is unchanged on failure.
    pub fn function_observation(
        self,
        kernel: &mut Kernel,
        replacement_context_ty: Ref,
        replace: Ref,
        modules: ContextualObservation,
    ) -> Result<FunctionObservation, WasmLogicError> {
        let mut staged = kernel.fork();
        join_same_syntax(&mut staged, modules.subject_ty, self.state_ty)
            .map_err(|_| WasmLogicError::FunctionObservation)?;
        let replacement_tail = staged.ty_arr(self.state_ty, modules.subject_ty)?;
        let expected = staged.ty_arr(replacement_context_ty, replacement_tail)?;
        let actual = staged.classifier(replace)?;
        join_same_syntax(&mut staged, actual, expected)
            .map_err(|_| WasmLogicError::FunctionObservation)?;
        let observation = FunctionObservation {
            function_ty: self.state_ty,
            replacement_context_ty,
            replace,
            modules,
        };
        *kernel = staged;
        Ok(observation)
    }

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

    /// Transports the source configuration of a checked `Steps` fact.
    ///
    /// `equality` must prove `before = replacement`. The result proves
    /// `Steps replacement after`, preserving every premise of both input
    /// theorems. This is ordinary equality congruence and does not assert that
    /// either configuration representation is faithful.
    ///
    /// # Errors
    ///
    /// Returns an error unless `steps_fact` proves `Steps before after` and
    /// `equality` proves the required oriented equality, or a checked
    /// congruence, beta-reduction, or equality-elimination step fails. `kernel`
    /// is unchanged on failure.
    pub fn transport_steps_before(
        self,
        kernel: &mut Kernel,
        before: Ref,
        replacement: Ref,
        after: Ref,
        steps_fact: Evidence,
        equality: covalence_logic_hol::ThmId,
    ) -> Result<Evidence, WasmLogicError> {
        transport_binary_fact(
            kernel,
            self.steps,
            self.state_ty,
            self.bool_ty,
            before,
            after,
            replacement,
            steps_fact,
            equality,
            true,
        )
    }

    /// Transports the target configuration of a checked `Steps` fact.
    ///
    /// `equality` must prove `after = replacement`. The result proves
    /// `Steps before replacement`, preserving every premise of both input
    /// theorems.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`Self::transport_steps_before`]. `kernel` is unchanged on failure.
    pub fn transport_steps_after(
        self,
        kernel: &mut Kernel,
        before: Ref,
        after: Ref,
        replacement: Ref,
        steps_fact: Evidence,
        equality: covalence_logic_hol::ThmId,
    ) -> Result<Evidence, WasmLogicError> {
        transport_binary_fact(
            kernel,
            self.steps,
            self.state_ty,
            self.bool_ty,
            before,
            after,
            replacement,
            steps_fact,
            equality,
            false,
        )
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
    /// completed store. It selects the export from the configuration returned
    /// by `instantiate`, then conjoins exact `Steps`, `store`, and `invoke`
    /// graph predicates.
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

    /// Constructs the five exact graph obligations for one admissible start.
    ///
    /// This is the immutable schema consumed by [`Self::prove_admissible_start`]:
    /// `$instantiate`, initialization `Steps`, pre-initialization
    /// exported-function selection, `$store`, and `$invoke`, in that order. It
    /// creates syntax, not facts.
    ///
    /// # Errors
    ///
    /// Returns an error if a witness or predicate is ill-typed or a checked
    /// application fails. `kernel` is unchanged on failure.
    pub fn admissible_start_obligations(
        self,
        kernel: &mut Kernel,
        exported: Ref,
        witness: AdmissibleStartWitness,
    ) -> Result<[Ref; 5], WasmLogicError> {
        let mut staged = kernel.fork();
        let obligations = start_propositions(&mut staged, self, exported, witness)?;
        *kernel = staged;
        Ok(obligations)
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
        let is_exported = apply(&mut staged, exported, &[*instantiation_start, *function])?;
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

    /// Constructs the claim that instantiating `program` cannot produce a
    /// configuration with an exported function.
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

    /// Proves that a program has no admissible start when no configuration
    /// produced by instantiating that program exports a function.
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
        let initialization = select_conjunct(&mut staged, prefix_fact, first_three, &[false])?;
        let exported_fact = select_conjunct(&mut staged, prefix_fact, first_three, &[true])?;
        let initialization_proposition = sole_positive_conclusion_ref(&staged, initialization)?;
        let instantiated_fact = select_conjunct(
            &mut staged,
            initialization,
            initialization_proposition,
            &[false],
        )?;
        let instantiated = sole_positive_conclusion_ref(&staged, instantiated_fact)?;
        let exported_proposition = sole_positive_conclusion_ref(&staged, exported_fact)?;
        let no_export_prefix = staged.op2(Op2::And, instantiated, exported_proposition)?;
        let prefix_fact =
            staged.and_right(instantiated_fact, exported_fact, positive(no_export_prefix))?;

        let mut denied = Evidence {
            proposition: cannot_export,
            theorem: cannot_export_fact,
            holds: true,
        };
        for &argument in &[witnesses[0], witnesses[1], witnesses[2], witnesses[4]] {
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
        join_alpha_equivalent(&mut staged, denied_prefix, no_export_prefix)
            .map_err(|source| WasmLogicError::Syntax { source })?;
        let denied_fact =
            staged.expand_conclusion(denied.theorem, positive(denied.proposition), None)?;
        staged.convert_conclusions(denied_fact, denied_prefix, no_export_prefix)?;
        staged.not_left(prefix_fact, positive(no_export_prefix))?;
        let contradiction = staged.cut(
            denied_fact,
            prefix_fact,
            positive(no_export_prefix).negated(),
        )?;
        staged.contract_theorem(contradiction)?;
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
    let mut variables = Vec::with_capacity(4);
    for offset in 0..4 {
        let name = first
            .checked_add(u64::try_from(offset).map_err(|_| KernelError::TooManyNames)?)
            .ok_or(KernelError::TooManyNames)?;
        variables.push(staged.tm_fv(name, execution.state_ty)?);
    }
    let [store, externs, start, function] = variables.as_slice() else {
        unreachable!()
    };
    let instantiated = apply(
        &mut staged,
        execution.instantiate,
        &[*store, program, *externs, *start],
    )?;
    let is_exported = apply(&mut staged, exported, &[*start, *function])?;
    let prefix = staged.op2(Op2::And, instantiated, is_exported)?;
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
        apply(
            kernel,
            exported,
            &[witness.instantiation_start, witness.function],
        )?,
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

#[allow(clippy::too_many_arguments)]
fn transport_binary_fact(
    kernel: &mut Kernel,
    predicate: Ref,
    value_ty: Ref,
    bool_ty: Ref,
    left: Ref,
    right: Ref,
    replacement: Ref,
    fact: Evidence,
    equality: covalence_logic_hol::ThmId,
    replace_left: bool,
) -> Result<Evidence, WasmLogicError> {
    if !fact.holds {
        return Err(WasmLogicError::StepFact);
    }
    let mut staged = kernel.fork();
    let source = apply(&mut staged, predicate, &[left, right])?;
    let fact = align_positive_fact(&mut staged, fact.theorem, source)?;
    let expected_equality = if replace_left {
        staged.eq(bool_ty, left, replacement)?
    } else {
        staged.eq(bool_ty, right, replacement)?
    };
    let equality = align_positive_fact(&mut staged, equality, expected_equality)?;
    let binder_name = staged.fresh_name(&[
        predicate,
        value_ty,
        bool_ty,
        left,
        right,
        replacement,
        source,
        expected_equality,
    ])?;
    let binder = staged.tm_fv(binder_name, value_ty)?;
    let body = if replace_left {
        apply(&mut staged, predicate, &[binder, right])?
    } else {
        apply(&mut staged, predicate, &[left, binder])?
    };
    let predicate_ty = staged.ty_arr(value_ty, bool_ty)?;
    let congruence_function = staged.lam_at(predicate_ty, binder, body)?;
    let lifted = staged.ap_term(equality, congruence_function)?;
    let old = if replace_left { left } else { right };
    let old_substitution = substitute(&mut staged, binder, old, body)
        .map_err(|source| WasmLogicError::Substitute { source })?;
    let old_beta = staged.tm_beta_fact(None, lifted.left, old_substitution.fact)?;
    staged.union_syn_fact(old_beta)?;
    join_same_syntax(&mut staged, old_substitution.output, source)
        .map_err(|source| WasmLogicError::Syntax { source })?;
    staged.convert_conclusions(fact, source, lifted.left)?;
    let transported = staged.eq_mp(lifted.theorem, fact)?;
    let replacement_substitution = substitute(&mut staged, binder, replacement, body)
        .map_err(|source| WasmLogicError::Substitute { source })?;
    let replacement_beta =
        staged.tm_beta_fact(None, lifted.right, replacement_substitution.fact)?;
    staged.union_syn_fact(replacement_beta)?;
    let target = if replace_left {
        apply(&mut staged, predicate, &[replacement, right])?
    } else {
        apply(&mut staged, predicate, &[left, replacement])?
    };
    join_same_syntax(&mut staged, replacement_substitution.output, target)
        .map_err(|source| WasmLogicError::Syntax { source })?;
    staged.convert_conclusions(transported, lifted.right, target)?;
    staged.contract_theorem(transported)?;
    *kernel = staged;
    Ok(Evidence {
        proposition: target,
        theorem: transported,
        holds: true,
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

/// Proves an application of a checked binary predicate whose beta-reduced body
/// is reflexive equality.
///
/// This is a generic structural-observation helper. It beta-reduces
/// `predicate left right`, asks the ordinary reflexive-condition proof to
/// discharge the resulting equality, and converts that checked theorem back
/// to the original application. It cannot turn a non-reflexive body into a
/// fact and introduces no evaluator or axiom authority.
///
/// # Errors
///
/// Returns an error unless `predicate` is a checked curried binary lambda, its
/// application beta-reduces successfully, and the reduced body is reflexive
/// equality. `kernel` is unchanged on failure.
pub fn prove_reflexive_binary_application(
    kernel: &mut Kernel,
    predicate: Ref,
    left: Ref,
    right: Ref,
) -> Result<Evidence, WasmLogicError> {
    let mut staged = kernel.fork();
    let (application, reduced) = reduce_binary_application(&mut staged, predicate, left, right)?;
    let reflexive = crate::prove_reflexive_condition(&mut staged, reduced)
        .map_err(|source| WasmLogicError::ReflexiveObservation { source })?
        .ok_or(WasmLogicError::ObservationFact)?;
    let theorem = staged.copy_theorem(reflexive.theorem)?;
    staged.convert_conclusions(theorem, reduced, application)?;
    *kernel = staged;
    Ok(Evidence {
        proposition: application,
        theorem,
        holds: true,
    })
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
    /// A structural observation did not beta-reduce to reflexive equality.
    #[snafu(display("supplied SpecTec structural observation is not reflexive"))]
    ObservationFact,
    /// Checked reflexive-condition proof construction failed.
    #[snafu(display("could not prove a reflexive SpecTec structural observation: {source}"))]
    ReflexiveObservation {
        /// Underlying relational proof failure.
        source: crate::DefinitionProofError,
    },
    /// A supplied admissible-start theorem is not one positive fact.
    #[snafu(display("supplied SpecTec admissible-start fact has the wrong shape"))]
    StartFact,
    /// A function replacement schema used a foreign carrier or operation type.
    #[snafu(display("invalid SpecTec function observation schema"))]
    FunctionObservation,
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
    fn spectec_function_observation_uses_the_erased_wasm_carrier() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let value = kernel.ty_fv(0, star).unwrap();
        let replacement_ty = kernel.ty_fv(1, star).unwrap();
        let outer_ty = kernel.ty_fv(2, star).unwrap();
        let pair_tail = kernel.ty_arr(value, value).unwrap();
        let pair_ty = kernel.ty_arr(value, pair_tail).unwrap();
        let steps_tail = kernel.ty_arr(value, bool_ty).unwrap();
        let steps_ty = kernel.ty_arr(value, steps_tail).unwrap();
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
        let replace_tail = kernel.ty_arr(value, value).unwrap();
        let replace_ty = kernel.ty_arr(replacement_ty, replace_tail).unwrap();
        let replace = kernel.tm_fv(16, replace_ty).unwrap();
        let plug_tail = kernel.ty_arr(value, value).unwrap();
        let plug_ty = kernel.ty_arr(outer_ty, plug_tail).unwrap();
        let admissible_tail = kernel.ty_arr(value, bool_ty).unwrap();
        let admissible_ty = kernel.ty_arr(outer_ty, admissible_tail).unwrap();
        let observe_ty = kernel.ty_arr(value, bool_ty).unwrap();
        let modules = ContextualObservation {
            subject_ty: value,
            context_ty: outer_ty,
            observed_ty: value,
            bool_ty,
            plug: kernel.tm_fv(17, plug_ty).unwrap(),
            admissible: kernel.tm_fv(18, admissible_ty).unwrap(),
            observe: kernel.tm_fv(19, observe_ty).unwrap(),
        };

        let functions = execution
            .function_observation(&mut kernel, replacement_ty, replace, modules)
            .unwrap();

        assert_eq!(functions.function_ty, value);
        assert_eq!(functions.modules, modules);
        let wrong = kernel.tm_fv(20, bool_ty).unwrap();
        let before = kernel.arena().clone();
        assert!(
            execution
                .function_observation(&mut kernel, replacement_ty, wrong, modules)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
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
        let propositions = execution
            .admissible_start_obligations(&mut kernel, exported, witness)
            .unwrap();
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
    fn steps_transport_is_checked_compositional_and_transactional() {
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
        let before = kernel.tm_fv(20, value).unwrap();
        let after = kernel.tm_fv(21, value).unwrap();
        let replacement_before = kernel.tm_fv(22, value).unwrap();
        let replacement_after = kernel.tm_fv(23, value).unwrap();
        let source = apply(&mut kernel, execution.steps, &[before, after]).unwrap();
        let source_fact = kernel.identity(positive(source)).unwrap();
        let before_equality = kernel.eq(bool_ty, before, replacement_before).unwrap();
        let before_equality_fact = kernel.identity(positive(before_equality)).unwrap();
        let after_equality = kernel.eq(bool_ty, after, replacement_after).unwrap();
        let after_equality_fact = kernel.identity(positive(after_equality)).unwrap();
        let transported_before = execution
            .transport_steps_before(
                &mut kernel,
                before,
                replacement_before,
                after,
                Evidence {
                    proposition: source,
                    theorem: source_fact,
                    holds: true,
                },
                before_equality_fact,
            )
            .unwrap();
        let transported = execution
            .transport_steps_after(
                &mut kernel,
                replacement_before,
                after,
                replacement_after,
                transported_before,
                after_equality_fact,
            )
            .unwrap();
        crate::EvidenceScope::positive(&[source, before_equality, after_equality])
            .check(&kernel, transported)
            .unwrap();

        let reversed = kernel.eq(bool_ty, replacement_before, before).unwrap();
        let reversed_fact = kernel.identity(positive(reversed)).unwrap();
        let before_failure = kernel.arena().clone();
        assert!(
            execution
                .transport_steps_before(
                    &mut kernel,
                    before,
                    replacement_before,
                    after,
                    Evidence {
                        proposition: source,
                        theorem: source_fact,
                        holds: true,
                    },
                    reversed_fact,
                )
                .is_err()
        );
        assert_eq!(kernel.arena(), &before_failure);
    }

    #[test]
    fn reflexive_binary_observation_is_checked_and_transactional() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let value = kernel.ty_fv(0, star).unwrap();
        let left = kernel.tm_fv(10, value).unwrap();
        let right = kernel.tm_fv(11, value).unwrap();
        let first = kernel.tm_fv(12, value).unwrap();
        let second = kernel.tm_fv(13, value).unwrap();
        let body = kernel.eq(bool_ty, first, first).unwrap();
        let second_ty = kernel.ty_arr(value, bool_ty).unwrap();
        let by_second = kernel.lam_at(second_ty, second, body).unwrap();
        let predicate_ty = kernel.ty_arr(value, second_ty).unwrap();
        let predicate = kernel.lam_at(predicate_ty, first, by_second).unwrap();

        let proved =
            prove_reflexive_binary_application(&mut kernel, predicate, left, right).unwrap();
        crate::EvidenceScope::positive(&[])
            .check(&kernel, proved)
            .unwrap();

        let non_reflexive_body = kernel.eq(bool_ty, first, second).unwrap();
        let non_reflexive_by_second = kernel
            .lam_at(second_ty, second, non_reflexive_body)
            .unwrap();
        let non_reflexive = kernel
            .lam_at(predicate_ty, first, non_reflexive_by_second)
            .unwrap();
        let before = kernel.arena().clone();
        assert!(
            prove_reflexive_binary_application(&mut kernel, non_reflexive, left, right).is_err()
        );
        assert_eq!(kernel.arena(), &before);
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

    #[test]
    fn export_list_invariant_proves_program_cannot_export() {
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
        let view = ExportedFunctionView {
            value_ty: value,
            bool_ty,
            module_instance: execution.moduleinst,
            exports: predicate(&mut kernel, value, bool_ty, 2, 16),
            member: predicate(&mut kernel, value, bool_ty, 2, 17),
            function_address: predicate(&mut kernel, value, bool_ty, 2, 18),
        };
        let program = kernel.tm_fv(19, value).unwrap();
        let empty = kernel.tm_fv(20, value).unwrap();
        let export_lists_equal = view
            .program_export_lists_equal(&mut kernel, execution, program, empty)
            .unwrap();
        let no_members = view.list_has_no_members(&mut kernel, empty).unwrap();
        let export_lists_equal_fact = kernel.identity(positive(export_lists_equal)).unwrap();
        let no_members_fact = kernel.identity(positive(no_members)).unwrap();
        let entry = kernel.tm_fv(21, value).unwrap();
        let denied = forall_elim(&mut kernel, no_members_fact, entry).unwrap();
        let membership = kernel
            .arena()
            .children(denied.proposition)
            .unwrap()
            .next()
            .unwrap();
        let membership_children = kernel
            .arena()
            .children(membership)
            .unwrap()
            .collect::<Vec<_>>();
        let [partial_membership, actual_list] = membership_children.as_slice() else {
            panic!("expected curried SpecTec membership application")
        };
        assert_eq!(*actual_list, empty);
        let partial_children = kernel
            .arena()
            .children(*partial_membership)
            .unwrap()
            .collect::<Vec<_>>();
        assert_eq!(partial_children, [view.member, entry]);
        let before = kernel.arena().clone();
        assert!(
            view.prove_no_export_entries_from_list_invariant(
                &mut kernel,
                execution,
                program,
                empty,
                no_members_fact,
                export_lists_equal_fact,
            )
            .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        let no_entries = view
            .prove_no_export_entries_from_list_invariant(
                &mut kernel,
                execution,
                program,
                empty,
                export_lists_equal_fact,
                no_members_fact,
            )
            .unwrap();
        let cannot_export = view
            .prove_program_cannot_export_from_no_entries(
                &mut kernel,
                execution,
                program,
                no_entries.theorem,
            )
            .unwrap();

        crate::EvidenceScope::positive(&[export_lists_equal, no_members])
            .check(&kernel, cannot_export)
            .unwrap();
    }
}
