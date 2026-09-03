//! Adapters from the complete `SpecTec` document to program-logic predicates.

use covalence_data_basic::Symbol;
use covalence_data_spectec::IlKind;
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, builtin::Op2};

use crate::{AssertionReachability, InterpretationKind, ParameterizedDocument};

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
        let mut staged = kernel.fork();
        let roots = [
            self.state_ty,
            self.bool_ty,
            self.instantiate,
            self.invoke,
            self.store,
            self.moduleinst,
            exported,
        ];
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
    /// A checked HOL construction failed.
    #[snafu(display("could not construct SpecTec program-logic adapter: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
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
    let tuple = document
        .operations()
        .find(|operation| {
            operation.kind() == InterpretationKind::Tuple
                && operation.signature.label == "tuple:2"
                && operation.signature.domains.as_ref()
                    == [document.schema.value(), document.schema.value()]
                && operation.signature.codomain == document.schema.value()
        })
        .ok_or_else(|| WasmLogicError::Operation {
            label: Symbol::new("tuple:2"),
        })?
        .reference;

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
        steps_ty: curried_ty,
        instantiate,
        invoke,
        store,
        moduleinst,
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
        let execution = SpecTecExecution {
            state_ty: value,
            bool_ty,
            steps: predicate(&mut kernel, value, bool_ty, 2, 10),
            steps_ty,
            instantiate: predicate(&mut kernel, value, bool_ty, 4, 11),
            invoke: predicate(&mut kernel, value, bool_ty, 4, 12),
            store: predicate(&mut kernel, value, bool_ty, 2, 13),
            moduleinst: predicate(&mut kernel, value, bool_ty, 2, 18),
        };
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
}
