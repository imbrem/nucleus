//! One-shot parameterized HOL interpretation for complete `SpecTec` documents.

use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex, MutexGuard, PoisonError},
};

use covalence_data_spectec::{
    DeclarationId, IlArgument, IlBinding, IlExpression, IlExpressionView, IlGrammarSymbol,
    IlIteration, IlKind, IlSchemaError, IlType,
};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, Tag, TyTag};

use crate::{
    HolEmbedding, HolFamilyError, HolSchema, HolSchemaError, HolTheoryError, LeastPredicateError,
    RelationalCall, RelationalCaseError, RelationalCondition, RelationalDocumentDefinition,
    RelationalResolver, RelationalTerm, Source, declare_hol_schema, existential_case,
    relational_document,
};

const LOCAL_NAME_BLOCK: u64 = 1 << 32;

/// One explicit free interpretation symbol introduced by parameterized lowering.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterpretationSymbol {
    /// Stable structural description and checked signature discriminator.
    pub label: String,
    /// Checked free term.
    pub reference: Ref,
    /// Checked classifier of `reference`.
    pub classifier: Ref,
}

/// Complete parameterized semantics of one exact `SpecTec` document.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParameterizedDocument {
    /// Checked generic declaration slots.
    pub schema: HolSchema,
    /// Explicit primitive/constructor interpretation parameters.
    pub interpretation: Vec<InterpretationSymbol>,
    /// Exact declaration constraints and their complete conjunction.
    pub semantics: RelationalDocumentDefinition,
}

/// Why a complete parameterized document could not be lowered.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ParameterizedError {
    /// A declaration-local lowering failed.
    #[snafu(display("parameterized SpecTec declaration {id:?} failed: {source}"))]
    Declaration {
        /// Exact structural selector.
        id: DeclarationId,
        /// Underlying contextual failure.
        source: Box<Self>,
    },
    /// Generic checked slots could not be declared.
    #[snafu(display("could not declare parameterized SpecTec schema: {source}"))]
    Schema {
        /// Underlying schema preparation failure.
        source: HolSchemaError,
    },
    /// A decoded IL node was structurally invalid.
    #[snafu(display("could not decode parameterized SpecTec semantics: {source}"))]
    Il {
        /// Underlying structural failure.
        source: IlSchemaError,
    },
    /// A checked HOL construction failed.
    #[snafu(display("could not construct parameterized SpecTec semantics: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Exact clause construction failed.
    #[snafu(display("could not construct parameterized clause: {source}"))]
    Clause {
        /// Underlying clause failure.
        source: RelationalCaseError,
    },
    /// Least-family construction failed.
    #[snafu(display("could not construct parameterized relation family: {source}"))]
    Least {
        /// Underlying least-family failure.
        source: LeastPredicateError,
    },
    /// Exact family construction failed.
    #[snafu(display("could not construct parameterized predicate family: {source}"))]
    Family {
        /// Underlying family failure.
        source: HolFamilyError,
    },
    /// Complete theory construction failed.
    #[snafu(display("could not close parameterized SpecTec theory: {source}"))]
    Theory {
        /// Underlying theory failure.
        source: HolTheoryError,
    },
    /// A source name or interpretation form could not be resolved uniquely.
    #[snafu(display("could not resolve parameterized SpecTec semantics: {message}"))]
    Resolve {
        /// Stable diagnostic.
        message: String,
    },
}

#[derive(Clone, Debug)]
struct SharedInterpretation {
    next_name: u64,
    symbols: BTreeMap<String, InterpretationSymbol>,
    canonical_types: BTreeMap<(Ref, Ref), Ref>,
    canonical_type_refs: BTreeMap<Ref, Ref>,
}

#[derive(Clone, Debug)]
struct ParameterizedResolver {
    embedding: HolEmbedding,
    schema: Arc<HolSchema>,
    bindings: BTreeMap<String, Ref>,
    type_bindings: BTreeMap<String, Ref>,
    definition_bindings: BTreeMap<String, Ref>,
    grammar_bindings: BTreeMap<String, Ref>,
    relations: BTreeMap<String, Ref>,
    expression_scopes: Vec<Vec<(String, Option<Ref>, Ref)>>,
    implicit_binders: Vec<Ref>,
    shared: Arc<Mutex<SharedInterpretation>>,
}

/// Transactionally declares generic slots and lowers an entire exact document
/// under explicit free interpretations of primitive and structural operations.
///
/// The returned theory states the `SpecTec` equations/rules parametrically over
/// `interpretation`; it does not assume those parameters, execute the spec, or
/// mint theorem facts.
///
/// # Errors
///
/// Returns the first schema, name-resolution, interpretation, declaration, or
/// checked theory failure. `kernel` is unchanged on failure.
pub fn parameterized_document(
    source: &Source,
    kernel: &mut Kernel,
    value: Ref,
    bool_ty: Ref,
) -> Result<ParameterizedDocument, ParameterizedError> {
    let mut staged = kernel.fork();
    let schema = declare_hol_schema(source, &mut staged, value, bool_ty)
        .map_err(|source| ParameterizedError::Schema { source })?;
    let roots = schema
        .declarations()
        .map(|(_, declaration)| declaration.reference())
        .chain([value, bool_ty])
        .collect::<Vec<_>>();
    let first = staged
        .fresh_name(&roots)
        .map_err(|source| ParameterizedError::Kernel { source })?;
    let next_name =
        first
            .checked_add(LOCAL_NAME_BLOCK)
            .ok_or_else(|| ParameterizedError::Resolve {
                message: "free-variable name range exhausted".to_owned(),
            })?;
    let shared = Arc::new(Mutex::new(SharedInterpretation {
        next_name,
        symbols: BTreeMap::new(),
        canonical_types: BTreeMap::new(),
        canonical_type_refs: BTreeMap::new(),
    }));
    let mut resolver = ParameterizedResolver {
        embedding: HolEmbedding::new(value, bool_ty),
        schema: Arc::new(schema.clone()),
        bindings: BTreeMap::new(),
        type_bindings: BTreeMap::new(),
        definition_bindings: BTreeMap::new(),
        grammar_bindings: BTreeMap::new(),
        relations: BTreeMap::new(),
        expression_scopes: Vec::new(),
        implicit_binders: Vec::new(),
        shared: Arc::clone(&shared),
    };
    for (_, declaration) in schema.declarations() {
        let classifier = staged
            .classifier(declaration.reference())
            .map_err(|source| ParameterizedError::Kernel { source })?;
        resolver.canonical_type(&staged, classifier)?;
    }
    let semantics = relational_document(&mut staged, &mut resolver, source, &schema, &[])?;
    let interpretation = shared
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .symbols
        .values()
        .cloned()
        .collect();
    *kernel = staged;
    Ok(ParameterizedDocument {
        schema,
        interpretation,
        semantics,
    })
}

fn arrow_children(
    kernel: &Kernel,
    reference: Ref,
) -> Result<Option<(Ref, Ref)>, ParameterizedError> {
    if kernel.arena().tag(reference) != Some(Tag::Ty(TyTag::Arr)) {
        return Ok(None);
    }
    let children = kernel
        .arena()
        .children(reference)
        .ok_or_else(|| ParameterizedError::Resolve {
            message: format!("missing arrow type {reference:?}"),
        })?
        .collect::<Vec<_>>();
    let [domain, codomain] = children.as_slice() else {
        return Err(ParameterizedError::Resolve {
            message: format!("malformed arrow type {reference:?}"),
        });
    };
    Ok(Some((*domain, *codomain)))
}

impl ParameterizedResolver {
    fn shared(&self) -> MutexGuard<'_, SharedInterpretation> {
        self.shared.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn canonical_type(&self, kernel: &Kernel, reference: Ref) -> Result<Ref, ParameterizedError> {
        if let Some(canonical) = self.shared().canonical_type_refs.get(&reference) {
            return Ok(*canonical);
        }
        let Some((domain, codomain)) = arrow_children(kernel, reference)? else {
            return Ok(reference);
        };
        let domain = self.canonical_type(kernel, domain)?;
        let codomain = self.canonical_type(kernel, codomain)?;
        let mut shared = self.shared();
        let canonical = *shared
            .canonical_types
            .entry((domain, codomain))
            .or_insert(reference);
        shared.canonical_type_refs.insert(reference, canonical);
        Ok(canonical)
    }

    fn resolve(&self, kind: IlKind, name: &str) -> Result<Ref, ParameterizedError> {
        let ids = self.schema.named(kind, name);
        let [id] = ids else {
            return Err(ParameterizedError::Resolve {
                message: format!("expected one {kind:?} named {name:?}, found {}", ids.len()),
            });
        };
        self.schema
            .declaration(*id)
            .map(crate::HolDeclaration::reference)
            .ok_or_else(|| ParameterizedError::Resolve {
                message: format!("missing checked slot for {kind:?} {name:?}"),
            })
    }

    fn take_name(&self) -> Result<u64, ParameterizedError> {
        let mut shared = self.shared();
        let name = shared.next_name;
        shared.next_name = name
            .checked_add(1)
            .ok_or_else(|| ParameterizedError::Resolve {
                message: "free-variable name range exhausted".to_owned(),
            })?;
        Ok(name)
    }

    fn primitive(
        &self,
        kernel: &mut Kernel,
        label: String,
        domains: &[Ref],
        codomain: Ref,
    ) -> Result<Ref, ParameterizedError> {
        let key = format!("{label}|{domains:?}->{codomain:?}");
        if let Some(symbol) = self.shared().symbols.get(&key) {
            return Ok(symbol.reference);
        }
        let classifier = domains.iter().rev().try_fold(codomain, |tail, &domain| {
            let arrow = kernel
                .ty_arr(domain, tail)
                .map_err(|source| ParameterizedError::Kernel { source })?;
            self.canonical_type(kernel, arrow)
        })?;
        let reference = kernel
            .tm_fv(self.take_name()?, classifier)
            .map_err(|source| ParameterizedError::Kernel { source })?;
        self.shared().symbols.insert(
            key,
            InterpretationSymbol {
                label,
                reference,
                classifier,
            },
        );
        Ok(reference)
    }

    fn apply(
        kernel: &mut Kernel,
        function: Ref,
        arguments: &[Ref],
    ) -> Result<Ref, ParameterizedError> {
        arguments.iter().try_fold(function, |function, &argument| {
            kernel
                .app(function, argument)
                .map_err(|source| ParameterizedError::Resolve {
                    message: format!(
                        "application of {function:?} to {argument:?} failed: {source}"
                    ),
                })
        })
    }

    fn structural_value(
        &self,
        kernel: &mut Kernel,
        label: String,
        children: &[Ref],
    ) -> Result<Ref, ParameterizedError> {
        let domains = children
            .iter()
            .map(|&child| {
                kernel
                    .classifier(child)
                    .map_err(|source| ParameterizedError::Kernel { source })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let primitive = self.primitive(kernel, label, &domains, self.embedding.value())?;
        Self::apply(kernel, primitive, children)
    }

    fn type_predicate(
        &mut self,
        kernel: &mut Kernel,
        ty: &IlType<'_>,
    ) -> Result<Ref, ParameterizedError> {
        if let IlType::Named { name, arguments } = ty
            && arguments.is_empty()
            && let Some(reference) = self.type_bindings.get(*name)
        {
            return Ok(*reference);
        }
        let classifier = self.embedding.ty(ty);
        let witness = kernel
            .tm_fv(self.take_name()?, classifier)
            .map_err(|source| ParameterizedError::Kernel { source })?;
        let membership = self.type_membership(kernel, ty, witness)?;
        let function_type = kernel
            .ty_arr(classifier, self.embedding.bool_ty())
            .map_err(|source| ParameterizedError::Kernel { source })?;
        let function_type = self.canonical_type(kernel, function_type)?;
        kernel
            .lam_at(function_type, witness, membership)
            .map_err(|source| ParameterizedError::Kernel { source })
    }

    fn non_expression_argument(
        &mut self,
        kernel: &mut Kernel,
        argument: &IlArgument<'_>,
    ) -> Result<Ref, ParameterizedError> {
        match argument {
            IlArgument::Type(ty) => self.type_predicate(kernel, ty),
            IlArgument::Definition(name) => self
                .definition_bindings
                .get(*name)
                .copied()
                .map_or_else(|| self.resolve(IlKind::Definition, name), Ok),
            IlArgument::Grammar(symbol) => {
                if let IlGrammarSymbol::Variable { name, arguments } = &**symbol
                    && arguments.is_empty()
                    && let Some(reference) = self.grammar_bindings.get(*name)
                {
                    return Ok(*reference);
                }
                self.structural_value(kernel, format!("grammar-argument:{symbol:?}"), &[])
            }
            IlArgument::Expression(_) => Err(ParameterizedError::Resolve {
                message: "expression argument was not lowered by the expression algebra".to_owned(),
            }),
        }
    }

    fn result_type(kernel: &Kernel, predicate: Ref) -> Result<Ref, ParameterizedError> {
        let classifier = kernel
            .classifier(predicate)
            .map_err(|source| ParameterizedError::Kernel { source })?;
        if kernel.arena().tag(classifier) != Some(Tag::Ty(TyTag::Arr)) {
            return Err(ParameterizedError::Resolve {
                message: "definition graph prefix does not accept a result".to_owned(),
            });
        }
        kernel
            .arena()
            .children(classifier)
            .and_then(|mut children| children.next())
            .ok_or_else(|| ParameterizedError::Resolve {
                message: "definition graph result classifier is malformed".to_owned(),
            })
    }
}

impl RelationalResolver for ParameterizedResolver {
    type Error = ParameterizedError;

    fn declaration_error(&mut self, id: DeclarationId, source: Self::Error) -> Self::Error {
        ParameterizedError::Declaration {
            id,
            source: Box::new(source),
        }
    }

    fn clause_scope(&mut self) -> Self {
        let mut child = self.clone();
        child.bindings.clear();
        child.type_bindings.clear();
        child.definition_bindings.clear();
        child.grammar_bindings.clear();
        child.expression_scopes.clear();
        child.implicit_binders.clear();
        child
    }

    fn enter_expression(
        &mut self,
        kernel: &mut Kernel,
        expression: &IlExpression<'_>,
    ) -> Result<(), Self::Error> {
        let view = expression
            .view()
            .map_err(|source| ParameterizedError::Il { source })?;
        let names = match view {
            IlExpressionView::Iterate { domains, .. } => domains
                .iter()
                .map(covalence_data_spectec::IlDomain::name)
                .collect::<Vec<_>>(),
            IlExpressionView::Variable("_") => vec!["_"],
            _ => return Ok(()),
        };
        let mut scope = Vec::with_capacity(names.len());
        for name in names {
            let reference = kernel
                .tm_fv(self.take_name()?, self.embedding.value())
                .map_err(|source| ParameterizedError::Kernel { source })?;
            let previous = self.bindings.insert(name.to_owned(), reference);
            scope.push((name.to_owned(), previous, reference));
        }
        self.expression_scopes.push(scope);
        Ok(())
    }

    fn leave_expression(&mut self, expression: &IlExpression<'_>) -> Result<(), Self::Error> {
        if !matches!(
            expression.view(),
            Ok(IlExpressionView::Iterate { .. } | IlExpressionView::Variable("_"))
        ) {
            return Ok(());
        }
        let scope = self
            .expression_scopes
            .pop()
            .ok_or_else(|| ParameterizedError::Resolve {
                message: "expression scope stack underflow".to_owned(),
            })?;
        for (name, previous, _) in scope.into_iter().rev() {
            if let Some(reference) = previous {
                self.bindings.insert(name, reference);
            } else {
                self.bindings.remove(&name);
            }
        }
        Ok(())
    }

    fn expression_binders(
        &mut self,
        expression: &IlExpression<'_>,
    ) -> Result<Vec<Ref>, Self::Error> {
        let mut binders = std::mem::take(&mut self.implicit_binders);
        if !matches!(
            expression.view(),
            Ok(IlExpressionView::Iterate { .. } | IlExpressionView::Variable("_"))
        ) {
            return Ok(binders);
        }
        let scoped: Vec<Ref> = self
            .expression_scopes
            .last()
            .map(|scope| scope.iter().map(|(_, _, reference)| *reference).collect())
            .ok_or_else(|| ParameterizedError::Resolve {
                message: "missing expression scope".to_owned(),
            })?;
        binders.extend(scoped);
        Ok(binders)
    }

    fn relation_scope(&mut self, candidates: &[(&str, Ref)]) -> Self {
        let mut child = self.clause_scope();
        child.relations = candidates
            .iter()
            .map(|(name, reference)| ((*name).to_owned(), *reference))
            .collect();
        child
    }

    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error {
        ParameterizedError::Il { source }
    }

    fn kernel_error(&mut self, source: KernelError) -> Self::Error {
        ParameterizedError::Kernel { source }
    }

    fn name_exhausted(&mut self) -> Self::Error {
        ParameterizedError::Resolve {
            message: "free-variable name range exhausted".to_owned(),
        }
    }

    fn case_error(&mut self, source: RelationalCaseError) -> Self::Error {
        ParameterizedError::Clause { source }
    }

    fn least_error(&mut self, source: LeastPredicateError) -> Self::Error {
        ParameterizedError::Least { source }
    }

    fn family_error(&mut self, source: HolFamilyError) -> Self::Error {
        ParameterizedError::Family { source }
    }

    fn theory_error(&mut self, source: HolTheoryError) -> Self::Error {
        ParameterizedError::Theory { source }
    }

    fn binding(&mut self, binding: &IlBinding<'_>, reference: Ref) -> Result<(), Self::Error> {
        let namespace = match binding {
            IlBinding::Expression { .. } => &mut self.bindings,
            IlBinding::Type { .. } => &mut self.type_bindings,
            IlBinding::Definition { .. } => &mut self.definition_bindings,
            IlBinding::Grammar { .. } => &mut self.grammar_bindings,
        };
        namespace.insert(binding.name().to_owned(), reference);
        Ok(())
    }

    fn binding_premise(
        &mut self,
        kernel: &mut Kernel,
        binding: &IlBinding<'_>,
        reference: Ref,
    ) -> Result<Option<Ref>, Self::Error> {
        let IlBinding::Expression { ty, .. } = binding else {
            return Ok(None);
        };
        self.type_membership(kernel, ty, reference).map(Some)
    }

    fn binding_type(
        &mut self,
        kernel: &mut Kernel,
        binding: &IlBinding<'_>,
    ) -> Result<Ref, Self::Error> {
        let ty = self
            .embedding
            .binding(kernel, binding)
            .map_err(|source| ParameterizedError::Kernel { source })?;
        self.canonical_type(kernel, ty)
    }

    fn variable(&mut self, kernel: &mut Kernel, name: &str) -> Result<Ref, Self::Error> {
        if let Some(reference) = self.bindings.get(name).copied() {
            return Ok(reference);
        }
        let reference = kernel
            .tm_fv(self.take_name()?, self.embedding.value())
            .map_err(|source| ParameterizedError::Kernel { source })?;
        self.bindings.insert(name.to_owned(), reference);
        self.implicit_binders.push(reference);
        Ok(reference)
    }

    fn argument(
        &mut self,
        kernel: &mut Kernel,
        argument: &IlArgument<'_>,
    ) -> Result<Ref, Self::Error> {
        self.non_expression_argument(kernel, argument)
    }

    fn pattern_argument(
        &mut self,
        kernel: &mut Kernel,
        argument: &IlArgument<'_>,
        formal: Ref,
    ) -> Result<Ref, Self::Error> {
        match argument {
            IlArgument::Definition(name) if !self.definition_bindings.contains_key(*name) => {
                self.definition_bindings.insert((*name).to_owned(), formal);
                Ok(formal)
            }
            IlArgument::Grammar(symbol)
                if matches!(
                    &**symbol,
                    IlGrammarSymbol::Variable { name, arguments }
                        if arguments.is_empty() && !self.grammar_bindings.contains_key(*name)
                ) =>
            {
                let IlGrammarSymbol::Variable { name, .. } = &**symbol else {
                    unreachable!()
                };
                self.grammar_bindings.insert((*name).to_owned(), formal);
                Ok(formal)
            }
            _ => self.non_expression_argument(kernel, argument),
        }
    }

    fn type_membership(
        &mut self,
        kernel: &mut Kernel,
        ty: &IlType<'_>,
        value: Ref,
    ) -> Result<Ref, Self::Error> {
        if let IlType::Named { name, arguments } = ty
            && arguments.is_empty()
        {
            if let Some(predicate) = self.type_bindings.get(*name).copied() {
                return Self::apply(kernel, predicate, &[value]);
            }
            if let Ok(predicate) = self.resolve(IlKind::Type, name) {
                return Self::apply(kernel, predicate, &[value]);
            }
        }
        if matches!(ty, IlType::Boolean) {
            return kernel
                .bool(self.embedding.bool_ty(), true)
                .map_err(|source| ParameterizedError::Kernel { source });
        }
        let domain = self.embedding.ty(ty);
        let predicate = self.primitive(
            kernel,
            format!("membership:{ty:?}"),
            &[domain],
            self.embedding.bool_ty(),
        )?;
        Self::apply(kernel, predicate, &[value])
    }

    fn type_classifier(
        &mut self,
        _kernel: &mut Kernel,
        ty: &IlType<'_>,
    ) -> Result<Ref, Self::Error> {
        Ok(self.embedding.ty(ty))
    }

    fn tuple_value(&mut self, kernel: &mut Kernel, elements: &[Ref]) -> Result<Ref, Self::Error> {
        self.structural_value(kernel, format!("tuple:{}", elements.len()), elements)
    }

    fn variant_value(
        &mut self,
        kernel: &mut Kernel,
        constructor: &str,
        payload: Ref,
    ) -> Result<Ref, Self::Error> {
        self.structural_value(kernel, format!("variant:{constructor}"), &[payload])
    }

    fn struct_value(
        &mut self,
        kernel: &mut Kernel,
        fields: &[(&str, Ref)],
    ) -> Result<Ref, Self::Error> {
        self.structural_value(
            kernel,
            format!(
                "struct:{:?}",
                fields.iter().map(|(name, _)| *name).collect::<Vec<_>>()
            ),
            &fields.iter().map(|(_, value)| *value).collect::<Vec<_>>(),
        )
    }

    fn grammar_value(
        &mut self,
        kernel: &mut Kernel,
        symbol: &IlGrammarSymbol<'_>,
        children: &[Ref],
    ) -> Result<Ref, Self::Error> {
        self.structural_value(kernel, format!("grammar:{symbol:?}"), children)
    }

    fn type_otherwise(&mut self) -> Self::Error {
        ParameterizedError::Resolve {
            message: "otherwise is unsupported in structural type premises".to_owned(),
        }
    }

    fn grammar_otherwise(&mut self) -> Self::Error {
        ParameterizedError::Resolve {
            message: "otherwise is unsupported in grammar premises".to_owned(),
        }
    }

    fn operation(
        &mut self,
        kernel: &mut Kernel,
        expression: &IlExpressionView<'_>,
        children: &[Ref],
    ) -> Result<Ref, Self::Error> {
        if let IlExpressionView::Boolean(value) = expression {
            return kernel
                .bool(self.embedding.bool_ty(), *value)
                .map_err(|source| ParameterizedError::Kernel { source });
        }
        let output = match expression {
            IlExpressionView::Unary {
                operand: "bool", ..
            }
            | IlExpressionView::Binary {
                operand: "bool", ..
            }
            | IlExpressionView::Comparison { .. }
            | IlExpressionView::Membership => self.embedding.bool_ty(),
            IlExpressionView::Subtype { target, .. } => self.embedding.ty(target),
            _ => self.embedding.value(),
        };
        let domains = children
            .iter()
            .map(|&child| {
                kernel
                    .classifier(child)
                    .map_err(|source| ParameterizedError::Kernel { source })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let primitive = self.primitive(
            kernel,
            format!("expression:{expression:?}"),
            &domains,
            output,
        )?;
        Self::apply(kernel, primitive, children)
    }

    fn call(
        &mut self,
        kernel: &mut Kernel,
        name: &str,
        arguments: &[IlArgument<'_>],
        expression_arguments: &[Ref],
    ) -> Result<RelationalCall, Self::Error> {
        let mut expression_arguments = expression_arguments.iter();
        let mut predicate = self
            .definition_bindings
            .get(name)
            .copied()
            .map_or_else(|| self.resolve(IlKind::Definition, name), Ok)?;
        for argument in arguments {
            let value = match argument {
                IlArgument::Expression(_) => {
                    *expression_arguments
                        .next()
                        .ok_or_else(|| ParameterizedError::Resolve {
                            message: format!("definition {name:?} expression arity mismatch"),
                        })?
                }
                _ => self.non_expression_argument(kernel, argument)?,
            };
            predicate = kernel.app(predicate, value).map_err(|source| {
                ParameterizedError::Resolve {
                    message: format!(
                        "definition {name:?} application of {predicate:?} to {value:?} failed: {source}"
                    ),
                }
            })?;
        }
        if expression_arguments.next().is_some() {
            return Err(ParameterizedError::Resolve {
                message: format!("definition {name:?} expression arity mismatch"),
            });
        }
        Ok(RelationalCall {
            predicate,
            result_type: Self::result_type(kernel, predicate)?,
        })
    }

    fn relation(
        &mut self,
        kernel: &mut Kernel,
        name: &str,
        argument: Ref,
    ) -> Result<Ref, Self::Error> {
        let predicate = self
            .relations
            .get(name)
            .copied()
            .map_or_else(|| self.resolve(IlKind::Relation, name), Ok)?;
        kernel
            .app(predicate, argument)
            .map_err(|source| ParameterizedError::Kernel { source })
    }

    fn iterated_premise(
        &mut self,
        kernel: &mut Kernel,
        iteration: &IlIteration<'_>,
        domains: &[(&str, RelationalTerm)],
        repeated: RelationalCondition,
    ) -> Result<RelationalCondition, Self::Error> {
        let mut binders = repeated.binders().to_vec();
        let mut premises = Vec::new();
        let mut values = Vec::new();
        for (_, domain) in domains {
            binders.extend_from_slice(domain.binders());
            premises.extend_from_slice(domain.premises());
            values.push(domain.value());
        }
        let repeated = existential_case(
            kernel,
            self.embedding.bool_ty(),
            repeated.binders(),
            repeated.premises(),
        )
        .map_err(|source| ParameterizedError::Kernel { source })?;
        values.push(repeated);
        let domains = values
            .iter()
            .map(|&value| {
                kernel
                    .classifier(value)
                    .map_err(|source| ParameterizedError::Kernel { source })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let primitive = self.primitive(
            kernel,
            format!("iterated-premise:{iteration:?}"),
            &domains,
            self.embedding.bool_ty(),
        )?;
        premises.push(Self::apply(kernel, primitive, &values)?);
        Ok(RelationalCondition::new(binders, premises, false))
    }

    fn nested_premise_bindings(&mut self, count: usize) -> Self::Error {
        ParameterizedError::Resolve {
            message: format!("nested relation premise has {count} bindings"),
        }
    }

    fn relation_otherwise(&mut self) -> Self::Error {
        ParameterizedError::Resolve {
            message: "otherwise is not monotone in a relation rule".to_owned(),
        }
    }
}
