use covalence_data_cbor::drisl::{self, CidCodec, CidHash, Policy};
use covalence_data_spectec::{
    ClauseId, DeclarationId, IlClauseSchema, IlDocument, IlExpression, IlExpressionKind,
    IlGrammarSymbol, IlKind, IlPremise, IlProductionSchema, IlRuleSchema, IlSchemaError, IlType,
    Limits,
};
use covalence_logic_hol::{Kernel, Tag, TmTag};
use covalence_nucleus_spectec::{
    ADD_SLICE_TYPE_NAME, AddSliceArtifact, AddSliceArtifactError, AddSlicePlan,
    AdmissibleStartFacts, AdmissibleStartWitness, ArtifactError, CompilationRecord, CompileError,
    Compiler, Coverage, CoverageArtifact, CoverageDisposition, CoveragePlan, Disposition,
    ExportedFunctionFacts, ExportedFunctionView, ExportedFunctionWitness, ExpressionAlgebra,
    GrammarAlgebra, GrammarChildren, HolCase, HolEmbedding, HolFamilyBranch, HolRule,
    HolTheoryError, IndexErasure, InterpretationKind, KernelRoot, RelationalCall, RelationalClause,
    RelationalCondition, RelationalDefinitionSchema, RelationalDefinitionSource,
    RelationalExpressionAlgebra, RelationalRelation, RelationalResolver, RelationalTerm,
    SelectedCompileError, SelectedCompiler, Source, SpecTecValueBuilder, TYPE_NAME,
    TranslationCase, TypeAlgebra, TypeChildren, begin_least_closed_family, close_family_definition,
    close_graph_equation, close_hol_rule, close_hol_rules, close_hol_theory, declare_hol_schema,
    empty_wasm_module, fold_expression, fold_grammar, fold_type, forwarding_wasm_module,
    least_closed_family, least_closed_predicate, ordered_cases, parameterized_document,
    parameterized_document_with, prove_reflexive_binary_application, relational_definition,
    relational_definition_declaration, relational_definition_schema, relational_document,
    relational_grammar_declaration, relational_hol_case, relational_hol_rule,
    relational_relation_declaration, relational_relations, relational_type_declaration,
    spectec_execution,
};

#[derive(Clone)]
struct TestRelationalResolver {
    x: covalence_logic_hol::Ref,
    y: covalence_logic_hol::Ref,
    add: covalence_logic_hol::Ref,
    graph: covalence_logic_hol::Ref,
    bool_ty: covalence_logic_hol::Ref,
    bound: std::collections::BTreeMap<String, covalence_logic_hol::Ref>,
    relations: std::collections::BTreeMap<String, covalence_logic_hol::Ref>,
}

fn elementary_condition_facts(
    kernel: &mut Kernel,
    conditions: &[covalence_logic_hol::Ref],
) -> (
    Vec<covalence_logic_hol::ThmId>,
    Vec<covalence_logic_hol::Ref>,
) {
    let mut remaining = Vec::new();
    let facts = conditions
        .iter()
        .map(|&condition| {
            if let Some(proved) =
                covalence_nucleus_spectec::prove_reflexive_condition(kernel, condition).unwrap()
            {
                proved.theorem
            } else {
                remaining.push(condition);
                kernel
                    .identity(covalence_logic_hol::Lit::positive(condition.get()))
                    .unwrap()
            }
        })
        .collect();
    (facts, remaining)
}

impl RelationalResolver for TestRelationalResolver {
    type Error = String;

    fn declaration_error(&mut self, _id: DeclarationId, source: Self::Error) -> Self::Error {
        source
    }

    fn clause_scope(&mut self) -> Self {
        let mut child = self.clone();
        child.bound.clear();
        child
    }

    fn restore_scope(&mut self, _scope: Self) {}

    fn enter_expression(
        &mut self,
        _kernel: &mut Kernel,
        _expression: &IlExpression<'_>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn leave_expression(&mut self, _expression: &IlExpression<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn expression_binders(
        &mut self,
        _expression: &IlExpression<'_>,
    ) -> Result<Vec<covalence_logic_hol::Ref>, Self::Error> {
        Ok(Vec::new())
    }

    fn relation_scope(&mut self, candidates: &[(&str, covalence_logic_hol::Ref)]) -> Self {
        let mut child = self.clause_scope();
        child.relations = candidates
            .iter()
            .map(|(name, candidate)| ((*name).to_owned(), *candidate))
            .collect();
        child
    }

    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error {
        source.to_string()
    }

    fn kernel_error(&mut self, source: covalence_logic_hol::KernelError) -> Self::Error {
        source.to_string()
    }

    fn name_exhausted(&mut self) -> Self::Error {
        "name range exhausted".to_owned()
    }

    fn case_error(
        &mut self,
        source: covalence_nucleus_spectec::RelationalCaseError,
    ) -> Self::Error {
        source.to_string()
    }

    fn least_error(
        &mut self,
        source: covalence_nucleus_spectec::LeastPredicateError,
    ) -> Self::Error {
        source.to_string()
    }

    fn family_error(&mut self, source: covalence_nucleus_spectec::HolFamilyError) -> Self::Error {
        source.to_string()
    }

    fn theory_error(&mut self, source: HolTheoryError) -> Self::Error {
        source.to_string()
    }

    fn binding(
        &mut self,
        binding: &covalence_data_spectec::IlBinding<'_>,
        reference: covalence_logic_hol::Ref,
    ) -> Result<(), Self::Error> {
        self.bound.insert(binding.name().to_owned(), reference);
        Ok(())
    }

    fn binding_premise(
        &mut self,
        kernel: &mut Kernel,
        binding: &covalence_data_spectec::IlBinding<'_>,
        reference: covalence_logic_hol::Ref,
    ) -> Result<Option<covalence_logic_hol::Ref>, Self::Error> {
        let covalence_data_spectec::IlBinding::Expression { ty, .. } = binding else {
            return Ok(None);
        };
        self.type_membership(kernel, ty, reference).map(Some)
    }

    fn binding_type(
        &mut self,
        kernel: &mut Kernel,
        binding: &covalence_data_spectec::IlBinding<'_>,
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        let value = kernel
            .classifier(self.x)
            .map_err(|error| error.to_string())?;
        HolEmbedding::new(value, self.bool_ty)
            .binding(kernel, binding)
            .map_err(|error| error.to_string())
    }

    fn variable(
        &mut self,
        _kernel: &mut Kernel,
        name: &str,
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        if let Some(reference) = self.bound.get(name) {
            return Ok(*reference);
        }
        match name {
            "x" => Ok(self.x),
            "y" => Ok(self.y),
            _ => Err("unbound variable".to_owned()),
        }
    }

    fn argument(
        &mut self,
        _kernel: &mut Kernel,
        _argument: &covalence_data_spectec::IlArgument<'_>,
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        Err("unexpected non-expression argument".to_owned())
    }

    fn type_membership(
        &mut self,
        kernel: &mut Kernel,
        _ty: &IlType<'_>,
        _value: covalence_logic_hol::Ref,
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        kernel
            .bool(self.bool_ty, true)
            .map_err(|error| error.to_string())
    }

    fn type_classifier(
        &mut self,
        kernel: &mut Kernel,
        ty: &IlType<'_>,
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        let value = kernel
            .classifier(self.x)
            .map_err(|error| error.to_string())?;
        Ok(HolEmbedding::new(value, self.bool_ty).ty(ty))
    }

    fn tuple_value(
        &mut self,
        _kernel: &mut Kernel,
        _elements: &[covalence_logic_hol::Ref],
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        Ok(self.x)
    }

    fn variant_value(
        &mut self,
        _kernel: &mut Kernel,
        _constructor: &str,
        _payload: covalence_logic_hol::Ref,
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        Ok(self.x)
    }

    fn struct_value(
        &mut self,
        _kernel: &mut Kernel,
        _fields: &[(&str, covalence_logic_hol::Ref)],
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        Ok(self.x)
    }

    fn grammar_value(
        &mut self,
        _kernel: &mut Kernel,
        _symbol: &IlGrammarSymbol<'_>,
        _children: &[covalence_logic_hol::Ref],
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        Ok(self.x)
    }

    fn type_otherwise(&mut self) -> Self::Error {
        "otherwise in structural type".to_owned()
    }

    fn grammar_otherwise(&mut self) -> Self::Error {
        "otherwise in grammar production".to_owned()
    }

    fn operation(
        &mut self,
        kernel: &mut Kernel,
        expression: &covalence_data_spectec::IlExpressionView<'_>,
        children: &[covalence_logic_hol::Ref],
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        if let covalence_data_spectec::IlExpressionView::Boolean(value) = expression {
            return kernel
                .bool(self.bool_ty, *value)
                .map_err(|error| error.to_string());
        }
        if !matches!(
            expression,
            covalence_data_spectec::IlExpressionView::Binary {
                operator: "add",
                ..
            }
        ) || children.len() != 2
        {
            return Err("unexpected primitive".to_owned());
        }
        let partial = kernel
            .app(self.add, children[0])
            .map_err(|error| error.to_string())?;
        kernel
            .app(partial, children[1])
            .map_err(|error| error.to_string())
    }

    fn call(
        &mut self,
        kernel: &mut Kernel,
        name: &str,
        _arguments: &[covalence_data_spectec::IlArgument<'_>],
        expression_arguments: &[covalence_logic_hol::Ref],
    ) -> Result<RelationalCall, Self::Error> {
        if name != "f" {
            return Err("unknown definition".to_owned());
        }
        let [argument] = expression_arguments else {
            return Err("call arity mismatch".to_owned());
        };
        let predicate = kernel
            .app(self.graph, *argument)
            .map_err(|error| error.to_string())?;
        let result_type = kernel
            .classifier(self.x)
            .map_err(|error| error.to_string())?;
        Ok(RelationalCall {
            predicate,
            result_type,
        })
    }

    fn relation(
        &mut self,
        kernel: &mut Kernel,
        name: &str,
        argument: covalence_logic_hol::Ref,
    ) -> Result<covalence_logic_hol::Ref, Self::Error> {
        if let Some(candidate) = self.relations.get(name) {
            return kernel
                .app(*candidate, argument)
                .map_err(|error| error.to_string());
        }
        kernel
            .bool(self.bool_ty, true)
            .map_err(|error| error.to_string())
    }

    fn iterated_premise(
        &mut self,
        _kernel: &mut Kernel,
        _iteration: &covalence_data_spectec::IlIteration<'_>,
        _domains: &[(&str, RelationalTerm)],
        repeated: covalence_nucleus_spectec::RelationalCondition,
    ) -> Result<covalence_nucleus_spectec::RelationalCondition, Self::Error> {
        Ok(repeated)
    }

    fn nested_premise_bindings(&mut self, count: usize) -> Self::Error {
        format!("unsupported nested premise bindings: {count}")
    }

    fn relation_otherwise(&mut self) -> Self::Error {
        "otherwise in relation rule".to_owned()
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Exercises binding, call, rule, and exact-clause composition.
fn relational_expression_fold_turns_calls_into_graph_premises() {
    let il = IlDocument::parse(
        b"(def \"g\" nat (clause (exp \"z\" nat) (exp \"flag\" bool) (call \"f\" (exp (bin add nat (var \"x\") (var \"y\")))) (if (bool true)) (let (var \"x\") (var \"x\")) (rule \"R\" \"R\" (var \"x\")) else))",
        Limits::default(),
    )
    .unwrap();
    let clause = il
        .clauses(DeclarationId::new(1, None).unwrap())
        .unwrap()
        .remove(0);
    let cursor = il.clause_cursor(clause.id()).unwrap();
    let schema = IlClauseSchema::decode(&cursor).unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(1, value).unwrap();
    let y = kernel.tm_fv(2, value).unwrap();
    let add = kernel.tm_fv(3, binary_ty).unwrap();
    let graph = kernel.tm_fv(4, graph_ty).unwrap();
    let resolver = TestRelationalResolver {
        x,
        y,
        add,
        graph,
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };
    let (term, explicit, conditions) = {
        let mut algebra = RelationalExpressionAlgebra::new(&mut kernel, resolver, bool_ty, 100);
        let explicit = algebra.bindings(schema.bindings()).unwrap();
        let term = fold_expression(schema.result(), &mut algebra).unwrap();
        let conditions = schema
            .premises()
            .iter()
            .map(|premise| algebra.premise(premise))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        assert_eq!(algebra.next_name(), 103);
        (term, explicit, conditions)
    };
    assert_eq!(conditions.len(), 4);
    assert!(conditions[3].otherwise());
    let semantic_binders = conditions
        .iter()
        .flat_map(|condition| condition.binders().iter().copied())
        .collect::<Vec<_>>();
    let semantic_premises = conditions
        .iter()
        .flat_map(|condition| condition.premises().iter().copied())
        .collect::<Vec<_>>();
    assert_eq!(explicit.len(), 2);
    assert!(
        kernel
            .equivalent(kernel.classifier(explicit[0]).unwrap(), value)
            .unwrap()
    );
    assert!(
        kernel
            .equivalent(kernel.classifier(explicit[1]).unwrap(), bool_ty)
            .unwrap()
    );
    assert_eq!(term.binders().len(), 1);
    assert_eq!(term.premises().len(), 1);
    assert!(
        kernel
            .equivalent(kernel.classifier(term.value()).unwrap(), value)
            .unwrap()
    );
    assert!(
        kernel
            .equivalent(kernel.classifier(term.premises()[0]).unwrap(), bool_ty)
            .unwrap()
    );
    let formal_value = kernel.tm_fv(300, value).unwrap();
    let formal_bool = kernel.tm_fv(301, bool_ty).unwrap();
    let formal_result = kernel.tm_fv(302, value).unwrap();
    let formal_inputs = [formal_value, formal_bool];
    let patterns = [
        RelationalTerm::new(explicit[0], Vec::new(), Vec::new()),
        RelationalTerm::new(explicit[1], Vec::new(), Vec::new()),
    ];
    let case = relational_hol_case(
        &mut kernel,
        bool_ty,
        &RelationalClause {
            formal_inputs: &formal_inputs,
            formal_result,
            explicit_locals: &explicit,
            patterns: &patterns,
            result: &term,
            semantic_binders: &semantic_binders,
            semantic_premises: &semantic_premises,
            otherwise: conditions.iter().any(RelationalCondition::otherwise),
        },
    )
    .unwrap();
    assert!(case.otherwise);
    assert!(
        kernel
            .equivalent(kernel.classifier(case.applicable).unwrap(), bool_ty)
            .unwrap()
    );
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let candidate = kernel.tm_fv(200, predicate_ty).unwrap();
    let semantic_premise = kernel.bool(bool_ty, true).unwrap();
    let rule = relational_hol_rule(&explicit, &[term], &[semantic_premise]);
    assert_eq!(rule.binders.len(), 3);
    assert_eq!(rule.premises.len(), 2);
    assert_eq!(rule.conclusion.len(), 1);
    let closure = close_hol_rule(&mut kernel, bool_ty, candidate, &rule).unwrap();
    assert!(
        kernel
            .equivalent(kernel.classifier(closure).unwrap(), bool_ty)
            .unwrap()
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Covers low-level and schema-derived definition APIs.
fn complete_clause_api_lowers_patterns_result_and_premises() {
    let il = IlDocument::parse(
        b"(def \"pick\" (exp \"a\" nat) (exp \"b\" nat) nat (clause (exp (var \"x\")) (exp (var \"y\")) (var \"x\") (if (bool true)) else))",
        Limits::default(),
    )
    .unwrap();
    let clause = il
        .clauses(DeclarationId::new(1, None).unwrap())
        .unwrap()
        .remove(0);
    let schema = IlClauseSchema::decode(&il.clause_cursor(clause.id()).unwrap()).unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(1, value).unwrap();
    let y = kernel.tm_fv(2, value).unwrap();
    let add = kernel.tm_fv(3, binary_ty).unwrap();
    let graph = kernel.tm_fv(4, graph_ty).unwrap();
    let formal_inputs = [
        kernel.tm_fv(10, value).unwrap(),
        kernel.tm_fv(11, value).unwrap(),
    ];
    let formal_result = kernel.tm_fv(12, value).unwrap();
    let mut resolver = TestRelationalResolver {
        x,
        y,
        add,
        graph,
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };
    let case = RelationalExpressionAlgebra::new(&mut kernel, resolver.clone(), bool_ty, 100)
        .clause(&schema, &formal_inputs, formal_result)
        .unwrap();

    assert!(case.otherwise);
    assert!(
        kernel
            .equivalent(kernel.classifier(case.produces).unwrap(), bool_ty)
            .unwrap()
    );
    let result_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let second_tail = kernel.ty_arr(value, result_tail).unwrap();
    let predicate_ty = kernel.ty_arr(value, second_tail).unwrap();
    let predicate = kernel.tm_fv(20, predicate_ty).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();
    let definition = relational_definition(
        &mut kernel,
        &mut resolver,
        &RelationalDefinitionSource {
            bool_ty,
            predicate,
            formal_inputs: &formal_inputs,
            formal_result,
            clauses: std::slice::from_ref(&schema),
            first_name: 200,
        },
    )
    .unwrap();
    assert_eq!(definition.cases.len(), 1);
    assert_eq!(definition.formal_inputs, formal_inputs);
    assert_eq!(definition.formal_result, formal_result);
    let schema_predicate = kernel.tm_fv(300, predicate_ty).unwrap();
    let derived = relational_definition_schema(
        &mut kernel,
        &mut resolver,
        &RelationalDefinitionSchema {
            bool_ty,
            predicate: schema_predicate,
            clauses: std::slice::from_ref(&schema),
            avoid: &[predicate, graph, x, y, add],
        },
    )
    .unwrap();
    assert_eq!(derived.formal_inputs.len(), 2);
    assert!(
        derived
            .formal_inputs
            .iter()
            .chain(std::iter::once(&derived.formal_result))
            .all(|&variable| kernel
                .equivalent(kernel.classifier(variable).unwrap(), value)
                .unwrap())
    );
    assert!(
        kernel
            .equivalent(kernel.classifier(derived.equation).unwrap(), bool_ty)
            .unwrap()
    );
    let not_graph = kernel.bool(bool_ty, true).unwrap();
    let before = kernel.arena().len();
    assert!(
        relational_definition_schema(
            &mut kernel,
            &mut resolver,
            &RelationalDefinitionSchema {
                bool_ty,
                predicate: not_graph,
                clauses: std::slice::from_ref(&schema),
                avoid: &[],
            },
        )
        .is_err()
    );
    assert_eq!(kernel.arena().len(), before);
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
#[allow(clippy::too_many_lines)]
fn exact_source_definition_lowers_from_selector_and_schema() {
    let bytes = b"(def \"id\" (exp \"x\" nat) nat (clause (exp (var \"x\")) (var \"x\"))) (typ \"T\" (inst (alias nat)))";
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let schema = declare_hol_schema(&source, &mut kernel, value, bool_ty).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(10_000, value).unwrap();
    let mut resolver = TestRelationalResolver {
        x,
        y: kernel.tm_fv(10_001, value).unwrap(),
        add: kernel.tm_fv(10_002, binary_ty).unwrap(),
        graph: kernel.tm_fv(10_003, graph_ty).unwrap(),
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };
    let definition = relational_definition_declaration(
        &mut kernel,
        &mut resolver,
        &source,
        &schema,
        DeclarationId::new(1, None).unwrap(),
        &[],
    )
    .unwrap();

    assert_eq!(definition.formal_inputs.len(), 1);
    assert_eq!(definition.cases.len(), 1);
    assert!(
        kernel
            .equivalent(kernel.classifier(definition.equation).unwrap(), bool_ty)
            .unwrap()
    );
    let production_witnesses = definition
        .match_production_witnesses(&mut kernel, 0, &[x])
        .unwrap()
        .unwrap();
    let inferred_result = definition
        .production_result(&mut kernel, 0, &[x], &production_witnesses)
        .unwrap();
    let definition_predicate = schema
        .declaration(DeclarationId::new(1, None).unwrap())
        .unwrap()
        .reference();
    let applied = kernel
        .app(definition_predicate, x)
        .and_then(|partial| kernel.app(partial, inferred_result))
        .unwrap();
    let matched = definition
        .match_application(&kernel, definition_predicate, applied)
        .unwrap();
    assert_eq!(matched.inputs(), &[x]);
    assert_eq!(matched.result(), inferred_result);
    assert!(
        definition
            .match_application(&kernel, resolver.graph, applied)
            .is_none()
    );
    let instance = definition
        .specialize(&mut kernel, bool_ty, &[x], inferred_result)
        .unwrap();
    let production_obligations = instance
        .production_obligations(&mut kernel, 0, &production_witnesses)
        .unwrap();
    let (production_facts, remaining) =
        elementary_condition_facts(&mut kernel, &production_obligations);
    let selected = instance
        .prove_production(
            &mut kernel,
            bool_ty,
            0,
            &production_witnesses,
            &production_facts,
        )
        .unwrap();
    let body = instance
        .prove_body_case(&mut kernel, bool_ty, 0, selected.theorem)
        .unwrap();
    assert!(remaining.len() < production_obligations.len());
    covalence_nucleus_spectec::EvidenceScope::positive(&remaining)
        .check(&kernel, body)
        .unwrap();
    let before = kernel.arena().len();
    assert!(
        relational_definition_declaration(
            &mut kernel,
            &mut resolver,
            &source,
            &schema,
            DeclarationId::new(2, None).unwrap(),
            &[],
        )
        .is_err()
    );
    assert_eq!(kernel.arena().len(), before);
}

#[test]
fn complete_relation_rule_lowers_to_inductive_hol_rule() {
    let il = IlDocument::parse(
        b"(rel \"R\" \"R\" nat (rule \"base\" (exp \"x\" nat) \"R\" (var \"x\") (if (bool true))))",
        Limits::default(),
    )
    .unwrap();
    let declaration = il
        .schema(DeclarationId::new(1, None).unwrap())
        .unwrap()
        .unwrap();
    let covalence_data_spectec::IlDeclarationBody::Relation { rules, .. } = declaration.body()
    else {
        panic!("expected relation")
    };
    let schema = IlRuleSchema::decode(&rules[0]).unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(1, value).unwrap();
    let resolver = TestRelationalResolver {
        x,
        y: kernel.tm_fv(2, value).unwrap(),
        add: kernel.tm_fv(3, binary_ty).unwrap(),
        graph: kernel.tm_fv(4, graph_ty).unwrap(),
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };
    let rule = RelationalExpressionAlgebra::new(&mut kernel, resolver, bool_ty, 100)
        .rule(&schema)
        .unwrap();
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let candidate = kernel.tm_fv(20, predicate_ty).unwrap();
    let closure = close_hol_rule(&mut kernel, bool_ty, candidate, &rule).unwrap();

    assert_eq!(rule.binders.len(), 1);
    assert_eq!(rule.premises.len(), 2); // Binding membership and explicit `if`.
    assert!(
        kernel
            .equivalent(kernel.classifier(closure).unwrap(), bool_ty)
            .unwrap()
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Covers decoding, mutual scope, hygiene, and slot equations.
fn mutually_recursive_relations_lower_to_one_least_hol_family() {
    let il = IlDocument::parse(
        br#"(rec
            (rel "R" "R" nat
              (rule "r" (exp "x" nat) "R" (var "x")
                (rule "S" "S" (var "x"))))
            (rel "S" "S" nat
              (rule "s" (exp "x" nat) "S" (var "x")
                (rule "R" "R" (var "x")))))"#,
        Limits::default(),
    )
    .unwrap();
    let first = il
        .schema(DeclarationId::new(1, Some(1)).unwrap())
        .unwrap()
        .unwrap();
    let second = il
        .schema(DeclarationId::new(1, Some(2)).unwrap())
        .unwrap()
        .unwrap();
    let covalence_data_spectec::IlDeclarationBody::Relation {
        rules: first_rules, ..
    } = first.body()
    else {
        panic!("expected first relation")
    };
    let covalence_data_spectec::IlDeclarationBody::Relation {
        rules: second_rules,
        ..
    } = second.body()
    else {
        panic!("expected second relation")
    };
    let first_rules = first_rules
        .iter()
        .map(IlRuleSchema::decode)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let second_rules = second_rules
        .iter()
        .map(IlRuleSchema::decode)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();

    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let first_predicate = kernel.tm_fv(20, predicate_ty).unwrap();
    let second_predicate = kernel.tm_fv(21, predicate_ty).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(1, value).unwrap();
    let mut resolver = TestRelationalResolver {
        x,
        y: kernel.tm_fv(2, value).unwrap(),
        add: kernel.tm_fv(3, binary_ty).unwrap(),
        graph: kernel.tm_fv(4, graph_ty).unwrap(),
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };
    let theorem_count = kernel.thm().live_theorems().count();
    let family = relational_relations(
        &mut kernel,
        &mut resolver,
        bool_ty,
        &[
            RelationalRelation {
                name: "R",
                predicate: first_predicate,
                rules: &first_rules,
            },
            RelationalRelation {
                name: "S",
                predicate: second_predicate,
                rules: &second_rules,
            },
        ],
    )
    .unwrap();

    assert_eq!(family.len(), 2);
    assert_eq!(family[0].predicate, first_predicate);
    assert_eq!(family[1].predicate, second_predicate);
    assert_ne!(family[0].least.candidate, first_predicate);
    assert_ne!(family[0].least.candidate, second_predicate);
    assert_ne!(family[1].least.candidate, first_predicate);
    assert_ne!(family[1].least.candidate, second_predicate);
    for relation in family {
        assert!(
            kernel
                .equivalent(
                    kernel.classifier(relation.least.predicate).unwrap(),
                    predicate_ty
                )
                .unwrap()
        );
        assert!(
            kernel
                .equivalent(kernel.classifier(relation.equation).unwrap(), bool_ty)
                .unwrap()
        );
    }
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn exact_source_relation_selector_lowers_complete_recursive_root() {
    let bytes = br#"(rec
        (rel "R" "R" nat
          (rule "r" (exp "x" nat) "R" (var "x") (rule "S" "S" (var "x"))))
        (rel "S" "S" nat
          (rule "s" (exp "x" nat) "S" (var "x") (rule "R" "R" (var "x")))))"#;
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let schema = declare_hol_schema(&source, &mut kernel, value, bool_ty).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(10_000, value).unwrap();
    let mut resolver = TestRelationalResolver {
        x,
        y: kernel.tm_fv(10_001, value).unwrap(),
        add: kernel.tm_fv(10_002, binary_ty).unwrap(),
        graph: kernel.tm_fv(10_003, graph_ty).unwrap(),
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };
    let family = relational_relation_declaration(
        &mut kernel,
        &mut resolver,
        &source,
        &schema,
        DeclarationId::new(1, Some(2)).unwrap(),
        &[],
    )
    .unwrap();

    assert_eq!(family.len(), 2);
    assert_eq!(
        family[0].predicate,
        schema
            .declaration(DeclarationId::new(1, Some(1)).unwrap())
            .unwrap()
            .reference()
    );
    assert_eq!(
        family[1].predicate,
        schema
            .declaration(DeclarationId::new(1, Some(2)).unwrap())
            .unwrap()
            .reference()
    );
    assert!(family.iter().all(|definition| {
        kernel
            .equivalent(kernel.classifier(definition.equation).unwrap(), bool_ty)
            .unwrap()
    }));
}

#[test]
fn expression_fold_is_bottom_up_and_target_independent() {
    struct CountAlgebra(Vec<IlExpressionKind>);

    impl ExpressionAlgebra for CountAlgebra {
        type Term = usize;
        type Error = String;

        fn schema_error(&mut self, source: IlSchemaError) -> Self::Error {
            source.to_string()
        }

        fn expression(
            &mut self,
            expression: &IlExpression<'_>,
            children: Vec<Self::Term>,
        ) -> Result<Self::Term, Self::Error> {
            self.0.push(expression.kind());
            Ok(1 + children.into_iter().sum::<usize>())
        }
    }

    let il = IlDocument::parse(
        b"(def \"f\" nat (clause (bin add nat (var \"x\") (var \"y\"))))",
        Limits::default(),
    )
    .unwrap();
    let clause = il
        .clauses(DeclarationId::new(1, None).unwrap())
        .unwrap()
        .remove(0);
    let cursor = il.clause_cursor(clause.id()).unwrap();
    let schema = IlClauseSchema::decode(&cursor).unwrap();
    let mut algebra = CountAlgebra(Vec::new());

    assert_eq!(fold_expression(schema.result(), &mut algebra).unwrap(), 3);
    assert_eq!(
        algebra.0,
        vec![
            IlExpressionKind::Variable,
            IlExpressionKind::Variable,
            IlExpressionKind::Binary,
        ]
    );
}

#[test]
fn type_fold_composes_with_dependent_expression_indices() {
    struct CountExpressions(usize);

    impl ExpressionAlgebra for CountExpressions {
        type Term = ();
        type Error = String;

        fn schema_error(&mut self, source: IlSchemaError) -> Self::Error {
            source.to_string()
        }

        fn expression(
            &mut self,
            _expression: &IlExpression<'_>,
            _children: Vec<Self::Term>,
        ) -> Result<Self::Term, Self::Error> {
            self.0 += 1;
            Ok(())
        }
    }

    struct CountTypes(usize);

    impl TypeAlgebra<()> for CountTypes {
        type Type = ();
        type Error = String;

        fn schema_error(&mut self, source: IlSchemaError) -> Self::Error {
            source.to_string()
        }

        fn ty(
            &mut self,
            _source: &IlType<'_>,
            _children: TypeChildren<'_, (), Self::Type>,
        ) -> Result<Self::Type, Self::Error> {
            self.0 += 1;
            Ok(())
        }
    }

    let il = IlDocument::parse(
        b"(def \"f\" (tup (bind (var \"n\") nat) (bind _ (iter nat (listn (var \"n\") \"i\")))) (clause (num (nat 0))))",
        Limits::default(),
    )
    .unwrap();
    let schema = il
        .schema(DeclarationId::new(1, None).unwrap())
        .unwrap()
        .unwrap();
    let covalence_data_spectec::IlDeclarationBody::Definition { result, .. } = schema.body() else {
        panic!("expected definition")
    };
    let ty = IlType::decode(result).unwrap();
    let mut expressions = CountExpressions(0);
    let mut types = CountTypes(0);

    fold_type(&ty, &mut expressions, &mut types).unwrap();

    assert_eq!(expressions.0, 2);
    assert_eq!(types.0, 4);
}

#[test]
fn grammar_fold_composes_expression_and_symbol_children() {
    struct Expressions(usize);
    impl ExpressionAlgebra for Expressions {
        type Term = ();
        type Error = String;
        fn schema_error(&mut self, source: IlSchemaError) -> String {
            source.to_string()
        }
        fn expression(
            &mut self,
            _expression: &IlExpression<'_>,
            _children: Vec<()>,
        ) -> Result<(), String> {
            self.0 += 1;
            Ok(())
        }
    }
    struct Types;
    impl TypeAlgebra<()> for Types {
        type Type = ();
        type Error = String;
        fn schema_error(&mut self, source: IlSchemaError) -> String {
            source.to_string()
        }
        fn ty(
            &mut self,
            _source: &IlType<'_>,
            _children: TypeChildren<'_, (), ()>,
        ) -> Result<(), String> {
            Ok(())
        }
    }
    struct Grammars(usize);
    impl GrammarAlgebra<(), ()> for Grammars {
        type Grammar = ();
        type Error = String;
        fn schema_error(&mut self, source: IlSchemaError) -> String {
            source.to_string()
        }
        fn grammar(
            &mut self,
            _source: &IlGrammarSymbol<'_>,
            _children: GrammarChildren<'_, (), (), ()>,
        ) -> Result<(), String> {
            self.0 += 1;
            Ok(())
        }
    }

    let il = IlDocument::parse(
        b"(gram \"G\" nat (prod (seq (text \"x\") (attr (var \"n\") (num 0x01))) (num (nat 0))))",
        Limits::default(),
    )
    .unwrap();
    let schema = il
        .schema(DeclarationId::new(1, None).unwrap())
        .unwrap()
        .unwrap();
    let covalence_data_spectec::IlDeclarationBody::Grammar { productions, .. } = schema.body()
    else {
        panic!("expected grammar")
    };
    let production = IlProductionSchema::decode(&productions[0]).unwrap();
    let mut expressions = Expressions(0);
    let mut types = Types;
    let mut grammars = Grammars(0);

    fold_grammar(
        production.symbol(),
        &mut expressions,
        &mut types,
        &mut grammars,
    )
    .unwrap();

    assert_eq!(expressions.0, 1);
    assert_eq!(grammars.0, 4);
}

#[test]
fn exact_grammar_declaration_lowers_productions_to_hol_family() {
    let bytes = br#"(gram "G" nat
        (prod (exp "x" nat) (text "a") (var "x")))"#;
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let schema = declare_hol_schema(&source, &mut kernel, value, bool_ty).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(10_000, value).unwrap();
    let mut resolver = TestRelationalResolver {
        x,
        y: kernel.tm_fv(10_001, value).unwrap(),
        add: kernel.tm_fv(10_002, binary_ty).unwrap(),
        graph: kernel.tm_fv(10_003, graph_ty).unwrap(),
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };
    let grammar = relational_grammar_declaration(
        &mut kernel,
        &mut resolver,
        &source,
        &schema,
        DeclarationId::new(1, None).unwrap(),
        &[x],
    )
    .unwrap();

    assert_eq!(grammar.formal_arguments.len(), 2);
    assert_eq!(grammar.definition.branches.len(), 1);
    assert!(
        kernel
            .equivalent(
                kernel.classifier(grammar.definition.equation).unwrap(),
                bool_ty
            )
            .unwrap()
    );
}

#[test]
fn ordered_graph_constraints_encode_otherwise_without_minting_facts() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let predicate = kernel.tm_fv(1, predicate_ty).unwrap();
    let argument = kernel.tm_fv(2, value).unwrap();
    let truth = kernel.bool(bool_ty, true).unwrap();
    let falsity = kernel.bool(bool_ty, false).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();
    let body = ordered_cases(
        &mut kernel,
        bool_ty,
        &[
            HolCase {
                applicable: truth,
                produces: falsity,
                otherwise: false,
            },
            HolCase {
                applicable: truth,
                produces: truth,
                otherwise: true,
            },
        ],
    )
    .unwrap();
    let equation = close_graph_equation(
        &mut kernel,
        bool_ty,
        predicate,
        &[argument],
        &[argument],
        body,
    )
    .unwrap();

    assert!(
        kernel
            .equivalent(kernel.classifier(equation).unwrap(), bool_ty)
            .unwrap()
    );
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn exact_family_definition_matches_indices_and_existential_locals() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let tail = kernel.ty_arr(value, bool_ty).unwrap();
    let predicate_ty = kernel.ty_arr(value, tail).unwrap();
    let predicate = kernel.tm_fv(1, predicate_ty).unwrap();
    let formal_index = kernel.tm_fv(2, value).unwrap();
    let formal_value = kernel.tm_fv(3, value).unwrap();
    let branch_index = kernel.tm_fv(4, value).unwrap();
    let branch_value = kernel.tm_fv(5, value).unwrap();
    let premise = kernel.bool(bool_ty, true).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();

    let definition = close_family_definition(
        &mut kernel,
        bool_ty,
        predicate,
        &[formal_index, formal_value],
        &[HolFamilyBranch {
            binders: vec![branch_index, branch_value],
            arguments: vec![branch_index, branch_value],
            premises: vec![premise],
        }],
    )
    .unwrap();

    assert_eq!(definition.branches.len(), 1);
    assert!(
        kernel
            .equivalent(kernel.classifier(definition.equation).unwrap(), bool_ty)
            .unwrap()
    );
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn complete_hol_theory_requires_exact_structural_coverage() {
    let bytes = b"(typ \"A\" (inst (alias nat))) (typ \"B\" (inst (alias nat)))";
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let first = DeclarationId::new(1, None).unwrap();
    let second = DeclarationId::new(2, None).unwrap();
    let foreign = DeclarationId::new(3, None).unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let truth = kernel.bool(bool_ty, true).unwrap();
    let falsity = kernel.bool(bool_ty, false).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();
    let mut constraints = std::collections::BTreeMap::from([(first, truth)]);

    assert!(matches!(
        close_hol_theory(&source, &mut kernel, bool_ty, &constraints),
        Err(HolTheoryError::Missing { id }) if id == second
    ));
    constraints.insert(second, falsity);
    constraints.insert(foreign, truth);
    assert!(matches!(
        close_hol_theory(&source, &mut kernel, bool_ty, &constraints),
        Err(HolTheoryError::Foreign { id }) if id == foreign
    ));
    constraints.remove(&foreign);
    let theory = close_hol_theory(&source, &mut kernel, bool_ty, &constraints).unwrap();

    assert_eq!(theory.constraints(), [(first, truth), (second, falsity)]);
    assert!(
        kernel
            .equivalent(kernel.classifier(theory.proposition()).unwrap(), bool_ty)
            .unwrap()
    );
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn complete_hol_theory_is_transactional_on_non_boolean_constraint() {
    let bytes = b"(typ \"A\" (inst (alias nat)))";
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let not_boolean = kernel.tm_fv(1, value).unwrap();
    let before = kernel.arena().len();

    assert!(matches!(
        close_hol_theory(
            &source,
            &mut kernel,
            bool_ty,
            &std::collections::BTreeMap::from([(
                DeclarationId::new(1, None).unwrap(),
                not_boolean,
            )]),
        ),
        Err(HolTheoryError::Kernel { .. })
    ));
    assert_eq!(kernel.arena().len(), before);
}

#[test]
#[allow(clippy::too_many_lines)] // Exercises all declaration dispatch paths and final coverage.
fn whole_document_lowering_closes_every_declaration_constraint() {
    let bytes = br#"(typ "T" (inst (alias nat)))
        (def "id" (exp "x" nat) nat
          (clause (exp (var "x")) (var "x")))
        (gram "G" nat
          (prod (exp "x" nat) (text "a") (var "x")))
        (rel "R" "R" nat
          (rule "base" (exp "x" nat) "R" (var "x") (if (bool true))))"#;
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let schema = declare_hol_schema(&source, &mut kernel, value, bool_ty).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(10_000, value).unwrap();
    let mut resolver = TestRelationalResolver {
        x,
        y: kernel.tm_fv(10_001, value).unwrap(),
        add: kernel.tm_fv(10_002, binary_ty).unwrap(),
        graph: kernel.tm_fv(10_003, graph_ty).unwrap(),
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };
    let theorem_count = kernel.thm().live_theorems().count();
    let document = relational_document(&mut kernel, &mut resolver, &source, &schema, &[x]).unwrap();

    assert_eq!(document.constraints().len(), source.declaration_count());
    assert_eq!(document.definitions().len(), 1);
    assert_eq!(
        document.theory().constraints().len(),
        source.declaration_count()
    );
    assert!(
        kernel
            .equivalent(
                kernel.classifier(document.theory().proposition()).unwrap(),
                bool_ty
            )
            .unwrap()
    );
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn least_closed_predicate_builds_direct_hol_definition() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let rule_value = kernel.tm_fv(50, value).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();

    let least = least_closed_predicate(&mut kernel, bool_ty, predicate_ty, |kernel, candidate| {
        let premise = kernel.bool(bool_ty, true)?;
        let rule = HolRule::new(vec![rule_value], vec![premise], vec![rule_value]);
        let closed = close_hol_rule(kernel, bool_ty, candidate, &rule)?;
        close_hol_rules(kernel, bool_ty, &[closed])
    })
    .unwrap();

    assert_eq!(least.predicate_ty, predicate_ty);
    assert_eq!(
        kernel.arena().tag(least.predicate),
        Some(Tag::Tm(TmTag::Lam))
    );
    let value_term = kernel.tm_fv(100, value).unwrap();
    let proposition = kernel.app(least.predicate, value_term).unwrap();
    assert!(
        kernel
            .equivalent(kernel.classifier(proposition).unwrap(), bool_ty)
            .unwrap()
    );
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn least_closed_predicate_is_transactional() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let before = kernel.arena().len();

    assert!(
        least_closed_predicate(&mut kernel, bool_ty, predicate_ty, |kernel, candidate| {
            kernel.app(candidate, candidate)
        })
        .is_err()
    );
    assert_eq!(kernel.arena().len(), before);
}

#[test]
fn least_closed_family_supports_mutual_rules() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let witness = kernel.tm_fv(40, value).unwrap();

    let family = least_closed_family(
        &mut kernel,
        bool_ty,
        &[predicate_ty, predicate_ty],
        |kernel, candidates| {
            let left_premise = kernel.app(candidates[1], witness)?;
            let right_premise = kernel.app(candidates[0], witness)?;
            let left = close_hol_rule(
                kernel,
                bool_ty,
                candidates[0],
                &HolRule::new(Vec::new(), vec![left_premise], vec![witness]),
            )?;
            let right = close_hol_rule(
                kernel,
                bool_ty,
                candidates[1],
                &HolRule::new(Vec::new(), vec![right_premise], vec![witness]),
            )?;
            close_hol_rules(kernel, bool_ty, &[left, right])
        },
    )
    .unwrap();

    assert_eq!(family.len(), 2);
    assert_ne!(family[0].candidate, family[1].candidate);
    assert_eq!(family[0].closure, family[1].closure);
    assert_eq!(
        kernel.arena().tag(family[0].predicate),
        Some(Tag::Tm(TmTag::Lam))
    );
    assert_eq!(
        kernel.arena().tag(family[1].predicate),
        Some(Tag::Tm(TmTag::Lam))
    );
}

#[test]
fn two_phase_least_family_exposes_candidates_transactionally() {
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let predicate_ty = kernel.ty_arr(value, bool_ty).unwrap();
    let witness = kernel.tm_fv(10, value).unwrap();
    let mut builder =
        begin_least_closed_family(&mut kernel, bool_ty, &[predicate_ty, predicate_ty]).unwrap();
    let closure = {
        let (staged, candidates) = builder.parts();
        let left = staged.app(candidates[0], witness).unwrap();
        let right = staged.app(candidates[1], witness).unwrap();
        staged
            .op2(covalence_logic_hol::builtin::Op2::And, left, right)
            .unwrap()
    };
    let family = builder.finish(closure).unwrap();

    assert_eq!(family.len(), 2);
    assert!(
        kernel
            .equivalent(
                kernel.classifier(family[0].predicate).unwrap(),
                predicate_ty
            )
            .unwrap()
    );
}

#[test]
fn generic_hol_schema_declares_every_wasm3_signature() {
    let source = Source::wasm3().unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();

    let schema = declare_hol_schema(&source, &mut kernel, value, bool_ty).unwrap();

    assert_eq!(schema.policy(), IndexErasure::ValuePredicate);
    assert_eq!(schema.value(), value);
    assert_eq!(schema.bool_ty(), bool_ty);
    assert_eq!(schema.len(), 980);
    assert!(!schema.is_empty());
    for declaration in source.declarations() {
        let target = schema.declaration(declaration.id()).unwrap();
        assert_eq!(target.kind(), declaration.kind());
        kernel.classifier(target.reference()).unwrap();
    }
    let x = kernel.tm_fv(10_000, value).unwrap();
    let y = kernel.tm_fv(10_001, value).unwrap();
    let result = kernel.tm_fv(10_002, value).unwrap();
    let min = schema
        .declaration(DeclarationId::new(6, None).unwrap())
        .unwrap()
        .reference();
    let min_at_x = kernel.app(min, x).unwrap();
    let min_at_y = kernel.app(min_at_x, y).unwrap();
    let min_graph = kernel.app(min_at_y, result).unwrap();
    assert!(
        kernel
            .equivalent(kernel.classifier(min_graph).unwrap(), bool_ty)
            .unwrap()
    );

    let n_membership = schema
        .declaration(DeclarationId::new(1, None).unwrap())
        .unwrap()
        .reference();
    let n_holds = kernel.app(n_membership, x).unwrap();
    assert!(
        kernel
            .equivalent(kernel.classifier(n_holds).unwrap(), bool_ty)
            .unwrap()
    );
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
#[ignore = "exhaustive audit; run explicitly in the release profile"]
#[allow(clippy::too_many_lines)] // Keeps one complete authority-boundary audit.
fn parameterized_lowering_covers_complete_pinned_wasm3_document() {
    let source = Source::wasm3().unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();

    let document = parameterized_document(&source, &mut kernel, value, bool_ty).unwrap();

    assert_eq!(
        document.semantics.constraints().len(),
        source.declaration_count()
    );
    assert_eq!(
        document.semantics.relations().len(),
        source
            .declarations()
            .iter()
            .filter(|declaration| declaration.kind() == IlKind::Relation)
            .count()
    );
    assert_eq!(
        document.semantics.definitions().len(),
        source
            .declarations()
            .iter()
            .filter(|declaration| declaration.kind() == IlKind::Definition)
            .count()
    );
    assert!(!document.interpretation.is_empty());
    assert!(!document.has_no_missing_interpretations());
    assert_eq!(
        document.grounding_obligations().len(),
        document.interpretation.len()
    );
    let kinds = document
        .grounding_obligations()
        .map(covalence_nucleus_spectec::InterpretationSymbol::kind)
        .collect::<std::collections::BTreeSet<_>>();
    for required in [
        InterpretationKind::Membership,
        InterpretationKind::Tuple,
        InterpretationKind::Variant,
        InterpretationKind::Struct,
        InterpretationKind::Expression,
        InterpretationKind::IteratedPremise,
    ] {
        assert!(
            kinds.contains(&required),
            "missing {required:?} in {kinds:?}"
        );
    }
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
    let [steps_id] = document.schema.named(IlKind::Relation, "Steps") else {
        panic!("expected one Steps relation")
    };
    let steps_definition = document.semantics.relations().get(steps_id).unwrap();
    assert_eq!(steps_definition.rules.len(), 2);
    assert_eq!(steps_definition.rule_schemas.len(), 2);
    assert!(!steps_definition.rule_schemas[0].binders.is_empty());
    assert!(!steps_definition.rule_schemas[0].premises.is_empty());
    assert_eq!(steps_definition.rule_schemas[0].binders.len(), 4);
    assert_eq!(steps_definition.rule_schemas[0].premises.len(), 2);
    for &rule in steps_definition.rules.iter() {
        assert_eq!(kernel.classifier(rule).unwrap(), bool_ty);
    }
    assert_eq!(
        kernel.classifier(steps_definition.least.closure).unwrap(),
        bool_ty
    );
    assert_eq!(
        kernel
            .classifier(steps_definition.least.characterization)
            .unwrap(),
        bool_ty
    );
    let steps_constraint = document
        .semantics
        .theory()
        .derive_constraint(&mut kernel, *steps_id)
        .unwrap();
    document
        .evidence_scope(&[])
        .check(&kernel, steps_constraint)
        .unwrap();
    let execution = spectec_execution(&mut kernel, &document).unwrap();
    let rule_argument = steps_definition.rule_schemas[0].conclusion[0];
    let partial_pair = kernel
        .arena()
        .children(rule_argument)
        .unwrap()
        .next()
        .unwrap();
    let exact_pair = kernel
        .arena()
        .children(partial_pair)
        .unwrap()
        .next()
        .unwrap();
    assert_eq!(execution.pair, exact_pair);
    let state_name = kernel
        .fresh_name(&[value, bool_ty, steps_constraint.proposition])
        .unwrap();
    let state = kernel.tm_fv(state_name, value).unwrap();
    let builder = SpecTecValueBuilder::new(&document);
    let instructions = builder.list(&mut kernel, &[]).unwrap();
    let configuration = builder
        .case_fields(&mut kernel, "%;%", &[state, instructions])
        .unwrap();
    let step_pair = execution
        .step_pair(&mut kernel, configuration, configuration)
        .unwrap();
    let reflexive_witnesses = [state, instructions, configuration, configuration];
    let reflexive_rule = steps_definition
        .specialize_rule(&mut kernel, 0, &reflexive_witnesses)
        .unwrap();
    assert_eq!(
        kernel.classifier(reflexive_rule.proposition).unwrap(),
        bool_ty
    );
    let reflexive_obligations = steps_definition
        .rule_obligations(&mut kernel, 0, &reflexive_witnesses)
        .unwrap();
    let (reflexive_condition_facts, reflexive_remaining) =
        elementary_condition_facts(&mut kernel, &reflexive_obligations);
    let reflexive_premises = steps_definition
        .prove_rule_obligations(
            &mut kernel,
            bool_ty,
            0,
            &reflexive_witnesses,
            &reflexive_condition_facts,
        )
        .unwrap();
    let reflexive_candidate = steps_definition
        .apply_specialized_rule(&mut kernel, reflexive_rule, reflexive_premises.theorem)
        .unwrap();
    document
        .evidence_scope(
            &std::iter::once(steps_definition.least.closure)
                .chain(reflexive_remaining.iter().copied())
                .collect::<Vec<_>>(),
        )
        .check(&kernel, reflexive_candidate)
        .unwrap();
    let reflexive_steps = steps_definition
        .close_rule_instance(&mut kernel, reflexive_candidate, steps_constraint.theorem)
        .unwrap();
    document
        .evidence_scope(&reflexive_remaining)
        .check(&kernel, reflexive_steps)
        .unwrap();
    let reflexive_pair = kernel
        .arena()
        .children(reflexive_steps.proposition)
        .unwrap()
        .nth(1)
        .unwrap();
    let mut pair_children = kernel.arena().children(reflexive_pair).unwrap();
    let reflexive_partial_pair = pair_children.next().unwrap();
    let reflexive_after = pair_children.next().unwrap();
    drop(pair_children);
    let reflexive_before = kernel
        .arena()
        .children(reflexive_partial_pair)
        .unwrap()
        .nth(1)
        .unwrap();
    let curried_reflexive_steps = execution
        .curry_steps_fact(
            &mut kernel,
            reflexive_before,
            reflexive_after,
            reflexive_steps,
        )
        .unwrap();
    document
        .evidence_scope(&reflexive_remaining)
        .check(&kernel, curried_reflexive_steps)
        .unwrap();
    let specialized_steps = document
        .semantics
        .theory()
        .specialize_constraint(&mut kernel, *steps_id, &[step_pair])
        .unwrap();
    document
        .evidence_scope(&[])
        .check(&kernel, specialized_steps)
        .unwrap();
    assert_eq!(
        kernel.classifier(specialized_steps.proposition).unwrap(),
        bool_ty
    );
    let wrong_argument = kernel.bool(bool_ty, false).unwrap();
    let before = kernel.arena().clone();
    assert!(
        document
            .semantics
            .theory()
            .specialize_constraint(&mut kernel, *steps_id, &[wrong_argument])
            .is_err()
    );
    assert_eq!(kernel.arena(), &before);
    assert!(kernel.thm().live_theorems().count() > theorem_count);
    let empty_module = empty_wasm_module(&mut kernel, &document).unwrap();
    assert_eq!(kernel.classifier(empty_module).unwrap(), value);
    let name_base = kernel
        .fresh_name(&[value, bool_ty, empty_module, execution.steps])
        .unwrap();
    let import_module = kernel.tm_fv(name_base, value).unwrap();
    let assert_name = kernel.tm_fv(name_base + 1, value).unwrap();
    let export_name = kernel.tm_fv(name_base + 2, value).unwrap();
    let forwarding = forwarding_wasm_module(
        &mut kernel,
        &document,
        import_module,
        assert_name,
        export_name,
    )
    .unwrap();
    assert_eq!(kernel.classifier(forwarding).unwrap(), value);
    assert_eq!(execution.state_ty, value);
    assert_eq!(execution.bool_ty, bool_ty);
    let steps_classifier = kernel.classifier(execution.steps).unwrap();
    assert_eq!(steps_classifier, execution.steps_ty);

    // End-to-end theorem assembly over the two actual structural module terms.
    // These graph propositions are explicit grounding premises; the test does
    // not turn the Wasmtime checks below into theorem authority.
    let binary_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let export_view = ExportedFunctionView {
        value_ty: value,
        bool_ty,
        module_instance: execution.moduleinst,
        exports: builder
            .struct_field_graph(
                &mut kernel,
                &[
                    "TYPES", "TAGS", "GLOBALS", "MEMS", "TABLES", "FUNCS", "DATAS", "ELEMS",
                    "EXPORTS",
                ],
                "EXPORTS",
            )
            .unwrap(),
        member: builder.membership_predicate().unwrap(),
        function_address: builder
            .struct_case_field_graph(&mut kernel, &["NAME", "ADDR"], "ADDR", "FUNC%")
            .unwrap(),
    };
    let exported = export_view.predicate(&mut kernel).unwrap();
    let [instantiate_id] = document.schema.named(IlKind::Definition, "instantiate") else {
        panic!("expected one $instantiate definition")
    };
    let instantiate_definition = document
        .semantics
        .definitions()
        .get(instantiate_id)
        .unwrap();
    let [allocmodule_id] = document.schema.named(IlKind::Definition, "allocmodule") else {
        panic!("expected one $allocmodule definition")
    };
    let allocmodule_definition = document
        .semantics
        .definitions()
        .get(allocmodule_id)
        .unwrap();
    let allocmodule_predicate = document
        .schema
        .declaration(*allocmodule_id)
        .unwrap()
        .reference();
    let [store_id] = document.schema.named(IlKind::Definition, "store") else {
        panic!("expected one $store definition")
    };
    let store_definition = document.semantics.definitions().get(store_id).unwrap();
    let [moduleinst_id] = document.schema.named(IlKind::Definition, "moduleinst") else {
        panic!("expected one $moduleinst definition")
    };
    let moduleinst_definition = document.semantics.definitions().get(moduleinst_id).unwrap();
    let [invoke_id] = document.schema.named(IlKind::Definition, "invoke") else {
        panic!("expected one $invoke definition")
    };
    let invoke_definition = document.semantics.definitions().get(invoke_id).unwrap();
    let witnesses = (name_base + 5..name_base + 14)
        .map(|name| kernel.tm_fv(name, value).unwrap())
        .collect::<Vec<_>>();
    let instantiate_binders = &instantiate_definition.case_artifacts[0].production_binders;
    let instantiate_name = kernel
        .fresh_name(&[
            forwarding,
            witnesses[1],
            witnesses[2],
            instantiate_definition.equation,
        ])
        .unwrap();
    let instantiate_witnesses = instantiate_binders
        .iter()
        .enumerate()
        .map(|(offset, &binder)| {
            let name = instantiate_name + u64::try_from(offset).unwrap();
            let classifier = kernel.classifier(binder).unwrap();
            kernel.tm_fv(name, classifier).unwrap()
        })
        .collect::<Vec<_>>();
    let instantiation_start = instantiate_definition
        .production_result(
            &mut kernel,
            0,
            &[witnesses[1], forwarding, witnesses[2]],
            &instantiate_witnesses,
        )
        .unwrap();
    let initialized = builder
        .case_fields(&mut kernel, "%;%", &[witnesses[7], witnesses[4]])
        .unwrap();
    let invoke_binders = &invoke_definition.case_artifacts[0].production_binders;
    let invoke_name = kernel
        .fresh_name(&[
            forwarding,
            witnesses[5],
            witnesses[6],
            witnesses[7],
            invoke_definition.equation,
        ])
        .unwrap();
    let invoke_witnesses = invoke_binders
        .iter()
        .enumerate()
        .map(|(offset, &binder)| {
            let name = invoke_name + u64::try_from(offset).unwrap();
            let classifier = kernel.classifier(binder).unwrap();
            kernel.tm_fv(name, classifier).unwrap()
        })
        .collect::<Vec<_>>();
    let initial = invoke_definition
        .production_result(
            &mut kernel,
            0,
            &[witnesses[7], witnesses[5], witnesses[6]],
            &invoke_witnesses,
        )
        .unwrap();
    let start = AdmissibleStartWitness {
        program: forwarding,
        initial,
        store: witnesses[1],
        externs: witnesses[2],
        instantiation_start,
        initialized,
        function: witnesses[5],
        arguments: witnesses[6],
        initialized_store: witnesses[7],
    };
    let obligations = execution
        .admissible_start_obligations(&mut kernel, exported, start)
        .unwrap();
    let mut obligation_facts = obligations.map(|proposition| {
        kernel
            .identity(covalence_logic_hol::Lit::positive(proposition.get()))
            .unwrap()
    });
    let function_address = builder.case(&mut kernel, "FUNC%", start.function).unwrap();
    let runtime_export = builder
        .struct_value(
            &mut kernel,
            &["NAME", "ADDR"],
            &[export_name, function_address],
        )
        .unwrap();
    let runtime_exports = builder.list(&mut kernel, &[runtime_export]).unwrap();
    let export_membership = builder
        .list_membership_law(&mut kernel, &[runtime_export])
        .unwrap();
    covalence_logic_hol_derived::join_same_syntax(
        &mut kernel,
        export_membership.list(),
        runtime_exports,
    )
    .unwrap();
    let export_membership_fact = kernel
        .identity(covalence_logic_hol::Lit::positive(
            export_membership.proposition().get(),
        ))
        .unwrap();
    let contains_export = builder
        .sequence_algebra(&mut kernel)
        .unwrap()
        .prove_member_at(&mut kernel, &export_membership, export_membership_fact, 0)
        .unwrap();
    document
        .evidence_scope(&[export_membership.proposition()])
        .check(&kernel, contains_export)
        .unwrap();
    let function_address_fact = builder
        .prove_struct_case_field(
            &mut kernel,
            &["NAME", "ADDR"],
            &[export_name, function_address],
            "ADDR",
            "FUNC%",
            start.function,
        )
        .unwrap();
    document
        .evidence_scope(&[])
        .check(&kernel, function_address_fact.evidence())
        .unwrap();
    let moduleinst_witnesses = moduleinst_definition
        .match_production_witnesses(&mut kernel, 0, &[start.instantiation_start])
        .unwrap()
        .unwrap();
    let module_instance = moduleinst_definition
        .production_result(
            &mut kernel,
            0,
            &[start.instantiation_start],
            &moduleinst_witnesses,
        )
        .unwrap();
    let moduleinst_instance = moduleinst_definition
        .specialize(
            &mut kernel,
            bool_ty,
            &[start.instantiation_start],
            module_instance,
        )
        .unwrap();
    assert_eq!(moduleinst_instance.cases.len(), 1);
    let moduleinst_conditions = moduleinst_instance
        .production_obligations(&mut kernel, 0, &moduleinst_witnesses)
        .unwrap();
    let (moduleinst_condition_facts, moduleinst_remaining) =
        elementary_condition_facts(&mut kernel, &moduleinst_conditions);
    let moduleinst_branch = moduleinst_instance
        .prove_production(
            &mut kernel,
            bool_ty,
            0,
            &moduleinst_witnesses,
            &moduleinst_condition_facts,
        )
        .unwrap();
    let moduleinst_body = moduleinst_instance
        .prove_body_case(&mut kernel, bool_ty, 0, moduleinst_branch.theorem)
        .unwrap();
    let moduleinst_fact = document
        .semantics
        .theory()
        .prove_specialized_from_body(
            &mut kernel,
            *moduleinst_id,
            &[start.instantiation_start, module_instance],
            moduleinst_body.theorem,
        )
        .unwrap();
    let export_witness = ExportedFunctionWitness {
        configuration: start.instantiation_start,
        function: start.function,
        module_instance,
        exports: runtime_exports,
        export_instance: runtime_export,
    };
    let exports_graph = kernel
        .app(export_view.exports, module_instance)
        .and_then(|partial| kernel.app(partial, runtime_exports))
        .unwrap();
    let export_graphs = [exports_graph];
    let export_graph_facts = export_graphs.map(|proposition| {
        kernel
            .identity(covalence_logic_hol::Lit::positive(proposition.get()))
            .unwrap()
    });
    obligation_facts[2] = export_view
        .prove_exported_function(
            &mut kernel,
            export_witness,
            ExportedFunctionFacts {
                module_instance: moduleinst_fact.theorem,
                exports: export_graph_facts[0],
                member: contains_export.theorem,
                function_address: function_address_fact.evidence().theorem,
            },
        )
        .unwrap()
        .theorem;
    let instantiate_instance = instantiate_definition
        .specialize(
            &mut kernel,
            bool_ty,
            &[start.store, start.program, start.externs],
            start.instantiation_start,
        )
        .unwrap();
    assert_eq!(instantiate_instance.cases.len(), 1);
    let instantiate_conditions = instantiate_instance
        .production_obligations(&mut kernel, 0, &instantiate_witnesses)
        .unwrap();
    let allocmodule_calls = instantiate_conditions
        .iter()
        .filter_map(|&condition| {
            allocmodule_definition.match_application(&kernel, allocmodule_predicate, condition)
        })
        .collect::<Vec<_>>();
    assert_eq!(allocmodule_calls.len(), 1);
    assert_eq!(allocmodule_calls[0].inputs().len(), 6);
    let (instantiate_condition_facts, instantiate_remaining) =
        elementary_condition_facts(&mut kernel, &instantiate_conditions);
    assert!(instantiate_remaining.len() < instantiate_conditions.len());
    let instantiate_branch = instantiate_instance
        .prove_production(
            &mut kernel,
            bool_ty,
            0,
            &instantiate_witnesses,
            &instantiate_condition_facts,
        )
        .unwrap();
    let instantiate_body = instantiate_instance
        .prove_body_case(&mut kernel, bool_ty, 0, instantiate_branch.theorem)
        .unwrap();
    obligation_facts[0] = document
        .semantics
        .theory()
        .prove_specialized_from_body(
            &mut kernel,
            *instantiate_id,
            &[
                start.store,
                start.program,
                start.externs,
                start.instantiation_start,
            ],
            instantiate_body.theorem,
        )
        .unwrap()
        .theorem;
    let initialization_before_equality = kernel
        .eq(bool_ty, reflexive_before, start.instantiation_start)
        .unwrap();
    let initialization_before_equality_fact = kernel
        .identity(covalence_logic_hol::Lit::positive(
            initialization_before_equality.get(),
        ))
        .unwrap();
    let initialization_after_equality = kernel
        .eq(bool_ty, reflexive_after, start.initialized)
        .unwrap();
    let initialization_after_equality_fact = kernel
        .identity(covalence_logic_hol::Lit::positive(
            initialization_after_equality.get(),
        ))
        .unwrap();
    let initialization_at_start = execution
        .transport_steps_before(
            &mut kernel,
            reflexive_before,
            start.instantiation_start,
            reflexive_after,
            curried_reflexive_steps,
            initialization_before_equality_fact,
        )
        .unwrap();
    obligation_facts[1] = execution
        .transport_steps_after(
            &mut kernel,
            start.instantiation_start,
            reflexive_after,
            start.initialized,
            initialization_at_start,
            initialization_after_equality_fact,
        )
        .unwrap()
        .theorem;
    let store_instance = store_definition
        .specialize(
            &mut kernel,
            bool_ty,
            &[start.initialized],
            start.initialized_store,
        )
        .unwrap();
    assert_eq!(store_instance.cases.len(), 1);
    let store_witnesses = store_definition
        .match_production_witnesses(&mut kernel, 0, &[start.initialized])
        .unwrap()
        .unwrap();
    let store_conditions = store_instance
        .production_obligations(&mut kernel, 0, &store_witnesses)
        .unwrap();
    let (store_condition_facts, store_remaining) =
        elementary_condition_facts(&mut kernel, &store_conditions);
    assert!(store_remaining.len() < store_conditions.len());
    let store_branch = store_instance
        .prove_production(
            &mut kernel,
            bool_ty,
            0,
            &store_witnesses,
            &store_condition_facts,
        )
        .unwrap();
    let store_body = store_instance
        .prove_body_case(&mut kernel, bool_ty, 0, store_branch.theorem)
        .unwrap();
    obligation_facts[3] = document
        .semantics
        .theory()
        .prove_specialized_from_body(
            &mut kernel,
            *store_id,
            &[start.initialized, start.initialized_store],
            store_body.theorem,
        )
        .unwrap()
        .theorem;

    let invoke_instance = invoke_definition
        .specialize(
            &mut kernel,
            bool_ty,
            &[start.initialized_store, start.function, start.arguments],
            start.initial,
        )
        .unwrap();
    assert_eq!(invoke_instance.cases.len(), 1);
    let invoke_conditions = invoke_instance
        .production_obligations(&mut kernel, 0, &invoke_witnesses)
        .unwrap();
    let (invoke_condition_facts, invoke_remaining) =
        elementary_condition_facts(&mut kernel, &invoke_conditions);
    assert!(invoke_remaining.len() < invoke_conditions.len());
    let invoke_branch = invoke_instance
        .prove_production(
            &mut kernel,
            bool_ty,
            0,
            &invoke_witnesses,
            &invoke_condition_facts,
        )
        .unwrap();
    let invoke_body = invoke_instance
        .prove_body_case(&mut kernel, bool_ty, 0, invoke_branch.theorem)
        .unwrap();
    obligation_facts[4] = document
        .semantics
        .theory()
        .prove_specialized_from_body(
            &mut kernel,
            *invoke_id,
            &[
                start.initialized_store,
                start.function,
                start.arguments,
                start.initial,
            ],
            invoke_body.theorem,
        )
        .unwrap()
        .theorem;
    let host_name = kernel
        .fresh_name(&[
            start.initial,
            start.initialized_store,
            start.arguments,
            invoke_definition.equation,
        ])
        .unwrap();
    let host_configuration = kernel.tm_fv(host_name, value).unwrap();
    let host_function = kernel.tm_fv(host_name + 1, value).unwrap();
    let expected_host_configuration = invoke_definition
        .production_result(
            &mut kernel,
            0,
            &[start.initialized_store, host_function, start.arguments],
            &invoke_witnesses,
        )
        .unwrap();
    let host_body = kernel
        .eq(bool_ty, host_configuration, expected_host_configuration)
        .unwrap();
    let host_by_function = kernel
        .lam_at(binary_tail, host_function, host_body)
        .unwrap();
    let host_call = kernel
        .lam_at(binary_ty, host_configuration, host_by_function)
        .unwrap();
    let starts = execution
        .prove_admissible_start(
            &mut kernel,
            exported,
            start,
            AdmissibleStartFacts {
                instantiated: obligation_facts[0],
                initialized: obligation_facts[1],
                exported: obligation_facts[2],
                store: obligation_facts[3],
                invoked: obligation_facts[4],
            },
        )
        .unwrap();
    let reachability = execution
        .assertion_reachability(&mut kernel, exported, host_call)
        .unwrap();
    let final_state = start.initial;
    let final_before_equality = kernel.eq(bool_ty, reflexive_before, start.initial).unwrap();
    let final_before_equality_fact = kernel
        .identity(covalence_logic_hol::Lit::positive(
            final_before_equality.get(),
        ))
        .unwrap();
    let final_after_equality = kernel.eq(bool_ty, reflexive_after, final_state).unwrap();
    let final_after_equality_fact = kernel
        .identity(covalence_logic_hol::Lit::positive(
            final_after_equality.get(),
        ))
        .unwrap();
    let final_at_initial = execution
        .transport_steps_before(
            &mut kernel,
            reflexive_before,
            start.initial,
            reflexive_after,
            curried_reflexive_steps,
            final_before_equality_fact,
        )
        .unwrap();
    let steps_fact = execution
        .transport_steps_after(
            &mut kernel,
            start.initial,
            reflexive_after,
            final_state,
            final_at_initial,
            final_after_equality_fact,
        )
        .unwrap();
    let calls_fact =
        prove_reflexive_binary_application(&mut kernel, host_call, final_state, start.function)
            .unwrap();
    let true_calls = reachability
        .prove_calls_assert(
            &mut kernel,
            forwarding,
            start.function,
            start.initial,
            final_state,
            starts.theorem,
            steps_fact.theorem,
            calls_fact.theorem,
        )
        .unwrap();

    let false_export_lists = export_view
        .program_export_lists_equal(&mut kernel, execution, empty_module, instructions)
        .unwrap();
    let empty_membership = builder.list_membership_law(&mut kernel, &[]).unwrap();
    assert_eq!(empty_membership.list(), instructions);
    let empty_membership_fact = kernel
        .identity(covalence_logic_hol::Lit::positive(
            empty_membership.proposition().get(),
        ))
        .unwrap();
    let empty_has_no_members = builder
        .sequence_algebra(&mut kernel)
        .unwrap()
        .prove_empty_has_no_members(&mut kernel, &empty_membership, empty_membership_fact)
        .unwrap();
    let false_export_lists_fact = kernel
        .identity(covalence_logic_hol::Lit::positive(false_export_lists.get()))
        .unwrap();
    let no_export_entries = export_view
        .prove_no_export_entries_from_list_invariant(
            &mut kernel,
            execution,
            empty_module,
            instructions,
            false_export_lists_fact,
            empty_has_no_members.theorem,
        )
        .unwrap();
    let cannot_export = export_view
        .prove_program_cannot_export_from_no_entries(
            &mut kernel,
            execution,
            empty_module,
            no_export_entries.theorem,
        )
        .unwrap();
    let no_false_start = execution
        .prove_no_admissible_start_from_no_export(
            &mut kernel,
            exported,
            empty_module,
            cannot_export.theorem,
        )
        .unwrap();
    let false_does_not_call = reachability
        .prove_never_calls_assert_from_no_start(
            &mut kernel,
            empty_module,
            start.function,
            no_false_start.theorem,
        )
        .unwrap();
    let observation = reachability
        .closed_program_observation(&mut kernel, start.function)
        .unwrap();
    let true_not_false = observation
        .prove_distinct(
            &mut kernel,
            forwarding,
            empty_module,
            true_calls.theorem,
            false_does_not_call.theorem,
        )
        .unwrap();
    let mut grounding = export_graphs.to_vec();
    grounding.extend(reflexive_remaining);
    grounding.extend(moduleinst_remaining);
    grounding.extend(instantiate_remaining);
    grounding.extend(store_remaining);
    grounding.extend(invoke_remaining);
    grounding.extend([
        initialization_before_equality,
        initialization_after_equality,
        final_before_equality,
        final_after_equality,
        false_export_lists,
        export_membership.proposition(),
        empty_membership.proposition(),
    ]);
    document
        .evidence_scope(&grounding)
        .check(&kernel, true_not_false)
        .unwrap();
    let closed_distinction = true_not_false.close_premises(&mut kernel).unwrap();
    assert!(
        kernel
            .thm()
            .get(closed_distinction.theorem)
            .unwrap()
            .lhs
            .rows()
            .next()
            .is_none()
    );
    assert_eq!(
        kernel.classifier(closed_distinction.proposition).unwrap(),
        bool_ty
    );
}

#[test]
fn parameterized_relations_encode_consecutive_otherwise_fallback() {
    let bytes = br#"(rel "R" "R" nat
        (rule "base" (exp "x" nat) "R" (var "x"))
        (rule "fallback" (exp "x" nat) "R" (var "x") else))"#;
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let theorem_count = kernel.thm().live_theorems().count();

    let document = parameterized_document(&source, &mut kernel, value, bool_ty).unwrap();

    assert_eq!(document.semantics.constraints().len(), 1);
    assert_eq!(kernel.thm().live_theorems().count(), theorem_count);
}

#[test]
fn immutable_interpretations_discharge_checked_grounding_obligations() {
    let bytes = b"(def \"zero\" nat (clause (num (nat 0))))";
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let parameterized = parameterized_document(&source, &mut kernel, value, bool_ty).unwrap();
    let supplied = parameterized
        .grounding_obligations()
        .next()
        .unwrap()
        .clone();
    assert!(parameterized.operations().len() >= parameterized.grounding_obligations().len());
    let provided =
        std::collections::BTreeMap::from([(supplied.signature.clone(), supplied.reference)]);

    let interpreted =
        parameterized_document_with(&source, &mut kernel, value, bool_ty, &provided).unwrap();

    assert!(
        interpreted
            .grounding_obligations()
            .all(|obligation| obligation.signature != supplied.signature)
    );
    assert!(interpreted.operations().any(|operation| {
        operation.signature == supplied.signature && operation.reference == supplied.reference
    }));

    let wrong = kernel.bool(bool_ty, true).unwrap();
    let incompatible = std::collections::BTreeMap::from([(supplied.signature, wrong)]);
    let before = kernel.arena().clone();
    assert!(
        parameterized_document_with(&source, &mut kernel, value, bool_ty, &incompatible).is_err()
    );
    assert_eq!(kernel.arena(), &before);
}

#[test]
#[allow(clippy::too_many_lines)]
fn empty_module_uses_exact_expression_constructor_vocabulary() {
    let bytes = br#"(def "empty" nat
        (clause (case "MODULE%%%%%%%%%%%" (tup
            (list) (list) (list) (list) (list) (list)
            (list) (list) (list) (opt) (list)))))"#;
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let document = parameterized_document(&source, &mut kernel, value, bool_ty).unwrap();
    let declaration = source.declarations()[0].id();
    let evidence = document
        .semantics
        .theory()
        .derive_constraint(&mut kernel, declaration)
        .unwrap();
    document
        .evidence_scope(&[])
        .check(&kernel, evidence)
        .unwrap();
    let before = kernel.arena().clone();
    let foreign = DeclarationId::new(999, None).unwrap();
    assert!(
        document
            .semantics
            .theory()
            .derive_constraint(&mut kernel, foreign)
            .is_err()
    );
    assert_eq!(kernel.arena(), &before);

    let builder = SpecTecValueBuilder::new(&document);
    let empty = builder.list(&mut kernel, &[]).unwrap();
    let before = kernel.arena().clone();
    assert!(builder.list(&mut kernel, &[empty]).is_err());
    assert_eq!(kernel.arena(), &before);

    let module = empty_wasm_module(&mut kernel, &document).unwrap();

    let empty_list_constructor = builder
        .structural_constructor(&mut kernel, "expression:List", 0)
        .unwrap();
    let module_constructor = builder
        .structural_constructor(&mut kernel, "expression:Case(\"MODULE%%%%%%%%%%%\")", 1)
        .unwrap();
    let constructor_laws = builder
        .constructor_laws_for(&mut kernel, &[module])
        .unwrap();
    assert!(
        constructor_laws
            .constructors()
            .contains(&empty_list_constructor)
    );
    assert!(
        constructor_laws
            .constructors()
            .contains(&module_constructor)
    );
    let constructor_count = constructor_laws.constructors().len();
    assert_eq!(constructor_count, 4);
    assert_eq!(
        constructor_laws.propositions().len(),
        constructor_count * (constructor_count + 1) / 2
    );
    assert!(
        constructor_laws
            .propositions()
            .iter()
            .all(|&law| kernel.classifier(law).unwrap() == bool_ty)
    );
    let non_value = kernel.bool(bool_ty, true).unwrap();
    let before = kernel.arena().clone();
    assert!(
        builder
            .constructor_laws_for(&mut kernel, &[non_value])
            .is_err()
    );
    assert_eq!(kernel.arena(), &before);

    assert_eq!(kernel.classifier(module).unwrap(), value);
    let module_fields = builder
        .match_case_fields(&kernel, "MODULE%%%%%%%%%%%", 11, module)
        .unwrap()
        .unwrap();
    assert_eq!(module_fields.len(), 11);
    assert_eq!(module_fields[10], empty);
    let before = kernel.arena().clone();
    assert!(
        builder
            .match_case_fields(&kernel, "MODULE%%%%%%%%%%%", 11, empty)
            .unwrap()
            .is_none()
    );
    assert_eq!(kernel.arena(), &before);
    let specialized = document
        .semantics
        .theory()
        .specialize_constraint(&mut kernel, declaration, &[module])
        .unwrap();
    let body = kernel
        .arena()
        .children(specialized.proposition)
        .unwrap()
        .nth(2)
        .unwrap();
    let body_fact = kernel
        .identity(covalence_logic_hol::Lit::positive(body.get()))
        .unwrap();
    let graph = document
        .semantics
        .theory()
        .prove_specialized_from_body(&mut kernel, declaration, &[module], body_fact)
        .unwrap();
    document
        .evidence_scope(&[body])
        .check(&kernel, graph)
        .unwrap();
    let unfolded = document
        .semantics
        .theory()
        .prove_body_from_specialized(&mut kernel, declaration, &[module], graph.theorem)
        .unwrap();
    document
        .evidence_scope(&[body])
        .check(&kernel, unfolded)
        .unwrap();
    let definition = document.semantics.definitions().get(&declaration).unwrap();
    let instance = definition
        .specialize(&mut kernel, bool_ty, &[], module)
        .unwrap();
    let before = kernel.arena().clone();
    assert!(
        instance
            .prove_only_production_from_body(&mut kernel, bool_ty, graph.theorem)
            .is_err()
    );
    assert_eq!(kernel.arena(), &before);
    let production = instance
        .prove_only_production_from_body(&mut kernel, bool_ty, unfolded.theorem)
        .unwrap();
    let opened = instance
        .open_production(&mut kernel, 0, production.theorem)
        .unwrap();
    assert_eq!(opened.conditions.len(), opened.facts.len());
    assert!(!opened.conditions.is_empty());
    for (&condition, &fact) in opened.conditions.iter().zip(&opened.facts) {
        document
            .evidence_scope(&[body])
            .check(
                &kernel,
                covalence_nucleus_spectec::Evidence {
                    proposition: condition,
                    theorem: fact,
                    holds: true,
                },
            )
            .unwrap();
    }
    let before = kernel.arena().clone();
    assert!(
        document
            .semantics
            .theory()
            .prove_body_from_specialized(&mut kernel, declaration, &[module], body_fact)
            .is_err()
    );
    assert_eq!(kernel.arena(), &before);
}

#[test]
fn empty_module_agrees_with_wasmtime_observation() {
    use covalence_lib_wasm::wasmtime::{Engine, Linker, Module, Store};

    // Canonical binary encoding of `(module)`. These bytes are deliberately
    // only interpreter-test input: they do not become HOL evidence.
    let bytes = b"\0asm\x01\0\0\0";
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    assert_eq!(module.imports().count(), 0);
    assert_eq!(module.exports().count(), 0);

    let mut store = Store::new(&engine, ());
    let linker = Linker::new(&engine);
    let instance = linker.instantiate(&mut store, &module).unwrap();
    assert_eq!(instance.exports(&mut store).count(), 0);
}

#[test]
fn forwarding_module_calls_assert_in_wasmtime() {
    use covalence_lib_wasm::wasmtime::{Caller, Engine, Func, Linker, Module, Store};

    // `(module (type (func)) (import "env" "assert" (func (type 0)))
    //          (export "run" (func 0)))`.
    let bytes = [
        0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, 0x01, 0x04, 0x01, 0x60, 0x00, 0x00, 0x02,
        0x0e, 0x01, 0x03, b'e', b'n', b'v', 0x06, b'a', b's', b's', b'e', b'r', b't', 0x00, 0x00,
        0x07, 0x07, 0x01, 0x03, b'r', b'u', b'n', 0x00, 0x00,
    ];
    let engine = Engine::default();
    let module = Module::new(&engine, bytes).unwrap();
    let mut store = Store::new(&engine, false);
    let mut linker = Linker::new(&engine);
    let assert = Func::wrap(&mut store, |mut caller: Caller<'_, bool>| {
        *caller.data_mut() = true;
    });
    linker.define(&mut store, "env", "assert", assert).unwrap();
    let instance = linker.instantiate(&mut store, &module).unwrap();
    let run = instance
        .get_typed_func::<(), ()>(&mut store, "run")
        .unwrap();

    assert!(!*store.data());
    run.call(&mut store, ()).unwrap();
    assert!(*store.data());
}

#[test]
fn pinned_otherwise_chains_do_not_negate_recursive_candidates() {
    let source = Source::wasm3().unwrap();
    for root in source.il().roots() {
        let family = source
            .il()
            .root_declarations(root)
            .iter()
            .filter(|declaration| declaration.kind() == IlKind::Relation)
            .map(covalence_data_spectec::IlDeclaration::name)
            .collect::<std::collections::BTreeSet<_>>();
        for declaration in source.il().root_declarations(root) {
            if declaration.kind() != IlKind::Relation {
                continue;
            }
            let schema = source.il().schema(declaration.id()).unwrap().unwrap();
            let covalence_data_spectec::IlDeclarationBody::Relation { rules, .. } = schema.body()
            else {
                unreachable!()
            };
            let rules = rules
                .iter()
                .map(IlRuleSchema::decode)
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            let mut chain = Vec::new();
            for rule in &rules {
                let otherwise = rule.premises().iter().any(premise_has_otherwise);
                if otherwise {
                    assert!(chain.iter().all(|earlier: &&IlRuleSchema<'_>| {
                        earlier
                            .premises()
                            .iter()
                            .all(|premise| !premise_mentions_relation(premise, &family))
                    }));
                } else {
                    chain.clear();
                }
                chain.push(rule);
            }
        }
    }
}

fn premise_has_otherwise(premise: &IlPremise<'_>) -> bool {
    match premise {
        IlPremise::Otherwise => true,
        IlPremise::Iterated { premise, .. } => premise_has_otherwise(premise),
        IlPremise::Rule(rule) => rule.premises().iter().any(premise_has_otherwise),
        IlPremise::If(_) | IlPremise::Let { .. } => false,
    }
}

fn premise_mentions_relation(
    premise: &IlPremise<'_>,
    family: &std::collections::BTreeSet<&str>,
) -> bool {
    match premise {
        IlPremise::Rule(rule) => {
            family.contains(rule.name())
                || rule
                    .premises()
                    .iter()
                    .any(|premise| premise_mentions_relation(premise, family))
        }
        IlPremise::Iterated { premise, .. } => premise_mentions_relation(premise, family),
        IlPremise::If(_) | IlPremise::Let { .. } | IlPremise::Otherwise => false,
    }
}

#[test]
fn generic_hol_schema_preserves_kind_qualified_duplicate_names() {
    let bytes = br#"(typ "same" (inst (alias nat)))
        (typ "same" (inst (alias nat)))
        (rel "same" "same" nat
          (rule "base" (exp "x" nat) "same" (var "x")))"#;
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();

    let schema = declare_hol_schema(&source, &mut kernel, value, bool_ty).unwrap();

    assert_eq!(
        schema.named(IlKind::Type, "same"),
        [
            DeclarationId::new(1, None).unwrap(),
            DeclarationId::new(2, None).unwrap(),
        ]
    );
    assert_eq!(
        schema.named(IlKind::Relation, "same"),
        [DeclarationId::new(3, None).unwrap()]
    );
    assert!(schema.named(IlKind::Definition, "same").is_empty());
}

#[test]
fn exact_alias_type_declaration_lowers_to_membership_equation() {
    let bytes = b"(typ \"T\" (inst (alias nat)))";
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let schema = declare_hol_schema(&source, &mut kernel, value, bool_ty).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(10_000, value).unwrap();
    let mut resolver = TestRelationalResolver {
        x,
        y: kernel.tm_fv(10_001, value).unwrap(),
        add: kernel.tm_fv(10_002, binary_ty).unwrap(),
        graph: kernel.tm_fv(10_003, graph_ty).unwrap(),
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };
    let definition = relational_type_declaration(
        &mut kernel,
        &mut resolver,
        &source,
        &schema,
        DeclarationId::new(1, None).unwrap(),
        &[],
    )
    .unwrap();

    assert_eq!(definition.formal_arguments.len(), 1);
    assert_eq!(definition.definition.branches.len(), 1);
    assert!(
        kernel
            .equivalent(
                kernel.classifier(definition.definition.equation).unwrap(),
                bool_ty
            )
            .unwrap()
    );
}

#[test]
fn exact_variant_and_struct_types_preserve_structural_branches() {
    let bytes = br#"(typ "V"
          (inst (variant
            (case "%" (exp "i" nat) (tup (bind (var "i") nat))))))
        (typ "S"
          (inst (struct (field "X" (exp "x" nat) nat))))"#;
    let il = IlDocument::parse(bytes, Limits::default()).unwrap();
    let source = Source::new(
        drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle"),
        drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        "test",
        "revision",
        &il,
    )
    .unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let value = kernel.ty_fv(0, star).unwrap();
    let schema = declare_hol_schema(&source, &mut kernel, value, bool_ty).unwrap();
    let binary_tail = kernel.ty_arr(value, value).unwrap();
    let binary_ty = kernel.ty_arr(value, binary_tail).unwrap();
    let graph_tail = kernel.ty_arr(value, bool_ty).unwrap();
    let graph_ty = kernel.ty_arr(value, graph_tail).unwrap();
    let x = kernel.tm_fv(10_000, value).unwrap();
    let mut resolver = TestRelationalResolver {
        x,
        y: kernel.tm_fv(10_001, value).unwrap(),
        add: kernel.tm_fv(10_002, binary_ty).unwrap(),
        graph: kernel.tm_fv(10_003, graph_ty).unwrap(),
        bool_ty,
        bound: std::collections::BTreeMap::new(),
        relations: std::collections::BTreeMap::new(),
    };

    let variant = relational_type_declaration(
        &mut kernel,
        &mut resolver,
        &source,
        &schema,
        DeclarationId::new(1, None).unwrap(),
        &[x],
    )
    .unwrap();
    let structure = relational_type_declaration(
        &mut kernel,
        &mut resolver,
        &source,
        &schema,
        DeclarationId::new(2, None).unwrap(),
        &[x],
    )
    .unwrap();

    assert_eq!(variant.definition.branches.len(), 1);
    assert_eq!(structure.definition.branches.len(), 1);
    assert!(
        [variant.definition.equation, structure.definition.equation]
            .into_iter()
            .all(|equation| kernel
                .equivalent(kernel.classifier(equation).unwrap(), bool_ty)
                .unwrap())
    );
}

#[test]
fn generic_hol_schema_is_transactional_on_embedding_failure() {
    let source = Source::wasm3().unwrap();
    let mut kernel = Kernel::new();
    let star = kernel.star().unwrap();
    let bool_ty = kernel.bool_ty(star).unwrap();
    let not_a_type = kernel.bool(bool_ty, true).unwrap();
    let before = kernel.arena().len();

    assert!(declare_hol_schema(&source, &mut kernel, not_a_type, bool_ty).is_err());
    assert_eq!(kernel.arena().len(), before);
}

#[test]
fn add_slice_exhaustively_classifies_exact_structural_forms() {
    let source = Source::wasm3().unwrap();
    let first = AddSlicePlan::build(&source).unwrap();
    let second = AddSlicePlan::build(&source).unwrap();
    assert_eq!(first, second);
    assert_eq!(first.declarations().len(), source.declaration_count());

    let translated = first
        .declarations()
        .iter()
        .map(|entry| entry.disposition)
        .chain(first.clauses().iter().map(|entry| entry.disposition))
        .chain(first.rules().iter().map(|entry| entry.disposition))
        .filter_map(|disposition| match disposition {
            Disposition::Translate { case, source } => Some((case, source)),
            Disposition::Reject(_) => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(translated.len(), 31);
    assert_eq!(
        translated
            .iter()
            .map(|(case, _)| *case)
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        translated.len()
    );
    assert!(
        translated
            .iter()
            .any(|(case, _)| *case == TranslationCase::BinaryOperationValueRule)
    );
    assert!(
        translated
            .iter()
            .any(|(case, _)| *case == TranslationCase::LocalGetRule)
    );
    assert!(
        first
            .declarations()
            .iter()
            .any(|entry| matches!(entry.disposition, Disposition::Reject(_)))
    );
    assert!(
        first
            .clauses()
            .iter()
            .any(|entry| matches!(entry.disposition, Disposition::Reject(_)))
    );
    assert!(
        first
            .rules()
            .iter()
            .any(|entry| matches!(entry.disposition, Disposition::Reject(_)))
    );

    for (_, span) in translated {
        assert!(span.first_line > 0);
        assert!(span.first_line <= span.last_line);
        let line_count = std::str::from_utf8(
            covalence_data_spectec::wasm3_source(span.path).expect("known pinned source path"),
        )
        .unwrap()
        .lines()
        .count();
        assert!(usize::try_from(span.last_line).unwrap() <= line_count);
    }
}

#[test]
fn add_slice_rejects_selected_rule_body_drift() {
    let original = Source::wasm3().unwrap();
    let mut bytes = covalence_data_spectec::WASM_3_AST_BYTES.to_vec();
    let rule = bytes
        .windows(b"\"binop-val\"".len())
        .position(|window| window == b"\"binop-val\"")
        .unwrap();
    let relative = bytes[rule..]
        .windows(b"\"binop_\"".len())
        .enumerate()
        .filter_map(|(position, window)| (window == b"\"binop_\"").then_some(position))
        .nth(1)
        .unwrap();
    let operation = rule + relative;
    bytes[operation + 4] = b'X';
    let il = IlDocument::parse(&bytes, Limits::default()).unwrap();
    let changed = Source::new(
        original.bundle(),
        original.ast(),
        original.release(),
        original.revision(),
        &il,
    )
    .unwrap();

    assert!(matches!(
        AddSlicePlan::build(&changed),
        Err(covalence_nucleus_spectec::AddSliceError::SemanticShape {
            case: TranslationCase::BinaryOperationValueRule,
            ..
        })
    ));
}

#[test]
fn generic_coverage_artifact_composes_without_add_policy() {
    let bundle = drisl::address(CidCodec::Drisl, CidHash::Sha256, b"bundle");
    let ast = drisl::address(CidCodec::Raw, CidHash::Sha256, b"ast");
    let id = DeclarationId::new(1, None).unwrap();
    let plan = CoveragePlan::new(
        vec![Coverage {
            id,
            disposition: "handled",
        }],
        Vec::new(),
        Vec::new(),
    );
    let artifact = CoverageArtifact::new(bundle, ast, plan);

    assert_eq!(artifact.bundle(), bundle);
    assert_eq!(artifact.ast(), ast);
    assert_eq!(artifact.plan().declarations()[0].disposition, "handled");
    let (actual_bundle, actual_ast, plan) = artifact.into_parts();
    assert_eq!((actual_bundle, actual_ast), (bundle, ast));
    assert_eq!(plan.declarations()[0].id, id);
}

#[test]
fn selected_compiler_requires_every_generic_plan_case_once() {
    let declaration = DeclarationId::new(1, None).unwrap();
    let clause = ClauseId::new(declaration, [3]).unwrap();
    let plan = CoveragePlan::new(
        vec![
            Coverage {
                id: declaration,
                disposition: CoverageDisposition::Translate {
                    case: 1_u8,
                    source: (),
                },
            },
            Coverage {
                id: DeclarationId::new(2, None).unwrap(),
                disposition: CoverageDisposition::Reject("outside"),
            },
        ],
        vec![Coverage {
            id: clause,
            disposition: CoverageDisposition::Translate {
                case: 2_u8,
                source: (),
            },
        }],
        Vec::new(),
    );
    let mut compiler = SelectedCompiler::new(&plan, Kernel::new()).unwrap();
    assert_eq!(compiler.required(), 2);
    compiler
        .lower(1, |kernel| {
            Ok(vec![KernelRoot::new("carrier", kernel.star()?)])
        })
        .unwrap();
    let star = compiler.roots(1).unwrap()[0].reference();
    let rows = compiler.kernel().len();
    assert!(matches!(
        compiler.lower(1, |_| Ok(Vec::new())),
        Err(SelectedCompileError::AlreadyLowered { .. })
    ));
    assert_eq!(compiler.kernel().len(), rows);
    assert!(matches!(
        compiler.lower(9, |_| Ok(Vec::new())),
        Err(SelectedCompileError::UnknownCase { .. })
    ));
    assert_eq!(compiler.kernel().len(), rows);
    compiler
        .lower(2, |kernel| {
            Ok(vec![KernelRoot::new("type", kernel.bool_ty(star)?)])
        })
        .unwrap();
    let selected = compiler.finish().unwrap();
    assert_eq!(selected.roots(&1).unwrap()[0].role(), "carrier");
    assert_eq!(selected.roots(&2).unwrap()[0].role(), "type");

    let incomplete = SelectedCompiler::new(&plan, Kernel::new()).unwrap();
    assert!(matches!(
        incomplete.finish(),
        Err(SelectedCompileError::MissingCase { .. })
    ));
}

#[test]
fn add_slice_has_canonical_translation_cid() {
    let source = Source::wasm3().unwrap();
    let artifact = AddSliceArtifact::build(&source).unwrap();
    let bytes = artifact.encode().unwrap();
    assert_eq!(artifact.encode().unwrap(), bytes);
    assert_eq!(artifact.bundle(), source.bundle());
    assert_eq!(artifact.ast(), source.ast());
    assert_eq!(artifact.plan(), &AddSlicePlan::build(&source).unwrap());
    assert_eq!(
        artifact.cid().unwrap(),
        drisl::address(CidCodec::Drisl, CidHash::Sha256, &bytes)
    );
    assert_eq!(artifact.cid().unwrap().codec(), CidCodec::Drisl);
    assert_eq!(artifact.cid().unwrap().hash(), CidHash::Sha256);
    assert!(Policy::ATPROTO.accepts(artifact.cid().unwrap()));
    assert!(drisl::addresses(artifact.cid().unwrap(), &bytes));
    assert_eq!(
        ADD_SLICE_TYPE_NAME,
        "io.github.imbrem.nucleus.spectecAddSliceV1"
    );

    let decoded = AddSliceArtifact::decode(&bytes).unwrap();
    assert_eq!(decoded, artifact);
    assert_eq!(decoded.encode().unwrap(), bytes);
    decoded.verify_source(&source).unwrap();
    assert_eq!(
        AddSliceArtifact::decode_for_source(&bytes, &source).unwrap(),
        artifact
    );

    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(matches!(
        AddSliceArtifact::decode(&trailing),
        Err(AddSliceArtifactError::RecordDecode { .. })
    ));

    let mut reordered_value = drisl::decode(Policy::ATPROTO, &bytes).unwrap();
    let covalence_data_cbor::drisl::Value::Map(fields) = &mut reordered_value else {
        panic!("artifact is a map");
    };
    let covalence_data_cbor::drisl::Value::Array(declarations) =
        fields.get_mut("declarations").unwrap()
    else {
        panic!("declarations is an array");
    };
    declarations.swap(0, 1);
    let reordered = drisl::encode(Policy::ATPROTO, &reordered_value).unwrap();
    let reordered = AddSliceArtifact::decode(&reordered).unwrap();
    assert!(matches!(
        reordered.verify_source(&source),
        Err(AddSliceArtifactError::SourceMismatch { .. })
    ));

    let mut value = drisl::decode(Policy::ATPROTO, &bytes).unwrap();
    let covalence_data_cbor::drisl::Value::Map(fields) = &mut value else {
        panic!("artifact is a map");
    };
    let covalence_data_cbor::drisl::Value::Array(declarations) =
        fields.get_mut("declarations").unwrap()
    else {
        panic!("declarations is an array");
    };
    declarations[1] = declarations[0].clone();
    let duplicate = drisl::encode(Policy::ATPROTO, &value).unwrap();
    assert!(matches!(
        AddSliceArtifact::decode(&duplicate),
        Err(AddSliceArtifactError::Schema { .. })
    ));
}

#[test]
fn wasm3_source_requires_every_declaration() {
    let source = Source::wasm3().unwrap();
    assert_eq!(source.declaration_count(), 980);
    let compiler = Compiler::new(source, Kernel::new());
    assert!(matches!(
        compiler.finish(),
        Err(CompileError::MissingDeclaration { .. })
    ));
}

#[test]
fn lowering_is_transactional_and_role_checked() {
    let source = Source::wasm3().unwrap();
    let first = DeclarationId::new(1, None).unwrap();
    let mut builder = Compiler::new(source, Kernel::new());
    let before = builder.kernel().len();
    assert!(matches!(
        builder.lower(first, |kernel| {
            let star = kernel.star()?;
            Ok(vec![
                KernelRoot::new("declaration", star),
                KernelRoot::new("declaration", star),
            ])
        }),
        Err(CompileError::DuplicateRole { .. })
    ));
    assert_eq!(builder.kernel().len(), before);
    assert_eq!(builder.completed(), 0);
}

#[test]
fn record_schema_uses_atproto_sha256_links() {
    assert_eq!(TYPE_NAME, "io.github.imbrem.nucleus.spectecCompilationV1");
    let source = Source::wasm3().unwrap();
    let compiler = Compiler::new(source, Kernel::new());
    let Err(CompileError::MissingDeclaration { id }) = compiler.finish() else {
        panic!("incomplete source must not freeze");
    };
    assert_eq!(id, DeclarationId::new(1, None).unwrap());

    let manifest = covalence_data_spectec::wasm3_bundle().unwrap();
    assert_eq!(manifest.manifest_cid().codec(), CidCodec::Drisl);
    assert_eq!(manifest.manifest_cid().hash(), CidHash::Sha256);
    assert!(Policy::ATPROTO.accepts(manifest.manifest_cid()));
    assert!(drisl::addresses(
        manifest.manifest_cid(),
        covalence_data_spectec::WASM_3_MANIFEST_BYTES
    ));
}

#[test]
fn complete_small_compilation_record_and_kernel_round_trip() {
    let il = IlDocument::parse(b"(typ \"T\" (inst (alias nat)))", Limits::default()).unwrap();
    let bundle_bytes = b"source manifest";
    let ast_bytes = b"(typ \"T\" (inst (alias nat)))";
    let bundle = drisl::address(CidCodec::Drisl, CidHash::Sha256, bundle_bytes);
    let ast = drisl::address(CidCodec::Raw, CidHash::Sha256, ast_bytes);
    let source = Source::new(bundle, ast, "test", "revision", &il).unwrap();
    let mut builder = Compiler::new(source, Kernel::new());
    let declaration = DeclarationId::new(1, None).unwrap();
    builder
        .lower(declaration, |kernel| {
            let star = kernel.star()?;
            Ok(vec![KernelRoot::new("declaration", star)])
        })
        .unwrap();
    let compiled = builder.finish().unwrap();

    let decoded = CompilationRecord::decode(compiled.record_drisl()).unwrap();
    assert_eq!(&decoded, compiled.record());
    assert_eq!(decoded.encode().unwrap(), compiled.record_drisl());
    let source = Source::new(bundle, ast, "test", "revision", &il).unwrap();
    decoded.verify_source(&source).unwrap();
    assert_eq!(
        decoded.verify_kernel(compiled.kernel_cbor()).unwrap(),
        *compiled.kernel().arena()
    );

    let mut damaged = compiled.kernel_cbor().to_vec();
    damaged.push(0);
    assert!(matches!(
        decoded.verify_kernel(&damaged),
        Err(ArtifactError::KernelAddress)
    ));
}
