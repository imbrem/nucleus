use covalence_data_basic::Symbol;
use covalence_data_cbor::drisl::{self, CidCodec, CidHash, Policy};
use covalence_data_spectec::{
    ClauseId, DeclarationId, IlClauseSchema, IlDocument, IlExpression, IlExpressionKind,
    IlGrammarSymbol, IlKind, IlPremise, IlProductionSchema, IlRuleSchema, IlSchemaError, IlType,
    Limits,
};
use covalence_logic_hol::{Kernel, Tag, TmTag};
use covalence_nucleus_spectec::{
    ADD_SLICE_TYPE_NAME, AddSliceArtifact, AddSliceArtifactError, AddSlicePlan, ArtifactError,
    CompilationRecord, CompileError, Compiler, Coverage, CoverageArtifact, CoverageDisposition,
    CoveragePlan, Disposition, ExpressionAlgebra, GrammarAlgebra, GrammarChildren, HolCase,
    HolEmbedding, HolFamilyBranch, HolRule, HolTheoryError, IndexErasure, InterpretationKind,
    KernelRoot, RelationalCall, RelationalClause, RelationalCondition, RelationalDefinitionSchema,
    RelationalDefinitionSource, RelationalExpressionAlgebra, RelationalRelation,
    RelationalResolver, RelationalTerm, SelectedCompileError, SelectedCompiler, Source, TYPE_NAME,
    TranslationCase, TypeAlgebra, TypeChildren, begin_least_closed_family, close_family_definition,
    close_graph_equation, close_hol_rule, close_hol_rules, close_hol_theory, declare_hol_schema,
    fold_expression, fold_grammar, fold_type, least_closed_family, least_closed_predicate,
    ordered_cases, parameterized_document, parameterized_document_with, relational_definition,
    relational_definition_declaration, relational_definition_schema, relational_document,
    relational_grammar_declaration, relational_hol_case, relational_hol_rule,
    relational_relation_declaration, relational_relations, relational_type_declaration,
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
    assert!(!document.interpretation.is_empty());
    assert!(!document.has_closed_interpretation());
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
    let provided = std::collections::BTreeMap::from([(
        Symbol::from(supplied.label.as_str()),
        supplied.reference,
    )]);

    let interpreted =
        parameterized_document_with(&source, &mut kernel, value, bool_ty, &provided).unwrap();

    assert!(
        interpreted
            .grounding_obligations()
            .all(|obligation| obligation.label != supplied.label)
    );

    let wrong = kernel.bool(bool_ty, true).unwrap();
    let incompatible = std::collections::BTreeMap::from([(supplied.label, wrong)]);
    let before = kernel.arena().clone();
    assert!(
        parameterized_document_with(&source, &mut kernel, value, bool_ty, &incompatible).is_err()
    );
    assert_eq!(kernel.arena(), &before);
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
