//! Relational HOL expression lowering over the generic expression fold.

use covalence_data_spectec::{
    IlArgument, IlBinding, IlClauseSchema, IlDomain, IlExpression, IlExpressionView, IlIteration,
    IlPremise, IlRuleSchema, IlSchemaError,
};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref};

use crate::{
    ExpressionAlgebra, HolCase, HolRule, LeastPredicate, LeastPredicateError,
    begin_least_closed_family, close_hol_rule, close_hol_rules, existential_case, fold_expression,
};

/// Relational meaning of one expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalTerm {
    value: Ref,
    binders: Vec<Ref>,
    premises: Vec<Ref>,
}

/// Resolved graph predicate and checked result classifier for one call.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RelationalCall {
    /// Graph predicate after applying every explicit input argument.
    pub predicate: Ref,
    /// Classifier of the fresh result accepted by `predicate`.
    pub result_type: Ref,
}

/// Why lowered clause terms could not form one exact HOL graph case.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum RelationalCaseError {
    /// Clause patterns did not cover the declaration's formal inputs exactly.
    #[snafu(display("clause has {actual} patterns; definition has {expected} inputs"))]
    Arity {
        /// Number of declaration inputs.
        expected: usize,
        /// Number of clause patterns.
        actual: usize,
    },
    /// A checked HOL constructor rejected the case.
    #[snafu(display("could not construct relational HOL clause case: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
}

/// Lowered ingredients of one source-ordered definition clause.
#[derive(Clone, Copy, Debug)]
pub struct RelationalClause<'a> {
    /// Universally bound declaration inputs.
    pub formal_inputs: &'a [Ref],
    /// Universally bound graph result.
    pub formal_result: Ref,
    /// Clause-local variables decoded from explicit bindings.
    pub explicit_locals: &'a [Ref],
    /// Lowered left-hand-side patterns in input order.
    pub patterns: &'a [RelationalTerm],
    /// Lowered right-hand-side result expression.
    pub result: &'a RelationalTerm,
    /// Fresh binders introduced while lowering semantic premises.
    pub semantic_binders: &'a [Ref],
    /// Lowered semantic premise propositions.
    pub semantic_premises: &'a [Ref],
    /// Whether this clause carries `otherwise`.
    pub otherwise: bool,
}

/// Lowered conjunction contributed by one premise subtree.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RelationalCondition {
    binders: Vec<Ref>,
    premises: Vec<Ref>,
    otherwise: bool,
}

/// Checked result of lowering one complete ordered definition body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalDefinition {
    /// Exact source-ordered cases.
    pub cases: Vec<HolCase>,
    /// Ordered disjunction used as the graph body.
    pub body: Ref,
    /// Universally closed exact graph equation.
    pub equation: Ref,
    /// First unused deterministic free-variable name.
    pub next_name: u64,
}

/// Inputs selecting one complete definition graph constraint.
#[derive(Clone, Copy, Debug)]
pub struct RelationalDefinitionSource<'a> {
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Candidate graph predicate supplied by the checked schema.
    pub predicate: Ref,
    /// Universally quantified declaration inputs.
    pub formal_inputs: &'a [Ref],
    /// Universally quantified graph result.
    pub formal_result: Ref,
    /// Decoded clauses in exact source order.
    pub clauses: &'a [IlClauseSchema<'a>],
    /// First deterministic name available to clause-local lowering.
    pub first_name: u64,
}

/// One member of a mutually recursive relation group.
#[derive(Clone, Copy, Debug)]
pub struct RelationalRelation<'a> {
    /// Exact relation name used by nested rule premises.
    pub name: &'a str,
    /// Checked curried predicate classifier.
    pub predicate_type: Ref,
    /// Decoded source rules in exact order.
    pub rules: &'a [IlRuleSchema<'a>],
}

impl RelationalCondition {
    /// Constructs a lowered premise condition.
    #[must_use]
    pub const fn new(binders: Vec<Ref>, premises: Vec<Ref>, otherwise: bool) -> Self {
        Self {
            binders,
            premises,
            otherwise,
        }
    }

    /// Returns fresh variables introduced by relational subexpressions.
    #[must_use]
    pub fn binders(&self) -> &[Ref] {
        &self.binders
    }

    /// Returns checked Boolean propositions in source order.
    #[must_use]
    pub fn premises(&self) -> &[Ref] {
        &self.premises
    }

    /// Returns whether this subtree contains `otherwise`.
    #[must_use]
    pub const fn otherwise(&self) -> bool {
        self.otherwise
    }

    fn append(&mut self, other: &Self) {
        self.binders.extend_from_slice(&other.binders);
        self.premises.extend_from_slice(&other.premises);
        self.otherwise |= other.otherwise;
    }
}

impl RelationalTerm {
    /// Constructs an already-lowered relational term.
    #[must_use]
    pub const fn new(value: Ref, binders: Vec<Ref>, premises: Vec<Ref>) -> Self {
        Self {
            value,
            binders,
            premises,
        }
    }

    /// Returns the checked value term.
    #[must_use]
    pub const fn value(&self) -> Ref {
        self.value
    }

    /// Returns fresh result variables introduced by partial calls.
    #[must_use]
    pub fn binders(&self) -> &[Ref] {
        &self.binders
    }

    /// Returns graph premises required to produce the value.
    #[must_use]
    pub fn premises(&self) -> &[Ref] {
        &self.premises
    }
}

/// Composes lowered terms and extra premises into one HOL closure rule.
///
/// Terms appear in exact conclusion-argument order. Their fresh binders and
/// graph dependencies are accumulated before caller-supplied semantic
/// premises, preserving deterministic source order.
#[must_use]
pub fn relational_hol_rule(
    explicit_binders: &[Ref],
    conclusion: &[RelationalTerm],
    semantic_premises: &[Ref],
) -> HolRule {
    let mut binders = explicit_binders.to_vec();
    let mut premises = Vec::new();
    let mut arguments = Vec::with_capacity(conclusion.len());
    for term in conclusion {
        arguments.push(term.value);
        binders.extend_from_slice(&term.binders);
        premises.extend_from_slice(&term.premises);
    }
    premises.extend_from_slice(semantic_premises);
    HolRule::new(binders, premises, arguments)
}

/// Builds one exact ordered graph case from lowered clause terms.
///
/// Applicability includes pattern matching, pattern dependencies, and semantic
/// premises, but deliberately excludes evaluation of the right-hand side. A
/// selected partial clause therefore still blocks a later `otherwise` clause.
/// Production additionally requires right-hand-side dependencies and equality
/// with `formal_result`. All clause-local and relationally introduced values
/// are existentially closed.
///
/// # Errors
///
/// Returns an error when pattern and formal-input arities differ, an equality
/// is ill-typed, a premise is not Boolean, or existential construction fails.
pub fn relational_hol_case(
    kernel: &mut Kernel,
    bool_ty: Ref,
    clause: &RelationalClause<'_>,
) -> Result<HolCase, RelationalCaseError> {
    if clause.formal_inputs.len() != clause.patterns.len() {
        return Err(RelationalCaseError::Arity {
            expected: clause.formal_inputs.len(),
            actual: clause.patterns.len(),
        });
    }

    let mut locals = clause.explicit_locals.to_vec();
    let mut applicability = Vec::new();
    for (&formal, pattern) in clause.formal_inputs.iter().zip(clause.patterns) {
        locals.extend_from_slice(pattern.binders());
        applicability.extend_from_slice(pattern.premises());
        applicability.push(
            kernel
                .eq(bool_ty, formal, pattern.value())
                .map_err(|source| RelationalCaseError::Kernel { source })?,
        );
    }
    locals.extend_from_slice(clause.semantic_binders);
    applicability.extend_from_slice(clause.semantic_premises);
    let applicable = existential_case(kernel, bool_ty, &locals, &applicability)
        .map_err(|source| RelationalCaseError::Kernel { source })?;

    let mut production_locals = locals;
    production_locals.extend_from_slice(clause.result.binders());
    let mut production = applicability;
    production.extend_from_slice(clause.result.premises());
    production.push(
        kernel
            .eq(bool_ty, clause.formal_result, clause.result.value())
            .map_err(|source| RelationalCaseError::Kernel { source })?,
    );
    let produces = existential_case(kernel, bool_ty, &production_locals, &production)
        .map_err(|source| RelationalCaseError::Kernel { source })?;

    Ok(HolCase {
        applicable,
        produces,
        otherwise: clause.otherwise,
    })
}

/// Supplies environment-dependent leaves and primitive meanings.
pub trait RelationalResolver {
    /// Lowering failure type.
    type Error;

    /// Creates an isolated clause-local resolver retaining global meanings.
    #[must_use]
    fn clause_scope(&mut self) -> Self
    where
        Self: Sized;

    /// Creates a resolver scope binding a complete recursive relation family.
    #[must_use]
    fn relation_scope(&mut self, candidates: &[(&str, Ref)]) -> Self
    where
        Self: Sized;

    /// Converts a structural schema failure.
    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error;

    /// Converts a checked kernel failure.
    fn kernel_error(&mut self, source: KernelError) -> Self::Error;

    /// Reports exhaustion of the caller-selected name range.
    fn name_exhausted(&mut self) -> Self::Error;

    /// Converts exact-clause assembly failure.
    fn case_error(&mut self, source: RelationalCaseError) -> Self::Error;

    /// Converts least-family construction failure.
    fn least_error(&mut self, source: LeastPredicateError) -> Self::Error;

    /// Registers one checked term for an explicit IL binding.
    ///
    /// # Errors
    ///
    /// Returns an error for duplicate names or a target classifier incompatible
    /// with the binding category.
    fn binding(&mut self, binding: &IlBinding<'_>, reference: Ref) -> Result<(), Self::Error>;

    /// Resolves the checked classifier of one explicit IL binding.
    ///
    /// # Errors
    ///
    /// Returns an error when its IL type or higher-order signature cannot be
    /// embedded in the selected HOL representation.
    fn binding_type(
        &mut self,
        kernel: &mut Kernel,
        binding: &IlBinding<'_>,
    ) -> Result<Ref, Self::Error>;

    /// Resolves one variable expression to a checked term.
    ///
    /// # Errors
    ///
    /// Returns an error for an unbound variable or incompatible target term.
    fn variable(&mut self, kernel: &mut Kernel, name: &str) -> Result<Ref, Self::Error>;

    /// Resolves one non-expression type, definition, or grammar argument.
    ///
    /// # Errors
    ///
    /// Returns an error for an unbound higher-order name, unresolved type
    /// family argument, or incompatible checked classifier.
    fn argument(
        &mut self,
        kernel: &mut Kernel,
        argument: &IlArgument<'_>,
    ) -> Result<Ref, Self::Error>;

    /// Lowers one non-variable, non-call constructor from child values.
    ///
    /// # Errors
    ///
    /// Returns an error for an unresolved primitive or rejected checked
    /// construction.
    fn operation(
        &mut self,
        kernel: &mut Kernel,
        expression: &IlExpressionView<'_>,
        children: &[Ref],
    ) -> Result<Ref, Self::Error>;

    /// Resolves a call and applies all explicit arguments, returning a graph
    /// predicate prefix that accepts one fresh result value.
    ///
    /// # Errors
    ///
    /// Returns an error for an unresolved definition, unsupported
    /// higher-order argument, arity mismatch, or rejected checked application.
    fn call(
        &mut self,
        kernel: &mut Kernel,
        name: &str,
        arguments: &[IlArgument<'_>],
        expression_arguments: &[Ref],
    ) -> Result<RelationalCall, Self::Error>;

    /// Applies a named relation to its lowered single argument.
    ///
    /// # Errors
    ///
    /// Returns an error for an unknown relation or ill-typed application.
    fn relation(
        &mut self,
        kernel: &mut Kernel,
        name: &str,
        argument: Ref,
    ) -> Result<Ref, Self::Error>;

    /// Lowers an iterated premise after its repeated condition and domain
    /// expressions have been lowered.
    ///
    /// # Errors
    ///
    /// Returns an error when the selected value representation cannot express
    /// the iteration or its named domains.
    fn iterated_premise(
        &mut self,
        kernel: &mut Kernel,
        iteration: &IlIteration<'_>,
        domains: &[(&str, RelationalTerm)],
        repeated: RelationalCondition,
    ) -> Result<RelationalCondition, Self::Error>;

    /// Reports nested relation-premise binders unsupported by this lowering.
    fn nested_premise_bindings(&mut self, count: usize) -> Self::Error;

    /// Reports an `otherwise` marker in an inductive relation rule.
    fn relation_otherwise(&mut self) -> Self::Error;
}

/// Transactionally lowers a complete ordered definition to one exact graph
/// equation.
///
/// Each clause receives a fresh resolver scope, preventing pattern bindings
/// from leaking between siblings. `formal_inputs` and `formal_result` are
/// universally closed in predicate-application order.
///
/// # Errors
///
/// Returns the first clause-lowering or checked HOL failure through the
/// resolver's typed error vocabulary. `kernel` is unchanged on failure.
pub fn relational_definition<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &RelationalDefinitionSource<'_>,
) -> Result<RelationalDefinition, R::Error>
where
    R: RelationalResolver,
{
    let mut staged = kernel.fork();
    let mut cases = Vec::with_capacity(source.clauses.len());
    let mut next_name = source.first_name;
    for clause in source.clauses {
        let clause_resolver = resolver.clause_scope();
        let mut algebra = RelationalExpressionAlgebra::new(
            &mut staged,
            clause_resolver,
            source.bool_ty,
            next_name,
        );
        cases.push(algebra.clause(clause, source.formal_inputs, source.formal_result)?);
        next_name = algebra.next_name();
    }
    let body = crate::ordered_cases(&mut staged, source.bool_ty, &cases)
        .map_err(|source| resolver.kernel_error(source))?;
    let mut arguments = source.formal_inputs.to_vec();
    arguments.push(source.formal_result);
    let equation = crate::close_graph_equation(
        &mut staged,
        source.bool_ty,
        source.predicate,
        &arguments,
        &arguments,
        body,
    )
    .map_err(|source| resolver.kernel_error(source))?;
    *kernel = staged;
    Ok(RelationalDefinition {
        cases,
        body,
        equation,
        next_name,
    })
}

/// Transactionally lowers complete mutually recursive relation groups to their
/// simultaneous least HOL predicates.
///
/// Every nested relation premise resolves against the checked candidate family
/// during rule lowering. Rule-local bindings are isolated from sibling rules.
///
/// # Errors
///
/// Returns the first candidate-family, rule-lowering, relation-resolution, or
/// checked closure failure through the resolver's typed error vocabulary.
/// `kernel` is unchanged on failure.
pub fn relational_relations<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    bool_ty: Ref,
    relations: &[RelationalRelation<'_>],
) -> Result<Vec<LeastPredicate>, R::Error>
where
    R: RelationalResolver,
{
    let predicate_types = relations
        .iter()
        .map(|relation| relation.predicate_type)
        .collect::<Vec<_>>();
    let mut builder = begin_least_closed_family(kernel, bool_ty, &predicate_types)
        .map_err(|source| resolver.least_error(source))?;
    let closure = {
        let (staged, candidates) = builder.parts();
        let candidate_names = relations
            .iter()
            .zip(candidates)
            .map(|(relation, &candidate)| (relation.name, candidate))
            .collect::<Vec<_>>();
        let mut scoped = resolver.relation_scope(&candidate_names);
        let roots = candidates.to_vec();
        let mut next_name = staged
            .fresh_name(&roots)
            .map_err(|source| resolver.kernel_error(source))?;
        let mut closures = Vec::new();
        for (relation, &candidate) in relations.iter().zip(candidates) {
            for schema in relation.rules {
                let rule_resolver = scoped.clause_scope();
                let mut algebra =
                    RelationalExpressionAlgebra::new(staged, rule_resolver, bool_ty, next_name);
                let rule = algebra.rule(schema)?;
                next_name = algebra.next_name();
                closures.push(
                    close_hol_rule(staged, bool_ty, candidate, &rule)
                        .map_err(|source| resolver.kernel_error(source))?,
                );
            }
        }
        close_hol_rules(staged, bool_ty, &closures)
            .map_err(|source| resolver.kernel_error(source))?
    };
    builder
        .finish(closure)
        .map_err(|source| resolver.least_error(source))
}

/// Concrete expression algebra producing relational HOL terms.
pub struct RelationalExpressionAlgebra<'a, R> {
    kernel: &'a mut Kernel,
    resolver: R,
    bool_ty: Ref,
    next_name: u64,
}

impl<'a, R> RelationalExpressionAlgebra<'a, R> {
    /// Starts a lowering with an explicit deterministic name range.
    #[must_use]
    pub const fn new(kernel: &'a mut Kernel, resolver: R, bool_ty: Ref, first_name: u64) -> Self {
        Self {
            kernel,
            resolver,
            bool_ty,
            next_name: first_name,
        }
    }

    /// Declares and registers explicit bindings in exact source order.
    ///
    /// # Errors
    ///
    /// Returns an error on name exhaustion, rejected checked classifiers, or a
    /// resolver registration failure.
    pub fn bindings(&mut self, bindings: &[IlBinding<'_>]) -> Result<Vec<Ref>, R::Error>
    where
        R: RelationalResolver,
    {
        let mut references = Vec::with_capacity(bindings.len());
        for binding in bindings {
            let classifier = self.resolver.binding_type(self.kernel, binding)?;
            let name = self.take_name()?;
            let reference = self
                .kernel
                .tm_fv(name, classifier)
                .map_err(|source| self.resolver.kernel_error(source))?;
            self.resolver.binding(binding, reference)?;
            references.push(reference);
        }
        Ok(references)
    }

    /// Lowers one heterogeneous argument as a relational term.
    ///
    /// # Errors
    ///
    /// Returns the first expression or resolver failure. Expression arguments
    /// retain introduced graph binders and premises; other categories are
    /// resolved as already checked terms.
    pub fn argument(&mut self, argument: &IlArgument<'_>) -> Result<RelationalTerm, R::Error>
    where
        R: RelationalResolver,
    {
        match argument {
            IlArgument::Expression(expression) => fold_expression(expression, self),
            IlArgument::Type(_) | IlArgument::Definition(_) | IlArgument::Grammar(_) => self
                .resolver
                .argument(self.kernel, argument)
                .map(|value| RelationalTerm::new(value, Vec::new(), Vec::new())),
        }
    }

    /// Lowers one complete definition clause to an exact ordered graph case.
    ///
    /// The algebra should be scoped to this clause so resolver bindings do not
    /// leak into a sibling clause.
    ///
    /// # Errors
    ///
    /// Returns the first binding, pattern, expression, premise, relation,
    /// iteration, arity, or checked HOL failure.
    pub fn clause(
        &mut self,
        schema: &IlClauseSchema<'_>,
        formal_inputs: &[Ref],
        formal_result: Ref,
    ) -> Result<HolCase, R::Error>
    where
        R: RelationalResolver,
    {
        let explicit_locals = self.bindings(schema.bindings())?;
        let patterns = schema
            .arguments()
            .iter()
            .map(|argument| self.argument(argument))
            .collect::<Result<Vec<_>, _>>()?;
        let result = fold_expression(schema.result(), self)?;
        let conditions = schema
            .premises()
            .iter()
            .map(|premise| self.premise(premise))
            .collect::<Result<Vec<_>, _>>()?;
        let semantic_binders = conditions
            .iter()
            .flat_map(|condition| condition.binders().iter().copied())
            .collect::<Vec<_>>();
        let semantic_premises = conditions
            .iter()
            .flat_map(|condition| condition.premises().iter().copied())
            .collect::<Vec<_>>();
        let otherwise = conditions.iter().any(RelationalCondition::otherwise);
        relational_hol_case(
            self.kernel,
            self.bool_ty,
            &RelationalClause {
                formal_inputs,
                formal_result,
                explicit_locals: &explicit_locals,
                patterns: &patterns,
                result: &result,
                semantic_binders: &semantic_binders,
                semantic_premises: &semantic_premises,
                otherwise,
            },
        )
        .map_err(|source| self.resolver.case_error(source))
    }

    /// Lowers one complete relation rule to an inductive HOL rule.
    ///
    /// # Errors
    ///
    /// Returns the first binding, conclusion, premise, relation, iteration, or
    /// checked HOL failure. `otherwise` is rejected because negative ordered
    /// fallback is not a monotone inductive rule.
    pub fn rule(&mut self, schema: &IlRuleSchema<'_>) -> Result<HolRule, R::Error>
    where
        R: RelationalResolver,
    {
        let mut binders = self.bindings(schema.bindings())?;
        let conclusion = fold_expression(schema.conclusion(), self)?;
        binders.extend_from_slice(conclusion.binders());
        let mut premises = conclusion.premises().to_vec();
        for premise in schema.premises() {
            let condition = self.premise(premise)?;
            if condition.otherwise() {
                return Err(self.resolver.relation_otherwise());
            }
            binders.extend_from_slice(condition.binders());
            premises.extend_from_slice(condition.premises());
        }
        Ok(HolRule::new(binders, premises, vec![conclusion.value()]))
    }

    /// Returns the next unused name after lowering.
    #[must_use]
    pub const fn next_name(&self) -> u64 {
        self.next_name
    }

    /// Consumes the algebra and returns its resolver.
    #[must_use]
    pub fn into_resolver(self) -> R {
        self.resolver
    }

    /// Lowers one complete premise subtree to relational HOL conditions.
    ///
    /// # Errors
    ///
    /// Returns the first expression, binding, relation, iteration, or checked
    /// HOL failure reported by the resolver.
    pub fn premise(&mut self, premise: &IlPremise<'_>) -> Result<RelationalCondition, R::Error>
    where
        R: RelationalResolver,
    {
        match premise {
            IlPremise::If(expression) => {
                let term = fold_expression(expression, self)?;
                let truth = self
                    .kernel
                    .bool(self.bool_ty, true)
                    .map_err(|source| self.resolver.kernel_error(source))?;
                let proposition = self
                    .kernel
                    .op2(covalence_logic_hol::builtin::Op2::And, truth, term.value())
                    .map_err(|source| self.resolver.kernel_error(source))?;
                let mut premises = term.premises().to_vec();
                premises.push(proposition);
                Ok(RelationalCondition::new(
                    term.binders().to_vec(),
                    premises,
                    false,
                ))
            }
            IlPremise::Let { left, right } => {
                let left = fold_expression(left, self)?;
                let right = fold_expression(right, self)?;
                let equality = self
                    .kernel
                    .eq(self.bool_ty, left.value(), right.value())
                    .map_err(|source| self.resolver.kernel_error(source))?;
                let mut binders = left.binders().to_vec();
                binders.extend_from_slice(right.binders());
                let mut premises = left.premises().to_vec();
                premises.extend_from_slice(right.premises());
                premises.push(equality);
                Ok(RelationalCondition::new(binders, premises, false))
            }
            IlPremise::Otherwise => Ok(RelationalCondition::new(Vec::new(), Vec::new(), true)),
            IlPremise::Rule(rule) => {
                if !rule.bindings().is_empty() {
                    return Err(self.resolver.nested_premise_bindings(rule.bindings().len()));
                }
                let conclusion = fold_expression(rule.conclusion(), self)?;
                let relation =
                    self.resolver
                        .relation(self.kernel, rule.name(), conclusion.value())?;
                let mut condition = RelationalCondition::new(
                    conclusion.binders().to_vec(),
                    conclusion.premises().to_vec(),
                    false,
                );
                condition.premises.push(relation);
                for nested in rule.premises() {
                    let nested = self.premise(nested)?;
                    condition.append(&nested);
                }
                Ok(condition)
            }
            IlPremise::Iterated {
                premise,
                iteration,
                domains,
            } => {
                let repeated = self.premise(premise)?;
                let domains = domains
                    .iter()
                    .map(|domain| self.lower_domain(domain))
                    .collect::<Result<Vec<_>, _>>()?;
                self.resolver
                    .iterated_premise(self.kernel, iteration, &domains, repeated)
            }
        }
    }

    fn lower_domain<'b>(
        &mut self,
        domain: &'b IlDomain<'b>,
    ) -> Result<(&'b str, RelationalTerm), R::Error>
    where
        R: RelationalResolver,
    {
        Ok((domain.name(), fold_expression(domain.expression(), self)?))
    }

    fn take_name(&mut self) -> Result<u64, R::Error>
    where
        R: RelationalResolver,
    {
        let name = self.next_name;
        self.next_name = self
            .next_name
            .checked_add(1)
            .ok_or_else(|| self.resolver.name_exhausted())?;
        Ok(name)
    }
}

impl<R: RelationalResolver> ExpressionAlgebra for RelationalExpressionAlgebra<'_, R> {
    type Term = RelationalTerm;
    type Error = R::Error;

    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error {
        self.resolver.schema_error(source)
    }

    fn expression(
        &mut self,
        expression: &IlExpression<'_>,
        children: Vec<Self::Term>,
    ) -> Result<Self::Term, Self::Error> {
        let mut binders = Vec::new();
        let mut premises = Vec::new();
        let mut values = Vec::with_capacity(children.len());
        for child in children {
            values.push(child.value);
            binders.extend(child.binders);
            premises.extend(child.premises);
        }
        let view = expression
            .view()
            .map_err(|source| self.resolver.schema_error(source))?;
        let value = match &view {
            IlExpressionView::Variable(name) => self.resolver.variable(self.kernel, name)?,
            IlExpressionView::Call { name, arguments } => {
                let call = self.resolver.call(self.kernel, name, arguments, &values)?;
                let name = self.take_name()?;
                let result = self
                    .kernel
                    .tm_fv(name, call.result_type)
                    .map_err(|source| self.resolver.kernel_error(source))?;
                let premise = self
                    .kernel
                    .app(call.predicate, result)
                    .map_err(|source| self.resolver.kernel_error(source))?;
                binders.push(result);
                premises.push(premise);
                result
            }
            _ => self.resolver.operation(self.kernel, &view, &values)?,
        };
        Ok(RelationalTerm::new(value, binders, premises))
    }
}
