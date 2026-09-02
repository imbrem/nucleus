//! Relational HOL expression lowering over the generic expression fold.

use covalence_data_spectec::{
    IlArgument, IlBinding, IlDomain, IlExpression, IlExpressionView, IlIteration, IlPremise,
    IlSchemaError,
};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref};

use crate::{ExpressionAlgebra, HolCase, HolRule, existential_case, fold_expression};

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

    /// Converts a structural schema failure.
    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error;

    /// Converts a checked kernel failure.
    fn kernel_error(&mut self, source: KernelError) -> Self::Error;

    /// Reports exhaustion of the caller-selected name range.
    fn name_exhausted(&mut self) -> Self::Error;

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
