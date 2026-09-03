//! Relational HOL expression lowering over the generic expression fold.

use std::{collections::BTreeSet, sync::Arc};

use covalence_data_spectec::{
    DeclarationId, IlArgument, IlBinding, IlClauseSchema, IlDeclarationBody, IlDomain,
    IlExpression, IlExpressionView, IlIteration, IlKind, IlPremise, IlRuleSchema, IlSchemaError,
};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Lit, Ref, Tag, TyTag, builtin::Op1, builtin::Op2};
use covalence_logic_hol_derived::{ForallError, forall_elim};

use crate::{
    Evidence, ExpressionAlgebra, HolCase, HolFamilyError, HolRule, HolSchema, HolTheoryError,
    LeastPredicate, LeastPredicateError, Source, begin_least_closed_family_avoiding,
    close_hol_rule, close_hol_rules, existential_case, fold_expression,
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
    /// A schema slot was not a curried graph predicate with a result argument.
    #[snafu(display("definition schema slot is not a function ending in bool"))]
    NotGraph,
    /// A lowered pattern did not share its formal input's classifier.
    #[snafu(display(
        "clause pattern {index} ({pattern:?}) does not match formal {formal:?}: {source}"
    ))]
    Pattern {
        /// Zero-based input position.
        index: usize,
        /// Universal formal input.
        formal: Ref,
        /// Lowered pattern value.
        pattern: Ref,
        /// Underlying checked failure.
        source: KernelError,
    },
    /// A lowered result did not share the formal result's classifier.
    #[snafu(display("clause result {result:?} does not match formal {formal:?}: {source}"))]
    Result {
        /// Universal formal result.
        formal: Ref,
        /// Lowered result value.
        result: Ref,
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
    /// Universally quantified graph inputs derived from the schema slot.
    pub formal_inputs: Vec<Ref>,
    /// Universally quantified graph result derived from the schema slot.
    pub formal_result: Ref,
    /// Exact source-ordered cases.
    pub cases: Vec<HolCase>,
    /// Ordered disjunction used as the graph body.
    pub body: Ref,
    /// Universally closed exact graph equation.
    pub equation: Ref,
    /// First unused deterministic free-variable name.
    pub next_name: u64,
}

/// Minimal inputs for lowering one complete checked definition schema.
#[derive(Clone, Copy, Debug)]
pub struct RelationalDefinitionSchema<'a> {
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Checked graph-predicate slot declared by the generic schema.
    pub predicate: Ref,
    /// Exact decoded clauses in source order.
    pub clauses: &'a [IlClauseSchema<'a>],
    /// Existing interpretation roots whose free-variable names are reserved.
    pub avoid: &'a [Ref],
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
    /// Checked semantic-predicate slot declared by the generic schema.
    pub predicate: Ref,
    /// Decoded source rules in exact order.
    pub rules: &'a [IlRuleSchema<'a>],
}

/// Exact definition of one schema relation slot by a least-family member.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalRelationDefinition {
    /// Free semantic slot supplied by the checked schema.
    pub predicate: Ref,
    /// Direct impredicative least predicate generated from the relation rules.
    pub least: LeastPredicate,
    /// Source-ordered universally closed rule propositions for this member.
    pub rules: Arc<[Ref]>,
    /// Source-ordered rules for the complete mutually recursive family.
    pub family_rules: Arc<[Ref]>,
    /// Checked proposition `predicate = least.predicate`.
    pub equation: Ref,
}

impl RelationalRelationDefinition {
    /// Derives one member rule from the complete family closure.
    ///
    /// The resulting theorem has `least.closure` as its single visible premise
    /// and the selected universally closed rule as its conclusion.
    ///
    /// # Errors
    ///
    /// Returns an error if `index` is absent, the retained rule is inconsistent
    /// with the family closure, or a checked theorem step fails. `kernel` is
    /// unchanged on failure.
    pub fn derive_rule(
        &self,
        kernel: &mut Kernel,
        index: usize,
    ) -> Result<Evidence, RelationProofError> {
        let target = *self
            .rules
            .get(index)
            .ok_or(RelationProofError::Missing { index })?;
        let family_index = self
            .family_rules
            .iter()
            .position(|&rule| rule == target)
            .ok_or(RelationProofError::Inconsistent)?;
        let mut staged = kernel.fork();
        let mut theorem = staged.identity(positive(target))?;
        for (candidate_index, &rule) in self.family_rules.iter().enumerate() {
            if candidate_index != family_index {
                staged.weaken(theorem, &[positive(rule)], &[])?;
            }
        }
        if self.family_rules.len() > 1 {
            theorem = staged.fold_premise(theorem, positive(self.least.closure))?;
        } else if self.family_rules.first().copied() != Some(self.least.closure) {
            return Err(RelationProofError::Inconsistent);
        }
        *kernel = staged;
        Ok(Evidence {
            proposition: target,
            theorem,
            holds: true,
        })
    }

    /// Derives and specializes one member rule at checked arguments.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`derive_rule`](Self::derive_rule), or if an argument does not match the
    /// next universal binder. `kernel` is unchanged on failure.
    pub fn specialize_rule(
        &self,
        kernel: &mut Kernel,
        index: usize,
        arguments: &[Ref],
    ) -> Result<Evidence, RelationProofError> {
        let mut staged = kernel.fork();
        let mut evidence = self.derive_rule(&mut staged, index)?;
        for &argument in arguments {
            let specialized = forall_elim(&mut staged, evidence.theorem, argument)
                .map_err(|source| RelationProofError::Specialize { source })?;
            evidence = Evidence {
                proposition: specialized.proposition,
                theorem: specialized.theorem,
                holds: true,
            };
        }
        *kernel = staged;
        Ok(evidence)
    }
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

/// Why a checked relation rule could not be derived or specialized.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
#[snafu(module)]
pub enum RelationProofError {
    /// The member has no rule at the requested source index.
    #[snafu(display("SpecTec relation rule index {index} is absent"))]
    Missing {
        /// Requested member-local rule index.
        index: usize,
    },
    /// Retained member and family rule metadata disagree.
    #[snafu(display("retained SpecTec relation rules are inconsistent with their closure"))]
    Inconsistent,
    /// A checked theorem step failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Universal specialization failed.
    #[snafu(display("could not specialize a SpecTec relation rule: {source}"))]
    Specialize {
        /// Underlying checked derived-rule failure.
        source: ForallError,
    },
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
    for (index, (&formal, pattern)) in clause.formal_inputs.iter().zip(clause.patterns).enumerate()
    {
        locals.extend_from_slice(pattern.binders());
        applicability.extend_from_slice(pattern.premises());
        applicability.push(
            kernel
                .eq(bool_ty, formal, pattern.value())
                .map_err(|source| RelationalCaseError::Pattern {
                    index,
                    formal,
                    pattern: pattern.value(),
                    source,
                })?,
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
            .map_err(|source| RelationalCaseError::Result {
                formal: clause.formal_result,
                result: clause.result.value(),
                source,
            })?,
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

    /// Attaches the structural declaration selector to a lowering failure.
    fn declaration_error(&mut self, id: DeclarationId, source: Self::Error) -> Self::Error;

    /// Creates an isolated clause-local resolver retaining global meanings.
    #[must_use]
    fn clause_scope(&mut self) -> Self
    where
        Self: Sized;

    /// Restores global resolver state after an isolated clause has completed.
    fn restore_scope(&mut self, scope: Self)
    where
        Self: Sized;

    /// Establishes any lexical bindings introduced by an expression before
    /// its semantic children are visited.
    ///
    /// # Errors
    ///
    /// Returns an error when the expression scope cannot be established.
    fn enter_expression(
        &mut self,
        kernel: &mut Kernel,
        expression: &IlExpression<'_>,
    ) -> Result<(), Self::Error>;

    /// Restores the environment after [`enter_expression`](Self::enter_expression).
    ///
    /// # Errors
    ///
    /// Returns an error when the expression scope cannot be restored.
    fn leave_expression(&mut self, expression: &IlExpression<'_>) -> Result<(), Self::Error>;

    /// Returns fresh binders introduced by the current expression scope.
    ///
    /// # Errors
    ///
    /// Returns an error when the active scope cannot supply its binders.
    fn expression_binders(
        &mut self,
        expression: &IlExpression<'_>,
    ) -> Result<Vec<Ref>, Self::Error>;

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

    /// Converts exact predicate-family assembly failure.
    fn family_error(&mut self, source: HolFamilyError) -> Self::Error;

    /// Converts complete-theory coverage or conjunction failure.
    fn theory_error(&mut self, source: HolTheoryError) -> Self::Error;

    /// Registers one checked term for an explicit IL binding.
    ///
    /// # Errors
    ///
    /// Returns an error for duplicate names or a target classifier incompatible
    /// with the binding category.
    fn binding(&mut self, binding: &IlBinding<'_>, reference: Ref) -> Result<(), Self::Error>;

    /// Produces the semantic well-formedness premise for one registered
    /// binding, if its category requires one.
    ///
    /// Expression bindings normally return membership in their decoded IL
    /// type. Higher-order/type bindings may return `None` when their checked
    /// classifier already expresses the complete requirement.
    ///
    /// # Errors
    ///
    /// Returns an unresolved-membership or checked application failure.
    fn binding_premise(
        &mut self,
        kernel: &mut Kernel,
        binding: &IlBinding<'_>,
        reference: Ref,
    ) -> Result<Option<Ref>, Self::Error>;

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

    /// Resolves a non-expression clause pattern with access to its formal.
    ///
    /// Higher-order shorthand patterns can use `formal` as their lexical
    /// binding. Other arguments use the ordinary argument interpretation.
    ///
    /// # Errors
    ///
    /// Returns an error when the pattern cannot be resolved at the formal.
    fn pattern_argument(
        &mut self,
        kernel: &mut Kernel,
        argument: &IlArgument<'_>,
        _formal: Ref,
    ) -> Result<Ref, Self::Error> {
        self.argument(kernel, argument)
    }

    /// Applies the HOL membership interpretation of one decoded IL type.
    ///
    /// # Errors
    ///
    /// Returns an error for an unresolved type family or an ill-typed checked
    /// predicate application.
    fn type_membership(
        &mut self,
        kernel: &mut Kernel,
        ty: &covalence_data_spectec::IlType<'_>,
        value: Ref,
    ) -> Result<Ref, Self::Error>;

    /// Resolves the checked classifier used for a witness of one IL type.
    ///
    /// # Errors
    ///
    /// Returns an error when the selected type embedding cannot classify the
    /// witness.
    fn type_classifier(
        &mut self,
        kernel: &mut Kernel,
        ty: &covalence_data_spectec::IlType<'_>,
    ) -> Result<Ref, Self::Error>;

    /// Constructs the interpreted value of a tuple payload.
    ///
    /// # Errors
    ///
    /// Returns an error for an unavailable tuple interpretation or rejected
    /// checked application.
    fn tuple_value(&mut self, kernel: &mut Kernel, elements: &[Ref]) -> Result<Ref, Self::Error>;

    /// Constructs one interpreted tagged-variant value.
    ///
    /// # Errors
    ///
    /// Returns an error for an unavailable constructor interpretation or
    /// rejected checked application.
    fn variant_value(
        &mut self,
        kernel: &mut Kernel,
        constructor: &str,
        payload: Ref,
    ) -> Result<Ref, Self::Error>;

    /// Constructs one interpreted record value from exact field names/order.
    ///
    /// # Errors
    ///
    /// Returns an error for an unavailable record interpretation or rejected
    /// checked application.
    fn struct_value(
        &mut self,
        kernel: &mut Kernel,
        fields: &[(&str, Ref)],
    ) -> Result<Ref, Self::Error>;

    /// Interprets one grammar-symbol constructor from its already-lowered
    /// semantic children.
    ///
    /// # Errors
    ///
    /// Returns an error for an unresolved grammar constructor/reference or a
    /// rejected checked application.
    fn grammar_value(
        &mut self,
        kernel: &mut Kernel,
        symbol: &covalence_data_spectec::IlGrammarSymbol<'_>,
        children: &[Ref],
    ) -> Result<Ref, Self::Error>;

    /// Reports an `otherwise` marker in a structural type side condition.
    fn type_otherwise(&mut self) -> Self::Error;

    /// Reports an `otherwise` marker in a grammar-production side condition.
    fn grammar_otherwise(&mut self) -> Self::Error;

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
        resolver.restore_scope(algebra.into_resolver());
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
        formal_inputs: source.formal_inputs.to_vec(),
        formal_result: source.formal_result,
        cases,
        body,
        equation,
        next_name,
    })
}

/// Derives a definition's formal inputs, result, and fresh-name range directly
/// from its checked schema slot, then lowers every decoded clause.
///
/// This is the whole-schema entry point. [`relational_definition`] remains the
/// lower-level form for callers that already own formal variables.
///
/// # Errors
///
/// Returns an error when the slot is not a curried graph predicate with at
/// least a result argument, name allocation fails, or clause lowering fails.
/// `kernel` is unchanged on failure.
pub fn relational_definition_schema<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &RelationalDefinitionSchema<'_>,
) -> Result<RelationalDefinition, R::Error>
where
    R: RelationalResolver,
{
    let mut staged = kernel.fork();
    let classifier = staged
        .classifier(source.predicate)
        .map_err(|error| resolver.kernel_error(error))?;
    let domains = graph_domains(&staged, classifier, source.bool_ty)
        .map_err(|error| resolver.case_error(error))?;
    let Some((result_type, input_types)) = domains.split_last() else {
        return Err(resolver.case_error(RelationalCaseError::NotGraph));
    };
    let roots = std::iter::once(source.predicate)
        .chain(std::iter::once(source.bool_ty))
        .chain(source.avoid.iter().copied())
        .collect::<Vec<_>>();
    let mut next_name = staged
        .fresh_name(&roots)
        .map_err(|error| resolver.kernel_error(error))?;
    let mut formal_inputs = Vec::with_capacity(input_types.len());
    for &input_type in input_types {
        formal_inputs.push(
            staged
                .tm_fv(next_name, input_type)
                .map_err(|error| resolver.kernel_error(error))?,
        );
        next_name = next_name
            .checked_add(1)
            .ok_or_else(|| resolver.name_exhausted())?;
    }
    let formal_result = staged
        .tm_fv(next_name, *result_type)
        .map_err(|error| resolver.kernel_error(error))?;
    next_name = next_name
        .checked_add(1)
        .ok_or_else(|| resolver.name_exhausted())?;
    let definition = relational_definition(
        &mut staged,
        resolver,
        &RelationalDefinitionSource {
            bool_ty: source.bool_ty,
            predicate: source.predicate,
            formal_inputs: &formal_inputs,
            formal_result,
            clauses: source.clauses,
            first_name: next_name,
        },
    )?;
    *kernel = staged;
    Ok(definition)
}

/// Decodes and lowers one complete definition selected from an exact source
/// and its checked generic schema.
///
/// All schema slots are reserved automatically for hygienic formal-variable
/// allocation. `avoid` adds primitive-interpretation or caller-owned roots.
///
/// # Errors
///
/// Returns an error for an absent/non-definition selector, a mismatched HOL
/// schema slot, malformed clause, or any schema-derived lowering failure.
/// `kernel` is unchanged on failure.
pub fn relational_definition_declaration<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &Source,
    schema: &HolSchema,
    id: DeclarationId,
    avoid: &[Ref],
) -> Result<RelationalDefinition, R::Error>
where
    R: RelationalResolver,
{
    let declaration = source
        .il()
        .schema(id)
        .map_err(|error| resolver.schema_error(error))?
        .ok_or_else(|| {
            resolver.schema_error(IlSchemaError::Shape {
                id,
                path: Vec::new(),
                expected: "inventoried definition declaration",
                actual: "missing declaration".to_owned(),
            })
        })?;
    let target = schema.declaration(id).ok_or_else(|| {
        resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "checked HOL definition slot",
            actual: "missing schema slot".to_owned(),
        })
    })?;
    let IlDeclarationBody::Definition { clauses, .. } = declaration.body() else {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "definition declaration",
            actual: format!("{:?} declaration", target.kind()),
        }));
    };
    if target.kind() != IlKind::Definition {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "HOL definition slot",
            actual: format!("HOL {:?} slot", target.kind()),
        }));
    }
    let clauses = clauses
        .iter()
        .map(IlClauseSchema::decode)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| resolver.schema_error(error))?;
    let reserved = schema
        .declarations()
        .map(|(_, declaration)| declaration.reference())
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
    relational_definition_schema(
        kernel,
        resolver,
        &RelationalDefinitionSchema {
            bool_ty: schema.bool_ty(),
            predicate: target.reference(),
            clauses: &clauses,
            avoid: &reserved,
        },
    )
}

pub(crate) fn graph_domains(
    kernel: &Kernel,
    predicate_type: Ref,
    bool_ty: Ref,
) -> Result<Vec<Ref>, RelationalCaseError> {
    let mut domains = Vec::new();
    let mut current = predicate_type;
    while kernel.arena().tag(current) == Some(Tag::Ty(TyTag::Arr)) {
        let children = kernel
            .arena()
            .children(current)
            .ok_or(RelationalCaseError::NotGraph)?
            .collect::<Vec<_>>();
        let [domain, codomain] = children.as_slice() else {
            return Err(RelationalCaseError::NotGraph);
        };
        domains.push(*domain);
        current = *codomain;
    }
    if !kernel
        .equivalent(current, bool_ty)
        .map_err(|source| RelationalCaseError::Kernel { source })?
    {
        return Err(RelationalCaseError::NotGraph);
    }
    Ok(domains)
}

/// Transactionally lowers complete mutually recursive relation groups to their
/// simultaneous least HOL predicates.
///
/// Every nested relation premise resolves against the checked candidate family
/// during rule lowering. Rule-local bindings are isolated from sibling rules.
/// A consecutive `otherwise` chain is guarded by the negated applicability of
/// the preceding alternatives; a new unguarded rule starts a new chain.
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
) -> Result<Vec<RelationalRelationDefinition>, R::Error>
where
    R: RelationalResolver,
{
    relational_relations_avoiding(kernel, resolver, bool_ty, relations, &[])
}

/// Lowers a complete mutually recursive relation family while reserving names
/// reachable from additional interpretation roots.
///
/// # Errors
///
/// Returns the same failures as [`relational_relations`]. `kernel` is unchanged
/// on failure.
pub fn relational_relations_avoiding<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    bool_ty: Ref,
    relations: &[RelationalRelation<'_>],
    avoid: &[Ref],
) -> Result<Vec<RelationalRelationDefinition>, R::Error>
where
    R: RelationalResolver,
{
    let mut staged = kernel.fork();
    let predicate_types = relations
        .iter()
        .map(|relation| {
            staged
                .classifier(relation.predicate)
                .map_err(|source| resolver.kernel_error(source))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let predicates = relations
        .iter()
        .map(|relation| relation.predicate)
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
    let mut builder =
        begin_least_closed_family_avoiding(&mut staged, bool_ty, &predicate_types, &predicates)
            .map_err(|source| resolver.least_error(source))?;
    let mut relation_rules = Vec::with_capacity(relations.len());
    let (closure, family_rules) = {
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
            let first_rule = closures.len();
            let mut preceding = None;
            for schema in relation.rules {
                let rule_resolver = scoped.clause_scope();
                let mut algebra =
                    RelationalExpressionAlgebra::new(staged, rule_resolver, bool_ty, next_name);
                let (mut rule, otherwise) = algebra.ordered_rule(schema)?;
                next_name = algebra.next_name();
                scoped.restore_scope(algebra.into_resolver());
                if otherwise {
                    if preceding.is_some_and(|guard| depends_on_any(staged, guard, candidates)) {
                        return Err(resolver.relation_otherwise());
                    }
                    let guard = ordered_rule_guard(staged, bool_ty, preceding, &rule)
                        .map_err(|source| resolver.kernel_error(source))?;
                    rule.premises.push(guard);
                }
                closures.push(
                    close_hol_rule(staged, bool_ty, candidate, &rule)
                        .map_err(|source| resolver.kernel_error(source))?,
                );
                let preceding_chain = if otherwise { preceding } else { None };
                preceding = Some(
                    extend_ordered_applicability(staged, bool_ty, preceding_chain, &rule)
                        .map_err(|source| resolver.kernel_error(source))?,
                );
            }
            relation_rules.push(Arc::from(&closures[first_rule..]));
        }
        let closure = close_hol_rules(staged, bool_ty, &closures)
            .map_err(|source| resolver.kernel_error(source))?;
        let family_rules = Arc::from(closures);
        resolver.restore_scope(scoped);
        (closure, family_rules)
    };
    let family = builder
        .finish(closure)
        .map_err(|source| resolver.least_error(source))?;
    let definitions = relations
        .iter()
        .zip(family)
        .zip(relation_rules)
        .map(|((relation, least), rules)| {
            staged
                .eq(bool_ty, relation.predicate, least.predicate)
                .map(|equation| RelationalRelationDefinition {
                    predicate: relation.predicate,
                    least,
                    rules,
                    family_rules: Arc::clone(&family_rules),
                    equation,
                })
                .map_err(|source| resolver.kernel_error(source))
        })
        .collect::<Result<Vec<_>, _>>()?;
    *kernel = staged;
    Ok(definitions)
}

fn depends_on_any(kernel: &Kernel, root: Ref, needles: &[Ref]) -> bool {
    let needles = needles.iter().copied().collect::<BTreeSet<_>>();
    let mut seen = BTreeSet::new();
    let mut pending = vec![root];
    while let Some(reference) = pending.pop() {
        if needles.contains(&reference) {
            return true;
        }
        if seen.insert(reference)
            && let Some(children) = kernel.arena().children(reference)
        {
            pending.extend(children);
        }
    }
    false
}

fn ordered_rule_guard(
    kernel: &mut Kernel,
    bool_ty: Ref,
    preceding: Option<Ref>,
    current: &HolRule,
) -> Result<Ref, KernelError> {
    debug_assert_eq!(current.conclusion.len(), 1);
    let argument = current.conclusion[0];
    let Some(preceding) = preceding else {
        return kernel.bool(bool_ty, true);
    };
    let applicable = kernel.app(preceding, argument)?;
    kernel.op1(Op1::Not, applicable)
}

fn extend_ordered_applicability(
    kernel: &mut Kernel,
    bool_ty: Ref,
    preceding: Option<Ref>,
    rule: &HolRule,
) -> Result<Ref, KernelError> {
    debug_assert_eq!(rule.conclusion.len(), 1);
    let conclusion = rule.conclusion[0];
    let argument_ty = kernel.classifier(conclusion)?;
    let roots = rule
        .binders
        .iter()
        .chain(rule.premises.iter())
        .copied()
        .chain(preceding)
        .chain([conclusion, bool_ty])
        .collect::<Vec<_>>();
    let formal = kernel.tm_fv(kernel.fresh_name(&roots)?, argument_ty)?;
    let mut premises = rule.premises.clone();
    premises.push(kernel.eq(bool_ty, formal, conclusion)?);
    let current = existential_case(kernel, bool_ty, &rule.binders, &premises)?;
    let body = if let Some(preceding) = preceding {
        let prior = kernel.app(preceding, formal)?;
        kernel.op2(Op2::Or, prior, current)?
    } else {
        current
    };
    let predicate_ty = kernel.ty_arr(argument_ty, bool_ty)?;
    kernel.lam_at(predicate_ty, formal, body)
}

/// Decodes and lowers the complete recursive relation root containing `id`.
///
/// Non-relation members of a mixed recursive root are left for their respective
/// declaration lowerers. Every relation member is tied to its checked schema
/// slot, and all schema slots plus `avoid` are reserved for name hygiene.
///
/// # Errors
///
/// Returns an error when `id` is absent or not a relation, a family member has
/// no matching relation slot, relation names repeat within the root, a rule is
/// malformed, or family lowering fails. `kernel` is unchanged on failure.
#[allow(clippy::too_many_lines)] // Keeps exact root/schema checks at one authority boundary.
pub fn relational_relation_declaration<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &Source,
    schema: &HolSchema,
    id: DeclarationId,
    avoid: &[Ref],
) -> Result<Vec<RelationalRelationDefinition>, R::Error>
where
    R: RelationalResolver,
{
    let selected = source
        .il()
        .declarations()
        .iter()
        .find(|declaration| declaration.id() == id)
        .ok_or_else(|| {
            resolver.schema_error(IlSchemaError::Shape {
                id,
                path: Vec::new(),
                expected: "inventoried relation declaration",
                actual: "missing declaration".to_owned(),
            })
        })?;
    if selected.kind() != IlKind::Relation {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "relation declaration",
            actual: format!("{:?} declaration", selected.kind()),
        }));
    }
    let root = source
        .il()
        .roots()
        .iter()
        .find(|root| root.ordinal() == id.root())
        .ok_or_else(|| {
            resolver.schema_error(IlSchemaError::Shape {
                id,
                path: Vec::new(),
                expected: "containing relation root",
                actual: "missing root".to_owned(),
            })
        })?;
    let mut decoded = Vec::new();
    let mut names = BTreeSet::new();
    for member in source.il().root_declarations(root) {
        if member.kind() != IlKind::Relation {
            continue;
        }
        if !names.insert(member.name()) {
            return Err(resolver.schema_error(IlSchemaError::Shape {
                id: member.id(),
                path: Vec::new(),
                expected: "unique relation name within recursive root",
                actual: format!("duplicate name {:?}", member.name()),
            }));
        }
        let declaration = source
            .il()
            .schema(member.id())
            .map_err(|error| resolver.schema_error(error))?
            .ok_or_else(|| {
                resolver.schema_error(IlSchemaError::Shape {
                    id: member.id(),
                    path: Vec::new(),
                    expected: "inventoried relation schema",
                    actual: "missing declaration".to_owned(),
                })
            })?;
        let IlDeclarationBody::Relation { rules, .. } = declaration.body() else {
            return Err(resolver.schema_error(IlSchemaError::Shape {
                id: member.id(),
                path: Vec::new(),
                expected: "relation declaration body",
                actual: "different declaration body".to_owned(),
            }));
        };
        let target = schema.declaration(member.id()).ok_or_else(|| {
            resolver.schema_error(IlSchemaError::Shape {
                id: member.id(),
                path: Vec::new(),
                expected: "checked HOL relation slot",
                actual: "missing schema slot".to_owned(),
            })
        })?;
        if target.kind() != IlKind::Relation {
            return Err(resolver.schema_error(IlSchemaError::Shape {
                id: member.id(),
                path: Vec::new(),
                expected: "HOL relation slot",
                actual: format!("HOL {:?} slot", target.kind()),
            }));
        }
        let rules = rules
            .iter()
            .map(IlRuleSchema::decode)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| resolver.schema_error(error))?;
        decoded.push((member.name(), target.reference(), rules));
    }
    let relations = decoded
        .iter()
        .map(|(name, predicate, rules)| RelationalRelation {
            name,
            predicate: *predicate,
            rules,
        })
        .collect::<Vec<_>>();
    let reserved = schema
        .declarations()
        .map(|(_, declaration)| declaration.reference())
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
    relational_relations_avoiding(kernel, resolver, schema.bool_ty(), &relations, &reserved)
}

/// Concrete expression algebra producing relational HOL terms.
pub struct RelationalExpressionAlgebra<'a, R> {
    kernel: &'a mut Kernel,
    resolver: R,
    bool_ty: Ref,
    next_name: u64,
    binding_premises: Vec<Ref>,
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
            binding_premises: Vec::new(),
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
            if let Some(premise) = self
                .resolver
                .binding_premise(self.kernel, binding, reference)?
            {
                self.binding_premises.push(premise);
            }
            references.push(reference);
        }
        Ok(references)
    }

    /// Removes semantic premises accumulated by explicit bindings.
    #[must_use]
    pub fn take_binding_premises(&mut self) -> Vec<Ref> {
        std::mem::take(&mut self.binding_premises)
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

    fn pattern_argument(
        &mut self,
        argument: &IlArgument<'_>,
        formal: Ref,
    ) -> Result<RelationalTerm, R::Error>
    where
        R: RelationalResolver,
    {
        match argument {
            IlArgument::Expression(expression) => fold_expression(expression, self),
            IlArgument::Type(_) | IlArgument::Definition(_) | IlArgument::Grammar(_) => self
                .resolver
                .pattern_argument(self.kernel, argument, formal)
                .map(|value| RelationalTerm::new(value, Vec::new(), Vec::new())),
        }
    }

    /// Applies the resolver's type-membership interpretation.
    ///
    /// # Errors
    ///
    /// Returns an unresolved-type or checked application failure.
    pub fn type_membership(
        &mut self,
        ty: &covalence_data_spectec::IlType<'_>,
        value: Ref,
    ) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.type_membership(self.kernel, ty, value)
    }

    /// Allocates one deterministic fresh witness of `classifier`.
    ///
    /// # Errors
    ///
    /// Returns an error on name exhaustion or rejected checked construction.
    pub fn fresh_variable(&mut self, classifier: Ref) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        let name = self.take_name()?;
        self.kernel
            .tm_fv(name, classifier)
            .map_err(|source| self.resolver.kernel_error(source))
    }

    /// Resolves the embedded classifier of one IL type.
    ///
    /// # Errors
    ///
    /// Returns an error when the resolver cannot classify the decoded type.
    pub fn type_classifier(
        &mut self,
        ty: &covalence_data_spectec::IlType<'_>,
    ) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.type_classifier(self.kernel, ty)
    }

    /// Constructs one interpreted tuple value.
    ///
    /// # Errors
    ///
    /// Returns an unavailable-interpretation or checked application failure.
    pub fn tuple_value(&mut self, elements: &[Ref]) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.tuple_value(self.kernel, elements)
    }

    /// Constructs one interpreted variant value.
    ///
    /// # Errors
    ///
    /// Returns an unavailable-constructor or checked application failure.
    pub fn variant_value(&mut self, constructor: &str, payload: Ref) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver
            .variant_value(self.kernel, constructor, payload)
    }

    /// Constructs one interpreted struct value.
    ///
    /// # Errors
    ///
    /// Returns an unavailable-record or checked application failure.
    pub fn struct_value(&mut self, fields: &[(&str, Ref)]) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.struct_value(self.kernel, fields)
    }

    /// Constructs one interpreted grammar-symbol value.
    ///
    /// # Errors
    ///
    /// Returns an unresolved-symbol or checked application failure.
    pub fn grammar_value(
        &mut self,
        symbol: &covalence_data_spectec::IlGrammarSymbol<'_>,
        children: &[Ref],
    ) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.grammar_value(self.kernel, symbol, children)
    }

    /// Registers an existing term for one decoded binding.
    ///
    /// # Errors
    ///
    /// Returns a duplicate-name or incompatible-binding failure.
    pub fn register_binding(
        &mut self,
        binding: &IlBinding<'_>,
        reference: Ref,
    ) -> Result<(), R::Error>
    where
        R: RelationalResolver,
    {
        self.resolver.binding(binding, reference)?;
        if let Some(premise) = self
            .resolver
            .binding_premise(self.kernel, binding, reference)?
        {
            self.binding_premises.push(premise);
        }
        Ok(())
    }

    /// Converts an unsupported structural `otherwise` premise.
    pub fn type_otherwise(&mut self) -> R::Error
    where
        R: RelationalResolver,
    {
        self.resolver.type_otherwise()
    }

    /// Converts an unsupported grammar `otherwise` premise.
    pub fn grammar_otherwise(&mut self) -> R::Error
    where
        R: RelationalResolver,
    {
        self.resolver.grammar_otherwise()
    }

    /// Converts a structural schema failure through the resolver.
    pub fn schema_error(&mut self, source: IlSchemaError) -> R::Error
    where
        R: RelationalResolver,
    {
        self.resolver.schema_error(source)
    }

    /// Converts an exact family-assembly failure through the resolver.
    pub fn family_error(&mut self, source: HolFamilyError) -> R::Error
    where
        R: RelationalResolver,
    {
        self.resolver.family_error(source)
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
        let binding_premises = self.take_binding_premises();
        let patterns = schema
            .arguments()
            .iter()
            .zip(formal_inputs)
            .map(|(argument, &formal)| self.pattern_argument(argument, formal))
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
        let semantic_premises = binding_premises
            .into_iter()
            .chain(
                conditions
                    .iter()
                    .flat_map(|condition| condition.premises().iter().copied()),
            )
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
        let (rule, otherwise) = self.ordered_rule(schema)?;
        if otherwise {
            return Err(self.resolver.relation_otherwise());
        }
        Ok(rule)
    }

    fn ordered_rule(&mut self, schema: &IlRuleSchema<'_>) -> Result<(HolRule, bool), R::Error>
    where
        R: RelationalResolver,
    {
        let mut binders = self.bindings(schema.bindings())?;
        let mut premises = self.take_binding_premises();
        let conclusion = fold_expression(schema.conclusion(), self)?;
        binders.extend_from_slice(conclusion.binders());
        premises.extend_from_slice(conclusion.premises());
        let mut otherwise = false;
        for premise in schema.premises() {
            let condition = self.premise(premise)?;
            otherwise |= condition.otherwise();
            binders.extend_from_slice(condition.binders());
            premises.extend_from_slice(condition.premises());
        }
        Ok((
            HolRule::new(binders, premises, vec![conclusion.value()]),
            otherwise,
        ))
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

    fn enter(&mut self, expression: &IlExpression<'_>) -> Result<(), Self::Error> {
        self.resolver.enter_expression(self.kernel, expression)
    }

    fn leave(&mut self, expression: &IlExpression<'_>) -> Result<(), Self::Error> {
        self.resolver.leave_expression(expression)
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
        binders.extend(self.resolver.expression_binders(expression)?);
        Ok(RelationalTerm::new(value, binders, premises))
    }
}
