//! Relational HOL expression lowering over the generic expression fold.

use covalence_data_spectec::{IlBinding, IlExpression, IlExpressionKind, IlSchemaError};
use covalence_logic_hol::{Kernel, KernelError, Ref};

use crate::{ExpressionAlgebra, HolRule};

/// Relational meaning of one expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalTerm {
    value: Ref,
    binders: Vec<Ref>,
    premises: Vec<Ref>,
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

    /// Resolves one variable expression to a checked term.
    ///
    /// # Errors
    ///
    /// Returns an error for an unbound variable or incompatible target term.
    fn variable(
        &mut self,
        kernel: &mut Kernel,
        expression: &IlExpression<'_>,
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
        expression: &IlExpression<'_>,
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
        expression: &IlExpression<'_>,
        arguments: &[Ref],
    ) -> Result<Ref, Self::Error>;
}

/// Concrete expression algebra producing relational HOL terms.
pub struct RelationalExpressionAlgebra<'a, R> {
    kernel: &'a mut Kernel,
    resolver: R,
    value_ty: Ref,
    bool_ty: Ref,
    next_name: u64,
}

impl<'a, R> RelationalExpressionAlgebra<'a, R> {
    /// Starts a lowering with an explicit deterministic name range.
    #[must_use]
    pub const fn new(
        kernel: &'a mut Kernel,
        resolver: R,
        value_ty: Ref,
        bool_ty: Ref,
        first_name: u64,
    ) -> Self {
        Self {
            kernel,
            resolver,
            value_ty,
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
            let classifier = self.binding_type(binding)?;
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

    fn binding_type(&mut self, binding: &IlBinding<'_>) -> Result<Ref, R::Error>
    where
        R: RelationalResolver,
    {
        let domains = match binding {
            IlBinding::Expression { .. } => return Ok(self.value_ty),
            IlBinding::Type { .. } => vec![self.value_ty],
            IlBinding::Definition { parameters, .. } => {
                vec![self.value_ty; parameters.len() + 1]
            }
            IlBinding::Grammar { parameters, .. } => {
                vec![self.value_ty; parameters.len() + 2]
            }
        };
        domains
            .iter()
            .rev()
            .try_fold(self.bool_ty, |tail, &domain| {
                self.kernel
                    .ty_arr(domain, tail)
                    .map_err(|source| self.resolver.kernel_error(source))
            })
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
        let value = match expression.kind() {
            IlExpressionKind::Variable => self.resolver.variable(self.kernel, expression)?,
            IlExpressionKind::Call => {
                let prefix = self.resolver.call(self.kernel, expression, &values)?;
                let name = self.take_name()?;
                let result = self
                    .kernel
                    .tm_fv(name, self.value_ty)
                    .map_err(|source| self.resolver.kernel_error(source))?;
                let premise = self
                    .kernel
                    .app(prefix, result)
                    .map_err(|source| self.resolver.kernel_error(source))?;
                binders.push(result);
                premises.push(premise);
                result
            }
            _ => self.resolver.operation(self.kernel, expression, &values)?,
        };
        Ok(RelationalTerm::new(value, binders, premises))
    }
}
