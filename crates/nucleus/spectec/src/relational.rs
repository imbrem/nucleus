//! Relational HOL expression lowering over the generic expression fold.

use covalence_data_spectec::{IlExpression, IlExpressionKind, IlSchemaError};
use covalence_logic_hol::{Kernel, KernelError, Ref};

use crate::ExpressionAlgebra;

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
    next_name: u64,
}

impl<'a, R> RelationalExpressionAlgebra<'a, R> {
    /// Starts a lowering with an explicit deterministic name range.
    #[must_use]
    pub const fn new(kernel: &'a mut Kernel, resolver: R, value_ty: Ref, first_name: u64) -> Self {
        Self {
            kernel,
            resolver,
            value_ty,
            next_name: first_name,
        }
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
                let name = self.next_name;
                self.next_name = self
                    .next_name
                    .checked_add(1)
                    .ok_or_else(|| self.resolver.name_exhausted())?;
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
