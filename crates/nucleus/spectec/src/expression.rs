//! Target-independent fold over validated IL expressions.

use covalence_data_spectec::{IlExpression, IlSchemaError};

/// Algebra receiving each expression after its semantic children.
pub trait ExpressionAlgebra {
    /// Target term produced for one expression.
    type Term;
    /// Target-specific or schema failure.
    type Error;

    /// Converts a structural schema failure into the algebra's error type.
    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error;

    /// Combines one validated node with already-folded direct children.
    ///
    /// # Errors
    ///
    /// Returns a target-specific error when this algebra cannot lower the
    /// supplied constructor and children.
    fn expression(
        &mut self,
        expression: &IlExpression<'_>,
        children: Vec<Self::Term>,
    ) -> Result<Self::Term, Self::Error>;
}

/// Folds one complete expression bottom-up with a caller-supplied algebra.
///
/// # Errors
///
/// Returns the algebra's conversion of the first structural schema error, or
/// the first target-specific error returned by the algebra itself.
pub fn fold_expression<A: ExpressionAlgebra>(
    expression: &IlExpression<'_>,
    algebra: &mut A,
) -> Result<A::Term, A::Error> {
    let children = expression
        .children()
        .map_err(|source| algebra.schema_error(source))?
        .iter()
        .map(|child| fold_expression(child, algebra))
        .collect::<Result<Vec<_>, _>>()?;
    algebra.expression(expression, children)
}
