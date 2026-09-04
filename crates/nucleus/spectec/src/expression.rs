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

    /// Enters the lexical scope of one expression before visiting children.
    ///
    /// The default has no effect. Binder-aware algebras can use this for
    /// iteration domains and restore their environment in [`leave`](Self::leave).
    ///
    /// # Errors
    ///
    /// Returns a target-specific scope-establishment failure.
    fn enter(&mut self, _expression: &IlExpression<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Leaves a scope previously established by [`enter`](Self::enter).
    ///
    /// This is called even when child lowering fails.
    ///
    /// # Errors
    ///
    /// Returns a target-specific scope-restoration failure.
    fn leave(&mut self, _expression: &IlExpression<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

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
    algebra.enter(expression)?;
    let result = (|| {
        let children = expression
            .children()
            .map_err(|source| algebra.schema_error(source))?
            .iter()
            .map(|child| fold_expression(child, algebra))
            .collect::<Result<Vec<_>, _>>()?;
        algebra.expression(expression, children)
    })();
    let leave = algebra.leave(expression);
    match (result, leave) {
        (Err(error), _) | (Ok(_), Err(error)) => Err(error),
        (Ok(term), Ok(())) => Ok(term),
    }
}
