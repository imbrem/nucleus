//! Target-independent fold over validated IL types.

use covalence_data_spectec::{
    IlArgument, IlCursor, IlExpression, IlIteration, IlNode, IlSchemaError, IlType,
};

use crate::{ExpressionAlgebra, fold_expression};

/// Already-folded heterogeneous argument of a named type.
pub enum TypeArgument<'a, Expression, Type> {
    /// Expression index.
    Expression(Expression),
    /// Type argument.
    Type(Type),
    /// Higher-order definition name.
    Definition(&'a str),
    /// Grammar-symbol argument retained in its parser-independent IL form.
    Grammar(&'a IlCursor<'a>),
}

/// Already-folded semantic children of one IL type.
pub enum TypeChildren<'a, Expression, Type> {
    /// Named type family and its heterogeneous arguments.
    Named {
        /// Exact family name.
        name: &'a str,
        /// Folded arguments in source order.
        arguments: Vec<TypeArgument<'a, Expression, Type>>,
    },
    /// Built-in Boolean type.
    Boolean,
    /// Built-in text type.
    Text,
    /// Built-in numeric type.
    Numeric(&'a str),
    /// Dependent tuple components. Ordinary product components have no binder.
    Tuple(Vec<(Option<Expression>, Type)>),
    /// Iterated element type and an optional folded fixed-length expression.
    Iterated {
        /// Folded element type.
        element: Box<Type>,
        /// Structural iteration form.
        iteration: &'a IlIteration<'a>,
        /// Folded length for fixed iteration, absent for opt/list/list1.
        length: Option<Expression>,
    },
}

/// Algebra receiving each type after all semantic children.
pub trait TypeAlgebra<Expression> {
    /// Target type produced by one node.
    type Type;
    /// Shared expression/schema/target failure.
    type Error;

    /// Converts a structural schema failure.
    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error;

    /// Combines one IL type with already-folded semantic children.
    ///
    /// # Errors
    ///
    /// Returns a target-specific failure when the type cannot be lowered.
    fn ty(
        &mut self,
        source: &IlType<'_>,
        children: TypeChildren<'_, Expression, Self::Type>,
    ) -> Result<Self::Type, Self::Error>;
}

/// Folds one complete IL type bottom-up with caller-supplied algebras.
///
/// # Errors
///
/// Returns the first expression, structural-schema, or target-type failure.
pub fn fold_type<E, T, X, Err>(
    ty: &IlType<'_>,
    expressions: &mut E,
    types: &mut T,
) -> Result<T::Type, Err>
where
    E: ExpressionAlgebra<Term = X, Error = Err>,
    T: TypeAlgebra<X, Error = Err>,
{
    let children = match ty {
        IlType::Named { name, arguments } => TypeChildren::Named {
            name,
            arguments: arguments
                .iter()
                .map(|argument| fold_argument(argument, expressions, types))
                .collect::<Result<Vec<_>, _>>()?,
        },
        IlType::Boolean => TypeChildren::Boolean,
        IlType::Text => TypeChildren::Text,
        IlType::Numeric(name) => TypeChildren::Numeric(name),
        IlType::Tuple(bindings) => TypeChildren::Tuple(
            bindings
                .iter()
                .map(|binding| {
                    let binder = if binding.binder().node() == IlNode::Symbol("_") {
                        None
                    } else {
                        let expression = IlExpression::decode(binding.binder())
                            .map_err(|source| types.schema_error(source))?;
                        Some(fold_expression(&expression, expressions)?)
                    };
                    let component = fold_type(binding.ty(), expressions, types)?;
                    Ok((binder, component))
                })
                .collect::<Result<Vec<_>, Err>>()?,
        ),
        IlType::Iterated { element, iteration } => {
            let length = match iteration {
                IlIteration::Fixed { length, .. } => {
                    let expression = IlExpression::decode(length)
                        .map_err(|source| types.schema_error(source))?;
                    Some(fold_expression(&expression, expressions)?)
                }
                IlIteration::Optional | IlIteration::List | IlIteration::NonEmptyList => None,
            };
            TypeChildren::Iterated {
                element: Box::new(fold_type(element, expressions, types)?),
                iteration,
                length,
            }
        }
    };
    types.ty(ty, children)
}

fn fold_argument<'a, E, T, X, Err>(
    argument: &'a IlArgument<'a>,
    expressions: &mut E,
    types: &mut T,
) -> Result<TypeArgument<'a, X, T::Type>, Err>
where
    E: ExpressionAlgebra<Term = X, Error = Err>,
    T: TypeAlgebra<X, Error = Err>,
{
    Ok(match argument {
        IlArgument::Expression(expression) => {
            TypeArgument::Expression(fold_expression(expression, expressions)?)
        }
        IlArgument::Type(ty) => TypeArgument::Type(fold_type(ty, expressions, types)?),
        IlArgument::Definition(name) => TypeArgument::Definition(name),
        IlArgument::Grammar(cursor) => TypeArgument::Grammar(cursor),
    })
}
