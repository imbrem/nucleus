//! Target-independent fold over validated IL grammar symbols.

use covalence_data_spectec::{IlArgument, IlGrammarSymbol, IlSchemaError};

use crate::{ExpressionAlgebra, TypeAlgebra, fold_expression, fold_type};

/// Already-folded heterogeneous argument of a grammar variable.
pub enum GrammarArgument<'a, Expression, Type, Grammar> {
    /// Expression argument.
    Expression(Expression),
    /// Type argument.
    Type(Type),
    /// Higher-order definition name.
    Definition(&'a str),
    /// Grammar-symbol argument.
    Grammar(Grammar),
}

/// Already-folded semantic children of one grammar symbol.
pub enum GrammarChildren<'a, Expression, Type, Grammar> {
    /// Empty input.
    Empty,
    /// Exact text terminal.
    Text(&'a str),
    /// Exact numeric terminal spelling.
    Number(&'a str),
    /// Ordered concatenation.
    Sequence(Vec<Grammar>),
    /// Ordered alternatives.
    Alternative(Vec<Grammar>),
    /// Inclusive numeric terminal range.
    Range {
        /// Lower endpoint spelling.
        lower: &'a str,
        /// Upper endpoint spelling.
        upper: &'a str,
    },
    /// Synthesized attribute attached to a symbol.
    Attribute {
        /// Folded attribute expression.
        value: Expression,
        /// Folded underlying grammar symbol.
        symbol: Box<Grammar>,
    },
    /// Iterated symbol and folded named domain expressions.
    Iterated {
        /// Folded repeated symbol.
        symbol: Box<Grammar>,
        /// Folded domains in source order.
        domains: Vec<(&'a str, Expression)>,
    },
    /// Grammar declaration or parameter reference.
    Variable {
        /// Exact grammar name.
        name: &'a str,
        /// Folded heterogeneous arguments.
        arguments: Vec<GrammarArgument<'a, Expression, Type, Grammar>>,
    },
}

/// Algebra receiving each grammar symbol after all semantic children.
pub trait GrammarAlgebra<Expression, Type> {
    /// Target grammar symbol produced by one node.
    type Grammar;
    /// Shared expression/type/schema/target failure.
    type Error;

    /// Converts a structural schema failure.
    fn schema_error(&mut self, source: IlSchemaError) -> Self::Error;

    /// Combines a symbol with its already-folded semantic children.
    ///
    /// # Errors
    ///
    /// Returns a target-specific failure when the symbol cannot be lowered.
    fn grammar(
        &mut self,
        source: &IlGrammarSymbol<'_>,
        children: GrammarChildren<'_, Expression, Type, Self::Grammar>,
    ) -> Result<Self::Grammar, Self::Error>;
}

/// Folds one complete grammar symbol bottom-up.
///
/// # Errors
///
/// Returns the first expression, type, schema, or target-grammar failure.
pub fn fold_grammar<E, T, G, X, Y, Err>(
    symbol: &IlGrammarSymbol<'_>,
    expressions: &mut E,
    types: &mut T,
    grammars: &mut G,
) -> Result<G::Grammar, Err>
where
    E: ExpressionAlgebra<Term = X, Error = Err>,
    T: TypeAlgebra<X, Type = Y, Error = Err>,
    G: GrammarAlgebra<X, Y, Error = Err>,
{
    let children = match symbol {
        IlGrammarSymbol::Empty => GrammarChildren::Empty,
        IlGrammarSymbol::Text(value) => GrammarChildren::Text(value),
        IlGrammarSymbol::Number(value) => GrammarChildren::Number(value),
        IlGrammarSymbol::Sequence(symbols) => GrammarChildren::Sequence(
            symbols
                .iter()
                .map(|child| fold_grammar(child, expressions, types, grammars))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        IlGrammarSymbol::Alternative(symbols) => GrammarChildren::Alternative(
            symbols
                .iter()
                .map(|child| fold_grammar(child, expressions, types, grammars))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        IlGrammarSymbol::Range { lower, upper } => GrammarChildren::Range { lower, upper },
        IlGrammarSymbol::Attribute { value, symbol } => GrammarChildren::Attribute {
            value: fold_expression(value, expressions)?,
            symbol: Box::new(fold_grammar(symbol, expressions, types, grammars)?),
        },
        IlGrammarSymbol::Iterated {
            symbol, domains, ..
        } => GrammarChildren::Iterated {
            symbol: Box::new(fold_grammar(symbol, expressions, types, grammars)?),
            domains: domains
                .iter()
                .map(|domain| {
                    fold_expression(domain.expression(), expressions)
                        .map(|value| (domain.name(), value))
                })
                .collect::<Result<Vec<_>, _>>()?,
        },
        IlGrammarSymbol::Variable { name, arguments } => GrammarChildren::Variable {
            name,
            arguments: arguments
                .iter()
                .map(|argument| fold_argument(argument, expressions, types, grammars))
                .collect::<Result<Vec<_>, _>>()?,
        },
    };
    grammars.grammar(symbol, children)
}

fn fold_argument<'a, E, T, G, X, Y, Err>(
    argument: &'a IlArgument<'a>,
    expressions: &mut E,
    types: &mut T,
    grammars: &mut G,
) -> Result<GrammarArgument<'a, X, Y, G::Grammar>, Err>
where
    E: ExpressionAlgebra<Term = X, Error = Err>,
    T: TypeAlgebra<X, Type = Y, Error = Err>,
    G: GrammarAlgebra<X, Y, Error = Err>,
{
    Ok(match argument {
        IlArgument::Expression(expression) => {
            GrammarArgument::Expression(fold_expression(expression, expressions)?)
        }
        IlArgument::Type(ty) => GrammarArgument::Type(fold_type(ty, expressions, types)?),
        IlArgument::Definition(name) => GrammarArgument::Definition(name),
        IlArgument::Grammar(symbol) => {
            GrammarArgument::Grammar(fold_grammar(symbol, expressions, types, grammars)?)
        }
    })
}
