//! Exact HOL graph equations for `SpecTec` attribute grammars.

use covalence_data_spectec::{
    DeclarationId, IlArgument, IlDeclarationBody, IlExpression, IlGrammarSymbol, IlIteration,
    IlKind, IlPremise, IlProductionSchema, IlSchemaError,
};
use covalence_logic_hol::{Kernel, Ref};

use crate::{
    HolFamilyBranch, HolFamilyDefinition, HolSchema, RelationalExpressionAlgebra,
    RelationalResolver, RelationalTerm, Source, close_family_definition, fold_expression,
    relational::graph_domains,
};

/// Checked exact definition of one attribute-grammar slot.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalGrammarDefinition {
    /// Declaration parameters, grammar input, and synthesized result.
    pub formal_arguments: Vec<Ref>,
    /// Exact disjunction of lowered production branches.
    pub definition: HolFamilyDefinition,
    /// First unused deterministic free-variable name.
    pub next_name: u64,
}

/// Decodes and lowers one complete grammar declaration selected from the exact
/// source and checked schema.
///
/// Each production becomes an existential branch. Declaration parameters are
/// registered against their universal schema variables, the complete grammar
/// symbol is interpreted bottom-up, and synthesized expressions and premises
/// retain their relational call dependencies.
///
/// # Errors
///
/// Returns an error for an absent/non-grammar selector, a mismatched schema
/// slot or arity, malformed production/symbol, unresolved interpretation,
/// unsupported `otherwise`, name exhaustion, or checked family failure.
/// `kernel` is unchanged on failure.
#[allow(clippy::too_many_lines)] // One exact source/schema/production authority boundary.
pub fn relational_grammar_declaration<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &Source,
    schema: &HolSchema,
    id: DeclarationId,
    avoid: &[Ref],
) -> Result<RelationalGrammarDefinition, R::Error>
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
                expected: "inventoried grammar declaration",
                actual: "missing declaration".to_owned(),
            })
        })?;
    let target = schema.declaration(id).ok_or_else(|| {
        resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "checked HOL grammar slot",
            actual: "missing schema slot".to_owned(),
        })
    })?;
    let IlDeclarationBody::Grammar {
        parameters,
        productions,
        ..
    } = declaration.body()
    else {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "grammar declaration",
            actual: format!("{:?} declaration", target.kind()),
        }));
    };
    if target.kind() != IlKind::Grammar {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "HOL grammar slot",
            actual: format!("HOL {:?} slot", target.kind()),
        }));
    }
    let productions = productions
        .iter()
        .map(IlProductionSchema::decode)
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| resolver.schema_error(error))?;

    let mut staged = kernel.fork();
    let predicate_type = staged
        .classifier(target.reference())
        .map_err(|error| resolver.kernel_error(error))?;
    let domains = graph_domains(&staged, predicate_type, schema.bool_ty())
        .map_err(|error| resolver.case_error(error))?;
    if domains.len() < 2 || domains.len() - 2 != parameters.len() {
        return Err(resolver.family_error(crate::HolFamilyError::Arity {
            expected: parameters.len() + 2,
            actual: domains.len(),
        }));
    }
    let reserved = schema
        .declarations()
        .map(|(_, declaration)| declaration.reference())
        .chain(avoid.iter().copied())
        .collect::<Vec<_>>();
    let mut next_name = staged
        .fresh_name(&reserved)
        .map_err(|error| resolver.kernel_error(error))?;
    let mut formal_arguments = Vec::with_capacity(domains.len());
    for domain in domains {
        formal_arguments.push(
            staged
                .tm_fv(next_name, domain)
                .map_err(|error| resolver.kernel_error(error))?,
        );
        next_name = next_name
            .checked_add(1)
            .ok_or_else(|| resolver.name_exhausted())?;
    }
    let parameter_count = parameters.len();
    let formal_parameters = &formal_arguments[..parameter_count];
    let mut branches = Vec::with_capacity(productions.len());
    for production in &productions {
        let scope = resolver.clause_scope();
        let mut algebra =
            RelationalExpressionAlgebra::new(&mut staged, scope, schema.bool_ty(), next_name);
        for (binding, &formal) in parameters.iter().zip(formal_parameters) {
            algebra.register_binding(binding, formal)?;
        }
        let mut binders = algebra.bindings(production.bindings())?;
        let binding_premises = algebra.take_binding_premises();
        let symbol = lower_symbol(&mut algebra, production.symbol())?;
        let result = fold_expression(production.result(), &mut algebra)?;
        binders.extend_from_slice(symbol.binders());
        binders.extend_from_slice(result.binders());
        let mut premises = binding_premises;
        premises.extend_from_slice(symbol.premises());
        premises.extend_from_slice(result.premises());
        append_side_conditions(
            &mut algebra,
            production.premises(),
            &mut binders,
            &mut premises,
        )?;
        let mut actual = formal_parameters.to_vec();
        actual.push(symbol.value());
        actual.push(result.value());
        next_name = algebra.next_name();
        branches.push(HolFamilyBranch {
            binders,
            arguments: actual,
            premises,
        });
    }
    let definition = close_family_definition(
        &mut staged,
        schema.bool_ty(),
        target.reference(),
        &formal_arguments,
        &branches,
    )
    .map_err(|error| resolver.family_error(error))?;
    *kernel = staged;
    Ok(RelationalGrammarDefinition {
        formal_arguments,
        definition,
        next_name,
    })
}

fn lower_symbol<R>(
    algebra: &mut RelationalExpressionAlgebra<'_, R>,
    symbol: &IlGrammarSymbol<'_>,
) -> Result<RelationalTerm, R::Error>
where
    R: RelationalResolver,
{
    let mut terms = Vec::new();
    match symbol {
        IlGrammarSymbol::Empty
        | IlGrammarSymbol::Text(_)
        | IlGrammarSymbol::Number(_)
        | IlGrammarSymbol::Range { .. } => {}
        IlGrammarSymbol::Sequence(symbols) | IlGrammarSymbol::Alternative(symbols) => {
            for child in symbols {
                terms.push(lower_symbol(algebra, child)?);
            }
        }
        IlGrammarSymbol::Attribute { value, symbol } => {
            terms.push(fold_expression(value, algebra)?);
            terms.push(lower_symbol(algebra, symbol)?);
        }
        IlGrammarSymbol::Iterated {
            symbol,
            iteration,
            domains,
        } => {
            terms.push(lower_symbol(algebra, symbol)?);
            if let IlIteration::Fixed { length, .. } = iteration {
                let expression =
                    IlExpression::decode(length).map_err(|error| algebra.schema_error(error))?;
                terms.push(fold_expression(&expression, algebra)?);
            }
            for domain in domains {
                terms.push(fold_expression(domain.expression(), algebra)?);
            }
        }
        IlGrammarSymbol::Variable { arguments, .. } => {
            for argument in arguments {
                terms.push(match argument {
                    IlArgument::Grammar(symbol) => lower_symbol(algebra, symbol)?,
                    IlArgument::Expression(_) | IlArgument::Type(_) | IlArgument::Definition(_) => {
                        algebra.argument(argument)?
                    }
                });
            }
        }
    }
    let mut binders = Vec::new();
    let mut premises = Vec::new();
    let values = terms
        .into_iter()
        .map(|term| {
            binders.extend_from_slice(term.binders());
            premises.extend_from_slice(term.premises());
            term.value()
        })
        .collect::<Vec<_>>();
    let value = algebra.grammar_value(symbol, &values)?;
    Ok(RelationalTerm::new(value, binders, premises))
}

fn append_side_conditions<R>(
    algebra: &mut RelationalExpressionAlgebra<'_, R>,
    source: &[IlPremise<'_>],
    binders: &mut Vec<Ref>,
    premises: &mut Vec<Ref>,
) -> Result<(), R::Error>
where
    R: RelationalResolver,
{
    for premise in source {
        let condition = algebra.premise(premise)?;
        if condition.otherwise() {
            return Err(algebra.grammar_otherwise());
        }
        binders.extend_from_slice(condition.binders());
        premises.extend_from_slice(condition.premises());
    }
    Ok(())
}
