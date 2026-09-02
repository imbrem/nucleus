//! Exact HOL membership equations for structural `SpecTec` type families.

use covalence_data_spectec::{
    DeclarationId, IlDeclarationBody, IlExpression, IlKind, IlNode, IlPremise, IlSchemaError,
    IlType, IlTypeDefinition, IlTypeInstance,
};
use covalence_logic_hol::{Kernel, Ref};

use crate::{
    HolFamilyBranch, HolFamilyDefinition, HolSchema, RelationalExpressionAlgebra,
    RelationalResolver, Source, close_family_definition, fold_expression,
    relational::graph_domains,
};

/// Checked result of lowering an exact structural type-family declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalTypeDefinition {
    /// Universally quantified family indices followed by the candidate value.
    pub formal_arguments: Vec<Ref>,
    /// Exact checked family equation.
    pub definition: HolFamilyDefinition,
    /// First unused deterministic free-variable name.
    pub next_name: u64,
}

/// Decodes and lowers every structural instance of one selected type declaration.
///
/// Aliases preserve target membership. Variants preserve constructor payload
/// membership and side conditions. Structs preserve exact field order,
/// membership, and side conditions.
///
/// # Errors
///
/// Returns an error for an absent/non-type selector, a mismatched schema slot,
/// malformed indices or fields, name exhaustion, unresolved membership or
/// constructors, or checked family construction failure. `kernel` is unchanged
/// on failure.
#[allow(clippy::too_many_lines)] // One exact source/schema/instance authority boundary.
pub fn relational_type_declaration<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &Source,
    schema: &HolSchema,
    id: DeclarationId,
    avoid: &[Ref],
) -> Result<RelationalTypeDefinition, R::Error>
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
                expected: "inventoried type declaration",
                actual: "missing declaration".to_owned(),
            })
        })?;
    let target = schema.declaration(id).ok_or_else(|| {
        resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "checked HOL type-family slot",
            actual: "missing schema slot".to_owned(),
        })
    })?;
    let IlDeclarationBody::Type { instances, .. } = declaration.body() else {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "type declaration",
            actual: format!("{:?} declaration", target.kind()),
        }));
    };
    if target.kind() != IlKind::Type {
        return Err(resolver.schema_error(IlSchemaError::Shape {
            id,
            path: Vec::new(),
            expected: "HOL type-family slot",
            actual: format!("HOL {:?} slot", target.kind()),
        }));
    }

    let mut staged = kernel.fork();
    let predicate_type = staged
        .classifier(target.reference())
        .map_err(|error| resolver.kernel_error(error))?;
    let domains = graph_domains(&staged, predicate_type, schema.bool_ty())
        .map_err(|error| resolver.case_error(error))?;
    if domains.is_empty() {
        return Err(resolver.case_error(crate::RelationalCaseError::NotGraph));
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
    let Some((&formal_value, formal_indices)) = formal_arguments.split_last() else {
        return Err(resolver.case_error(crate::RelationalCaseError::NotGraph));
    };
    let mut branches = Vec::with_capacity(instances.len());
    for instance in instances {
        match instance.definition() {
            IlTypeDefinition::Alias(alias) => {
                let scope = resolver.clause_scope();
                let mut algebra = RelationalExpressionAlgebra::new(
                    &mut staged,
                    scope,
                    schema.bool_ty(),
                    next_name,
                );
                let mut binders = algebra.bindings(instance.bindings())?;
                let mut premises = Vec::new();
                let mut actual = lower_indices(
                    &mut algebra,
                    instance,
                    formal_indices.len(),
                    &mut binders,
                    &mut premises,
                )?;
                premises.push(algebra.type_membership(alias, formal_value)?);
                actual.push(formal_value);
                next_name = algebra.next_name();
                branches.push(HolFamilyBranch {
                    binders,
                    arguments: actual,
                    premises,
                });
            }
            IlTypeDefinition::Variant(cases) => {
                for case in cases {
                    let scope = resolver.clause_scope();
                    let mut algebra = RelationalExpressionAlgebra::new(
                        &mut staged,
                        scope,
                        schema.bool_ty(),
                        next_name,
                    );
                    let mut binders = algebra.bindings(instance.bindings())?;
                    binders.extend(algebra.bindings(case.bindings())?);
                    let mut premises = Vec::new();
                    let mut actual = lower_indices(
                        &mut algebra,
                        instance,
                        formal_indices.len(),
                        &mut binders,
                        &mut premises,
                    )?;
                    let payload =
                        lower_payload(&mut algebra, case.payload(), &mut binders, &mut premises)?;
                    append_side_conditions(
                        &mut algebra,
                        case.premises(),
                        &mut binders,
                        &mut premises,
                    )?;
                    actual.push(algebra.variant_value(case.name(), payload)?);
                    next_name = algebra.next_name();
                    branches.push(HolFamilyBranch {
                        binders,
                        arguments: actual,
                        premises,
                    });
                }
            }
            IlTypeDefinition::Struct(fields) => {
                let scope = resolver.clause_scope();
                let mut algebra = RelationalExpressionAlgebra::new(
                    &mut staged,
                    scope,
                    schema.bool_ty(),
                    next_name,
                );
                let mut binders = algebra.bindings(instance.bindings())?;
                let mut premises = Vec::new();
                let mut actual = lower_indices(
                    &mut algebra,
                    instance,
                    formal_indices.len(),
                    &mut binders,
                    &mut premises,
                )?;
                let mut values = Vec::with_capacity(fields.len());
                for field in fields {
                    let field_binders = algebra.bindings(field.bindings())?;
                    let [field_value] = field_binders.as_slice() else {
                        return Err(resolver.schema_error(IlSchemaError::Shape {
                            id,
                            path: Vec::new(),
                            expected: "struct field with exactly one value binding",
                            actual: format!("field with {} bindings", field_binders.len()),
                        }));
                    };
                    binders.push(*field_value);
                    premises.push(algebra.type_membership(field.value(), *field_value)?);
                    append_side_conditions(
                        &mut algebra,
                        field.premises(),
                        &mut binders,
                        &mut premises,
                    )?;
                    values.push((field.name(), *field_value));
                }
                actual.push(algebra.struct_value(&values)?);
                next_name = algebra.next_name();
                branches.push(HolFamilyBranch {
                    binders,
                    arguments: actual,
                    premises,
                });
            }
        }
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
    Ok(RelationalTypeDefinition {
        formal_arguments,
        definition,
        next_name,
    })
}

fn lower_indices<R>(
    algebra: &mut RelationalExpressionAlgebra<'_, R>,
    instance: &IlTypeInstance<'_>,
    expected: usize,
    binders: &mut Vec<Ref>,
    premises: &mut Vec<Ref>,
) -> Result<Vec<Ref>, R::Error>
where
    R: RelationalResolver,
{
    let arguments = instance
        .arguments()
        .iter()
        .map(|argument| algebra.argument(argument))
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.len() != expected {
        return Err(algebra.family_error(crate::HolFamilyError::Arity {
            expected,
            actual: arguments.len(),
        }));
    }
    Ok(arguments
        .into_iter()
        .map(|argument| {
            binders.extend_from_slice(argument.binders());
            premises.extend_from_slice(argument.premises());
            argument.value()
        })
        .collect())
}

fn lower_payload<R>(
    algebra: &mut RelationalExpressionAlgebra<'_, R>,
    ty: &IlType<'_>,
    binders: &mut Vec<Ref>,
    premises: &mut Vec<Ref>,
) -> Result<Ref, R::Error>
where
    R: RelationalResolver,
{
    if let IlType::Tuple(components) = ty {
        let mut elements = Vec::with_capacity(components.len());
        for component in components {
            let value = if component.binder().node() == IlNode::Symbol("_") {
                let classifier = algebra.type_classifier(component.ty())?;
                let witness = algebra.fresh_variable(classifier)?;
                binders.push(witness);
                witness
            } else {
                let expression = IlExpression::decode(component.binder())
                    .map_err(|error| algebra.schema_error(error))?;
                let term = fold_expression(&expression, algebra)?;
                binders.extend_from_slice(term.binders());
                premises.extend_from_slice(term.premises());
                term.value()
            };
            premises.push(algebra.type_membership(component.ty(), value)?);
            elements.push(value);
        }
        algebra.tuple_value(&elements)
    } else {
        let classifier = algebra.type_classifier(ty)?;
        let witness = algebra.fresh_variable(classifier)?;
        binders.push(witness);
        premises.push(algebra.type_membership(ty, witness)?);
        Ok(witness)
    }
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
            return Err(algebra.type_otherwise());
        }
        binders.extend_from_slice(condition.binders());
        premises.extend_from_slice(condition.premises());
    }
    Ok(())
}
