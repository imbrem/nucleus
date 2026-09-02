//! Exact HOL membership equations for structural `SpecTec` type families.

use covalence_data_spectec::{
    DeclarationId, IlDeclarationBody, IlKind, IlSchemaError, IlTypeDefinition,
};
use covalence_logic_hol::{Kernel, Ref};

use crate::{
    HolFamilyBranch, HolFamilyDefinition, HolSchema, RelationalExpressionAlgebra,
    RelationalResolver, Source, close_family_definition, relational::graph_domains,
};

/// Checked result of lowering an exact alias-only type-family declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalTypeDefinition {
    /// Universally quantified family indices followed by the candidate value.
    pub formal_arguments: Vec<Ref>,
    /// Exact checked family equation.
    pub definition: HolFamilyDefinition,
    /// First unused deterministic free-variable name.
    pub next_name: u64,
}

/// Decodes and lowers every alias instance of one selected type declaration.
///
/// Each instance becomes an existential branch matching its heterogeneous
/// family indices and requiring the candidate value to belong to the aliased
/// type. Variant and struct instances are deliberately rejected until their
/// constructor representation is supplied; they are never silently erased.
///
/// # Errors
///
/// Returns an error for an absent/non-type selector, a mismatched schema slot,
/// a variant or struct instance, malformed indices, name exhaustion, unresolved
/// membership, or checked family construction failure. `kernel` is unchanged
/// on failure.
#[allow(clippy::too_many_lines)] // One exact source/schema/instance authority boundary.
pub fn relational_type_alias_declaration<R>(
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
        let IlTypeDefinition::Alias(alias) = instance.definition() else {
            return Err(resolver.schema_error(IlSchemaError::Shape {
                id,
                path: Vec::new(),
                expected: "alias type instance",
                actual: "variant or struct type instance".to_owned(),
            }));
        };
        let scope = resolver.clause_scope();
        let mut algebra =
            RelationalExpressionAlgebra::new(&mut staged, scope, schema.bool_ty(), next_name);
        let mut binders = algebra.bindings(instance.bindings())?;
        let arguments = instance
            .arguments()
            .iter()
            .map(|argument| algebra.argument(argument))
            .collect::<Result<Vec<_>, _>>()?;
        if arguments.len() != formal_indices.len() {
            return Err(resolver.family_error(crate::HolFamilyError::Arity {
                expected: formal_indices.len(),
                actual: arguments.len(),
            }));
        }
        let mut premises = Vec::new();
        let mut actual = Vec::with_capacity(formal_arguments.len());
        for argument in arguments {
            binders.extend_from_slice(argument.binders());
            premises.extend_from_slice(argument.premises());
            actual.push(argument.value());
        }
        premises.push(algebra.type_membership(alias, formal_value)?);
        actual.push(formal_value);
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
    Ok(RelationalTypeDefinition {
        formal_arguments,
        definition,
        next_name,
    })
}
