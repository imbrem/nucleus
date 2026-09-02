//! Transactional whole-document `SpecTec` semantics assembly.

use std::collections::{BTreeMap, BTreeSet};

use covalence_data_spectec::{DeclarationId, IlKind};
use covalence_logic_hol::{Kernel, Ref};

use crate::{
    HolSchema, HolTheory, RelationalResolver, Source, close_hol_theory,
    relational_definition_declaration, relational_grammar_declaration,
    relational_relation_declaration, relational_type_declaration,
};

/// Complete exact semantic constraints for one elaborated document.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RelationalDocumentDefinition {
    constraints: BTreeMap<DeclarationId, Ref>,
    theory: HolTheory,
}

impl RelationalDocumentDefinition {
    /// Returns exactly one checked constraint per structural declaration.
    #[must_use]
    pub const fn constraints(&self) -> &BTreeMap<DeclarationId, Ref> {
        &self.constraints
    }

    /// Returns the source-ordered conjunction of all declaration constraints.
    #[must_use]
    pub const fn theory(&self) -> &HolTheory {
        &self.theory
    }
}

/// Transactionally lowers every declaration in an exact source and checked
/// schema, then closes their constraints into one HOL model proposition.
///
/// Type, definition, and grammar declarations are dispatched individually.
/// Every recursive relation root is lowered exactly once and contributes one
/// slot equation per relation member. `avoid` reserves caller-owned primitive
/// interpretation roots throughout the pass.
///
/// # Errors
///
/// Returns the first type, definition, grammar, relation-family, exact-coverage,
/// or checked conjunction failure through the resolver's error vocabulary.
/// `kernel` is unchanged on failure.
pub fn relational_document<R>(
    kernel: &mut Kernel,
    resolver: &mut R,
    source: &Source,
    schema: &HolSchema,
    avoid: &[Ref],
) -> Result<RelationalDocumentDefinition, R::Error>
where
    R: RelationalResolver,
{
    let mut staged = kernel.fork();
    let mut constraints = BTreeMap::new();
    let mut lowered_relations = BTreeSet::new();
    for declaration in source.declarations() {
        let id = declaration.id();
        let constraint = match declaration.kind() {
            IlKind::Type => Some(
                relational_type_declaration(&mut staged, resolver, source, schema, id, avoid)
                    .map_err(|source| resolver.declaration_error(id, source))?
                    .definition
                    .equation,
            ),
            IlKind::Definition => Some(
                relational_definition_declaration(&mut staged, resolver, source, schema, id, avoid)
                    .map_err(|source| resolver.declaration_error(id, source))?
                    .equation,
            ),
            IlKind::Grammar => Some(
                relational_grammar_declaration(&mut staged, resolver, source, schema, id, avoid)
                    .map_err(|source| resolver.declaration_error(id, source))?
                    .definition
                    .equation,
            ),
            IlKind::Relation if lowered_relations.contains(&id) => None,
            IlKind::Relation => {
                let relation_ids = source
                    .declarations()
                    .iter()
                    .filter(|member| {
                        member.kind() == IlKind::Relation && member.id().root() == id.root()
                    })
                    .map(crate::SourceDeclaration::id)
                    .collect::<Vec<_>>();
                let definitions = relational_relation_declaration(
                    &mut staged,
                    resolver,
                    source,
                    schema,
                    id,
                    avoid,
                )
                .map_err(|source| resolver.declaration_error(id, source))?;
                if definitions.len() != relation_ids.len() {
                    return Err(resolver.family_error(crate::HolFamilyError::Arity {
                        expected: relation_ids.len(),
                        actual: definitions.len(),
                    }));
                }
                for (member, definition) in relation_ids.into_iter().zip(definitions) {
                    lowered_relations.insert(member);
                    constraints.insert(member, definition.equation);
                }
                None
            }
        };
        if let Some(constraint) = constraint {
            constraints.insert(id, constraint);
        }
    }
    let theory = close_hol_theory(source, &mut staged, schema.bool_ty(), &constraints)
        .map_err(|error| resolver.theory_error(error))?;
    *kernel = staged;
    Ok(RelationalDocumentDefinition {
        constraints,
        theory,
    })
}
