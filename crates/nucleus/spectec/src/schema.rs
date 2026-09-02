//! Checked HOL signature environment for the generic `SpecTec` schema.

use std::collections::BTreeMap;

use covalence_data_spectec::{DeclarationId, IlDeclarationBody, IlKind, IlSchemaError, IlType};
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref};

use crate::Source;

/// Explicit embedding policy for dependent `SpecTec` types in HOL.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IndexErasure {
    /// All non-Boolean values share one HOL carrier; each `typ` declaration is
    /// represented by a membership predicate over that carrier.
    ValuePredicate,
}

/// Checked target signature for one source declaration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HolDeclaration {
    kind: IlKind,
    reference: Ref,
}

impl HolDeclaration {
    /// Returns the source declaration category.
    #[must_use]
    pub const fn kind(self) -> IlKind {
        self.kind
    }

    /// Returns the checked semantic-predicate slot.
    #[must_use]
    pub const fn reference(self) -> Ref {
        self.reference
    }
}

/// Complete checked signature environment awaiting semantic bodies.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HolSchema {
    policy: IndexErasure,
    value: Ref,
    bool_ty: Ref,
    declarations: BTreeMap<DeclarationId, HolDeclaration>,
}

impl HolSchema {
    /// Returns the explicit dependent-index embedding policy.
    #[must_use]
    pub const fn policy(&self) -> IndexErasure {
        self.policy
    }

    /// Returns the shared non-Boolean value carrier.
    #[must_use]
    pub const fn value(&self) -> Ref {
        self.value
    }

    /// Returns the exact HOL Boolean type.
    #[must_use]
    pub const fn bool_ty(&self) -> Ref {
        self.bool_ty
    }

    /// Resolves one declaration by stable structural selector.
    #[must_use]
    pub fn declaration(&self, id: DeclarationId) -> Option<HolDeclaration> {
        self.declarations.get(&id).copied()
    }

    /// Returns the number of checked declaration signatures.
    #[must_use]
    pub fn len(&self) -> usize {
        self.declarations.len()
    }

    /// Returns whether no declaration signatures are present.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.declarations.is_empty()
    }
}

/// Why generic schema signatures could not be constructed in HOL.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum HolSchemaError {
    /// A source declaration did not match the generic IL schema.
    #[snafu(display("could not decode SpecTec declaration schema: {source}"))]
    Schema {
        /// Underlying structural failure.
        source: IlSchemaError,
    },
    /// A checked HOL constructor rejected the embedding.
    #[snafu(display("could not construct SpecTec HOL signature: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
}

/// Constructs checked target signatures for every source declaration.
///
/// This is a transactional preparation stage, not a completed semantics. Type
/// declarations become parameterized membership predicates; definitions become
/// input/output graph predicates; grammars become input/output predicates; and
/// relations become predicates. Semantic bodies must replace these slots before
/// a direct compilation can finish.
///
/// # Errors
///
/// Returns an error if any of the 980 pinned declarations fails generic schema
/// decoding, `value` is not a type of kind `star`, `bool_ty` is not the checked
/// Boolean type, or a signature constructor is rejected. `kernel` is unchanged
/// on failure.
pub fn declare_hol_schema(
    source: &Source,
    kernel: &mut Kernel,
    value: Ref,
    bool_ty: Ref,
) -> Result<HolSchema, HolSchemaError> {
    let mut staged = kernel.fork();
    staged
        .bool(bool_ty, false)
        .map_err(|source| HolSchemaError::Kernel { source })?;
    let value_identity = staged
        .ty_arr(value, value)
        .map_err(|source| HolSchemaError::Kernel { source })?;
    let mut roots = vec![value, bool_ty, value_identity];
    let mut declarations = BTreeMap::new();
    for declaration in source.il().declarations() {
        let schema = source
            .il()
            .schema(declaration.id())
            .map_err(|source| HolSchemaError::Schema { source })?
            .ok_or_else(|| HolSchemaError::Schema {
                source: IlSchemaError::Shape {
                    id: declaration.id(),
                    path: Vec::new(),
                    expected: "inventoried declaration schema",
                    actual: "missing".to_owned(),
                },
            })?;
        let classifier = signature_type(&mut staged, schema.body(), value, bool_ty)?;
        let name = staged
            .fresh_name(&roots)
            .map_err(|source| HolSchemaError::Kernel { source })?;
        let reference = staged
            .tm_fv(name, classifier)
            .map_err(|source| HolSchemaError::Kernel { source })?;
        roots.push(reference);
        declarations.insert(
            declaration.id(),
            HolDeclaration {
                kind: declaration.kind(),
                reference,
            },
        );
    }
    *kernel = staged;
    Ok(HolSchema {
        policy: IndexErasure::ValuePredicate,
        value,
        bool_ty,
        declarations,
    })
}

fn signature_type(
    kernel: &mut Kernel,
    body: &IlDeclarationBody<'_>,
    value: Ref,
    bool_ty: Ref,
) -> Result<Ref, HolSchemaError> {
    let (domains, codomain) = match body {
        IlDeclarationBody::Type { parameters, .. } => (vec![value; parameters.len() + 1], bool_ty),
        IlDeclarationBody::Definition {
            parameters, result, ..
        } => {
            let result = erased_type(
                &IlType::decode(result).map_err(|source| HolSchemaError::Schema { source })?,
                value,
                bool_ty,
            );
            let mut domains = vec![value; parameters.len()];
            domains.push(result);
            (domains, bool_ty)
        }
        IlDeclarationBody::Grammar {
            parameters, result, ..
        } => {
            let result = erased_type(
                &IlType::decode(result).map_err(|source| HolSchemaError::Schema { source })?,
                value,
                bool_ty,
            );
            let mut domains = vec![value; parameters.len() + 1];
            domains.push(result);
            (domains, bool_ty)
        }
        IlDeclarationBody::Relation { argument, .. } => {
            let argument = erased_type(
                &IlType::decode(argument).map_err(|source| HolSchemaError::Schema { source })?,
                value,
                bool_ty,
            );
            (vec![argument], bool_ty)
        }
    };
    curry(kernel, &domains, codomain)
}

const fn erased_type(ty: &IlType<'_>, value: Ref, bool_ty: Ref) -> Ref {
    match ty {
        IlType::Boolean => bool_ty,
        IlType::Named { .. }
        | IlType::Text
        | IlType::Numeric(_)
        | IlType::Tuple(_)
        | IlType::Iterated { .. } => value,
    }
}

fn curry(kernel: &mut Kernel, domains: &[Ref], codomain: Ref) -> Result<Ref, HolSchemaError> {
    domains.iter().rev().try_fold(codomain, |tail, &domain| {
        kernel
            .ty_arr(domain, tail)
            .map_err(|source| HolSchemaError::Kernel { source })
    })
}
