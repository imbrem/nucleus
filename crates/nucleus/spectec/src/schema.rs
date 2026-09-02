//! Checked HOL signature environment for the generic `SpecTec` schema.

use std::collections::BTreeMap;

use covalence_data_spectec::{
    DeclarationId, IlBinding, IlDeclarationBody, IlKind, IlSchemaError, IlType,
};
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

/// Compositional classifier embedding selected for `SpecTec` IL.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HolEmbedding {
    value: Ref,
    bool_ty: Ref,
}

impl HolEmbedding {
    /// Constructs an embedding from a shared value carrier and HOL Boolean.
    #[must_use]
    pub const fn new(value: Ref, bool_ty: Ref) -> Self {
        Self { value, bool_ty }
    }

    /// Returns the shared non-Boolean value carrier.
    #[must_use]
    pub const fn value(self) -> Ref {
        self.value
    }

    /// Returns the HOL Boolean classifier.
    #[must_use]
    pub const fn bool_ty(self) -> Ref {
        self.bool_ty
    }

    /// Erases one decoded IL type to its HOL classifier.
    #[must_use]
    pub const fn ty(self, ty: &IlType<'_>) -> Ref {
        match ty {
            IlType::Boolean => self.bool_ty,
            IlType::Named { .. }
            | IlType::Text
            | IlType::Numeric(_)
            | IlType::Tuple(_)
            | IlType::Iterated { .. } => self.value,
        }
    }

    /// Constructs the checked classifier of one explicit binding.
    ///
    /// Definition and grammar parameters remain predicates and are classified
    /// recursively; they are not collapsed into ordinary values.
    ///
    /// # Errors
    ///
    /// Returns an error when a checked function classifier cannot be built.
    pub fn binding(self, kernel: &mut Kernel, binding: &IlBinding<'_>) -> Result<Ref, KernelError> {
        match binding {
            IlBinding::Expression { ty, .. } => Ok(self.ty(ty)),
            IlBinding::Type { .. } => curry(kernel, &[self.value], self.bool_ty),
            IlBinding::Definition {
                parameters, result, ..
            } => {
                let mut domains = self.parameters(kernel, parameters)?;
                domains.push(self.ty(result));
                curry(kernel, &domains, self.bool_ty)
            }
            IlBinding::Grammar {
                parameters, result, ..
            } => {
                let mut domains = self.parameters(kernel, parameters)?;
                domains.push(self.value);
                domains.push(self.ty(result));
                curry(kernel, &domains, self.bool_ty)
            }
        }
    }

    fn parameters(
        self,
        kernel: &mut Kernel,
        parameters: &[IlBinding<'_>],
    ) -> Result<Vec<Ref>, KernelError> {
        parameters
            .iter()
            .map(|parameter| self.binding(kernel, parameter))
            .collect()
    }
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
    names: BTreeMap<IlKind, BTreeMap<String, Vec<DeclarationId>>>,
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

    /// Returns every structural selector carrying an exact kind-qualified name.
    ///
    /// Names are lookup metadata rather than trusted identity, so duplicate
    /// declarations remain visible in exact source order.
    #[must_use]
    pub fn named(&self, kind: IlKind, name: &str) -> &[DeclarationId] {
        self.names
            .get(&kind)
            .and_then(|declarations| declarations.get(name))
            .map_or(&[], Vec::as_slice)
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
    let mut names = BTreeMap::<IlKind, BTreeMap<String, Vec<DeclarationId>>>::new();
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
        let classifier = signature_type(
            &mut staged,
            schema.body(),
            HolEmbedding::new(value, bool_ty),
        )?;
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
        names
            .entry(declaration.kind())
            .or_default()
            .entry(declaration.name().to_owned())
            .or_default()
            .push(declaration.id());
    }
    *kernel = staged;
    Ok(HolSchema {
        policy: IndexErasure::ValuePredicate,
        value,
        bool_ty,
        declarations,
        names,
    })
}

fn signature_type(
    kernel: &mut Kernel,
    body: &IlDeclarationBody<'_>,
    embedding: HolEmbedding,
) -> Result<Ref, HolSchemaError> {
    let (domains, codomain) = match body {
        IlDeclarationBody::Type { parameters, .. } => {
            let mut domains = embedding
                .parameters(kernel, parameters)
                .map_err(|source| HolSchemaError::Kernel { source })?;
            domains.push(embedding.value);
            (domains, embedding.bool_ty)
        }
        IlDeclarationBody::Definition {
            parameters, result, ..
        } => {
            let result = erased_type(
                &IlType::decode(result).map_err(|source| HolSchemaError::Schema { source })?,
                embedding,
            );
            let mut domains = embedding
                .parameters(kernel, parameters)
                .map_err(|source| HolSchemaError::Kernel { source })?;
            domains.push(result);
            (domains, embedding.bool_ty)
        }
        IlDeclarationBody::Grammar {
            parameters, result, ..
        } => {
            let result = erased_type(
                &IlType::decode(result).map_err(|source| HolSchemaError::Schema { source })?,
                embedding,
            );
            let mut domains = embedding
                .parameters(kernel, parameters)
                .map_err(|source| HolSchemaError::Kernel { source })?;
            domains.push(embedding.value);
            domains.push(result);
            (domains, embedding.bool_ty)
        }
        IlDeclarationBody::Relation { argument, .. } => {
            let argument = erased_type(
                &IlType::decode(argument).map_err(|source| HolSchemaError::Schema { source })?,
                embedding,
            );
            (vec![argument], embedding.bool_ty)
        }
    };
    curry(kernel, &domains, codomain).map_err(|source| HolSchemaError::Kernel { source })
}

const fn erased_type(ty: &IlType<'_>, embedding: HolEmbedding) -> Ref {
    embedding.ty(ty)
}

fn curry(kernel: &mut Kernel, domains: &[Ref], codomain: Ref) -> Result<Ref, KernelError> {
    domains
        .iter()
        .rev()
        .try_fold(codomain, |tail, &domain| kernel.ty_arr(domain, tail))
}
