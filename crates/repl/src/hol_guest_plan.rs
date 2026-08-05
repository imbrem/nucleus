//! Canonical, bounded, untrusted HOL guest plans and checked replay.
//!
//! Executors can construct or transport these bytes without receiving a
//! database, theorem, signer, or kernel capability. Nucleus authority begins
//! only when the key-holding service independently decodes and replays a plan.

use std::collections::HashSet;
use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::{
    Connection, ContextId, ExportId, Hol, Kernel, NamespaceExport, NamespaceId, Operation, Policy,
    SignedHolSnapshot, TermId, Theorem, TypeId,
};

use crate::SignedHolArtifact;

pub(crate) const MAX_RECIPE_NODES: usize = 128;
pub(crate) const MAX_RECIPE_NAME_BYTES: usize = 256;
/// Maximum canonical bytes accepted from an untrusted guest executor.
pub const MAX_SEALED_HOL_RECIPE_BYTES: usize = 64 * 1024;

const RECIPE_VERSION: u8 = 0;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RecipeSort {
    Type,
    Term,
    Context,
    Theorem,
    Namespace,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RecipeNode {
    BoolType,
    Bound {
        index: u32,
        ty: usize,
    },
    Lambda {
        parameter_type: usize,
        body: usize,
    },
    Bool(bool),
    EmptyContext,
    Beta {
        context: usize,
        abstraction: usize,
        argument: usize,
    },
    Persist {
        theorem: usize,
    },
    Namespace {
        name: Option<String>,
    },
    ExportTheorem {
        namespace: usize,
        export: i64,
        theorem: usize,
        name: Option<String>,
    },
    ExportContext {
        namespace: usize,
        export: i64,
        context: usize,
        name: Option<String>,
    },
}

/// A canonical, bounded recipe which carries no proof authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SealedHolProofRecipe {
    bytes: Vec<u8>,
    nodes: Vec<RecipeNode>,
    selected_namespace: usize,
}

impl SealedHolProofRecipe {
    /// Decodes and structurally validates canonical bytes from an untrusted executor.
    ///
    /// This checks the byte and node bounds, exact tags, UTF-8/name bounds, backward
    /// dependencies and sorts, theorem persistence before export, the selected
    /// namespace, trailing bytes, and canonical re-encoding. It proves no theorem.
    ///
    /// # Errors
    ///
    /// Returns an error for any malformed, oversized, non-canonical, or
    /// structurally inconsistent recipe.
    pub fn from_untrusted_bytes(bytes: &[u8]) -> Result<Self, HolProofRecipeError> {
        if bytes.len() > MAX_SEALED_HOL_RECIPE_BYTES {
            return Err(HolProofRecipeError::Invalid(
                "sealed recipe exceeds byte limit",
            ));
        }
        let mut decoder = Decoder::new(bytes);
        if decoder.byte()? != RECIPE_VERSION {
            return Err(HolProofRecipeError::Invalid(
                "unsupported sealed recipe version",
            ));
        }
        let count = usize::from(decoder.u16()?);
        if count > MAX_RECIPE_NODES {
            return Err(HolProofRecipeError::Invalid(
                "sealed recipe exceeds node limit",
            ));
        }
        let selected_namespace = usize::from(decoder.u16()?);
        let mut nodes = Vec::with_capacity(count);
        for _ in 0..count {
            nodes.push(decoder.node()?);
        }
        decoder.finish()?;
        validate_structure(&nodes, selected_namespace)?;
        let canonical = encode(&nodes, selected_namespace)?;
        if canonical != bytes {
            return Err(HolProofRecipeError::Invalid(
                "sealed recipe is not canonical",
            ));
        }
        Ok(Self {
            bytes: canonical,
            nodes,
            selected_namespace,
        })
    }

    /// Returns the exact canonical representation safe to move across an
    /// untrusted subprocess, Worker, or machine boundary.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    #[cfg(any(not(target_arch = "wasm32"), test))]
    pub(crate) fn seal(
        nodes: Vec<RecipeNode>,
        selected_namespace: usize,
    ) -> Result<Self, HolProofRecipeError> {
        validate_structure(&nodes, selected_namespace)?;
        let bytes = encode(&nodes, selected_namespace)?;
        Ok(Self {
            bytes,
            nodes,
            selected_namespace,
        })
    }

    pub(crate) fn replay(&self, kernel: &Kernel) -> Result<SignedHolArtifact, HolProofRecipeError> {
        replay(kernel, &self.nodes, self.selected_namespace)
    }
}

/// Rejection while decoding or replaying an untrusted HOL proof recipe.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum HolProofRecipeError {
    /// The representation or dependency graph is malformed.
    Invalid(&'static str),
    /// Checked insertion, proof replay, export, or signing failed.
    Replay(String),
    /// The resulting signed database exceeds the shared artifact bound.
    ArtifactTooLarge { size: usize, maximum: usize },
}

impl fmt::Display for HolProofRecipeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(message) => write!(formatter, "invalid sealed HOL recipe: {message}"),
            Self::Replay(message) => write!(formatter, "HOL recipe replay failed: {message}"),
            Self::ArtifactTooLarge { size, maximum } => {
                write!(
                    formatter,
                    "signed artifact is {size} bytes; maximum is {maximum}"
                )
            }
        }
    }
}

impl StdError for HolProofRecipeError {}

fn validate_structure(
    nodes: &[RecipeNode],
    selected_namespace: usize,
) -> Result<(), HolProofRecipeError> {
    if nodes.len() > MAX_RECIPE_NODES {
        return Err(HolProofRecipeError::Invalid(
            "sealed recipe exceeds node limit",
        ));
    }
    let mut sorts = Vec::with_capacity(nodes.len());
    let mut persisted = HashSet::new();
    for (current, node) in nodes.iter().enumerate() {
        let require = |index: usize, expected: RecipeSort| {
            if index >= current {
                return Err(HolProofRecipeError::Invalid(
                    "recipe dependency is not backward",
                ));
            }
            if sorts.get(index) != Some(&expected) {
                return Err(HolProofRecipeError::Invalid(
                    "recipe dependency has wrong sort",
                ));
            }
            Ok(())
        };
        let sort = match node {
            RecipeNode::BoolType => RecipeSort::Type,
            RecipeNode::Bound { ty, .. } => {
                require(*ty, RecipeSort::Type)?;
                RecipeSort::Term
            }
            RecipeNode::Lambda {
                parameter_type,
                body,
            } => {
                require(*parameter_type, RecipeSort::Type)?;
                require(*body, RecipeSort::Term)?;
                RecipeSort::Term
            }
            RecipeNode::Bool(_) => RecipeSort::Term,
            RecipeNode::EmptyContext => RecipeSort::Context,
            RecipeNode::Beta {
                context,
                abstraction,
                argument,
            } => {
                require(*context, RecipeSort::Context)?;
                require(*abstraction, RecipeSort::Term)?;
                require(*argument, RecipeSort::Term)?;
                RecipeSort::Theorem
            }
            RecipeNode::Persist { theorem } => {
                require(*theorem, RecipeSort::Theorem)?;
                persisted.insert(*theorem);
                RecipeSort::Theorem
            }
            RecipeNode::Namespace { name } => {
                validate_name(name.as_deref())?;
                RecipeSort::Namespace
            }
            RecipeNode::ExportTheorem {
                namespace,
                theorem,
                name,
                ..
            } => {
                require(*namespace, RecipeSort::Namespace)?;
                require(*theorem, RecipeSort::Theorem)?;
                if !persisted.contains(theorem) {
                    return Err(HolProofRecipeError::Invalid(
                        "exported theorem was not persisted",
                    ));
                }
                validate_name(name.as_deref())?;
                RecipeSort::Theorem
            }
            RecipeNode::ExportContext {
                namespace,
                context,
                name,
                ..
            } => {
                require(*namespace, RecipeSort::Namespace)?;
                require(*context, RecipeSort::Context)?;
                validate_name(name.as_deref())?;
                RecipeSort::Context
            }
        };
        sorts.push(sort);
    }
    if sorts.get(selected_namespace) != Some(&RecipeSort::Namespace) {
        return Err(HolProofRecipeError::Invalid(
            "selected node is not a namespace",
        ));
    }
    Ok(())
}

fn validate_name(name: Option<&str>) -> Result<(), HolProofRecipeError> {
    if name.is_some_and(|name| name.len() > MAX_RECIPE_NAME_BYTES) {
        Err(HolProofRecipeError::Invalid(
            "recipe name exceeds byte limit",
        ))
    } else {
        Ok(())
    }
}

fn encode(nodes: &[RecipeNode], selected_namespace: usize) -> Result<Vec<u8>, HolProofRecipeError> {
    let count = u16::try_from(nodes.len())
        .map_err(|_| HolProofRecipeError::Invalid("node count does not fit encoding"))?;
    let selected = u16::try_from(selected_namespace)
        .map_err(|_| HolProofRecipeError::Invalid("selected namespace does not fit encoding"))?;
    let mut bytes = Vec::new();
    bytes.push(RECIPE_VERSION);
    bytes.extend_from_slice(&count.to_be_bytes());
    bytes.extend_from_slice(&selected.to_be_bytes());
    for node in nodes {
        encode_node(&mut bytes, node)?;
        if bytes.len() > MAX_SEALED_HOL_RECIPE_BYTES {
            return Err(HolProofRecipeError::Invalid(
                "sealed recipe exceeds byte limit",
            ));
        }
    }
    Ok(bytes)
}

fn encode_index(bytes: &mut Vec<u8>, index: usize) -> Result<(), HolProofRecipeError> {
    let index = u16::try_from(index)
        .map_err(|_| HolProofRecipeError::Invalid("recipe index does not fit encoding"))?;
    bytes.extend_from_slice(&index.to_be_bytes());
    Ok(())
}

fn encode_name(bytes: &mut Vec<u8>, name: Option<&str>) -> Result<(), HolProofRecipeError> {
    match name {
        None => bytes.push(0),
        Some(name) => {
            validate_name(Some(name))?;
            bytes.push(1);
            let length = u16::try_from(name.len())
                .map_err(|_| HolProofRecipeError::Invalid("recipe name does not fit encoding"))?;
            bytes.extend_from_slice(&length.to_be_bytes());
            bytes.extend_from_slice(name.as_bytes());
        }
    }
    Ok(())
}

fn encode_node(bytes: &mut Vec<u8>, node: &RecipeNode) -> Result<(), HolProofRecipeError> {
    match node {
        RecipeNode::BoolType => bytes.push(0),
        RecipeNode::Bound { index, ty } => {
            bytes.push(1);
            bytes.extend_from_slice(&index.to_be_bytes());
            encode_index(bytes, *ty)?;
        }
        RecipeNode::Lambda {
            parameter_type,
            body,
        } => {
            bytes.push(2);
            encode_index(bytes, *parameter_type)?;
            encode_index(bytes, *body)?;
        }
        RecipeNode::Bool(value) => {
            bytes.push(3);
            bytes.push(u8::from(*value));
        }
        RecipeNode::EmptyContext => bytes.push(4),
        RecipeNode::Beta {
            context,
            abstraction,
            argument,
        } => {
            bytes.push(5);
            encode_index(bytes, *context)?;
            encode_index(bytes, *abstraction)?;
            encode_index(bytes, *argument)?;
        }
        RecipeNode::Persist { theorem } => {
            bytes.push(6);
            encode_index(bytes, *theorem)?;
        }
        RecipeNode::Namespace { name } => {
            bytes.push(7);
            encode_name(bytes, name.as_deref())?;
        }
        RecipeNode::ExportTheorem {
            namespace,
            export,
            theorem,
            name,
        } => {
            bytes.push(8);
            encode_index(bytes, *namespace)?;
            bytes.extend_from_slice(&export.to_be_bytes());
            encode_index(bytes, *theorem)?;
            encode_name(bytes, name.as_deref())?;
        }
        RecipeNode::ExportContext {
            namespace,
            export,
            context,
            name,
        } => {
            bytes.push(9);
            encode_index(bytes, *namespace)?;
            bytes.extend_from_slice(&export.to_be_bytes());
            encode_index(bytes, *context)?;
            encode_name(bytes, name.as_deref())?;
        }
    }
    Ok(())
}

struct Decoder<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Decoder<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn finish(self) -> Result<(), HolProofRecipeError> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(HolProofRecipeError::Invalid("trailing sealed recipe bytes"))
        }
    }

    fn take(&mut self, length: usize) -> Result<&'a [u8], HolProofRecipeError> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(HolProofRecipeError::Invalid(
                "sealed recipe offset overflow",
            ))?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(HolProofRecipeError::Invalid("truncated sealed recipe"))?;
        self.offset = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, HolProofRecipeError> {
        Ok(self.take(1)?[0])
    }
    fn u16(&mut self) -> Result<u16, HolProofRecipeError> {
        Ok(u16::from_be_bytes(
            self.take(2)?.try_into().expect("exact width"),
        ))
    }
    fn u32(&mut self) -> Result<u32, HolProofRecipeError> {
        Ok(u32::from_be_bytes(
            self.take(4)?.try_into().expect("exact width"),
        ))
    }
    fn i64(&mut self) -> Result<i64, HolProofRecipeError> {
        Ok(i64::from_be_bytes(
            self.take(8)?.try_into().expect("exact width"),
        ))
    }

    fn index(&mut self) -> Result<usize, HolProofRecipeError> {
        Ok(usize::from(self.u16()?))
    }

    fn name(&mut self) -> Result<Option<String>, HolProofRecipeError> {
        match self.byte()? {
            0 => Ok(None),
            1 => {
                let length = usize::from(self.u16()?);
                if length > MAX_RECIPE_NAME_BYTES {
                    return Err(HolProofRecipeError::Invalid(
                        "recipe name exceeds byte limit",
                    ));
                }
                let name = std::str::from_utf8(self.take(length)?)
                    .map_err(|_| HolProofRecipeError::Invalid("recipe name is not UTF-8"))?;
                Ok(Some(name.to_owned()))
            }
            _ => Err(HolProofRecipeError::Invalid(
                "invalid optional recipe name tag",
            )),
        }
    }

    fn node(&mut self) -> Result<RecipeNode, HolProofRecipeError> {
        match self.byte()? {
            0 => Ok(RecipeNode::BoolType),
            1 => Ok(RecipeNode::Bound {
                index: self.u32()?,
                ty: self.index()?,
            }),
            2 => Ok(RecipeNode::Lambda {
                parameter_type: self.index()?,
                body: self.index()?,
            }),
            3 => match self.byte()? {
                0 => Ok(RecipeNode::Bool(false)),
                1 => Ok(RecipeNode::Bool(true)),
                _ => Err(HolProofRecipeError::Invalid("invalid Boolean recipe value")),
            },
            4 => Ok(RecipeNode::EmptyContext),
            5 => Ok(RecipeNode::Beta {
                context: self.index()?,
                abstraction: self.index()?,
                argument: self.index()?,
            }),
            6 => Ok(RecipeNode::Persist {
                theorem: self.index()?,
            }),
            7 => Ok(RecipeNode::Namespace { name: self.name()? }),
            8 => Ok(RecipeNode::ExportTheorem {
                namespace: self.index()?,
                export: self.i64()?,
                theorem: self.index()?,
                name: self.name()?,
            }),
            9 => Ok(RecipeNode::ExportContext {
                namespace: self.index()?,
                export: self.i64()?,
                context: self.index()?,
                name: self.name()?,
            }),
            _ => Err(HolProofRecipeError::Invalid(
                "unknown sealed recipe node tag",
            )),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct BetaGuestPolicy;

impl Policy for BetaGuestPolicy {
    fn allows(&mut self, operation: Operation) -> bool {
        matches!(
            operation,
            Operation::InsertType
                | Operation::InsertTerm
                | Operation::ProveConversionBeta
                | Operation::ProveConversionEquality
                | Operation::PersistJudgement
                | Operation::DefineNamespace
                | Operation::ExportNamespaceValue
                | Operation::ExportSignedSnapshot
        )
    }
}

enum Value {
    Type(TypeId),
    Term(TermId),
    Context(ContextId),
    Theorem {
        context: ContextId,
        conclusion: TermId,
    },
    Namespace(NamespaceId),
    Unit,
}

fn replay(
    kernel: &Kernel,
    recipe: &[RecipeNode],
    selected_namespace: usize,
) -> Result<SignedHolArtifact, HolProofRecipeError> {
    let mut db: Connection<Hol<BetaGuestPolicy>> =
        kernel.open_hol(BetaGuestPolicy).map_err(replay_error)?;
    let mut values = Vec::with_capacity(recipe.len());
    for node in recipe {
        let value = match node {
            RecipeNode::BoolType => Value::Type(db.insert_bool_type().map_err(replay_error)?),
            RecipeNode::Bound { index, ty } => Value::Term(
                db.insert_bound_term(*index, type_at(&values, *ty)?)
                    .map_err(replay_error)?,
            ),
            RecipeNode::Lambda {
                parameter_type,
                body,
            } => Value::Term(
                db.insert_lambda(type_at(&values, *parameter_type)?, term_at(&values, *body)?)
                    .map_err(replay_error)?,
            ),
            RecipeNode::Bool(value) => {
                Value::Term(db.insert_bool_term(*value).map_err(replay_error)?)
            }
            RecipeNode::EmptyContext => Value::Context(ContextId::empty()),
            RecipeNode::Namespace { name } => Value::Namespace(
                db.create_namespace(Some(NamespaceId::root()), name.as_deref())
                    .map_err(replay_error)?,
            ),
            RecipeNode::Beta { .. }
            | RecipeNode::Persist { .. }
            | RecipeNode::ExportTheorem { .. }
            | RecipeNode::ExportContext { .. } => Value::Unit,
        };
        values.push(value);
    }
    db.with_proof_session(|mut proof| {
        let mut theorems: Vec<Option<Theorem<'_>>> = (0..recipe.len()).map(|_| None).collect();
        for (index, node) in recipe.iter().enumerate() {
            match node {
                RecipeNode::Beta {
                    context,
                    abstraction,
                    argument,
                } => {
                    let theorem = crate::hol_recipes::beta(
                        &mut proof,
                        context_at(&values, *context)?,
                        term_at(&values, *abstraction)?,
                        term_at(&values, *argument)?,
                    )
                    .map_err(replay_error)?;
                    values[index] = Value::Theorem {
                        context: theorem.context(),
                        conclusion: theorem.conclusion(),
                    };
                    theorems[index] = Some(theorem);
                }
                RecipeNode::Persist { theorem } => {
                    let theorem = theorems
                        .get(*theorem)
                        .and_then(Option::as_ref)
                        .ok_or_else(value_error)?;
                    proof.persist_theorem(theorem).map_err(replay_error)?;
                }
                _ => {}
            }
        }
        Ok::<_, HolProofRecipeError>(())
    })?;
    for node in recipe {
        match node {
            RecipeNode::ExportTheorem {
                namespace,
                export,
                theorem,
                name,
            } => db
                .export_value(
                    namespace_at(&values, *namespace)?,
                    ExportId::from_i64(*export),
                    NamespaceExport::Term(theorem_at(&values, *theorem)?.1),
                    name.as_deref(),
                )
                .map_err(replay_error)?,
            RecipeNode::ExportContext {
                namespace,
                export,
                context,
                name,
            } => db
                .export_value(
                    namespace_at(&values, *namespace)?,
                    ExportId::from_i64(*export),
                    NamespaceExport::Context(context_at(&values, *context)?),
                    name.as_deref(),
                )
                .map_err(replay_error)?,
            _ => {}
        }
    }
    let namespace = namespace_at(&values, selected_namespace)?;
    let snapshot = kernel.export_hol(&mut db).map_err(replay_error)?;
    snapshot_artifact(namespace, &snapshot)
}

fn snapshot_artifact(
    namespace: NamespaceId,
    snapshot: &SignedHolSnapshot,
) -> Result<SignedHolArtifact, HolProofRecipeError> {
    let image = snapshot.image().bytes();
    if image.len() > crate::MAX_IMAGE_BYTES {
        return Err(HolProofRecipeError::ArtifactTooLarge {
            size: image.len(),
            maximum: crate::MAX_IMAGE_BYTES,
        });
    }
    let attestation = snapshot.attestation();
    Ok(SignedHolArtifact {
        namespace_id: namespace.get(),
        image: image.to_vec(),
        schema: attestation.schema(),
        image_hash: attestation.image(),
        signer: attestation.signer(),
        public_key: attestation.public_key().to_vec(),
        signature: attestation.signature().to_vec(),
    })
}

fn value_error() -> HolProofRecipeError {
    HolProofRecipeError::Replay("internally inconsistent recipe value".into())
}
fn replay_error(error: impl fmt::Display) -> HolProofRecipeError {
    HolProofRecipeError::Replay(error.to_string())
}
fn type_at(values: &[Value], index: usize) -> Result<TypeId, HolProofRecipeError> {
    match values.get(index) {
        Some(Value::Type(value)) => Ok(*value),
        _ => Err(value_error()),
    }
}
fn term_at(values: &[Value], index: usize) -> Result<TermId, HolProofRecipeError> {
    match values.get(index) {
        Some(Value::Term(value)) => Ok(*value),
        _ => Err(value_error()),
    }
}
fn context_at(values: &[Value], index: usize) -> Result<ContextId, HolProofRecipeError> {
    match values.get(index) {
        Some(Value::Context(value)) => Ok(*value),
        _ => Err(value_error()),
    }
}
fn theorem_at(values: &[Value], index: usize) -> Result<(ContextId, TermId), HolProofRecipeError> {
    match values.get(index) {
        Some(Value::Theorem {
            context,
            conclusion,
        }) => Ok((*context, *conclusion)),
        _ => Err(value_error()),
    }
}
fn namespace_at(values: &[Value], index: usize) -> Result<NamespaceId, HolProofRecipeError> {
    match values.get(index) {
        Some(Value::Namespace(value)) => Ok(*value),
        _ => Err(value_error()),
    }
}

#[cfg(test)]
pub(crate) fn closed_beta_test_recipe() -> SealedHolProofRecipe {
    SealedHolProofRecipe::seal(
        vec![
            RecipeNode::BoolType,
            RecipeNode::Bound { index: 0, ty: 0 },
            RecipeNode::Lambda {
                parameter_type: 0,
                body: 1,
            },
            RecipeNode::Bool(true),
            RecipeNode::EmptyContext,
            RecipeNode::Beta {
                context: 4,
                abstraction: 2,
                argument: 3,
            },
            RecipeNode::Persist { theorem: 5 },
            RecipeNode::Namespace {
                name: Some("demo".into()),
            },
            RecipeNode::ExportContext {
                namespace: 7,
                export: 0,
                context: 4,
                name: None,
            },
            RecipeNode::ExportTheorem {
                namespace: 7,
                export: 1,
                theorem: 5,
                name: None,
            },
        ],
        7,
    )
    .expect("canonical beta test recipe")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn closed_beta() -> SealedHolProofRecipe {
        closed_beta_test_recipe()
    }

    #[test]
    fn canonical_recipe_round_trips_and_replays() {
        let recipe = closed_beta();
        assert_eq!(
            SealedHolProofRecipe::from_untrusted_bytes(recipe.as_bytes()).unwrap(),
            recipe
        );
        let kernel = Kernel::ephemeral();
        let artifact = recipe.replay(&kernel).unwrap();
        assert_eq!(artifact.signer(), kernel.key_id());
    }

    #[test]
    fn rejects_forward_wrong_sort_unpersisted_and_trailing_recipes() {
        assert!(
            SealedHolProofRecipe::seal(vec![RecipeNode::Bound { index: 0, ty: 0 }], 0).is_err()
        );
        assert!(
            SealedHolProofRecipe::seal(
                vec![
                    RecipeNode::BoolType,
                    RecipeNode::Lambda {
                        parameter_type: 0,
                        body: 0
                    }
                ],
                0
            )
            .is_err()
        );
        assert!(
            SealedHolProofRecipe::seal(
                vec![
                    RecipeNode::BoolType,
                    RecipeNode::Namespace { name: None },
                    RecipeNode::ExportTheorem {
                        namespace: 1,
                        export: 0,
                        theorem: 0,
                        name: None
                    }
                ],
                1
            )
            .is_err()
        );
        let mut bytes = closed_beta().as_bytes().to_vec();
        bytes.push(0);
        assert!(SealedHolProofRecipe::from_untrusted_bytes(&bytes).is_err());
    }

    #[test]
    fn rejects_oversized_untrusted_recipe_before_decode() {
        assert!(matches!(
            SealedHolProofRecipe::from_untrusted_bytes(&vec![0; MAX_SEALED_HOL_RECIPE_BYTES + 1]),
            Err(HolProofRecipeError::Invalid(
                "sealed recipe exceeds byte limit"
            ))
        ));
    }
}
