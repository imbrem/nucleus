//! Canonical, bounded, untrusted HOL guest plans and checked replay.
//!
//! Executors can construct or transport these bytes without receiving a
//! database, theorem, signer, or kernel capability. Nucleus authority begins
//! only when the key-holding service independently decodes and replays a plan.

use std::collections::HashSet;
use std::error::Error as StdError;
use std::fmt;

use covalence_nucleus::{
    Connection, ContextId, Conversion, ExportId, Hol, Kernel, NamespaceExport, NamespaceId,
    Operation, Policy, SignedHolSnapshot, TermId, TermInstantiation, Theorem, TypeId,
    TypeInstantiation,
};

use crate::SignedHolArtifact;

pub(crate) const MAX_RECIPE_NODES: usize = 128;
pub(crate) const MAX_RECIPE_NAME_BYTES: usize = 256;
/// Maximum canonical bytes accepted from an untrusted guest executor.
pub const MAX_SEALED_HOL_RECIPE_BYTES: usize = 64 * 1024;

const RECIPE_VERSION: u8 = 3;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum RecipeSort {
    Type,
    Term,
    Context,
    Theorem,
    Namespace,
    TermInstantiationMap,
    TypeInstantiationMap,
    Conversion,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RecipeNode {
    BoolType,
    FreeType {
        symbol: i64,
    },
    Bound {
        index: u32,
        ty: usize,
    },
    FreeTerm {
        symbol: i64,
        ty: usize,
    },
    Lambda {
        parameter_type: usize,
        body: usize,
    },
    Bool(bool),
    Application {
        function: usize,
        argument: usize,
    },
    Epsilon {
        predicate: usize,
    },
    EmptyContext,
    ConversionReflexivity {
        term: usize,
    },
    ConversionSymmetry {
        conversion: usize,
    },
    ConversionTransitivity {
        first: usize,
        second: usize,
    },
    ConversionApplication {
        function: usize,
        argument: usize,
    },
    ConversionLambda {
        parameter_type: usize,
        body: usize,
    },
    ConversionBeta {
        abstraction: usize,
        argument: usize,
    },
    ConversionEta {
        function: usize,
    },
    ConversionEpsilon {
        predicate: usize,
    },
    ConversionEquality {
        context: usize,
        conversion: usize,
    },
    ConvertTheorem {
        theorem: usize,
        conversion: usize,
    },
    EmptyTermInstantiationMap,
    ExtendTermInstantiationMap {
        base: usize,
        variable: usize,
        replacement: usize,
    },
    TermInstantiation {
        theorem: usize,
        instantiations: usize,
    },
    EmptyTypeInstantiationMap,
    ExtendTypeInstantiationMap {
        base: usize,
        variable: usize,
        replacement: usize,
    },
    TypeInstantiation {
        theorem: usize,
        instantiations: usize,
    },
    Abstraction {
        theorem: usize,
        variable: usize,
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

#[allow(clippy::too_many_lines)]
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
    let mut term_map_keys: Vec<Option<HashSet<usize>>> = Vec::with_capacity(nodes.len());
    let mut type_map_keys: Vec<Option<HashSet<usize>>> = Vec::with_capacity(nodes.len());
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
        let mut term_keys = None;
        let mut type_keys = None;
        let sort = match node {
            RecipeNode::BoolType | RecipeNode::FreeType { .. } => RecipeSort::Type,
            RecipeNode::Bound { ty, .. } | RecipeNode::FreeTerm { ty, .. } => {
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
            RecipeNode::Application { function, argument } => {
                require(*function, RecipeSort::Term)?;
                require(*argument, RecipeSort::Term)?;
                RecipeSort::Term
            }
            RecipeNode::Epsilon { predicate } => {
                require(*predicate, RecipeSort::Term)?;
                RecipeSort::Term
            }
            RecipeNode::EmptyContext => RecipeSort::Context,
            RecipeNode::ConversionReflexivity { term } => {
                require(*term, RecipeSort::Term)?;
                RecipeSort::Conversion
            }
            RecipeNode::ConversionSymmetry { conversion } => {
                require(*conversion, RecipeSort::Conversion)?;
                RecipeSort::Conversion
            }
            RecipeNode::ConversionTransitivity { first, second }
            | RecipeNode::ConversionApplication {
                function: first,
                argument: second,
            } => {
                require(*first, RecipeSort::Conversion)?;
                require(*second, RecipeSort::Conversion)?;
                RecipeSort::Conversion
            }
            RecipeNode::ConversionLambda {
                parameter_type,
                body,
            } => {
                require(*parameter_type, RecipeSort::Type)?;
                require(*body, RecipeSort::Conversion)?;
                RecipeSort::Conversion
            }
            RecipeNode::ConversionBeta {
                abstraction,
                argument,
            } => {
                require(*abstraction, RecipeSort::Term)?;
                require(*argument, RecipeSort::Term)?;
                RecipeSort::Conversion
            }
            RecipeNode::ConversionEta { function } => {
                require(*function, RecipeSort::Term)?;
                RecipeSort::Conversion
            }
            RecipeNode::ConversionEpsilon { predicate } => {
                require(*predicate, RecipeSort::Conversion)?;
                RecipeSort::Conversion
            }
            RecipeNode::ConversionEquality {
                context,
                conversion,
            } => {
                require(*context, RecipeSort::Context)?;
                require(*conversion, RecipeSort::Conversion)?;
                RecipeSort::Theorem
            }
            RecipeNode::ConvertTheorem {
                theorem,
                conversion,
            } => {
                require(*theorem, RecipeSort::Theorem)?;
                require(*conversion, RecipeSort::Conversion)?;
                RecipeSort::Theorem
            }
            RecipeNode::EmptyTermInstantiationMap => {
                term_keys = Some(HashSet::new());
                RecipeSort::TermInstantiationMap
            }
            RecipeNode::ExtendTermInstantiationMap {
                base,
                variable,
                replacement,
            } => {
                require(*base, RecipeSort::TermInstantiationMap)?;
                require(*variable, RecipeSort::Term)?;
                require(*replacement, RecipeSort::Term)?;
                let mut keys = term_map_keys
                    .get(*base)
                    .and_then(Option::as_ref)
                    .cloned()
                    .ok_or(HolProofRecipeError::Invalid(
                        "term-instantiation map base is invalid",
                    ))?;
                if !keys.insert(*variable) {
                    return Err(HolProofRecipeError::Invalid(
                        "duplicate term-instantiation recipe key",
                    ));
                }
                term_keys = Some(keys);
                RecipeSort::TermInstantiationMap
            }
            RecipeNode::TermInstantiation {
                theorem,
                instantiations,
            } => {
                require(*theorem, RecipeSort::Theorem)?;
                require(*instantiations, RecipeSort::TermInstantiationMap)?;
                RecipeSort::Theorem
            }
            RecipeNode::EmptyTypeInstantiationMap => {
                type_keys = Some(HashSet::new());
                RecipeSort::TypeInstantiationMap
            }
            RecipeNode::ExtendTypeInstantiationMap {
                base,
                variable,
                replacement,
            } => {
                require(*base, RecipeSort::TypeInstantiationMap)?;
                require(*variable, RecipeSort::Type)?;
                require(*replacement, RecipeSort::Type)?;
                let mut keys = type_map_keys
                    .get(*base)
                    .and_then(Option::as_ref)
                    .cloned()
                    .ok_or(HolProofRecipeError::Invalid(
                        "type-instantiation map base is invalid",
                    ))?;
                if !keys.insert(*variable) {
                    return Err(HolProofRecipeError::Invalid(
                        "duplicate type-instantiation recipe key",
                    ));
                }
                type_keys = Some(keys);
                RecipeSort::TypeInstantiationMap
            }
            RecipeNode::TypeInstantiation {
                theorem,
                instantiations,
            } => {
                require(*theorem, RecipeSort::Theorem)?;
                require(*instantiations, RecipeSort::TypeInstantiationMap)?;
                RecipeSort::Theorem
            }
            RecipeNode::Abstraction { theorem, variable } => {
                require(*theorem, RecipeSort::Theorem)?;
                require(*variable, RecipeSort::Term)?;
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
        term_map_keys.push(term_keys);
        type_map_keys.push(type_keys);
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

#[allow(clippy::too_many_lines)]
fn encode_node(bytes: &mut Vec<u8>, node: &RecipeNode) -> Result<(), HolProofRecipeError> {
    match node {
        RecipeNode::BoolType => bytes.push(0),
        RecipeNode::FreeType { symbol } => {
            bytes.push(11);
            bytes.extend_from_slice(&symbol.to_be_bytes());
        }
        RecipeNode::Bound { index, ty } => {
            bytes.push(1);
            bytes.extend_from_slice(&index.to_be_bytes());
            encode_index(bytes, *ty)?;
        }
        RecipeNode::FreeTerm { symbol, ty } => {
            bytes.push(12);
            bytes.extend_from_slice(&symbol.to_be_bytes());
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
        RecipeNode::Application { function, argument } => {
            bytes.push(0x20);
            encode_index(bytes, *function)?;
            encode_index(bytes, *argument)?;
        }
        RecipeNode::Epsilon { predicate } => {
            bytes.push(0x21);
            encode_index(bytes, *predicate)?;
        }
        RecipeNode::EmptyContext => bytes.push(4),
        RecipeNode::ConversionReflexivity { term } => {
            bytes.push(0x30);
            encode_index(bytes, *term)?;
        }
        RecipeNode::ConversionSymmetry { conversion } => {
            bytes.push(0x31);
            encode_index(bytes, *conversion)?;
        }
        RecipeNode::ConversionTransitivity { first, second } => {
            bytes.push(0x32);
            encode_index(bytes, *first)?;
            encode_index(bytes, *second)?;
        }
        RecipeNode::ConversionApplication { function, argument } => {
            bytes.push(0x33);
            encode_index(bytes, *function)?;
            encode_index(bytes, *argument)?;
        }
        RecipeNode::ConversionLambda {
            parameter_type,
            body,
        } => {
            bytes.push(0x34);
            encode_index(bytes, *parameter_type)?;
            encode_index(bytes, *body)?;
        }
        RecipeNode::ConversionBeta {
            abstraction,
            argument,
        } => {
            bytes.push(0x35);
            encode_index(bytes, *abstraction)?;
            encode_index(bytes, *argument)?;
        }
        RecipeNode::ConversionEta { function } => {
            bytes.push(0x36);
            encode_index(bytes, *function)?;
        }
        RecipeNode::ConversionEpsilon { predicate } => {
            bytes.push(0x37);
            encode_index(bytes, *predicate)?;
        }
        RecipeNode::ConversionEquality {
            context,
            conversion,
        } => {
            bytes.push(0x38);
            encode_index(bytes, *context)?;
            encode_index(bytes, *conversion)?;
        }
        RecipeNode::ConvertTheorem {
            theorem,
            conversion,
        } => {
            bytes.push(0x39);
            encode_index(bytes, *theorem)?;
            encode_index(bytes, *conversion)?;
        }
        RecipeNode::EmptyTermInstantiationMap => bytes.push(13),
        RecipeNode::ExtendTermInstantiationMap {
            base,
            variable,
            replacement,
        } => {
            bytes.push(14);
            encode_index(bytes, *base)?;
            encode_index(bytes, *variable)?;
            encode_index(bytes, *replacement)?;
        }
        RecipeNode::TermInstantiation {
            theorem,
            instantiations,
        } => {
            bytes.push(15);
            encode_index(bytes, *theorem)?;
            encode_index(bytes, *instantiations)?;
        }
        RecipeNode::EmptyTypeInstantiationMap => bytes.push(16),
        RecipeNode::ExtendTypeInstantiationMap {
            base,
            variable,
            replacement,
        } => {
            bytes.push(17);
            encode_index(bytes, *base)?;
            encode_index(bytes, *variable)?;
            encode_index(bytes, *replacement)?;
        }
        RecipeNode::TypeInstantiation {
            theorem,
            instantiations,
        } => {
            bytes.push(18);
            encode_index(bytes, *theorem)?;
            encode_index(bytes, *instantiations)?;
        }
        RecipeNode::Abstraction { theorem, variable } => {
            bytes.push(19);
            encode_index(bytes, *theorem)?;
            encode_index(bytes, *variable)?;
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

    #[allow(clippy::too_many_lines)]
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
            11 => Ok(RecipeNode::FreeType {
                symbol: self.i64()?,
            }),
            12 => Ok(RecipeNode::FreeTerm {
                symbol: self.i64()?,
                ty: self.index()?,
            }),
            13 => Ok(RecipeNode::EmptyTermInstantiationMap),
            14 => Ok(RecipeNode::ExtendTermInstantiationMap {
                base: self.index()?,
                variable: self.index()?,
                replacement: self.index()?,
            }),
            15 => Ok(RecipeNode::TermInstantiation {
                theorem: self.index()?,
                instantiations: self.index()?,
            }),
            16 => Ok(RecipeNode::EmptyTypeInstantiationMap),
            17 => Ok(RecipeNode::ExtendTypeInstantiationMap {
                base: self.index()?,
                variable: self.index()?,
                replacement: self.index()?,
            }),
            18 => Ok(RecipeNode::TypeInstantiation {
                theorem: self.index()?,
                instantiations: self.index()?,
            }),
            19 => Ok(RecipeNode::Abstraction {
                theorem: self.index()?,
                variable: self.index()?,
            }),
            0x20 => Ok(RecipeNode::Application {
                function: self.index()?,
                argument: self.index()?,
            }),
            0x21 => Ok(RecipeNode::Epsilon {
                predicate: self.index()?,
            }),
            0x30 => Ok(RecipeNode::ConversionReflexivity {
                term: self.index()?,
            }),
            0x31 => Ok(RecipeNode::ConversionSymmetry {
                conversion: self.index()?,
            }),
            0x32 => Ok(RecipeNode::ConversionTransitivity {
                first: self.index()?,
                second: self.index()?,
            }),
            0x33 => Ok(RecipeNode::ConversionApplication {
                function: self.index()?,
                argument: self.index()?,
            }),
            0x34 => Ok(RecipeNode::ConversionLambda {
                parameter_type: self.index()?,
                body: self.index()?,
            }),
            0x35 => Ok(RecipeNode::ConversionBeta {
                abstraction: self.index()?,
                argument: self.index()?,
            }),
            0x36 => Ok(RecipeNode::ConversionEta {
                function: self.index()?,
            }),
            0x37 => Ok(RecipeNode::ConversionEpsilon {
                predicate: self.index()?,
            }),
            0x38 => Ok(RecipeNode::ConversionEquality {
                context: self.index()?,
                conversion: self.index()?,
            }),
            0x39 => Ok(RecipeNode::ConvertTheorem {
                theorem: self.index()?,
                conversion: self.index()?,
            }),
            _ => Err(HolProofRecipeError::Invalid(
                "unknown sealed recipe node tag",
            )),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct ProofGuestPolicy;

impl Policy for ProofGuestPolicy {
    fn allows(&mut self, operation: Operation) -> bool {
        matches!(
            operation,
            Operation::InsertType
                | Operation::InsertTerm
                | Operation::ProveConversionReflexivity
                | Operation::ProveConversionSymmetry
                | Operation::ProveConversionTransitivity
                | Operation::ProveConversionApplication
                | Operation::ProveConversionLambda
                | Operation::ProveConversionBeta
                | Operation::ProveConversionEta
                | Operation::ProveConversionEpsilon
                | Operation::ProveConversionEquality
                | Operation::ProveTheoremConversion
                | Operation::ProveTermInstantiation
                | Operation::ProveTypeInstantiation
                | Operation::ProveAbstraction
                | Operation::DefineContext
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
    TermInstantiationMap(Vec<TermInstantiation>),
    TypeInstantiationMap(Vec<TypeInstantiation>),
    Unit,
}

#[allow(clippy::too_many_lines)]
fn replay(
    kernel: &Kernel,
    recipe: &[RecipeNode],
    selected_namespace: usize,
) -> Result<SignedHolArtifact, HolProofRecipeError> {
    let mut db: Connection<Hol<ProofGuestPolicy>> =
        kernel.open_hol(ProofGuestPolicy).map_err(replay_error)?;
    let mut values = Vec::with_capacity(recipe.len());
    for node in recipe {
        let value = match node {
            RecipeNode::BoolType => Value::Type(db.insert_bool_type().map_err(replay_error)?),
            RecipeNode::FreeType { symbol } => {
                Value::Type(db.insert_free_type(*symbol).map_err(replay_error)?)
            }
            RecipeNode::Bound { index, ty } => Value::Term(
                db.insert_bound_term(*index, type_at(&values, *ty)?)
                    .map_err(replay_error)?,
            ),
            RecipeNode::FreeTerm { symbol, ty } => Value::Term(
                db.insert_free_term(*symbol, type_at(&values, *ty)?)
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
            RecipeNode::Application { function, argument } => Value::Term(
                db.insert_application(term_at(&values, *function)?, term_at(&values, *argument)?)
                    .map_err(replay_error)?,
            ),
            RecipeNode::Epsilon { predicate } => Value::Term(
                db.insert_epsilon(term_at(&values, *predicate)?)
                    .map_err(replay_error)?,
            ),
            RecipeNode::EmptyContext => Value::Context(ContextId::empty()),
            RecipeNode::Namespace { name } => Value::Namespace(
                db.create_namespace(Some(NamespaceId::root()), name.as_deref())
                    .map_err(replay_error)?,
            ),
            RecipeNode::EmptyTermInstantiationMap => Value::TermInstantiationMap(Vec::new()),
            RecipeNode::ExtendTermInstantiationMap {
                base,
                variable,
                replacement,
            } => {
                let mut map = term_instantiation_map_at(&values, *base)?.to_vec();
                map.push(TermInstantiation {
                    variable: term_at(&values, *variable)?,
                    replacement: term_at(&values, *replacement)?,
                });
                Value::TermInstantiationMap(map)
            }
            RecipeNode::EmptyTypeInstantiationMap => Value::TypeInstantiationMap(Vec::new()),
            RecipeNode::ExtendTypeInstantiationMap {
                base,
                variable,
                replacement,
            } => {
                let mut map = type_instantiation_map_at(&values, *base)?.to_vec();
                map.push(TypeInstantiation {
                    variable: type_at(&values, *variable)?,
                    replacement: type_at(&values, *replacement)?,
                });
                Value::TypeInstantiationMap(map)
            }
            RecipeNode::ConversionReflexivity { .. }
            | RecipeNode::ConversionSymmetry { .. }
            | RecipeNode::ConversionTransitivity { .. }
            | RecipeNode::ConversionApplication { .. }
            | RecipeNode::ConversionLambda { .. }
            | RecipeNode::ConversionBeta { .. }
            | RecipeNode::ConversionEta { .. }
            | RecipeNode::ConversionEpsilon { .. }
            | RecipeNode::ConversionEquality { .. }
            | RecipeNode::ConvertTheorem { .. }
            | RecipeNode::TermInstantiation { .. }
            | RecipeNode::TypeInstantiation { .. }
            | RecipeNode::Abstraction { .. }
            | RecipeNode::Persist { .. }
            | RecipeNode::ExportTheorem { .. }
            | RecipeNode::ExportContext { .. } => Value::Unit,
        };
        values.push(value);
    }
    replay_theorems(&mut db, recipe, &mut values)?;
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

#[allow(clippy::too_many_lines)]
fn replay_theorems<P: Policy>(
    db: &mut Connection<Hol<P>>,
    recipe: &[RecipeNode],
    values: &mut [Value],
) -> Result<(), HolProofRecipeError> {
    db.with_proof_session(|mut proof| {
        let mut conversions: Vec<Option<Conversion<'_>>> =
            (0..recipe.len()).map(|_| None).collect();
        let mut theorems: Vec<Option<Theorem<'_>>> = (0..recipe.len()).map(|_| None).collect();
        for (index, node) in recipe.iter().enumerate() {
            match node {
                RecipeNode::ConversionReflexivity { term } => {
                    conversions[index] = Some(
                        proof
                            .conversion_reflexivity(term_at(values, *term)?)
                            .map_err(replay_error)?,
                    );
                }
                RecipeNode::ConversionSymmetry { conversion } => {
                    conversions[index] = Some(
                        proof
                            .conversion_symmetry(conversion_at_index(&conversions, *conversion)?)
                            .map_err(replay_error)?,
                    );
                }
                RecipeNode::ConversionTransitivity { first, second } => {
                    conversions[index] = Some(
                        proof
                            .conversion_transitivity(
                                conversion_at_index(&conversions, *first)?,
                                conversion_at_index(&conversions, *second)?,
                            )
                            .map_err(replay_error)?,
                    );
                }
                RecipeNode::ConversionApplication { function, argument } => {
                    conversions[index] = Some(
                        proof
                            .conversion_application(
                                conversion_at_index(&conversions, *function)?,
                                conversion_at_index(&conversions, *argument)?,
                            )
                            .map_err(replay_error)?,
                    );
                }
                RecipeNode::ConversionLambda {
                    parameter_type,
                    body,
                } => {
                    conversions[index] = Some(
                        proof
                            .conversion_lambda(
                                type_at(values, *parameter_type)?,
                                conversion_at_index(&conversions, *body)?,
                            )
                            .map_err(replay_error)?,
                    );
                }
                RecipeNode::ConversionBeta {
                    abstraction,
                    argument,
                } => {
                    conversions[index] = Some(
                        proof
                            .conversion_beta(
                                term_at(values, *abstraction)?,
                                term_at(values, *argument)?,
                            )
                            .map_err(replay_error)?,
                    );
                }
                RecipeNode::ConversionEta { function } => {
                    conversions[index] = Some(
                        proof
                            .conversion_eta(term_at(values, *function)?)
                            .map_err(replay_error)?,
                    );
                }
                RecipeNode::ConversionEpsilon { predicate } => {
                    conversions[index] = Some(
                        proof
                            .conversion_epsilon(conversion_at_index(&conversions, *predicate)?)
                            .map_err(replay_error)?,
                    );
                }
                RecipeNode::ConversionEquality {
                    context,
                    conversion,
                } => {
                    let theorem = proof
                        .prove_conversion_equality(
                            context_at(values, *context)?,
                            conversion_at_index(&conversions, *conversion)?,
                        )
                        .map_err(replay_error)?;
                    values[index] = Value::Theorem {
                        context: theorem.context(),
                        conclusion: theorem.conclusion(),
                    };
                    theorems[index] = Some(theorem);
                }
                RecipeNode::ConvertTheorem {
                    theorem,
                    conversion,
                } => {
                    let theorem = proof
                        .convert_theorem(
                            theorem_at_index(&theorems, *theorem)?,
                            conversion_at_index(&conversions, *conversion)?,
                        )
                        .map_err(replay_error)?;
                    values[index] = Value::Theorem {
                        context: theorem.context(),
                        conclusion: theorem.conclusion(),
                    };
                    theorems[index] = Some(theorem);
                }
                RecipeNode::TermInstantiation {
                    theorem,
                    instantiations,
                } => {
                    let theorem = proof
                        .instantiate_terms(
                            theorem_at_index(&theorems, *theorem)?,
                            term_instantiation_map_at(values, *instantiations)?,
                        )
                        .map_err(replay_error)?;
                    values[index] = Value::Theorem {
                        context: theorem.context(),
                        conclusion: theorem.conclusion(),
                    };
                    theorems[index] = Some(theorem);
                }
                RecipeNode::TypeInstantiation {
                    theorem,
                    instantiations,
                } => {
                    let theorem = proof
                        .instantiate_types(
                            theorem_at_index(&theorems, *theorem)?,
                            type_instantiation_map_at(values, *instantiations)?,
                        )
                        .map_err(replay_error)?;
                    values[index] = Value::Theorem {
                        context: theorem.context(),
                        conclusion: theorem.conclusion(),
                    };
                    theorems[index] = Some(theorem);
                }
                RecipeNode::Abstraction { theorem, variable } => {
                    let theorem = proof
                        .abstraction(
                            theorem_at_index(&theorems, *theorem)?,
                            term_at(values, *variable)?,
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
    })
}

fn conversion_at_index<'a, 'brand>(
    conversions: &'a [Option<Conversion<'brand>>],
    index: usize,
) -> Result<&'a Conversion<'brand>, HolProofRecipeError> {
    conversions
        .get(index)
        .and_then(Option::as_ref)
        .ok_or_else(value_error)
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

fn theorem_at_index<'a, 'brand>(
    theorems: &'a [Option<Theorem<'brand>>],
    index: usize,
) -> Result<&'a Theorem<'brand>, HolProofRecipeError> {
    theorems
        .get(index)
        .and_then(Option::as_ref)
        .ok_or_else(value_error)
}

fn term_instantiation_map_at(
    values: &[Value],
    index: usize,
) -> Result<&[TermInstantiation], HolProofRecipeError> {
    match values.get(index) {
        Some(Value::TermInstantiationMap(value)) => Ok(value),
        _ => Err(value_error()),
    }
}

fn type_instantiation_map_at(
    values: &[Value],
    index: usize,
) -> Result<&[TypeInstantiation], HolProofRecipeError> {
    match values.get(index) {
        Some(Value::TypeInstantiationMap(value)) => Ok(value),
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
            RecipeNode::ConversionBeta {
                abstraction: 2,
                argument: 3,
            },
            RecipeNode::ConversionEquality {
                context: 4,
                conversion: 5,
            },
            RecipeNode::Persist { theorem: 6 },
            RecipeNode::Namespace {
                name: Some("demo".into()),
            },
            RecipeNode::ExportContext {
                namespace: 8,
                export: 0,
                context: 4,
                name: None,
            },
            RecipeNode::ExportTheorem {
                namespace: 8,
                export: 1,
                theorem: 6,
                name: None,
            },
        ],
        8,
    )
    .expect("canonical beta test recipe")
}

#[cfg(test)]
fn closed_eta_test_recipe() -> SealedHolProofRecipe {
    SealedHolProofRecipe::seal(
        vec![
            RecipeNode::BoolType,
            RecipeNode::Bound { index: 0, ty: 0 },
            RecipeNode::Lambda {
                parameter_type: 0,
                body: 1,
            },
            RecipeNode::EmptyContext,
            RecipeNode::ConversionEta { function: 2 },
            RecipeNode::ConversionEquality {
                context: 3,
                conversion: 4,
            },
            RecipeNode::Persist { theorem: 5 },
            RecipeNode::Namespace {
                name: Some("eta-demo".into()),
            },
            RecipeNode::ExportContext {
                namespace: 7,
                export: 0,
                context: 3,
                name: Some("empty_context".into()),
            },
            RecipeNode::ExportTheorem {
                namespace: 7,
                export: 1,
                theorem: 5,
                name: Some("identity_eta".into()),
            },
        ],
        7,
    )
    .expect("canonical eta test recipe")
}

#[cfg(test)]
pub(crate) fn schematic_binding_test_recipe() -> SealedHolProofRecipe {
    SealedHolProofRecipe::seal(
        vec![
            RecipeNode::FreeType { symbol: 0 },
            RecipeNode::Bound { index: 0, ty: 0 },
            RecipeNode::Lambda {
                parameter_type: 0,
                body: 1,
            },
            RecipeNode::FreeTerm { symbol: 0, ty: 0 },
            RecipeNode::FreeTerm { symbol: 1, ty: 0 },
            RecipeNode::EmptyContext,
            RecipeNode::ConversionBeta {
                abstraction: 2,
                argument: 3,
            },
            RecipeNode::ConversionEquality {
                context: 5,
                conversion: 6,
            },
            RecipeNode::EmptyTermInstantiationMap,
            RecipeNode::ExtendTermInstantiationMap {
                base: 8,
                variable: 3,
                replacement: 4,
            },
            RecipeNode::TermInstantiation {
                theorem: 7,
                instantiations: 9,
            },
            RecipeNode::Abstraction {
                theorem: 10,
                variable: 4,
            },
            RecipeNode::BoolType,
            RecipeNode::EmptyTypeInstantiationMap,
            RecipeNode::ExtendTypeInstantiationMap {
                base: 13,
                variable: 0,
                replacement: 12,
            },
            RecipeNode::TypeInstantiation {
                theorem: 11,
                instantiations: 14,
            },
            RecipeNode::Persist { theorem: 15 },
            RecipeNode::Namespace {
                name: Some("schematic-binding-demo".into()),
            },
            RecipeNode::ExportContext {
                namespace: 17,
                export: 0,
                context: 5,
                name: Some("empty_context".into()),
            },
            RecipeNode::ExportTheorem {
                namespace: 17,
                export: 1,
                theorem: 15,
                name: Some("schematic_identity_binding".into()),
            },
        ],
        17,
    )
    .expect("canonical schematic-binding test recipe")
}

#[cfg(test)]
pub(crate) fn nested_identity_conversion_test_recipe() -> SealedHolProofRecipe {
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
            RecipeNode::ConversionReflexivity { term: 2 },
            RecipeNode::ConversionBeta {
                abstraction: 2,
                argument: 3,
            },
            RecipeNode::ConversionApplication {
                function: 5,
                argument: 6,
            },
            RecipeNode::ConversionTransitivity {
                first: 7,
                second: 6,
            },
            RecipeNode::ConversionEquality {
                context: 4,
                conversion: 8,
            },
            RecipeNode::Persist { theorem: 9 },
            RecipeNode::Namespace {
                name: Some("conversion-demo".into()),
            },
            RecipeNode::ExportContext {
                namespace: 11,
                export: 0,
                context: 4,
                name: Some("empty_context".into()),
            },
            RecipeNode::ExportTheorem {
                namespace: 11,
                export: 1,
                theorem: 9,
                name: Some("nested_identity_beta".into()),
            },
        ],
        11,
    )
    .expect("canonical nested-identity conversion recipe")
}

#[cfg(test)]
pub(crate) const SCHEMATIC_BINDING_WIRE: &[u8] = &[
    3, 0, 20, 0, 17, 11, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 12, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 53, 0, 2, 0, 3, 56, 0, 5, 0, 6, 13,
    14, 0, 8, 0, 3, 0, 4, 15, 0, 7, 0, 9, 19, 0, 10, 0, 4, 0, 16, 17, 0, 13, 0, 0, 0, 12, 18, 0,
    11, 0, 14, 6, 0, 15, 7, 1, 0, 22, 115, 99, 104, 101, 109, 97, 116, 105, 99, 45, 98, 105, 110,
    100, 105, 110, 103, 45, 100, 101, 109, 111, 9, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 13,
    101, 109, 112, 116, 121, 95, 99, 111, 110, 116, 101, 120, 116, 8, 0, 17, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 15, 1, 0, 26, 115, 99, 104, 101, 109, 97, 116, 105, 99, 95, 105, 100, 101, 110, 116, 105,
    116, 121, 95, 98, 105, 110, 100, 105, 110, 103,
];

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
    fn canonical_eta_recipe_round_trips_and_replays() {
        const VERSION_3_ETA_RECIPE: &[u8] = &[
            3, 0, 10, 0, 7, // version, node count, selected namespace
            0, // bool type
            1, 0, 0, 0, 0, 0, 0, // bound 0 : node 0
            2, 0, 0, 0, 1, // lambda node 0, node 1
            4, // empty context
            0x36, 0, 2, // eta conversion of node 2
            0x38, 0, 3, 0, 4, // conversion equality in node 3
            6, 0, 5, // persist node 5
            7, 1, 0, 8, b'e', b't', b'a', b'-', b'd', b'e', b'm', b'o', 9, 0, 7, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 3, 1, 0, 13, b'e', b'm', b'p', b't', b'y', b'_', b'c', b'o', b'n', b't', b'e',
            b'x', b't', 8, 0, 7, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 1, 0, 12, b'i', b'd', b'e', b'n',
            b't', b'i', b't', b'y', b'_', b'e', b't', b'a',
        ];
        let recipe = closed_eta_test_recipe();
        assert_eq!(recipe.as_bytes(), VERSION_3_ETA_RECIPE);
        assert_eq!(
            SealedHolProofRecipe::from_untrusted_bytes(VERSION_3_ETA_RECIPE).unwrap(),
            recipe
        );
        let kernel = Kernel::ephemeral();
        let artifact = recipe.replay(&kernel).unwrap();
        assert_eq!(artifact.signer(), kernel.key_id());
    }

    #[test]
    fn canonical_nested_identity_conversion_has_fixed_wire_and_replays() {
        const VERSION_3_NESTED_IDENTITY: &[u8] = &[
            3, 0, 14, 0, 11, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 3, 1, 4, 0x30, 0, 2, 0x35, 0,
            2, 0, 3, 0x33, 0, 5, 0, 6, 0x32, 0, 7, 0, 6, 0x38, 0, 4, 0, 8, 6, 0, 9, 7, 1, 0, 15,
            b'c', b'o', b'n', b'v', b'e', b'r', b's', b'i', b'o', b'n', b'-', b'd', b'e', b'm',
            b'o', 9, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 1, 0, 13, b'e', b'm', b'p', b't', b'y',
            b'_', b'c', b'o', b'n', b't', b'e', b'x', b't', 8, 0, 11, 0, 0, 0, 0, 0, 0, 0, 1, 0, 9,
            1, 0, 20, b'n', b'e', b's', b't', b'e', b'd', b'_', b'i', b'd', b'e', b'n', b't', b'i',
            b't', b'y', b'_', b'b', b'e', b't', b'a',
        ];
        let recipe = nested_identity_conversion_test_recipe();
        assert_eq!(recipe.as_bytes(), VERSION_3_NESTED_IDENTITY);
        assert_eq!(
            SealedHolProofRecipe::from_untrusted_bytes(VERSION_3_NESTED_IDENTITY).unwrap(),
            recipe
        );
        let kernel = Kernel::ephemeral();
        let artifact = recipe.replay(&kernel).unwrap();
        assert_eq!(artifact.signer(), kernel.key_id());
    }

    #[test]
    fn canonical_schematic_binding_recipe_has_fixed_wire_and_replays() {
        let recipe = schematic_binding_test_recipe();
        assert_eq!(
            SealedHolProofRecipe::from_untrusted_bytes(recipe.as_bytes()).unwrap(),
            recipe
        );
        let kernel = Kernel::ephemeral();
        let artifact = recipe.replay(&kernel).unwrap();
        assert_eq!(artifact.signer(), kernel.key_id());
        assert_eq!(recipe.as_bytes(), SCHEMATIC_BINDING_WIRE);
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
                    RecipeNode::EmptyContext,
                    RecipeNode::ConversionEta { function: 1 }
                ],
                1
            )
            .is_err()
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
        for version in [1, 2] {
            let mut old_version = closed_beta().as_bytes().to_vec();
            old_version[0] = version;
            assert!(matches!(
                SealedHolProofRecipe::from_untrusted_bytes(&old_version),
                Err(HolProofRecipeError::Invalid(
                    "unsupported sealed recipe version"
                ))
            ));
        }

        assert!(
            SealedHolProofRecipe::seal(
                vec![
                    RecipeNode::BoolType,
                    RecipeNode::EmptyTermInstantiationMap,
                    RecipeNode::ExtendTermInstantiationMap {
                        base: 1,
                        variable: 0,
                        replacement: 0,
                    },
                    RecipeNode::Namespace { name: None },
                ],
                3,
            )
            .is_err()
        );
    }

    #[test]
    fn conversion_structure_rejects_forward_and_wrong_sort_dependencies() {
        let invalid = [
            vec![
                RecipeNode::Bool(true),
                RecipeNode::ConversionSymmetry { conversion: 0 },
                RecipeNode::Namespace { name: None },
            ],
            vec![
                RecipeNode::BoolType,
                RecipeNode::Bool(true),
                RecipeNode::ConversionLambda {
                    parameter_type: 1,
                    body: 0,
                },
                RecipeNode::Namespace { name: None },
            ],
            vec![
                RecipeNode::Bool(true),
                RecipeNode::ConversionReflexivity { term: 0 },
                RecipeNode::ConversionTransitivity {
                    first: 1,
                    second: 3,
                },
                RecipeNode::Namespace { name: None },
            ],
        ];
        for nodes in invalid {
            let selected = nodes.len() - 1;
            assert!(SealedHolProofRecipe::seal(nodes, selected).is_err());
        }
    }

    #[test]
    fn remaining_conversion_forms_replay_checked_positive_cases() {
        let recipe = SealedHolProofRecipe::seal(
            vec![
                RecipeNode::BoolType,
                RecipeNode::Bound { index: 0, ty: 0 },
                RecipeNode::Lambda {
                    parameter_type: 0,
                    body: 1,
                },
                RecipeNode::Bool(true),
                RecipeNode::Application {
                    function: 2,
                    argument: 3,
                },
                RecipeNode::Epsilon { predicate: 2 },
                RecipeNode::ConversionBeta {
                    abstraction: 2,
                    argument: 3,
                },
                RecipeNode::ConversionSymmetry { conversion: 6 },
                RecipeNode::ConversionSymmetry { conversion: 7 },
                RecipeNode::ConversionLambda {
                    parameter_type: 0,
                    body: 8,
                },
                RecipeNode::ConversionEta { function: 2 },
                RecipeNode::ConversionEpsilon { predicate: 10 },
                RecipeNode::EmptyContext,
                RecipeNode::ConversionEquality {
                    context: 12,
                    conversion: 9,
                },
                RecipeNode::Persist { theorem: 13 },
                RecipeNode::Namespace { name: None },
                RecipeNode::ExportContext {
                    namespace: 15,
                    export: 0,
                    context: 12,
                    name: None,
                },
                RecipeNode::ExportTheorem {
                    namespace: 15,
                    export: 1,
                    theorem: 13,
                    name: None,
                },
            ],
            15,
        )
        .unwrap();
        assert_eq!(
            SealedHolProofRecipe::from_untrusted_bytes(recipe.as_bytes()).unwrap(),
            recipe
        );
        recipe.replay(&Kernel::ephemeral()).unwrap();
    }

    #[test]
    fn theorem_transport_rechecks_the_conversion_endpoint_during_replay() {
        let recipe = SealedHolProofRecipe::seal(
            vec![
                RecipeNode::Bool(true),
                RecipeNode::EmptyContext,
                RecipeNode::ConversionReflexivity { term: 0 },
                RecipeNode::ConversionEquality {
                    context: 1,
                    conversion: 2,
                },
                RecipeNode::ConvertTheorem {
                    theorem: 3,
                    conversion: 2,
                },
                RecipeNode::Namespace { name: None },
            ],
            5,
        )
        .unwrap();
        assert!(matches!(
            recipe.replay(&Kernel::ephemeral()),
            Err(HolProofRecipeError::Replay(message))
                if message.contains("does not match conversion endpoint")
        ));
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

    #[test]
    fn rejects_unknown_truncated_and_duplicate_map_encodings() {
        let mut unknown = schematic_binding_test_recipe().as_bytes().to_vec();
        unknown[5] = u8::MAX;
        assert!(matches!(
            SealedHolProofRecipe::from_untrusted_bytes(&unknown),
            Err(HolProofRecipeError::Invalid(
                "unknown sealed recipe node tag"
            ))
        ));
        for retired_tag in [5, 10] {
            assert!(matches!(
                SealedHolProofRecipe::from_untrusted_bytes(&[3, 0, 1, 0, 0, retired_tag]),
                Err(HolProofRecipeError::Invalid(
                    "unknown sealed recipe node tag"
                ))
            ));
        }

        let mut truncated = schematic_binding_test_recipe().as_bytes().to_vec();
        truncated.pop();
        assert!(matches!(
            SealedHolProofRecipe::from_untrusted_bytes(&truncated),
            Err(HolProofRecipeError::Invalid("truncated sealed recipe"))
        ));

        assert!(matches!(
            SealedHolProofRecipe::seal(
                vec![
                    RecipeNode::FreeType { symbol: 0 },
                    RecipeNode::FreeTerm { symbol: 0, ty: 0 },
                    RecipeNode::FreeTerm { symbol: 1, ty: 0 },
                    RecipeNode::EmptyTermInstantiationMap,
                    RecipeNode::ExtendTermInstantiationMap {
                        base: 3,
                        variable: 1,
                        replacement: 2,
                    },
                    RecipeNode::ExtendTermInstantiationMap {
                        base: 4,
                        variable: 1,
                        replacement: 2,
                    },
                    RecipeNode::Namespace { name: None },
                ],
                6,
            ),
            Err(HolProofRecipeError::Invalid(
                "duplicate term-instantiation recipe key"
            ))
        ));

        assert!(matches!(
            SealedHolProofRecipe::seal(
                vec![
                    RecipeNode::FreeType { symbol: 0 },
                    RecipeNode::BoolType,
                    RecipeNode::EmptyTypeInstantiationMap,
                    RecipeNode::ExtendTypeInstantiationMap {
                        base: 2,
                        variable: 0,
                        replacement: 1,
                    },
                    RecipeNode::ExtendTypeInstantiationMap {
                        base: 3,
                        variable: 0,
                        replacement: 1,
                    },
                    RecipeNode::Namespace { name: None },
                ],
                5,
            ),
            Err(HolProofRecipeError::Invalid(
                "duplicate type-instantiation recipe key"
            ))
        ));
    }

    #[test]
    fn nucleus_rejects_distinct_recipe_keys_that_canonicalize_to_one_free_term() {
        let recipe = SealedHolProofRecipe::seal(
            vec![
                RecipeNode::FreeType { symbol: 0 },
                RecipeNode::Bound { index: 0, ty: 0 },
                RecipeNode::Lambda {
                    parameter_type: 0,
                    body: 1,
                },
                RecipeNode::FreeTerm { symbol: 0, ty: 0 },
                RecipeNode::FreeTerm { symbol: 0, ty: 0 },
                RecipeNode::FreeTerm { symbol: 1, ty: 0 },
                RecipeNode::EmptyContext,
                RecipeNode::ConversionBeta {
                    abstraction: 2,
                    argument: 3,
                },
                RecipeNode::ConversionEquality {
                    context: 6,
                    conversion: 7,
                },
                RecipeNode::EmptyTermInstantiationMap,
                RecipeNode::ExtendTermInstantiationMap {
                    base: 9,
                    variable: 3,
                    replacement: 5,
                },
                RecipeNode::ExtendTermInstantiationMap {
                    base: 10,
                    variable: 4,
                    replacement: 5,
                },
                RecipeNode::TermInstantiation {
                    theorem: 8,
                    instantiations: 11,
                },
                RecipeNode::Namespace { name: None },
            ],
            13,
        )
        .unwrap();
        assert!(matches!(
            recipe.replay(&Kernel::ephemeral()),
            Err(HolProofRecipeError::Replay(message))
                if message.contains("occurs more than once")
        ));
    }
}
