//! Pinned `SpecTec` source bundles and a resource-bounded elaborated IL reader.
//!
//! `SpecTec` remains userspace. This crate verifies byte identity and recognizes
//! the upstream S-expression shape; neither operation grants theorem authority
//! or establishes correspondence with the WebAssembly specification.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Component, Path},
};

use covalence_data_cbor::drisl::{self, Cid, CidCodec, CidHash, Policy, Value};
use covalence_data_sexpr::{
    Document, Event, ParseError, Parser, PrintError, Printer, StructureError,
};
use covalence_lib_error::snafu::Snafu;

mod il;
mod wasm3;

pub use il::{
    ClauseId, DeclarationId, IlArgument, IlBinding, IlChildren, IlClause, IlClauseSchema, IlCursor,
    IlDeclaration, IlDeclarationBody, IlDeclarationSchema, IlDocument, IlDomain, IlError,
    IlExpression, IlExpressionKind, IlForm, IlIteration, IlKind, IlNode, IlPremise,
    IlProductionSchema, IlRoot, IlRule, IlRuleSchema, IlSchemaError, IlType, IlTypeBinding,
    RootOrdinal, RuleId,
};
pub use wasm3::{WASM_3_AST_BYTES, WASM_3_MANIFEST_BYTES, Wasm3Bundle, Wasm3Error, wasm3_bundle};

/// Schema discriminator for pinned `SpecTec` source bundles.
pub const FORMAT: &str = "io.github.imbrem.nucleus.spectecBundleV1";

/// Official upstream repository pinned by the first bundle.
pub const WASM_UPSTREAM: &str = "https://github.com/WebAssembly/spec";

/// Official WebAssembly 3.0 working-group release commit.
pub const WASM_3_REVISION: &str = "9d36019973201a19f9c9ebb0f10828b2fe2374aa";

/// Upstream release name carrying [`WASM_3_REVISION`].
pub const WASM_3_RELEASE: &str = "wg-3.0";

/// `SpecTec` version reported by the pinned executable.
pub const SPECTEC_VERSION: &str = "0.5";

/// Exact ordered source set passed to `SpecTec` for the Wasm 3.0 bundle.
pub const WASM_3_SOURCES: &[&str] = &[
    "0.1-aux.vars.spectec",
    "0.2-aux.num.spectec",
    "0.3-aux.seq.spectec",
    "1.0-syntax.profiles.spectec",
    "1.1-syntax.values.spectec",
    "1.2-syntax.types.spectec",
    "1.3-syntax.instructions.spectec",
    "1.4-syntax.modules.spectec",
    "2.0-validation.contexts.spectec",
    "2.1-validation.types.spectec",
    "2.2-validation.subtyping.spectec",
    "2.3-validation.instructions.spectec",
    "2.4-validation.modules.spectec",
    "3.0-numerics.relaxed.spectec",
    "3.1-numerics.scalar.spectec",
    "3.2-numerics.vector.spectec",
    "4.0-execution.configurations.spectec",
    "4.1-execution.values.spectec",
    "4.2-execution.types.spectec",
    "4.3-execution.instructions.spectec",
    "4.4-execution.modules.spectec",
    "5.1-binary.values.spectec",
    "5.2-binary.types.spectec",
    "5.3-binary.instructions.spectec",
    "5.4-binary.modules.spectec",
    "6.0-text.lexical.spectec",
    "6.1-text.values.spectec",
    "6.2-text.types.spectec",
    "6.3-text.instructions.spectec",
    "6.3-text.modules.spectec",
    "X.1-notation.syntax.spectec",
    "X.2-notation.typing.spectec",
    "X.3-notation.execution.spectec",
    "X.4-notation.binary.spectec",
    "X.5-notation.text.spectec",
];

/// Resource limits applied before constructing a recursive owned AST.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Limits {
    /// Maximum UTF-8 input bytes.
    pub bytes: usize,
    /// Maximum parser events.
    pub events: u64,
    /// Maximum list nesting.
    pub depth: usize,
    /// Maximum top-level forms.
    pub roots: u64,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            bytes: 8 * 1024 * 1024,
            events: 2_000_000,
            depth: 256,
            roots: 100_000,
        }
    }
}

/// Structural metrics for one elaborated `SpecTec` IL document.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AstSummary {
    /// Exact source bytes.
    pub bytes: u64,
    /// Total open, atom, and close events.
    pub events: u64,
    /// Number of top-level forms.
    pub roots: u64,
    /// Greatest list nesting reached.
    pub max_depth: u64,
}

/// A bounded parsed `SpecTec` IL document.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParsedAst {
    /// Owned S-expression document with source spans.
    pub document: Document,
    /// Metrics checked before the document was constructed.
    pub summary: AstSummary,
}

/// Why elaborated `SpecTec` IL could not be read under a resource policy.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum AstError {
    /// Input was not UTF-8.
    #[snafu(display("SpecTec AST is not UTF-8: {source}"))]
    Utf8 {
        /// UTF-8 decoder failure.
        source: std::str::Utf8Error,
    },
    /// Input exceeded the byte budget.
    #[snafu(display("SpecTec AST is {actual} bytes; limit is {limit}"))]
    Bytes {
        /// Actual input bytes.
        actual: usize,
        /// Configured byte limit.
        limit: usize,
    },
    /// Input exceeded the event budget.
    #[snafu(display("SpecTec AST has more than {limit} events"))]
    Events {
        /// Configured event limit.
        limit: u64,
    },
    /// Input exceeded the nesting budget.
    #[snafu(display("SpecTec AST nesting exceeds {limit}"))]
    Depth {
        /// Configured nesting limit.
        limit: usize,
    },
    /// Input exceeded the top-level form budget.
    #[snafu(display("SpecTec AST has more than {limit} top-level forms"))]
    Roots {
        /// Configured root limit.
        limit: u64,
    },
    /// Upstream IL roots must be proper lists.
    #[snafu(display("SpecTec AST has a top-level atom at byte {offset}"))]
    TopLevelAtom {
        /// Source byte offset.
        offset: u64,
    },
    /// S-expression syntax was malformed.
    #[snafu(display("could not parse SpecTec AST: {source}"))]
    Parse {
        /// Concrete syntax failure.
        source: ParseError,
    },
    /// A parser event stream was structurally invalid.
    #[snafu(display("could not construct SpecTec AST: {source}"))]
    Structure {
        /// Event folding failure.
        source: StructureError,
    },
    /// A recognized document could not be printed losslessly.
    #[snafu(display("could not print SpecTec AST: {source}"))]
    Print {
        /// Concrete printing failure.
        source: PrintError,
    },
}

/// Parses an elaborated `SpecTec` IL S-expression under explicit limits.
///
/// # Errors
///
/// Returns an error for non-UTF-8 or malformed syntax, top-level atoms, or any
/// configured resource limit. Limits are checked before recursive AST storage
/// is constructed.
///
/// # Panics
///
/// Panics only on a target whose address space can hold a slice longer than
/// `u64::MAX` bytes.
pub fn parse_ast(bytes: &[u8], limits: Limits) -> Result<ParsedAst, AstError> {
    if bytes.len() > limits.bytes {
        return Err(AstError::Bytes {
            actual: bytes.len(),
            limit: limits.bytes,
        });
    }
    let input = std::str::from_utf8(bytes).map_err(|source| AstError::Utf8 { source })?;
    let mut events = Vec::new();
    let mut event_count = 0_u64;
    let mut roots = 0_u64;
    let mut depth = 0_usize;
    let mut max_depth = 0_usize;

    for event in Parser::new(input) {
        let event = event.map_err(|source| AstError::Parse { source })?;
        event_count = event_count.checked_add(1).ok_or(AstError::Events {
            limit: limits.events,
        })?;
        if event_count > limits.events {
            return Err(AstError::Events {
                limit: limits.events,
            });
        }
        match &event {
            Event::Open { .. } => {
                if depth == 0 {
                    roots = roots.checked_add(1).ok_or(AstError::Roots {
                        limit: limits.roots,
                    })?;
                    if roots > limits.roots {
                        return Err(AstError::Roots {
                            limit: limits.roots,
                        });
                    }
                }
                depth = depth.checked_add(1).ok_or(AstError::Depth {
                    limit: limits.depth,
                })?;
                if depth > limits.depth {
                    return Err(AstError::Depth {
                        limit: limits.depth,
                    });
                }
                max_depth = max_depth.max(depth);
            }
            Event::Atom { span, .. } if depth == 0 => {
                return Err(AstError::TopLevelAtom { offset: span.start });
            }
            Event::Atom { .. } => {}
            Event::Close { .. } => {
                depth = depth.saturating_sub(1);
            }
        }
        events.push(event);
    }

    let document =
        Document::from_events(events).map_err(|source| AstError::Structure { source })?;
    Ok(ParsedAst {
        document,
        summary: AstSummary {
            bytes: u64::try_from(bytes.len()).expect("usize fits in u64"),
            events: event_count,
            roots,
            max_depth: u64::try_from(max_depth).expect("usize fits in u64"),
        },
    })
}

/// Canonically prints a bounded `SpecTec` AST with one final newline.
///
/// # Errors
///
/// Returns any parsing, resource, or lossless-printing error.
pub fn canonical_ast(bytes: &[u8], limits: Limits) -> Result<String, AstError> {
    let parsed = parse_ast(bytes, limits)?;
    let mut output = Printer::default()
        .document(&parsed.document)
        .map_err(|source| AstError::Print { source })?;
    output.push('\n');
    Ok(output)
}

/// One content-addressed file named by a bundle manifest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Artifact {
    /// Bundle-relative path.
    pub path: String,
    /// Exact byte length.
    pub bytes: u64,
    /// Raw SHA-256 CID for the exact bytes.
    pub cid: Cid,
}

impl Artifact {
    /// Describes exact bytes using a raw SHA-256 CID.
    ///
    /// # Panics
    ///
    /// Panics only on a target whose address space can hold a slice longer than
    /// `u64::MAX` bytes.
    #[must_use]
    pub fn from_bytes(path: impl Into<String>, bytes: &[u8]) -> Self {
        Self {
            path: path.into(),
            bytes: u64::try_from(bytes.len()).expect("usize fits in u64"),
            cid: drisl::address(CidCodec::Raw, CidHash::Sha256, bytes),
        }
    }

    /// Checks byte length and content address.
    ///
    /// # Errors
    ///
    /// Returns a typed mismatch without interpreting the bytes.
    ///
    /// # Panics
    ///
    /// Panics only on a target whose address space can hold a slice longer than
    /// `u64::MAX` bytes.
    pub fn verify(&self, bytes: &[u8]) -> Result<(), ArtifactError> {
        if self.cid.codec() != CidCodec::Raw || self.cid.hash() != CidHash::Sha256 {
            return Err(ArtifactError::Link {
                path: self.path.clone(),
            });
        }
        let actual = u64::try_from(bytes.len()).expect("usize fits in u64");
        if actual != self.bytes {
            return Err(ArtifactError::Length {
                path: self.path.clone(),
                expected: self.bytes,
                actual,
            });
        }
        if !drisl::addresses(self.cid, bytes) {
            return Err(ArtifactError::Address {
                path: self.path.clone(),
            });
        }
        Ok(())
    }
}

/// A pinned elaborated IL artifact and its checked structural metrics.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AstArtifact {
    /// Exact content-addressed bytes emitted by upstream `SpecTec`.
    pub artifact: Artifact,
    /// Structural metrics under the bundle policy.
    pub summary: AstSummary,
}

/// Complete immutable provenance for one `SpecTec` bundle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BundleManifest {
    /// Upstream repository URL.
    pub upstream: String,
    /// Exact upstream Git commit.
    pub revision: String,
    /// Human release name resolving to the commit.
    pub release: String,
    /// `SpecTec` executable version.
    pub generator_version: String,
    /// Exact semantic command arguments after the executable name.
    pub generator_arguments: Vec<String>,
    /// Ordered source artifacts.
    pub sources: Vec<Artifact>,
    /// Generated elaborated IL.
    pub ast: AstArtifact,
    /// License/provenance text shipped with the bundle.
    pub licenses: Vec<Artifact>,
}

impl BundleManifest {
    /// Encodes the manifest in canonical `ATProto` DRISL normal form.
    ///
    /// # Errors
    ///
    /// Returns an error if a recorded unsigned metric does not fit DRISL's
    /// signed integer domain or if canonical encoding fails.
    pub fn encode(&self) -> Result<Vec<u8>, ManifestError> {
        let value = self.to_value()?;
        drisl::encode(Policy::ATPROTO, &value).map_err(|source| ManifestError::Encode { source })
    }

    /// Decodes one complete canonical manifest.
    ///
    /// # Errors
    ///
    /// Rejects noncanonical DRISL, links outside the `ATProto` SHA-256 policy,
    /// missing fields, wrong value kinds, negative metrics, or format drift.
    pub fn decode(bytes: &[u8]) -> Result<Self, ManifestError> {
        let value = drisl::decode(Policy::ATPROTO, bytes)
            .map_err(|source| ManifestError::Decode { source })?;
        Self::from_value(&value)
    }

    /// Converts this record to its extensional DRISL value.
    ///
    /// # Errors
    ///
    /// Returns an error if an unsigned metric is outside the signed DRISL
    /// integer domain.
    pub fn to_value(&self) -> Result<Value, ManifestError> {
        self.validate()?;
        Ok(Value::Map(BTreeMap::from([
            ("format".to_owned(), Value::Text(FORMAT.to_owned())),
            (
                "upstream".to_owned(),
                Value::Map(BTreeMap::from([
                    ("repository".to_owned(), Value::Text(self.upstream.clone())),
                    ("release".to_owned(), Value::Text(self.release.clone())),
                    ("revision".to_owned(), Value::Text(self.revision.clone())),
                ])),
            ),
            (
                "generator".to_owned(),
                Value::Map(BTreeMap::from([
                    (
                        "arguments".to_owned(),
                        Value::Array(
                            self.generator_arguments
                                .iter()
                                .cloned()
                                .map(Value::Text)
                                .collect(),
                        ),
                    ),
                    (
                        "version".to_owned(),
                        Value::Text(self.generator_version.clone()),
                    ),
                ])),
            ),
            (
                "sources".to_owned(),
                Value::Array(
                    self.sources
                        .iter()
                        .map(artifact_value)
                        .collect::<Result<_, _>>()?,
                ),
            ),
            (
                "ast".to_owned(),
                Value::Map(BTreeMap::from([
                    ("artifact".to_owned(), artifact_value(&self.ast.artifact)?),
                    (
                        "events".to_owned(),
                        metric("ast.events", self.ast.summary.events)?,
                    ),
                    (
                        "maxDepth".to_owned(),
                        metric("ast.maxDepth", self.ast.summary.max_depth)?,
                    ),
                    (
                        "roots".to_owned(),
                        metric("ast.roots", self.ast.summary.roots)?,
                    ),
                ])),
            ),
            (
                "licenses".to_owned(),
                Value::Array(
                    self.licenses
                        .iter()
                        .map(artifact_value)
                        .collect::<Result<_, _>>()?,
                ),
            ),
        ])))
    }

    fn validate(&self) -> Result<(), ManifestError> {
        let artifacts = self
            .sources
            .iter()
            .chain([&self.ast.artifact])
            .chain(&self.licenses);
        for artifact in artifacts.clone() {
            validate_artifact(artifact)?;
        }
        unique_artifact_paths(artifacts)
    }

    fn from_value(value: &Value) -> Result<Self, ManifestError> {
        let root = value_map(value, "manifest")?;
        let format = value_text(field(root, "format")?, "format")?;
        if format != FORMAT {
            return Err(ManifestError::Format {
                actual: format.to_owned(),
            });
        }
        let upstream = value_map(field(root, "upstream")?, "upstream")?;
        let generator = value_map(field(root, "generator")?, "generator")?;
        let ast = value_map(field(root, "ast")?, "ast")?;

        let arguments = value_array(field(generator, "arguments")?, "generator.arguments")?
            .iter()
            .map(|value| value_text(value, "generator.arguments[]").map(ToOwned::to_owned))
            .collect::<Result<Vec<_>, _>>()?;
        let sources = value_array(field(root, "sources")?, "sources")?
            .iter()
            .map(|value| parse_artifact(value, "sources[]"))
            .collect::<Result<Vec<_>, _>>()?;
        let licenses = value_array(field(root, "licenses")?, "licenses")?
            .iter()
            .map(|value| parse_artifact(value, "licenses[]"))
            .collect::<Result<Vec<_>, _>>()?;
        let artifact = parse_artifact(field(ast, "artifact")?, "ast.artifact")?;
        let ast_bytes = artifact.bytes;
        let manifest = Self {
            upstream: value_text(field(upstream, "repository")?, "upstream.repository")?.to_owned(),
            revision: value_text(field(upstream, "revision")?, "upstream.revision")?.to_owned(),
            release: value_text(field(upstream, "release")?, "upstream.release")?.to_owned(),
            generator_version: value_text(field(generator, "version")?, "generator.version")?
                .to_owned(),
            generator_arguments: arguments,
            sources,
            ast: AstArtifact {
                artifact,
                summary: AstSummary {
                    bytes: ast_bytes,
                    events: value_u64(field(ast, "events")?, "ast.events")?,
                    roots: value_u64(field(ast, "roots")?, "ast.roots")?,
                    max_depth: value_u64(field(ast, "maxDepth")?, "ast.maxDepth")?,
                },
            },
            licenses,
        };
        manifest.validate()?;
        Ok(manifest)
    }
}

/// Why pinned bytes disagreed with a manifest artifact.
#[derive(Clone, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ArtifactError {
    /// The artifact address was not a raw SHA-256 CID.
    #[snafu(display("artifact {path:?} is not addressed by a raw SHA-256 CID"))]
    Link {
        /// Bundle-relative path.
        path: String,
    },
    /// Byte length differed.
    #[snafu(display("artifact {path:?} is {actual} bytes; expected {expected}"))]
    Length {
        /// Bundle-relative path.
        path: String,
        /// Manifest length.
        expected: u64,
        /// Actual length.
        actual: u64,
    },
    /// SHA-256 content address differed.
    #[snafu(display("artifact {path:?} does not match its SHA-256 CID"))]
    Address {
        /// Bundle-relative path.
        path: String,
    },
}

/// Why a canonical `SpecTec` bundle manifest was rejected.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ManifestError {
    /// Canonical DRISL decoding failed.
    #[snafu(display("could not decode SpecTec manifest: {source}"))]
    Decode {
        /// DRISL decoder failure.
        source: drisl::DecodeError,
    },
    /// Canonical DRISL encoding failed.
    #[snafu(display("could not encode SpecTec manifest: {source}"))]
    Encode {
        /// DRISL encoder failure.
        source: drisl::EncodeError,
    },
    /// A required map field was absent.
    #[snafu(display("SpecTec manifest is missing field {field:?}"))]
    Missing {
        /// Missing field name.
        field: &'static str,
    },
    /// A field had the wrong DRISL kind.
    #[snafu(display("SpecTec manifest field {field:?} must be {expected}"))]
    Kind {
        /// Field path.
        field: &'static str,
        /// Required value kind.
        expected: &'static str,
    },
    /// An unsigned metric did not fit the DRISL integer domain.
    #[snafu(display("SpecTec manifest metric {field:?} is outside signed 64-bit range"))]
    Metric {
        /// Metric path.
        field: &'static str,
    },
    /// The schema discriminator was unknown.
    #[snafu(display("unsupported SpecTec manifest format {actual:?}"))]
    Format {
        /// Rejected discriminator.
        actual: String,
    },
    /// An artifact path was empty, absolute, or escaped the bundle root.
    #[snafu(display("SpecTec artifact path {path:?} is not a safe bundle-relative path"))]
    ArtifactPath {
        /// Rejected path.
        path: String,
    },
    /// Two manifest artifacts used the same bundle-relative path.
    #[snafu(display("SpecTec artifact path {path:?} occurs more than once"))]
    DuplicatePath {
        /// Repeated path.
        path: String,
    },
}

fn artifact_value(artifact: &Artifact) -> Result<Value, ManifestError> {
    Ok(Value::Map(BTreeMap::from([
        ("path".to_owned(), Value::Text(artifact.path.clone())),
        (
            "bytes".to_owned(),
            metric("artifact.bytes", artifact.bytes)?,
        ),
        ("cid".to_owned(), Value::Link(artifact.cid)),
    ])))
}

fn parse_artifact(value: &Value, field_name: &'static str) -> Result<Artifact, ManifestError> {
    let value = value_map(value, field_name)?;
    let artifact = Artifact {
        path: value_text(field(value, "path")?, "artifact.path")?.to_owned(),
        bytes: value_u64(field(value, "bytes")?, "artifact.bytes")?,
        cid: value_link(field(value, "cid")?, "artifact.cid")?,
    };
    validate_artifact(&artifact)?;
    Ok(artifact)
}

fn validate_artifact(artifact: &Artifact) -> Result<(), ManifestError> {
    let path = Path::new(&artifact.path);
    if artifact.path.is_empty()
        || artifact.path.contains('\\')
        || path.is_absolute()
        || !path
            .components()
            .all(|part| matches!(part, Component::Normal(_)))
    {
        return Err(ManifestError::ArtifactPath {
            path: artifact.path.clone(),
        });
    }
    if artifact.cid.codec() != CidCodec::Raw || artifact.cid.hash() != CidHash::Sha256 {
        return Err(ManifestError::Kind {
            field: "artifact.cid",
            expected: "a raw SHA-256 CID link",
        });
    }
    Ok(())
}

fn unique_artifact_paths<'a>(
    artifacts: impl IntoIterator<Item = &'a Artifact>,
) -> Result<(), ManifestError> {
    let mut paths = BTreeSet::new();
    for artifact in artifacts {
        if !paths.insert(&artifact.path) {
            return Err(ManifestError::DuplicatePath {
                path: artifact.path.clone(),
            });
        }
    }
    Ok(())
}

fn metric(field: &'static str, value: u64) -> Result<Value, ManifestError> {
    i64::try_from(value)
        .map(Value::Integer)
        .map_err(|_| ManifestError::Metric { field })
}

fn field<'a>(
    map: &'a BTreeMap<String, Value>,
    field: &'static str,
) -> Result<&'a Value, ManifestError> {
    map.get(field).ok_or(ManifestError::Missing { field })
}

fn value_map<'a>(
    value: &'a Value,
    field: &'static str,
) -> Result<&'a BTreeMap<String, Value>, ManifestError> {
    let Value::Map(value) = value else {
        return Err(ManifestError::Kind {
            field,
            expected: "a map",
        });
    };
    Ok(value)
}

fn value_array<'a>(value: &'a Value, field: &'static str) -> Result<&'a [Value], ManifestError> {
    let Value::Array(value) = value else {
        return Err(ManifestError::Kind {
            field,
            expected: "an array",
        });
    };
    Ok(value)
}

fn value_text<'a>(value: &'a Value, field: &'static str) -> Result<&'a str, ManifestError> {
    let Value::Text(value) = value else {
        return Err(ManifestError::Kind {
            field,
            expected: "text",
        });
    };
    Ok(value)
}

fn value_link(value: &Value, field: &'static str) -> Result<Cid, ManifestError> {
    let Value::Link(value) = value else {
        return Err(ManifestError::Kind {
            field,
            expected: "a CID link",
        });
    };
    Ok(*value)
}

fn value_u64(value: &Value, field: &'static str) -> Result<u64, ManifestError> {
    let Value::Integer(value) = value else {
        return Err(ManifestError::Kind {
            field,
            expected: "a non-negative integer",
        });
    };
    u64::try_from(*value).map_err(|_| ManifestError::Metric { field })
}
