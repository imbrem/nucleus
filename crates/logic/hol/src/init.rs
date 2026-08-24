//! Deterministic compilation of the transitional checked init manifest.
//!
//! This is the executable Boolean slice of `theories/init.json`, not a second
//! general constructor catalogue. Its deliberately small raw-node vocabulary
//! is expected to migrate into the shared manifest work tracked by issue #745.

use std::collections::{BTreeMap, BTreeSet};

use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use serde::{Deserialize, Serialize};

use crate::{Arena, Kernel, KernelError, Ref};

/// The only checked init-manifest format currently accepted by the compiler.
pub const FORMAT: &str = "nucleus.hol.init.checked-boolean-v0";

/// An ordered, opcode-free init manifest.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Manifest {
    /// Format discriminator. Must equal [`FORMAT`].
    pub format: String,
    /// Human-readable migration note tying this slice to issue #745.
    pub migration: String,
    /// Definitions in dependency order.
    pub declarations: Vec<Declaration>,
}

impl Manifest {
    /// Returns the canonical content hash of this complete manifest record.
    ///
    /// The hash covers the deterministic CBOR encoding of every manifest
    /// field, including the format, migration note, declaration names,
    /// dependencies, and raw rows. This is distinct from [`Arena::addr`],
    /// which hashes only the compiled arena prefix and deliberately excludes
    /// names and migration metadata.
    ///
    /// # Panics
    ///
    /// Panics only if this manifest's derived Serde implementation rejects
    /// encoding to an in-memory buffer.
    #[must_use]
    pub fn addr(&self) -> O256 {
        let mut bytes = Vec::new();
        covalence_lib_cbor::into_writer(self, &mut bytes)
            .expect("serializing a checked init manifest into memory cannot fail");
        O256::from_bytes(&bytes)
    }
}

/// One named raw definition.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct Declaration {
    /// Stable public name of the final row.
    pub name: String,
    /// Exact earlier declarations referenced by the body.
    pub dependencies: Vec<String>,
    /// Ordered primitive rows; the final row defines `name`.
    pub body: Vec<RawRow>,
}

/// One locally named row in a definition body.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct RawRow {
    /// Name visible to later rows in the same body.
    pub id: String,
    /// Opcode-free primitive constructor.
    #[serde(flatten)]
    pub node: RawNode,
}

/// Primitive Ethane nodes allowed in the first checked Boolean slice.
///
/// Serde's internally tagged representation rejects every unknown tag,
/// including `Op1`, `Op2`, and literal-surface opcodes.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "tag", deny_unknown_fields)]
pub enum RawNode {
    /// `kind.star`.
    #[serde(rename = "kind.star")]
    KindStar,
    /// `ty.bool`, classified by `star`.
    #[serde(rename = "ty.bool")]
    BoolTy { star: String },
    /// `ty.arr`.
    #[serde(rename = "ty.arr")]
    TyArr { domain: String, codomain: String },
    /// Intrinsically typed free term variable.
    #[serde(rename = "tm.fv")]
    TmFv { name: u64, ty: String },
    /// Term abstraction over an explicit free-variable row.
    #[serde(rename = "tm.lam")]
    TmLam {
        function_ty: String,
        binder: String,
        body: String,
    },
    /// Object-language equality.
    #[serde(rename = "tm.eq")]
    TmEq {
        bool_ty: String,
        left: String,
        right: String,
    },
}

/// Checked result and stable declaration-name index.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Compiled {
    arena: Arena,
    names: BTreeMap<String, Ref>,
    manifest_addr: O256,
}

impl Compiled {
    /// Borrows the checked arena prefix.
    #[must_use]
    pub const fn arena(&self) -> &Arena {
        &self.arena
    }

    /// Creates a kernel initialized with this compiled arena prefix.
    ///
    /// Kernels created from compiled prefixes with the same arena address and
    /// length can copy prefix references between one another as identities.
    /// Manifest names and migration metadata do not affect that identity.
    #[must_use]
    pub fn kernel(&self) -> Kernel {
        Kernel::with_init_prefix(self.arena.clone())
    }

    /// Returns the complete source-manifest hash used for this compilation.
    ///
    /// Unlike [`Arena::addr`], this changes when stable names or migration
    /// metadata change even if the compiled arena prefix stays identical.
    #[must_use]
    pub const fn manifest_addr(&self) -> O256 {
        self.manifest_addr
    }

    /// Resolves one stable declaration name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Ref> {
        self.names.get(name).copied()
    }

    /// Iterates stable names in lexical order.
    #[must_use]
    pub fn names(&self) -> impl ExactSizeIterator<Item = (&str, Ref)> {
        self.names
            .iter()
            .map(|(name, reference)| (name.as_str(), *reference))
    }
}

/// A rejected checked init manifest.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CompileError {
    /// The top-level format discriminator is unsupported.
    #[snafu(display("unsupported init manifest format {actual:?}"))]
    Format { actual: String },
    /// A declaration or local row has an empty name.
    #[snafu(display("init manifest names must not be empty"))]
    EmptyName,
    /// A declaration repeats an earlier stable name.
    #[snafu(display("duplicate declaration name {name:?}"))]
    DuplicateDeclaration { name: String },
    /// A definition has no rows and therefore no root.
    #[snafu(display("definition {name:?} has no body rows"))]
    EmptyBody { name: String },
    /// A local row name is repeated within a definition.
    #[snafu(display("duplicate local row name {name:?} in definition {declaration:?}"))]
    DuplicateLocal { declaration: String, name: String },
    /// A row refers to neither an earlier local nor an earlier declaration.
    #[snafu(display("unresolved or forward reference {name:?} in definition {declaration:?}"))]
    UnresolvedReference { declaration: String, name: String },
    /// The explicit dependency list differs from references actually used.
    #[snafu(display(
        "definition {declaration:?} declares dependencies {declared:?}, but uses {used:?}"
    ))]
    DependencyMismatch {
        declaration: String,
        declared: Vec<String>,
        used: Vec<String>,
    },
    /// A raw row failed checked kernel construction.
    #[snafu(display("definition {declaration:?} row {row:?} failed validation: {source}"))]
    Kernel {
        declaration: String,
        row: String,
        source: KernelError,
    },
}

/// Validates and compiles a manifest to a checked Ethane arena prefix.
///
/// # Errors
///
/// Returns an error for an unsupported format, duplicate or empty names,
/// unresolved/forward references, inaccurate dependencies, empty bodies, or a
/// raw row rejected by the existing Ethane kernel constructors.
#[allow(clippy::too_many_lines)]
pub fn compile(manifest: &Manifest) -> Result<Compiled, CompileError> {
    if manifest.format != FORMAT {
        return Err(CompileError::Format {
            actual: manifest.format.clone(),
        });
    }

    let mut kernel = Kernel::new();
    let mut globals = BTreeMap::new();
    for declaration in &manifest.declarations {
        if declaration.name.is_empty() {
            return Err(CompileError::EmptyName);
        }
        if globals.contains_key(&declaration.name) {
            return Err(CompileError::DuplicateDeclaration {
                name: declaration.name.clone(),
            });
        }
        if declaration.body.is_empty() {
            return Err(CompileError::EmptyBody {
                name: declaration.name.clone(),
            });
        }

        let declared = declaration
            .dependencies
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        if declared.len() != declaration.dependencies.len()
            || declaration
                .dependencies
                .iter()
                .any(|name| !globals.contains_key(name))
        {
            return Err(CompileError::DependencyMismatch {
                declaration: declaration.name.clone(),
                declared: declaration.dependencies.clone(),
                used: Vec::new(),
            });
        }

        let mut locals = BTreeMap::new();
        let mut used = BTreeSet::new();
        let mut root = None;
        for row in &declaration.body {
            if row.id.is_empty() {
                return Err(CompileError::EmptyName);
            }
            if locals.contains_key(&row.id) {
                return Err(CompileError::DuplicateLocal {
                    declaration: declaration.name.clone(),
                    name: row.id.clone(),
                });
            }
            let resolve = |name: &str, used: &mut BTreeSet<String>| {
                if let Some(reference) = locals.get(name) {
                    Ok(*reference)
                } else if let Some(reference) = globals.get(name) {
                    used.insert(name.to_owned());
                    Ok(*reference)
                } else {
                    Err(CompileError::UnresolvedReference {
                        declaration: declaration.name.clone(),
                        name: name.to_owned(),
                    })
                }
            };
            let result = match &row.node {
                RawNode::KindStar => kernel.star(),
                RawNode::BoolTy { star } => kernel.bool_ty(resolve(star, &mut used)?),
                RawNode::TyArr { domain, codomain } => {
                    kernel.ty_arr(resolve(domain, &mut used)?, resolve(codomain, &mut used)?)
                }
                RawNode::TmFv { name, ty } => kernel.tm_fv(*name, resolve(ty, &mut used)?),
                RawNode::TmLam {
                    function_ty,
                    binder,
                    body,
                } => kernel.lam_at(
                    resolve(function_ty, &mut used)?,
                    resolve(binder, &mut used)?,
                    resolve(body, &mut used)?,
                ),
                RawNode::TmEq {
                    bool_ty,
                    left,
                    right,
                } => kernel.eq(
                    resolve(bool_ty, &mut used)?,
                    resolve(left, &mut used)?,
                    resolve(right, &mut used)?,
                ),
            }
            .map_err(|source| CompileError::Kernel {
                declaration: declaration.name.clone(),
                row: row.id.clone(),
                source,
            })?;
            locals.insert(row.id.clone(), result);
            root = Some(result);
        }

        if used != declared {
            return Err(CompileError::DependencyMismatch {
                declaration: declaration.name.clone(),
                declared: declared.into_iter().collect(),
                used: used.into_iter().collect(),
            });
        }
        let Some(root) = root else {
            return Err(CompileError::EmptyBody {
                name: declaration.name.clone(),
            });
        };
        globals.insert(declaration.name.clone(), root);
    }

    Ok(Compiled {
        arena: kernel.into_arena(),
        names: globals,
        manifest_addr: manifest.addr(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire;
    use covalence_lib_json::serde_json;

    #[cfg(not(feature = "buck-test-fixtures"))]
    const FIXTURE: &str = include_str!("../../../../theories/init-boolean.checked.json");
    #[cfg(feature = "buck-test-fixtures")]
    const FIXTURE: &str = include_str!("../theories/init-boolean.checked.json");
    #[cfg(not(feature = "buck-test-fixtures"))]
    const SCHEMA: &str = include_str!("../../../../theories/init-boolean.checked.schema.json");
    #[cfg(feature = "buck-test-fixtures")]
    const SCHEMA: &str = include_str!("../theories/init-boolean.checked.schema.json");

    #[test]
    fn fixture_compiles_deterministically_and_round_trips() {
        let manifest: Manifest = serde_json::from_str(FIXTURE).unwrap();
        assert_eq!(
            serde_json::from_str::<Manifest>(&serde_json::to_string(&manifest).unwrap()).unwrap(),
            manifest
        );
        let first = compile(&manifest).unwrap();
        let second = compile(&manifest).unwrap();
        assert_eq!(first, second);
        assert_eq!(
            first.names().map(|(name, _)| name).collect::<Vec<_>>(),
            [
                "and",
                "bool",
                "bool->bool",
                "bool->bool->bool",
                "false",
                "imp",
                "not",
                "or",
                "star",
                "true",
            ]
        );
        assert_eq!(first.arena().len(), 33);
        assert_eq!(first.get("star"), Ref::new(1));
        assert_eq!(first.get("bool"), Ref::new(2));
        assert_eq!(first.get("bool->bool"), Ref::new(3));
        assert_eq!(first.get("bool->bool->bool"), Ref::new(4));
        assert_eq!(first.get("true"), Ref::new(7));
        assert_eq!(first.get("false"), Ref::new(12));
        assert_eq!(first.get("not"), Ref::new(15));
        assert_eq!(first.get("and"), Ref::new(21));
        assert_eq!(first.get("or"), Ref::new(27));
        assert_eq!(first.get("imp"), Ref::new(33));

        let mut bytes = Vec::new();
        wire::serialize(first.arena(), &mut bytes).unwrap();
        assert_eq!(wire::deserialize(bytes.as_slice()).unwrap(), *first.arena());
        assert_eq!(
            first.arena().addr(),
            O256::from_hex("fdc14876fecbb5c84b5692a88fd3e80c91fc6f72799a91787eb8871d143e0ade")
                .unwrap()
        );
        assert_eq!(
            first.manifest_addr(),
            O256::from_hex("ae74e6a0bc7efe384c699afbc805822a9fe145e6f04366145923b071d41888d0")
                .unwrap()
        );
    }

    #[test]
    fn manifest_hash_covers_names_and_migration_beyond_the_arena_prefix() {
        let manifest: Manifest = serde_json::from_str(FIXTURE).unwrap();
        let compiled = compile(&manifest).unwrap();

        let mut renamed = manifest.clone();
        renamed.declarations.last_mut().unwrap().name = "logical-not".into();
        let renamed = compile(&renamed).unwrap();
        assert_eq!(renamed.arena().addr(), compiled.arena().addr());
        assert_ne!(renamed.manifest_addr(), compiled.manifest_addr());

        let mut migrated = manifest.clone();
        migrated.migration.push_str(" (updated)");
        let migrated = compile(&migrated).unwrap();
        assert_eq!(migrated.arena().addr(), compiled.arena().addr());
        assert_ne!(migrated.manifest_addr(), compiled.manifest_addr());
    }

    #[test]
    fn copy_uses_compiled_arena_identity_and_rejects_prefix_mismatch_atomically() {
        let manifest: Manifest = serde_json::from_str(FIXTURE).unwrap();
        let compiled = compile(&manifest).unwrap();
        let mut metadata_changed = manifest.clone();
        metadata_changed.migration.push_str(" (metadata only)");
        let metadata_changed = compile(&metadata_changed).unwrap();
        assert_eq!(compiled.arena().addr(), metadata_changed.arena().addr());
        assert_ne!(compiled.manifest_addr(), metadata_changed.manifest_addr());

        let root = compiled.get("false").unwrap();
        let source = compiled.kernel();
        let mut destination = metadata_changed.kernel();
        let original_len = destination.len();
        let copied = destination.copy_term_from(&source, root).unwrap();
        assert_eq!(copied.get(root), Some(root));
        assert_eq!(copied.roots(), [root]);
        assert_eq!(destination.len(), original_len);

        let mut arena_changed = manifest;
        let RawNode::TmFv { name, .. } = &mut arena_changed.declarations[4].body[0].node else {
            panic!("fixture row must be a free variable");
        };
        *name += 1;
        let arena_changed = compile(&arena_changed).unwrap();
        assert_ne!(compiled.arena().addr(), arena_changed.arena().addr());
        let mut mismatched = arena_changed.kernel();
        let before = mismatched.arena().clone();
        assert!(matches!(
            mismatched.copy_term_from(&source, root),
            Err(KernelError::InitPrefixMismatch)
        ));
        assert_eq!(*mismatched.arena(), before);

        let mut empty = Kernel::new();
        assert!(matches!(
            empty.copy_terms_from(&source, &[]),
            Err(KernelError::InitPrefixMismatch)
        ));
        assert!(empty.is_empty());
    }

    #[test]
    fn free_variable_names_match_the_schema_u64_boundaries() {
        let schema: serde_json::Value = serde_json::from_str(SCHEMA).unwrap();
        assert_eq!(
            schema["$defs"]["tmFv"]["properties"]["name"]["maximum"],
            u64::MAX
        );

        let at_max = FIXTURE.replacen("\"name\": 0", &format!("\"name\": {}", u64::MAX), 1);
        assert!(serde_json::from_str::<Manifest>(&at_max).is_ok());

        let above_max = FIXTURE.replacen("\"name\": 0", "\"name\": 18446744073709551616", 1);
        assert!(serde_json::from_str::<Manifest>(&above_max).is_err());
    }

    #[test]
    fn serde_rejects_opcode_and_unknown_tags() {
        for tag in ["Op1", "Op2", "tm.nat", "unknown"] {
            let text = FIXTURE.replacen("kind.star", tag, 1);
            assert!(
                serde_json::from_str::<Manifest>(&text).is_err(),
                "accepted {tag}"
            );
        }
    }

    #[test]
    fn validation_rejects_forward_references_and_dependency_drift() {
        let mut manifest: Manifest = serde_json::from_str(FIXTURE).unwrap();
        manifest.declarations[0].body[0].node = RawNode::BoolTy {
            star: "bool".into(),
        };
        assert!(matches!(
            compile(&manifest),
            Err(CompileError::UnresolvedReference { .. })
        ));

        let mut manifest: Manifest = serde_json::from_str(FIXTURE).unwrap();
        manifest.declarations[1].dependencies.clear();
        assert!(matches!(
            compile(&manifest),
            Err(CompileError::DependencyMismatch { .. })
        ));
    }
}
