//! Dependency-ordered compilation from a virtual resource tree.

use std::collections::{BTreeMap, BTreeSet};

use covalence_data_vfs::ResourceVfs;
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;

use super::{
    CompiledModule, ModuleError, Namespace, SExpr, TheoryError, compile_module, read_module,
};

/// One source resource included in a compiled tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceUnit {
    module: String,
    resource: String,
    address: O256,
    length: u64,
}

impl SourceUnit {
    /// Returns the dot-qualified module name.
    #[must_use]
    pub fn module(&self) -> &str {
        &self.module
    }

    /// Returns the opaque VFS resource key used to load the module.
    #[must_use]
    pub fn resource(&self) -> &str {
        &self.resource
    }

    /// Returns the address of the exact source bytes.
    #[must_use]
    pub const fn address(&self) -> O256 {
        self.address
    }

    /// Returns the source length in bytes.
    #[must_use]
    pub const fn length(&self) -> u64 {
        self.length
    }
}

/// A checked combined module and its untrusted dependency manifest.
#[derive(Debug)]
pub struct CompiledTree {
    root: String,
    module: CompiledModule,
    namespace: Namespace,
    sources: Vec<SourceUnit>,
}

impl CompiledTree {
    /// Returns the requested root module name.
    #[must_use]
    pub fn root(&self) -> &str {
        &self.root
    }

    /// Borrows the checked combined module.
    #[must_use]
    pub const fn module(&self) -> &CompiledModule {
        &self.module
    }

    /// Borrows the root module's explicit public namespace.
    #[must_use]
    pub const fn namespace(&self) -> &Namespace {
        &self.namespace
    }

    /// Returns dependency-first source metadata, with each module listed once.
    #[must_use]
    pub fn sources(&self) -> &[SourceUnit] {
        &self.sources
    }

    /// Splits the checked module from its untrusted source manifest.
    #[must_use]
    pub fn into_parts(self) -> (CompiledModule, Namespace, Vec<SourceUnit>) {
        (self.module, self.namespace, self.sources)
    }
}

/// Failure to load or compile a virtual source tree.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum TreeError {
    /// A module name cannot map canonically to a `.cov` path.
    #[snafu(display("invalid module name {module:?}"))]
    InvalidModule {
        /// Rejected module name.
        module: String,
    },
    /// A resource could not be read through the mounted VFS.
    #[snafu(display("could not resolve module {module:?} as {resource:?}: {source}"))]
    Resource {
        /// Module being loaded.
        module: String,
        /// Opaque resource key supplied to the VFS.
        resource: String,
        /// Underlying VFS error.
        source: std::io::Error,
    },
    /// A `.cov` resource is not UTF-8 text.
    #[snafu(display("module {module:?} is not UTF-8: {source}"))]
    Utf8 {
        /// Module being decoded.
        module: String,
        /// UTF-8 validation failure.
        source: std::str::Utf8Error,
    },
    /// A resource length cannot be represented by the portable metadata type.
    #[snafu(display("module {module:?} is larger than u64::MAX bytes"))]
    TooLarge {
        /// Module whose resource is too large.
        module: String,
    },
    /// One source module has malformed S-expression syntax.
    #[snafu(display("could not parse module {module:?}: {source}"))]
    Source {
        /// Module being parsed.
        module: String,
        /// Existing source-language failure.
        source: TheoryError,
    },
    /// Imports contain a dependency cycle.
    #[snafu(display("module import cycle reaches {module:?}"))]
    Cycle {
        /// Module observed twice on the active dependency path.
        module: String,
    },
    /// Internal dependency bookkeeping became inconsistent.
    #[snafu(display("module dependency state is inconsistent for {module:?}"))]
    Inconsistent {
        /// Module missing from completed bookkeeping.
        module: String,
    },
    /// Source refers to a dependency name that was not exported to it.
    #[snafu(display("module {module:?} cannot access private name {name:?}"))]
    PrivateName {
        /// Module containing the rejected reference.
        module: String,
        /// Known definition absent from the module's import surface.
        name: String,
    },
    /// The combined source tree was rejected by the existing compiler.
    #[snafu(transparent)]
    Compile {
        /// Existing module-compiler failure.
        source: ModuleError,
    },
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Visit {
    Active,
    Complete,
}

struct Pending {
    forms: Vec<SExpr>,
    unit: SourceUnit,
    dependencies: Vec<String>,
    definitions: Vec<String>,
    exports: Vec<Export>,
}

struct Export {
    dependency: String,
    mode: ExportMode,
}

enum ExportMode {
    Module,
    Rename(String),
    Open,
}

/// Compiles one module and its transitive `(import module.name)` dependencies.
///
/// The logical module name is passed to the VFS unchanged. A folder-backed
/// mount may conventionally resolve `nat.defs` to `nat/defs.cov`; a CAS-backed
/// mount may resolve the same name through an index to unrelated hash-addressed
/// bytes. Each file is automatically nested under its logical module namespace.
/// Resource loading and dependency resolution are untrusted; the resulting
/// definitions still pass through the existing checked compiler.
///
/// The supplied [`ResourceVfs`] can expose the same mounted files to `SQLite`,
/// allowing adjacent `.sqlite`, `.wasm`, and arbitrary binary resources without
/// changing the source resolver or coercing them to text.
///
/// # Errors
///
/// Returns an error for invalid names, missing resources, non-UTF-8 `.cov`
/// files, malformed forms, import cycles, or checked compilation failure.
pub fn compile_tree(root: &str, resources: &impl ResourceVfs) -> Result<CompiledTree, TreeError> {
    let (pending, ordered) = load_tree(root, resources)?;
    assemble_tree(root, pending, ordered)
}

fn load_tree(
    root: &str,
    resources: &impl ResourceVfs,
) -> Result<(BTreeMap<String, Pending>, Vec<String>), TreeError> {
    validate_module(root)?;
    let mut visits = BTreeMap::<String, Visit>::new();
    let mut pending = BTreeMap::<String, Pending>::new();
    let mut stack = vec![(root.to_owned(), false)];
    let mut ordered = Vec::<String>::new();

    while let Some((module, exiting)) = stack.pop() {
        if exiting {
            visits.insert(module.clone(), Visit::Complete);
            ordered.push(module);
            continue;
        }
        match visits.get(&module) {
            Some(Visit::Complete) => continue,
            Some(Visit::Active) => return Err(TreeError::Cycle { module }),
            None => {}
        }

        validate_module(&module)?;
        let resource = module.clone();
        let bytes = resources
            .read(&resource)
            .map_err(|source| TreeError::Resource {
                module: module.clone(),
                resource: resource.clone(),
                source,
            })?;
        let source = std::str::from_utf8(&bytes).map_err(|source| TreeError::Utf8 {
            module: module.clone(),
            source,
        })?;
        let parsed = read_module(source).map_err(|source| TreeError::Source {
            module: module.clone(),
            source,
        })?;
        let Directives {
            body: forms,
            dependencies,
            exports,
        } = split_directives(&module, parsed)?;
        let definitions = definition_names(&module, &forms)?;
        let length = u64::try_from(bytes.len()).map_err(|_| TreeError::TooLarge {
            module: module.clone(),
        })?;
        let unit = SourceUnit {
            module: module.clone(),
            resource,
            address: O256::from_bytes(&bytes),
            length,
        };
        visits.insert(module.clone(), Visit::Active);
        pending.insert(
            module.clone(),
            Pending {
                forms,
                unit,
                dependencies: dependencies.clone(),
                definitions,
                exports,
            },
        );
        stack.push((module, true));
        for dependency in dependencies.into_iter().rev() {
            stack.push((dependency, false));
        }
    }
    Ok((pending, ordered))
}

fn assemble_tree(
    root: &str,
    mut pending: BTreeMap<String, Pending>,
    ordered: Vec<String>,
) -> Result<CompiledTree, TreeError> {
    let mut combined = Vec::new();
    let mut sources = Vec::new();
    let mut published = BTreeMap::<String, BTreeMap<String, String>>::new();
    let all_definitions = pending
        .values()
        .flat_map(|entry| entry.definitions.iter().cloned())
        .collect::<BTreeSet<_>>();
    for name in ordered {
        let entry = pending
            .remove(&name)
            .ok_or_else(|| TreeError::Inconsistent {
                module: name.clone(),
            })?;
        let aliases = entry
            .dependencies
            .iter()
            .filter_map(|dependency| published.get(dependency))
            .flat_map(|exports| exports.iter())
            .map(|(public, origin)| (public.clone(), origin.clone()))
            .collect::<BTreeMap<_, _>>();
        let forms = entry
            .forms
            .into_iter()
            .map(|form| {
                validate_visibility(&name, &form, &all_definitions, &entry.definitions, &aliases)?;
                Ok(rewrite_aliases(form, &aliases))
            })
            .collect::<Result<Vec<_>, TreeError>>()?;
        combined.push(wrap_module(&name, forms)?);
        let mut exports = entry
            .definitions
            .iter()
            .map(|definition| (definition.clone(), definition.clone()))
            .collect::<BTreeMap<_, _>>();
        for export in &entry.exports {
            let dependency =
                published
                    .get(&export.dependency)
                    .ok_or_else(|| TreeError::Inconsistent {
                        module: export.dependency.clone(),
                    })?;
            for (public, origin) in dependency {
                let suffix = public.strip_prefix(&export.dependency).ok_or_else(|| {
                    TreeError::Inconsistent {
                        module: export.dependency.clone(),
                    }
                })?;
                let alias = match &export.mode {
                    ExportMode::Module => public.clone(),
                    ExportMode::Rename(alias) => format!("{name}.{alias}{suffix}"),
                    ExportMode::Open => format!("{name}{suffix}"),
                };
                exports.insert(alias, origin.clone());
            }
        }
        published.insert(name, exports);
        sources.push(entry.unit);
    }
    let source = super::module::render(&combined);
    let module = compile_module(&source).map_err(|source| TreeError::Compile { source })?;
    let mut namespace = Namespace::default();
    let root_exports = published
        .remove(root)
        .ok_or_else(|| TreeError::Inconsistent {
            module: root.to_owned(),
        })?;
    for (public, origin) in root_exports {
        let reference = module
            .namespace()
            .get(&origin)
            .ok_or_else(|| TreeError::Inconsistent {
                module: origin.clone(),
            })?;
        namespace.insert(&public, reference);
    }
    Ok(CompiledTree {
        root: root.to_owned(),
        module,
        namespace,
        sources,
    })
}

struct Directives {
    body: Vec<SExpr>,
    dependencies: Vec<String>,
    exports: Vec<Export>,
}

fn split_directives(owner: &str, forms: Vec<SExpr>) -> Result<Directives, TreeError> {
    let mut body = Vec::new();
    let mut dependencies = Vec::new();
    let mut exports = Vec::new();
    let mut seen = BTreeSet::new();
    for form in forms {
        let dependency = match &form {
            SExpr::List(items)
                if matches!(items.first(), Some(SExpr::Atom(head)) if head == "import")
                    && items.len() == 2 =>
            {
                match &items[1] {
                    SExpr::Atom(name) => Some(name.clone()),
                    SExpr::O256(_) | SExpr::List(_) => {
                        return Err(TreeError::InvalidModule {
                            module: format!("{owner} import"),
                        });
                    }
                }
            }
            _ => None,
        };
        if let Some(dependency) = dependency {
            validate_module(&dependency)?;
            if seen.insert(dependency.clone()) {
                dependencies.push(dependency);
            }
        } else if let Some(export) = parse_export(owner, &form)? {
            exports.push(export);
        } else {
            body.push(form);
        }
    }
    if let Some(export) = exports
        .iter()
        .find(|export| !seen.contains(&export.dependency))
    {
        return Err(TreeError::InvalidModule {
            module: format!("{owner} export of unimported {}", export.dependency),
        });
    }
    Ok(Directives {
        body,
        dependencies,
        exports,
    })
}

fn parse_export(owner: &str, form: &SExpr) -> Result<Option<Export>, TreeError> {
    let SExpr::List(items) = form else {
        return Ok(None);
    };
    let Some(SExpr::Atom(head)) = items.first() else {
        return Ok(None);
    };
    let (dependency, mode) = match (head.as_str(), items.as_slice()) {
        ("export", [_, SExpr::Atom(dependency)]) => (dependency.clone(), ExportMode::Module),
        ("export", [_, SExpr::List(rename)]) => {
            let [SExpr::Atom(dependency), SExpr::Atom(alias)] = rename.as_slice() else {
                return Err(TreeError::InvalidModule {
                    module: format!("{owner} export"),
                });
            };
            if alias.contains('.') {
                return Err(TreeError::InvalidModule {
                    module: alias.clone(),
                });
            }
            validate_module(alias)?;
            (dependency.clone(), ExportMode::Rename(alias.clone()))
        }
        ("include", [_, SExpr::Atom(dependency)]) => (dependency.clone(), ExportMode::Open),
        ("export" | "include", _) => {
            return Err(TreeError::InvalidModule {
                module: format!("{owner} export"),
            });
        }
        _ => return Ok(None),
    };
    validate_module(&dependency)?;
    Ok(Some(Export { dependency, mode }))
}

fn definition_names(module: &str, forms: &[SExpr]) -> Result<Vec<String>, TreeError> {
    let mut names = Vec::new();
    collect_definition_names(module, forms, &mut names)?;
    Ok(names)
}

fn collect_definition_names(
    prefix: &str,
    forms: &[SExpr],
    names: &mut Vec<String>,
) -> Result<(), TreeError> {
    for form in forms {
        let SExpr::List(items) = form else {
            continue;
        };
        match items.as_slice() {
            [SExpr::Atom(head), SExpr::Atom(name), ..] if head == "define" => {
                validate_module(name)?;
                names.push(format!("{prefix}.{name}"));
            }
            [SExpr::Atom(head), SExpr::Atom(name), nested @ ..] if head == "namespace" => {
                if name.contains('.') {
                    return Err(TreeError::InvalidModule {
                        module: name.clone(),
                    });
                }
                validate_module(name)?;
                collect_definition_names(&format!("{prefix}.{name}"), nested, names)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn rewrite_aliases(expression: SExpr, aliases: &BTreeMap<String, String>) -> SExpr {
    match expression {
        SExpr::Atom(name) => aliases
            .get(&name)
            .cloned()
            .map_or(SExpr::Atom(name), SExpr::Atom),
        SExpr::O256(value) => SExpr::O256(value),
        SExpr::List(items) => SExpr::List(
            items
                .into_iter()
                .map(|item| rewrite_aliases(item, aliases))
                .collect(),
        ),
    }
}

fn validate_visibility(
    module: &str,
    expression: &SExpr,
    all_definitions: &BTreeSet<String>,
    local_definitions: &[String],
    aliases: &BTreeMap<String, String>,
) -> Result<(), TreeError> {
    match expression {
        SExpr::Atom(name) => {
            if all_definitions.contains(name)
                && !local_definitions.contains(name)
                && !aliases.contains_key(name)
            {
                return Err(TreeError::PrivateName {
                    module: module.to_owned(),
                    name: name.clone(),
                });
            }
        }
        SExpr::O256(_) => {}
        SExpr::List(items) => {
            for item in items {
                validate_visibility(module, item, all_definitions, local_definitions, aliases)?;
            }
        }
    }
    Ok(())
}

fn validate_module(module: &str) -> Result<(), TreeError> {
    let valid = !module.is_empty()
        && module.split('.').all(|part| {
            !part.is_empty()
                && part
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-'))
        });
    if !valid {
        return Err(TreeError::InvalidModule {
            module: module.to_owned(),
        });
    }
    Ok(())
}

fn wrap_module(module: &str, forms: Vec<SExpr>) -> Result<SExpr, TreeError> {
    let mut body = forms;
    for part in module.split('.').rev() {
        let mut namespace = Vec::with_capacity(body.len() + 2);
        namespace.push(SExpr::Atom("namespace".to_owned()));
        namespace.push(SExpr::Atom(part.to_owned()));
        namespace.extend(body);
        body = vec![SExpr::List(namespace)];
    }
    body.pop().ok_or_else(|| TreeError::Inconsistent {
        module: module.to_owned(),
    })
}
