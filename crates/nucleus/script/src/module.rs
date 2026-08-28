//! Tree-shaped module metadata around the checked theory compiler.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write,
};

use covalence_data_sexpr::Atom;
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_logic_hol::{Kernel, Ref};

use super::{CompiledTheory, SExpr, TheoryError, atom, compile_theory, list, read_module};

/// One content-addressed dependency declared by a source module.
///
/// Imports are external metadata in the initial language. Resolution and the
/// policy mapping a friendly name to these addresses deliberately remain
/// outside the kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImportDecl {
    name: String,
    arena: O256,
    metadata: O256,
}

impl ImportDecl {
    pub(super) fn new(name: String, arena: O256, metadata: O256) -> Self {
        Self {
            name,
            arena,
            metadata,
        }
    }

    /// Returns the import's local namespace name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the imported kernel-arena address.
    #[must_use]
    pub const fn arena(&self) -> O256 {
        self.arena
    }

    /// Returns the imported namespace-metadata address.
    #[must_use]
    pub const fn metadata(&self) -> O256 {
        self.metadata
    }
}

/// An immutable-by-convention tree mapping source names to local HOL rows.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Namespace {
    bindings: BTreeMap<String, Ref>,
    children: BTreeMap<String, Self>,
}

impl Namespace {
    /// Resolves a dot-separated name from this namespace root.
    #[must_use]
    pub fn get(&self, path: &str) -> Option<Ref> {
        let mut parts = path.split('.').peekable();
        let mut namespace = self;
        while let Some(part) = parts.next() {
            if parts.peek().is_none() {
                return namespace.bindings.get(part).copied();
            }
            namespace = namespace.children.get(part)?;
        }
        None
    }

    /// Iterates bindings directly contained in this namespace.
    #[must_use]
    pub fn bindings(&self) -> impl ExactSizeIterator<Item = (&str, Ref)> {
        self.bindings
            .iter()
            .map(|(name, reference)| (name.as_str(), *reference))
    }

    /// Iterates immediate child namespaces.
    #[must_use]
    pub fn children(&self) -> impl ExactSizeIterator<Item = (&str, &Self)> {
        self.children
            .iter()
            .map(|(name, namespace)| (name.as_str(), namespace))
    }

    pub(super) fn insert(&mut self, path: &str, reference: Ref) {
        let mut parts = path.split('.').peekable();
        let mut namespace = self;
        while let Some(part) = parts.next() {
            if parts.peek().is_none() {
                namespace.bindings.insert(part.to_owned(), reference);
                return;
            }
            namespace = namespace.children.entry(part.to_owned()).or_default();
        }
    }
}

/// A checked kernel paired with disposable module-navigation metadata.
#[derive(Debug)]
pub struct CompiledModule {
    theory: CompiledTheory,
    namespace: Namespace,
    imports: Vec<ImportDecl>,
}

impl CompiledModule {
    /// Borrows the checked compilation result.
    #[must_use]
    pub const fn theory(&self) -> &CompiledTheory {
        &self.theory
    }

    /// Borrows the checked kernel.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        self.theory.kernel()
    }

    /// Borrows the root namespace.
    #[must_use]
    pub const fn namespace(&self) -> &Namespace {
        &self.namespace
    }

    /// Borrows declared content-addressed dependencies.
    #[must_use]
    pub fn imports(&self) -> &[ImportDecl] {
        &self.imports
    }

    /// Splits checked state from all disposable navigation metadata.
    #[must_use]
    pub fn into_parts(self) -> (CompiledTheory, Namespace, Vec<ImportDecl>) {
        (self.theory, self.namespace, self.imports)
    }
}

/// A rejected module wrapper or underlying theory.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ModuleError {
    /// Module structure or import metadata is malformed.
    #[snafu(display("invalid module form: {message}"))]
    Invalid {
        /// Grammar diagnostic.
        message: String,
    },
    /// Flattened checked theory compilation failed.
    #[snafu(transparent)]
    Theory {
        /// Underlying userspace compiler failure.
        source: TheoryError,
    },
}

/// Compiles nested namespace forms through the existing checked theory API.
///
/// ```text
/// form := (define ...)
///       | (namespace name form ...)
///       | (import name arena-hash metadata-hash)
/// ```
///
/// Names resolve from the innermost namespace outward. A dot-qualified name
/// resolves from the module root. Imports are recorded but not resolved.
///
/// # Errors
///
/// Returns an error for malformed module structure, duplicate qualified names,
/// invalid hashes, unresolved names, or checked HOL construction failure.
pub fn compile_module(source: &str) -> Result<CompiledModule, ModuleError> {
    let forms = read_module(source)?;
    let mut definitions = BTreeSet::new();
    collect_definitions(&forms, &[], &mut definitions)?;
    let mut flat = Vec::new();
    let mut imports = Vec::new();
    flatten(&forms, &[], &definitions, &mut flat, &mut imports)?;
    let source = render(&flat);
    let theory = compile_theory(&source)?;
    let mut namespace = Namespace::default();
    for (name, reference) in theory.symbols() {
        namespace.insert(name, reference);
    }
    Ok(CompiledModule {
        theory,
        namespace,
        imports,
    })
}

/// Produces a canonical, userspace inspection form for a kernel and metadata.
///
/// `%n` denotes the one-based local HOL row `n`. This first delaborator is
/// intentionally lossless for names and imports but does not pretend to
/// reconstruct the higher-level proof program that happened to create rows.
#[must_use]
pub fn delaborate_module(kernel: &Kernel, namespace: &Namespace, imports: &[ImportDecl]) -> String {
    let mut output = format!(
        "(#kernel {} {})\n",
        kernel.arena().addr(),
        kernel.arena().len()
    );
    for import in imports {
        writeln!(
            output,
            "(import {} {} {})",
            import.name,
            Atom::encode_o256(import.arena),
            Atom::encode_o256(import.metadata)
        )
        .expect("writing to a String cannot fail");
    }
    let mut named = BTreeSet::new();
    collect_references(namespace, &mut named);
    for index in 1..i32::MAX {
        let Some(reference) = Ref::new(index) else {
            break;
        };
        if kernel.arena().tag(reference).is_none() {
            break;
        }
        if !named.contains(&reference) {
            writeln!(output, "(anonymous %{index})").expect("writing to a String cannot fail");
        }
    }
    render_namespace(namespace, 0, &mut output);
    output
}

fn collect_references(namespace: &Namespace, output: &mut BTreeSet<Ref>) {
    output.extend(namespace.bindings.values().copied());
    for child in namespace.children.values() {
        collect_references(child, output);
    }
}

fn collect_definitions(
    forms: &[SExpr],
    scope: &[String],
    definitions: &mut BTreeSet<String>,
) -> Result<(), ModuleError> {
    for form in forms {
        let items = list(form, "a module form")?;
        match items.first().map(atom).transpose()? {
            Some("define") => {
                let local = items.get(1).ok_or_else(|| ModuleError::Invalid {
                    message: "define is missing its name".to_owned(),
                })?;
                let name = qualify_definition(scope, atom(local)?)?;
                if !definitions.insert(name.clone()) {
                    return Err(ModuleError::Invalid {
                        message: format!("duplicate definition {name:?}"),
                    });
                }
            }
            Some("namespace") => {
                let local = items.get(1).ok_or_else(|| ModuleError::Invalid {
                    message: "namespace is missing its name".to_owned(),
                })?;
                let mut nested = scope.to_vec();
                nested.push(validate_part(atom(local)?)?.to_owned());
                collect_definitions(&items[2..], &nested, definitions)?;
            }
            Some("import") => {}
            _ => return module_invalid("expected define, namespace, or import form"),
        }
    }
    Ok(())
}

fn flatten(
    forms: &[SExpr],
    scope: &[String],
    definitions: &BTreeSet<String>,
    output: &mut Vec<SExpr>,
    imports: &mut Vec<ImportDecl>,
) -> Result<(), ModuleError> {
    for form in forms {
        let items = list(form, "a module form")?;
        match items.first().map(atom).transpose()? {
            Some("define") => output.push(rewrite_define(items, scope, definitions)?),
            Some("namespace") => {
                let mut nested = scope.to_vec();
                nested.push(validate_part(atom(&items[1])?)?.to_owned());
                flatten(&items[2..], &nested, definitions, output, imports)?;
            }
            Some("import") => imports.push(parse_import(items, scope)?),
            _ => return module_invalid("expected define, namespace, or import form"),
        }
    }
    Ok(())
}

fn rewrite_define(
    items: &[SExpr],
    scope: &[String],
    definitions: &BTreeSet<String>,
) -> Result<SExpr, ModuleError> {
    if !matches!(items.len(), 4 | 5) {
        return module_invalid("expected (define name ('type ...) [type] term)");
    }
    let name = qualify_definition(scope, atom(&items[1])?)?;
    let parameters = list(&items[2], "a type-parameter list")?;
    let mut bound = parameters
        .iter()
        .map(atom)
        .collect::<Result<BTreeSet<_>, _>>()?;
    let mut rewritten = vec![
        SExpr::Atom("define".to_owned()),
        SExpr::Atom(name),
        items[2].clone(),
    ];
    for expression in &items[3..] {
        rewritten.push(rewrite(expression, scope, definitions, &mut bound));
    }
    Ok(SExpr::List(rewritten))
}

fn rewrite(
    expression: &SExpr,
    scope: &[String],
    definitions: &BTreeSet<String>,
    bound: &mut BTreeSet<&str>,
) -> SExpr {
    match expression {
        SExpr::Atom(name) => {
            if bound.contains(name.as_str()) || is_builtin(name) || name.starts_with('\'') {
                return expression.clone();
            }
            SExpr::Atom(resolve(scope, name, definitions).unwrap_or_else(|| name.clone()))
        }
        SExpr::O256(value) => SExpr::O256(*value),
        SExpr::List(items) => {
            let mut nested_bound = bound.clone();
            if let Some(SExpr::Atom(operator)) = items.first()
                && matches!(operator.as_str(), "lambda" | "exists" | "forall")
                && let Some(SExpr::Atom(name)) = items.get(1)
            {
                nested_bound.insert(name);
            }
            SExpr::List(
                items
                    .iter()
                    .map(|item| rewrite(item, scope, definitions, &mut nested_bound))
                    .collect(),
            )
        }
    }
}

fn resolve(scope: &[String], name: &str, definitions: &BTreeSet<String>) -> Option<String> {
    if name.contains('.') {
        return definitions.contains(name).then(|| name.to_owned());
    }
    for depth in (0..=scope.len()).rev() {
        let candidate = if depth == 0 {
            name.to_owned()
        } else {
            format!("{}.{}", scope[..depth].join("."), name)
        };
        if definitions.contains(&candidate) {
            return Some(candidate);
        }
    }
    None
}

fn parse_import(items: &[SExpr], scope: &[String]) -> Result<ImportDecl, ModuleError> {
    if items.len() != 4 {
        return module_invalid("import expects a name, arena hash, and metadata hash");
    }
    let name = qualify(scope, atom(&items[1])?)?;
    let arena = address(&items[2], "arena")?;
    let metadata = address(&items[3], "metadata")?;
    Ok(ImportDecl {
        name,
        arena,
        metadata,
    })
}

fn address(expression: &SExpr, role: &str) -> Result<O256, ModuleError> {
    match expression {
        SExpr::O256(value) => Ok(*value),
        SExpr::Atom(_) | SExpr::List(_) => {
            module_invalid(format!("import {role} must use the !hex O256 atom"))
        }
    }
}

fn qualify(scope: &[String], local: &str) -> Result<String, ModuleError> {
    validate_part(local)?;
    Ok(if scope.is_empty() {
        local.to_owned()
    } else {
        format!("{}.{}", scope.join("."), local)
    })
}

fn qualify_definition(scope: &[String], local: &str) -> Result<String, ModuleError> {
    if local.is_empty() {
        return module_invalid("definition names cannot be empty");
    }
    for part in local.split('.') {
        validate_part(part)?;
    }
    Ok(if scope.is_empty() {
        local.to_owned()
    } else {
        format!("{}.{}", scope.join("."), local)
    })
}

fn validate_part(name: &str) -> Result<&str, ModuleError> {
    if name.is_empty() || name.contains(['.', '/']) || name.starts_with('%') {
        return module_invalid("namespace names cannot be empty or contain ., /, or start with %");
    }
    Ok(name)
}

fn is_builtin(name: &str) -> bool {
    matches!(
        name,
        "define"
            | "bool"
            | "true"
            | "false"
            | "->"
            | "not"
            | "and"
            | "or"
            | "imp"
            | "="
            | "lambda"
            | "inst"
            | "exists"
            | "forall"
            | "ty.exists"
            | "ty.forall"
    )
}

pub(super) fn render(forms: &[SExpr]) -> String {
    let mut output = String::new();
    for form in forms {
        render_expr(form, &mut output);
        output.push('\n');
    }
    output
}

fn render_expr(expression: &SExpr, output: &mut String) {
    match expression {
        SExpr::Atom(atom) => output.push_str(atom),
        SExpr::O256(value) => output.push_str(&Atom::encode_o256(*value)),
        SExpr::List(items) => {
            output.push('(');
            for (index, item) in items.iter().enumerate() {
                if index != 0 {
                    output.push(' ');
                }
                render_expr(item, output);
            }
            output.push(')');
        }
    }
}

fn render_namespace(namespace: &Namespace, depth: usize, output: &mut String) {
    let indent = "  ".repeat(depth);
    for (name, reference) in namespace.bindings() {
        writeln!(output, "{indent}(name {name} %{})", reference.get())
            .expect("writing to a String cannot fail");
    }
    for (name, child) in namespace.children() {
        writeln!(output, "{indent}(namespace {name}").expect("writing to a String cannot fail");
        render_namespace(child, depth + 1, output);
        writeln!(output, "{indent})").expect("writing to a String cannot fail");
    }
}

fn module_invalid<T>(message: impl Into<String>) -> Result<T, ModuleError> {
    Err(ModuleError::Invalid {
        message: message.into(),
    })
}
