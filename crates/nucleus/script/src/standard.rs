//! Canonical userspace scripts for the logical and natural init segments.

use std::fmt::Write as _;

use covalence_data_sexpr::{Atom, Expr, ExprKind, Repr, SpannedRepr, parse};
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_logic_hol::{Kernel, init};

use super::{ImportDecl, InitLibraryError, Namespace, compile_init_slice};

/// Exact source of the logical init segment.
pub const LOGICAL_INIT_SCRIPT: &str = include_str!("../logical-init.sexpr");

/// Exact source of the natural-number init segment.
pub const NATURAL_INIT_SCRIPT: &str = include_str!("../natural-init.sexpr");

const LOGICAL_MANIFEST: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../theories/init-boolean.checked.json"
));
const LOGICAL_ACCELERATOR: &str = "nucleus.logical.init.checked-boolean-v0";
const NATURAL_ACCELERATOR: &str = "nucleus.natural.init.v0";

const fn address(hex: &str) -> O256 {
    match O256::from_hex(hex) {
        Ok(value) => value,
        Err(_) => panic!("pinned init address is invalid"),
    }
}

/// The three independently useful identities pinned for a script compilation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SegmentTriple {
    /// Hash of the exact S-expression source bytes.
    pub script: O256,
    /// Hash of the kernel-plus-metadata output object.
    pub output: O256,
    /// Hash of the checked kernel arena alone.
    pub kernel: O256,
}

/// Pinned source, output-object, and kernel identities for logical init.
pub const LOGICAL_INIT_TRIPLE: SegmentTriple = SegmentTriple {
    script: address("daa7b5ebf70583e39688e2a7e48b6204b427248008c2e6e4dd9b070208df5d5b"),
    output: address("b3b4ca5eb6ba5c5d9835aadf08b019fb58ae29d93fa112153fa295be96ea2304"),
    kernel: address("f8c65ffe8817adda472f44bfa039738351b88524abaf9f9d798c6cef714ac964"),
};

/// Pinned source, output-object, and kernel identities for natural init.
pub const NATURAL_INIT_TRIPLE: SegmentTriple = SegmentTriple {
    script: address("7678eb034e81e7ff40845e48d66edff71b21f48ff16ba40ad43f3ab4f2d32c3a"),
    output: address("c140d7b08bd314beb49f2299a9027d695848868b726306fae1af6dd9c24eb7fa"),
    kernel: address("08b577109951887e8acca5a3039d7e0d1a324f1b0aad02da120993bceff18953"),
};

/// The content-addressed result of one init script.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SegmentOutput {
    kernel: O256,
    metadata: O256,
}

impl SegmentOutput {
    /// Returns the checked arena address.
    #[must_use]
    pub const fn kernel(self) -> O256 {
        self.kernel
    }

    /// Returns the external namespace/import metadata address.
    #[must_use]
    pub const fn metadata(self) -> O256 {
        self.metadata
    }

    /// Hashes the versioned fixed-width output-object encoding.
    #[must_use]
    pub fn addr(self) -> O256 {
        let mut bytes = b"nucleus.hol-script.output-v0\0".to_vec();
        bytes.extend_from_slice(self.kernel.as_ref());
        bytes.extend_from_slice(self.metadata.as_ref());
        O256::from_bytes(bytes)
    }
}

/// A compiled checked segment plus its disposable userspace metadata.
#[derive(Debug)]
pub struct StandardSegment {
    kernel: Kernel,
    namespace: Namespace,
    imports: Vec<ImportDecl>,
    script: O256,
    output: SegmentOutput,
}

impl StandardSegment {
    /// Borrows the checked kernel.
    #[must_use]
    pub const fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Borrows the external namespace tree.
    #[must_use]
    pub const fn namespace(&self) -> &Namespace {
        &self.namespace
    }

    /// Borrows the declared imports.
    #[must_use]
    pub fn imports(&self) -> &[ImportDecl] {
        &self.imports
    }

    /// Returns the exact source-script address.
    #[must_use]
    pub const fn script_addr(&self) -> O256 {
        self.script
    }

    /// Returns the kernel-plus-metadata output object.
    #[must_use]
    pub const fn output(&self) -> SegmentOutput {
        self.output
    }
}

/// A rejected standard userspace init script.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum StandardSegmentError {
    /// The shared S-expression reader rejected the source.
    #[snafu(display("could not read init script: {message}"))]
    Read { message: String },
    /// The script does not have its accelerator's fixed minimal grammar.
    #[snafu(display("invalid init script: {message}"))]
    Form { message: String },
    /// Checked construction rejected the logical manifest.
    #[snafu(display("checked logical init construction failed: {source}"))]
    Logical { source: init::CompileError },
    /// Checked construction rejected natural init assembly.
    #[snafu(display("checked natural init construction failed: {source}"))]
    Natural { source: InitLibraryError },
}

/// Compiles the exact logical init script through its versioned accelerator.
///
/// The accelerator and script are userspace. Every resulting arena row is
/// still admitted by the checked logical-manifest compiler.
///
/// # Errors
///
/// Returns an error if the script shape or embedded manifest is rejected.
pub fn compile_standard_logical() -> Result<StandardSegment, StandardSegmentError> {
    expect_logical_script(LOGICAL_INIT_SCRIPT)?;
    let manifest: init::Manifest = covalence_lib_json::serde_json::from_str(LOGICAL_MANIFEST)
        .map_err(|error| StandardSegmentError::Form {
            message: format!("embedded logical manifest is not JSON: {error}"),
        })?;
    let compiled =
        init::compile(&manifest).map_err(|source| StandardSegmentError::Logical { source })?;
    let mut namespace = Namespace::default();
    for (name, reference) in compiled.names() {
        namespace.insert(name, reference);
    }
    Ok(segment(
        compiled.kernel(),
        namespace,
        Vec::new(),
        LOGICAL_INIT_SCRIPT,
    ))
}

/// Compiles the natural init script after checking its exact logical import.
///
/// # Errors
///
/// Returns an error if the source/import is malformed or mismatched, or any
/// existing checked construction used by the natural accelerator rejects.
pub fn compile_standard_natural(
    logical: &StandardSegment,
) -> Result<StandardSegment, StandardSegmentError> {
    let import = expect_natural_script(NATURAL_INIT_SCRIPT)?;
    if import.arena() != logical.output.kernel || import.metadata() != logical.output.metadata {
        return Err(StandardSegmentError::Form {
            message: "logical import does not match the supplied segment".to_owned(),
        });
    }
    let manifest: init::Manifest = covalence_lib_json::serde_json::from_str(LOGICAL_MANIFEST)
        .map_err(|error| StandardSegmentError::Form {
            message: format!("embedded logical manifest is not JSON: {error}"),
        })?;
    let checked =
        init::compile(&manifest).map_err(|source| StandardSegmentError::Logical { source })?;
    let slice =
        compile_init_slice(&checked).map_err(|source| StandardSegmentError::Natural { source })?;
    let mut namespace = Namespace::default();
    for (name, reference) in slice.symbols() {
        namespace.insert(name, reference);
    }
    Ok(segment(
        slice.kernel(),
        namespace,
        vec![import],
        NATURAL_INIT_SCRIPT,
    ))
}

fn segment(
    kernel: Kernel,
    namespace: Namespace,
    imports: Vec<ImportDecl>,
    source: &str,
) -> StandardSegment {
    let output = SegmentOutput {
        kernel: kernel.arena().addr(),
        metadata: metadata_addr(&namespace, &imports),
    };
    StandardSegment {
        kernel,
        namespace,
        imports,
        script: O256::from_bytes(source.as_bytes()),
        output,
    }
}

fn metadata_addr(namespace: &Namespace, imports: &[ImportDecl]) -> O256 {
    let mut text = String::from("nucleus.hol-script.metadata-v0\n");
    for import in imports {
        writeln!(
            text,
            "import\t{}\t{}\t{}",
            import.name(),
            import.arena(),
            import.metadata()
        )
        .expect("writing to a String cannot fail");
    }
    write_namespace(namespace, "", &mut text);
    O256::from_bytes(text.as_bytes())
}

fn write_namespace(namespace: &Namespace, prefix: &str, output: &mut String) {
    for (name, reference) in namespace.bindings() {
        let qualified = if prefix.is_empty() {
            name.to_owned()
        } else {
            format!("{prefix}.{name}")
        };
        writeln!(output, "name\t{qualified}\t{}", reference.get())
            .expect("writing to a String cannot fail");
    }
    for (name, child) in namespace.children() {
        let qualified = if prefix.is_empty() {
            name.to_owned()
        } else {
            format!("{prefix}.{name}")
        };
        write_namespace(child, &qualified, output);
    }
}

fn expect_logical_script(source: &str) -> Result<(), StandardSegmentError> {
    let document = parse(source).map_err(|error| StandardSegmentError::Read {
        message: error.to_string(),
    })?;
    if document.expressions().len() != 1
        || directive_form(&document.expressions()[0]) != Some(LOGICAL_ACCELERATOR)
    {
        return Err(StandardSegmentError::Form {
            message: "expected the logical init accelerator".to_owned(),
        });
    }
    Ok(())
}

fn expect_natural_script(source: &str) -> Result<ImportDecl, StandardSegmentError> {
    let document = parse(source).map_err(|error| StandardSegmentError::Read {
        message: error.to_string(),
    })?;
    let [import, accelerator] = document.expressions() else {
        return Err(StandardSegmentError::Form {
            message: "expected one import followed by the natural init accelerator".to_owned(),
        });
    };
    let import = import_form(import)?;
    if directive_form(accelerator) != Some(NATURAL_ACCELERATOR) {
        return Err(StandardSegmentError::Form {
            message: "expected the natural init accelerator".to_owned(),
        });
    }
    Ok(import)
}

fn directive_form(expression: &Expr) -> Option<&str> {
    let ExprKind::List(node) = expression.node() else {
        return None;
    };
    let [head, name] = SpannedRepr::list_items(node) else {
        return None;
    };
    match (atom(head)?, atom(name)?) {
        (Atom::Directive(directive), Atom::Symbol(name)) if directive == "accelerator" => {
            Some(name)
        }
        _ => None,
    }
}

fn import_form(expression: &Expr) -> Result<ImportDecl, StandardSegmentError> {
    let ExprKind::List(node) = expression.node() else {
        return invalid("import must be a list");
    };
    let [head, name, arena, metadata] = SpannedRepr::list_items(node) else {
        return invalid("import expects a name and two O256 atoms");
    };
    let (
        Some(Atom::Symbol(head)),
        Some(Atom::Symbol(name)),
        Some(Atom::O256(arena)),
        Some(Atom::O256(metadata)),
    ) = (atom(head), atom(name), atom(arena), atom(metadata))
    else {
        return invalid("import expects a symbolic name and two O256 atoms");
    };
    if head != "import" || name != "logical" {
        return invalid("natural init imports exactly the logical segment");
    }
    Ok(ImportDecl::new(name.to_string(), *arena, *metadata))
}

fn atom(expression: &Expr) -> Option<&Atom> {
    let ExprKind::Atom(node) = expression.node() else {
        return None;
    };
    Some(SpannedRepr::atom(node))
}

fn invalid<T>(message: impl Into<String>) -> Result<T, StandardSegmentError> {
    Err(StandardSegmentError::Form {
        message: message.into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standard_segment_triples_are_pinned() {
        let logical = compile_standard_logical().expect("logical segment");
        assert_eq!(
            SegmentTriple {
                script: logical.script_addr(),
                output: logical.output().addr(),
                kernel: logical.output().kernel(),
            },
            LOGICAL_INIT_TRIPLE
        );
        let natural = compile_standard_natural(&logical).expect("natural segment");
        assert_eq!(
            SegmentTriple {
                script: natural.script_addr(),
                output: natural.output().addr(),
                kernel: natural.output().kernel(),
            },
            NATURAL_INIT_TRIPLE
        );
        assert_eq!(natural.imports()[0].arena(), logical.output().kernel());
        assert_eq!(natural.imports()[0].metadata(), logical.output().metadata());
    }
}
