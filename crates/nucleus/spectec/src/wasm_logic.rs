//! Adapters from the complete `SpecTec` document to program-logic predicates.

use covalence_data_spectec::IlKind;
use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref};

use crate::{InterpretationKind, ParameterizedDocument};

/// The execution predicates extracted from one lowered `SpecTec` document.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpecTecExecution {
    /// Shared erased configuration classifier.
    pub state_ty: Ref,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
    /// Curried `state -> state -> bool` view of `Steps`.
    pub steps: Ref,
    /// Exact checked classifier of `steps`.
    pub steps_ty: Ref,
}

/// Why the WebAssembly program-logic adapter could not be constructed.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum WasmLogicError {
    /// The exact lowered document lacks one required declaration.
    #[snafu(display("expected one SpecTec {kind:?} declaration named {name:?}, found {count}"))]
    Declaration {
        /// Required declaration category.
        kind: IlKind,
        /// Required exact source name.
        name: &'static str,
        /// Number of matching declarations.
        count: usize,
    },
    /// The lowering did not use one required structural interpretation.
    #[snafu(display("missing SpecTec interpretation operation {label:?}"))]
    Operation {
        /// Required stable operation label.
        label: &'static str,
    },
    /// A checked HOL construction failed.
    #[snafu(display("could not construct SpecTec program-logic adapter: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
}

/// Extracts a checked curried view of the WebAssembly `Steps` relation.
///
/// The `SpecTec` IL represents a multi-argument relation as a predicate over one
/// interpreted tuple. This adapter retrieves the exact lowered `Steps` slot and
/// the exact tuple constructor used by that lowering, then constructs
/// `lambda before after. Steps(tuple(before, after))`. It does not assert the
/// complete theory or create a theorem.
///
/// # Errors
///
/// Returns an error unless `Steps` is unique, the binary tuple operation was
/// used by the lowering, and all checked applications and abstractions typecheck.
/// `kernel` is unchanged on failure.
pub fn spectec_execution(
    kernel: &mut Kernel,
    document: &ParameterizedDocument,
) -> Result<SpecTecExecution, WasmLogicError> {
    let ids = document.schema.named(IlKind::Relation, "Steps");
    let [id] = ids else {
        return Err(WasmLogicError::Declaration {
            kind: IlKind::Relation,
            name: "Steps",
            count: ids.len(),
        });
    };
    let relation = document
        .schema
        .declaration(*id)
        .ok_or(WasmLogicError::Declaration {
            kind: IlKind::Relation,
            name: "Steps",
            count: 0,
        })?
        .reference();
    let tuple = document
        .operations()
        .find(|operation| {
            operation.kind() == InterpretationKind::Tuple
                && operation.signature.label == "tuple:2"
                && operation.signature.domains.as_ref()
                    == [document.schema.value(), document.schema.value()]
                && operation.signature.codomain == document.schema.value()
        })
        .ok_or(WasmLogicError::Operation { label: "tuple:2" })?
        .reference;

    let mut staged = kernel.fork();
    let roots = [
        relation,
        tuple,
        document.schema.value(),
        document.schema.bool_ty(),
    ];
    let before_name = staged
        .fresh_name(&roots)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let after_name = before_name.checked_add(1).ok_or(WasmLogicError::Kernel {
        source: KernelError::TooManyNames,
    })?;
    let before = staged
        .tm_fv(before_name, document.schema.value())
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let after = staged
        .tm_fv(after_name, document.schema.value())
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let pair = staged
        .app(tuple, before)
        .and_then(|tuple| staged.app(tuple, after))
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let related = staged
        .app(relation, pair)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let predicate_ty = staged
        .ty_arr(document.schema.value(), document.schema.bool_ty())
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let inner = staged
        .lam_at(predicate_ty, after, related)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let curried_ty = staged
        .ty_arr(document.schema.value(), predicate_ty)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    let steps = staged
        .lam_at(curried_ty, before, inner)
        .map_err(|source| WasmLogicError::Kernel { source })?;
    *kernel = staged;
    Ok(SpecTecExecution {
        state_ty: document.schema.value(),
        bool_ty: document.schema.bool_ty(),
        steps,
        steps_ty: curried_ty,
    })
}
