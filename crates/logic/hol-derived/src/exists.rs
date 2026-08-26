//! Userspace opening of the Hilbert-choice encoding of term existentials.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, SynFactId, Tag, TmTag};

use crate::{ModelError, substitute};

/// The witness chosen by `∃x. body` and the checked beta-reduced body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OpenedExists {
    /// Hilbert-choice witness selected by the existential encoding.
    pub witness: Ref,
    /// Body after replacing its binder with [`witness`](Self::witness).
    pub body: Ref,
    /// Capture-avoiding substitution certificate for the lambda body.
    pub substitution: SynFactId,
    /// Conversion certificate from the encoded existential to [`body`](Self::body).
    pub beta: SynFactId,
}

/// Exact declaration targets for opening one encoded term existential.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OpenedExistsDecl {
    /// The predeclared Hilbert-choice witness.
    pub witness: Ref,
    /// The predeclared beta-reduced body.
    pub body: Ref,
}

/// A failure while opening an encoded term existential.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ExistsError {
    /// A checked kernel operation rejected the derived step.
    #[snafu(display("existential opening was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Capture-avoiding substitution could not be derived.
    #[snafu(display("existential substitution failed: {source}"))]
    Substitution {
        /// Underlying userspace traversal failure.
        source: ModelError,
    },
    /// The supplied row is not the application-of-choice encoding of `exists`.
    #[snafu(display("reference {reference:?} is not an encoded term existential"))]
    WrongForm {
        /// Rejected source row.
        reference: Ref,
    },
}

impl From<KernelError> for ExistsError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

impl From<ModelError> for ExistsError {
    fn from(source: ModelError) -> Self {
        Self::Substitution { source }
    }
}

/// Opens one `Kernel::exists_tm` row at its Hilbert-choice witness.
///
/// The returned beta fact is also unioned into the kernel's conversion
/// column, so the original existential and the returned body immediately have
/// the same semantic representative. This is a sound checked mutation, not a
/// theorem rule.
///
/// # Errors
///
/// Returns an error unless `source` has exactly the checked
/// `app (lam binder body) witness` shape emitted by `Kernel::exists_tm`, and
/// unless substitution, beta conversion, and conversion union all succeed.
pub fn open_exists(kernel: &mut Kernel, source: Ref) -> Result<OpenedExists, ExistsError> {
    open_exists_impl(kernel, source, None)
}

/// Opens one encoded existential at exact predeclared witness and body rows.
///
/// The declaration has no authority. This userspace helper checks that the
/// witness is the one physically encoded by `source`, recursively derives the
/// ordinary substitution certificate, relates its output to the declared
/// body, and invokes the unchanged kernel beta rule.
///
/// # Errors
///
/// Returns an error unless `source` has the standard encoding, its witness is
/// exact, the declared body is alpha-equivalent to checked substitution, and
/// the kernel accepts every certificate step.
pub fn open_exists_at(
    kernel: &mut Kernel,
    source: Ref,
    declaration: OpenedExistsDecl,
) -> Result<OpenedExists, ExistsError> {
    open_exists_impl(kernel, source, Some(declaration))
}

fn open_exists_impl(
    kernel: &mut Kernel,
    source: Ref,
    declaration: Option<OpenedExistsDecl>,
) -> Result<OpenedExists, ExistsError> {
    if kernel.arena().tag(source) != Some(Tag::Tm(TmTag::App)) {
        return Err(ExistsError::WrongForm { reference: source });
    }
    let application: Vec<_> = kernel
        .arena()
        .children(source)
        .ok_or(KernelError::MissingDefinition { reference: source })?
        .collect();
    let [predicate, witness] = application.as_slice() else {
        return Err(ExistsError::WrongForm { reference: source });
    };
    if kernel.arena().tag(*predicate) != Some(Tag::Tm(TmTag::Lam))
        || kernel.arena().tag(*witness) != Some(Tag::Tm(TmTag::Eps))
    {
        return Err(ExistsError::WrongForm { reference: source });
    }
    let lambda: Vec<_> = kernel
        .arena()
        .children(*predicate)
        .ok_or(KernelError::MissingDefinition {
            reference: *predicate,
        })?
        .collect();
    let [binder, input_body] = lambda.as_slice() else {
        return Err(ExistsError::WrongForm { reference: source });
    };
    if declaration.is_some_and(|declaration| declaration.witness != *witness) {
        return Err(ExistsError::WrongForm { reference: source });
    }

    let substitution = substitute(kernel, *binder, *witness, *input_body)?;
    let (body, substitution_fact) = if let Some(declaration) = declaration {
        let target = crate::join_alpha_equivalent(kernel, substitution.output, declaration.body)
            .map_err(ModelError::from)?;
        (
            declaration.body,
            kernel.syn_trans(None, substitution.fact, target)?,
        )
    } else {
        (substitution.output, substitution.fact)
    };
    let beta = kernel.tm_beta_fact(None, source, substitution_fact)?;
    kernel.union_syn_fact(beta)?;
    Ok(OpenedExists {
        witness: *witness,
        body,
        substitution: substitution_fact,
        beta,
    })
}
