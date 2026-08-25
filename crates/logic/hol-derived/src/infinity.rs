//! A usable userspace package projected from the axiom of infinity.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{InfinityAxiom, Kernel, KernelError, Ref, Sort, SynFactId, ThmId};

use crate::{ChosenModel, ExistsError, ModelError, ModelExt, open_exists};

/// A chosen infinite carrier and the structure supplied by `ax.inf`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Infinity {
    /// Closed type-existence sentence and its axiom theorem.
    pub axiom: InfinityAxiom,
    /// Chosen carrier and its specification theorem.
    pub model: ChosenModel,
    /// Concrete infinite carrier type.
    pub carrier: Ref,
    /// Injective endomap on [`carrier`](Self::carrier).
    pub map: Ref,
    /// Point outside the image of [`map`](Self::map).
    pub missed: Ref,
    /// Equality-reflection and missed-point property for the chosen structure.
    pub property: Ref,
    /// The theorem whose conclusion is conversion-equal to [`property`](Self::property).
    pub theorem: ThmId,
    /// Outer beta certificate selecting [`map`](Self::map).
    pub map_beta: SynFactId,
    /// Inner beta certificate selecting [`missed`](Self::missed).
    pub missed_beta: SynFactId,
}

/// A failure while projecting the infinity package.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum InfinityError {
    /// A checked kernel operation rejected the package.
    #[snafu(display("infinity package was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Type-level model selection failed.
    #[snafu(display("infinity model selection failed: {source}"))]
    Model {
        /// Underlying userspace failure.
        source: ModelError,
    },
    /// A term existential in the canonical package could not be opened.
    #[snafu(display("infinity witness selection failed: {source}"))]
    Exists {
        /// Underlying userspace failure.
        source: ExistsError,
    },
}

impl From<KernelError> for InfinityError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

impl From<ModelError> for InfinityError {
    fn from(source: ModelError) -> Self {
        Self::Model { source }
    }
}

impl From<ExistsError> for InfinityError {
    fn from(source: ExistsError) -> Self {
        Self::Exists { source }
    }
}

/// Derived infinity-package operations over a checked kernel.
pub trait InfinityExt {
    /// Takes on `ax.inf` and projects its chosen carrier, map, and missed point.
    ///
    /// # Errors
    ///
    /// Returns an error unless the kernel already carries the `ax.inf`
    /// capability, `bool_ty` is its Boolean type, model selection succeeds,
    /// and both canonical term existentials admit checked beta opening.
    fn choose_infinity(&mut self, bool_ty: Ref) -> Result<Infinity, InfinityError>;
}

impl InfinityExt for Kernel {
    fn choose_infinity(&mut self, bool_ty: Ref) -> Result<Infinity, InfinityError> {
        let axiom = self.inf_exists(bool_ty)?;
        let model = self.choose_model(axiom.theorem)?;
        let map = open_exists(self, model.specification)?;
        let missed = open_exists(self, map.body)?;

        if self.category(model.ty)? != Sort::Ty
            || self.category(map.witness)? != Sort::Tm
            || self.category(missed.witness)? != Sort::Tm
            || self.classifier(missed.body)? != bool_ty
        {
            return Err(KernelError::InvalidTheoremRule {
                rule: "infinity package projection",
            }
            .into());
        }

        Ok(Infinity {
            axiom,
            model,
            carrier: model.ty,
            map: map.witness,
            missed: missed.witness,
            property: missed.body,
            theorem: model.theorem,
            map_beta: map.beta,
            missed_beta: missed.beta,
        })
    }
}
