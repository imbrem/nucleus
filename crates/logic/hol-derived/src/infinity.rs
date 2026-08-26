//! A usable userspace package projected from the axiom of infinity.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    InfinityAxiom, Kernel, KernelError, Lit, Ref, Sort, SynFactId, ThmId, builtin::Op2,
};

use crate::{
    ChosenModel, ChosenModelDecl, ChosenModelProof, ExistsError, ModelError, ModelExt, open_exists,
};

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
    /// Existential selecting [`missed`](Self::missed).
    pub missed_exists: Ref,
    /// Point outside the image of [`map`](Self::map).
    pub missed: Ref,
    /// Equality-reflection and missed-point property for the chosen structure.
    pub property: Ref,
    /// `∀x y. map x = map y = (x = y)`.
    pub reflects_equality: Ref,
    /// `∀x. ¬(map x = missed)`.
    pub avoids_missed: Ref,
    /// The theorem concluding exactly [`property`](Self::property).
    pub theorem: ThmId,
    /// The theorem concluding exactly [`reflects_equality`](Self::reflects_equality).
    pub reflects_equality_theorem: ThmId,
    /// The theorem concluding exactly [`avoids_missed`](Self::avoids_missed).
    pub avoids_missed_theorem: ThmId,
    /// Outer beta certificate selecting [`map`](Self::map).
    pub map_beta: SynFactId,
    /// Inner beta certificate selecting [`missed`](Self::missed).
    pub missed_beta: SynFactId,
}

/// Stable syntax and binder layout of the infinity axiom sentence.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InfinityAxiomDecl {
    /// Closed type-existence sentence.
    pub exists_type: Ref,
    /// Open body quantified by the sentence.
    pub body: Ref,
    /// Bound carrier name.
    pub carrier_name: u64,
    /// First reserved binder name.
    pub base_name: u64,
}

/// Stable syntax of the selected infinity package.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InfinityDecl {
    /// Exact axiom sentence declaration.
    pub axiom: InfinityAxiomDecl,
    /// Exact selected-model declaration.
    pub model: ChosenModelDecl,
    /// Concrete infinite carrier.
    pub carrier: Ref,
    /// Injective endomap.
    pub map: Ref,
    /// Existential selecting a point outside the endomap image.
    pub missed_exists: Ref,
    /// Point outside the endomap image.
    pub missed: Ref,
    /// Conjunction of the two structure laws.
    pub property: Ref,
    /// Equality-reflection law.
    pub reflects_equality: Ref,
    /// Missed-point law.
    pub avoids_missed: Ref,
}

impl InfinityDecl {
    /// Iterates every syntax reference needed for exact replay.
    pub fn references(&self) -> impl Iterator<Item = Ref> + '_ {
        [self.axiom.exists_type, self.axiom.body]
            .into_iter()
            .chain(self.model.references())
            .chain([
                self.carrier,
                self.map,
                self.missed_exists,
                self.missed,
                self.property,
                self.reflects_equality,
                self.avoids_missed,
            ])
    }

    /// Remaps every syntax reference while retaining binder metadata.
    ///
    /// # Errors
    ///
    /// Returns the first error produced by `map`.
    pub fn try_map<E>(self, mut map: impl FnMut(Ref) -> Result<Ref, E>) -> Result<Self, E> {
        Ok(Self {
            axiom: InfinityAxiomDecl {
                exists_type: map(self.axiom.exists_type)?,
                body: map(self.axiom.body)?,
                carrier_name: self.axiom.carrier_name,
                base_name: self.axiom.base_name,
            },
            model: self.model.try_map(&mut map)?,
            carrier: map(self.carrier)?,
            map: map(self.map)?,
            missed_exists: map(self.missed_exists)?,
            missed: map(self.missed)?,
            property: map(self.property)?,
            reflects_equality: map(self.reflects_equality)?,
            avoids_missed: map(self.avoids_missed)?,
        })
    }
}

/// Kernel-local theorem and beta evidence certifying an [`InfinityDecl`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InfinityProof {
    /// Theorem concluding the axiom sentence.
    pub axiom: ThmId,
    /// Selected-model evidence.
    pub model: ChosenModelProof,
    /// Exact theorem for the conjunction of laws.
    pub property: ThmId,
    /// Exact theorem for equality reflection.
    pub reflects_equality: ThmId,
    /// Exact theorem for the missed-point law.
    pub avoids_missed: ThmId,
    /// Beta certificate selecting the map.
    pub map_beta: SynFactId,
    /// Beta certificate selecting the missed point.
    pub missed_beta: SynFactId,
}

impl Infinity {
    /// Forgets theorem/cache identity while retaining exact syntax.
    #[must_use]
    pub const fn declaration(self) -> InfinityDecl {
        InfinityDecl {
            axiom: InfinityAxiomDecl {
                exists_type: self.axiom.exists_type,
                body: self.axiom.body,
                carrier_name: self.axiom.carrier_name,
                base_name: self.axiom.base_name,
            },
            model: self.model.declaration(),
            carrier: self.carrier,
            map: self.map,
            missed_exists: self.missed_exists,
            missed: self.missed,
            property: self.property,
            reflects_equality: self.reflects_equality,
            avoids_missed: self.avoids_missed,
        }
    }

    /// Projects the kernel-local evidence for this declaration.
    #[must_use]
    pub const fn proof(self) -> InfinityProof {
        InfinityProof {
            axiom: self.axiom.theorem,
            model: self.model.proof(),
            property: self.theorem,
            reflects_equality: self.reflects_equality_theorem,
            avoids_missed: self.avoids_missed_theorem,
            map_beta: self.map_beta,
            missed_beta: self.missed_beta,
        }
    }
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

    /// Projects infinity using an explicit five-name allocation block.
    ///
    /// This is the replay form: userspace can consume binder metadata from a
    /// frozen declaration instead of allowing unrelated arena suffixes to
    /// choose a parallel alpha-variant.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`choose_infinity`](Self::choose_infinity),
    /// or if the requested name block overflows.
    fn choose_infinity_at(
        &mut self,
        bool_ty: Ref,
        base_name: u64,
    ) -> Result<Infinity, InfinityError>;
}

impl InfinityExt for Kernel {
    fn choose_infinity(&mut self, bool_ty: Ref) -> Result<Infinity, InfinityError> {
        let axiom = self.inf_exists(bool_ty)?;
        project_infinity(self, bool_ty, axiom)
    }

    fn choose_infinity_at(
        &mut self,
        bool_ty: Ref,
        base_name: u64,
    ) -> Result<Infinity, InfinityError> {
        let axiom = self.inf_exists_at(bool_ty, base_name)?;
        project_infinity(self, bool_ty, axiom)
    }
}

fn project_infinity(
    kernel: &mut Kernel,
    bool_ty: Ref,
    axiom: InfinityAxiom,
) -> Result<Infinity, InfinityError> {
    let model = kernel.choose_model(axiom.theorem)?;
    let map = open_exists(kernel, model.specification)?;
    let missed = open_exists(kernel, map.body)?;

    if kernel.category(model.ty)? != Sort::Ty
        || kernel.category(map.witness)? != Sort::Tm
        || kernel.category(missed.witness)? != Sort::Tm
        || kernel.classifier(missed.body)? != bool_ty
    {
        return Err(KernelError::InvalidTheoremRule {
            rule: "infinity package projection",
        }
        .into());
    }

    if kernel.arena().op2(missed.body) != Some(Op2::And) {
        return Err(KernelError::InvalidTheoremRule {
            rule: "infinity package conjunction",
        }
        .into());
    }
    let properties: Vec<_> = kernel
        .arena()
        .children(missed.body)
        .ok_or(KernelError::MissingDefinition {
            reference: missed.body,
        })?
        .collect();
    let [reflects_equality, avoids_missed] = properties.as_slice() else {
        return Err(KernelError::InvalidTheoremRule {
            rule: "infinity package conjunction",
        }
        .into());
    };

    // Retain the chosen-model theorem as evidence for `ChosenModel`; the
    // package theorem is a converted copy whose physical atom is exactly
    // the beta-opened conjunction.
    let theorem = kernel.copy_theorem(model.theorem)?;
    kernel.convert_theorem(theorem, model.specification, missed.body)?;
    let property = Lit::positive(missed.body.get());
    let reflects_equality_theorem = kernel.expand_conclusion(theorem, property, Some(false))?;
    let avoids_missed_theorem = kernel.expand_conclusion(theorem, property, Some(true))?;

    Ok(Infinity {
        axiom,
        model,
        carrier: model.ty,
        map: map.witness,
        missed_exists: map.body,
        missed: missed.witness,
        property: missed.body,
        reflects_equality: *reflects_equality,
        avoids_missed: *avoids_missed,
        theorem,
        reflects_equality_theorem,
        avoids_missed_theorem,
        map_beta: map.beta,
        missed_beta: missed.beta,
    })
}
