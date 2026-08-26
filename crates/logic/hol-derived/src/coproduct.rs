//! Language-independent userspace interfaces for coproduct construction.

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_logic_hol::{Kernel, KernelError, Ref, Sort, Tag, TyTag, builtin::Op2};

use crate::{ModelError, Subtype, SubtypeError, SubtypeExt, substitute};

/// Failure to specialize or derive a userspace coproduct package.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum CoproductError {
    /// Checked type substitution rejected the open schema.
    #[snafu(display("could not specialize coproduct schema: {source}"))]
    Substitution {
        /// Underlying userspace substitution failure.
        source: ModelError,
    },
    /// A checked kernel query rejected one of the specialized rows.
    #[snafu(display("could not inspect specialized coproduct schema: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// The guarded-subtype package was rejected.
    #[snafu(display("could not construct coproduct subtype: {source}"))]
    Subtype {
        /// Underlying userspace subtype failure.
        source: SubtypeError,
    },
    /// The supplied schema did not specialize to a Boolean term.
    #[snafu(display("coproduct schema did not specialize to a Boolean term"))]
    NotBoolean,
    /// Temporary binder names exhausted the unsigned name space.
    #[snafu(display("coproduct construction exhausted variable names"))]
    NameExhausted,
}

/// A checked binary coproduct representation assembled outside the TCB.
#[derive(Debug)]
pub struct Coproduct {
    /// Left summand type.
    pub left: Ref,
    /// Right summand type.
    pub right: Ref,
    /// Church-encoded carrier before guarding it by the image predicate.
    pub carrier: Ref,
    /// Exact left-predicate argument type `left → bool` of [`carrier`](Self::carrier).
    pub left_predicate_ty: Ref,
    /// Exact right-predicate argument type `right → bool` of [`carrier`](Self::carrier).
    pub right_predicate_ty: Ref,
    /// Exact tail `right_predicate_ty → bool` of [`carrier`](Self::carrier).
    pub carrier_tail: Ref,
    /// Church injection `left → carrier`.
    pub left_church: Ref,
    /// Church injection `right → carrier`.
    pub right_church: Ref,
    /// Predicate selecting the union of the two injection images.
    pub predicate: Ref,
    /// Guarded subtype package for the image predicate.
    pub subtype: Subtype,
    /// Concrete coproduct type.
    pub ty: Ref,
    /// Left injection `left → ty`.
    pub inl: Ref,
    /// Exact classifier row of [`inl`](Self::inl).
    pub inl_ty: Ref,
    /// Right injection `right → ty`.
    pub inr: Ref,
    /// Exact classifier row of [`inr`](Self::inr).
    pub inr_ty: Ref,
}

/// Language-independent userspace construction of binary coproduct syntax.
pub trait CoproductExt {
    /// Constructs a guarded Church coproduct using the `ax.sub` capability.
    ///
    /// # Errors
    ///
    /// Returns an error unless the capability is present, `bool_ty` is the
    /// Boolean type, and both summands are checked types of kind `star`.
    fn coproduct(
        &mut self,
        bool_ty: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Coproduct, CoproductError>;

    /// Constructs the same syntax without invoking the subtype axiom.
    ///
    /// The returned subtype laws are unsupported statements, making this
    /// suitable for hashing, transport, and comparison but not proof.
    ///
    /// # Errors
    ///
    /// Returns an error unless `bool_ty` is Boolean and both summands are
    /// checked types of kind `star`.
    fn coproduct_terms(
        &mut self,
        bool_ty: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Coproduct, CoproductError>;
}

impl CoproductExt for Kernel {
    fn coproduct(
        &mut self,
        bool_ty: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Coproduct, CoproductError> {
        coproduct_transaction(self, bool_ty, left, right, true)
    }

    fn coproduct_terms(
        &mut self,
        bool_ty: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Coproduct, CoproductError> {
        coproduct_transaction(self, bool_ty, left, right, false)
    }
}

fn coproduct_transaction(
    kernel: &mut Kernel,
    bool_ty: Ref,
    left: Ref,
    right: Ref,
    guarded: bool,
) -> Result<Coproduct, CoproductError> {
    let mut staged = kernel.fork();
    let package = build_coproduct(&mut staged, bool_ty, left, right, guarded)?;
    *kernel = staged;
    Ok(package)
}

fn build_coproduct(
    kernel: &mut Kernel,
    bool_ty: Ref,
    left: Ref,
    right: Ref,
    guarded: bool,
) -> Result<Coproduct, CoproductError> {
    let left_predicate = kernel.ty_arr(left, bool_ty).context(KernelSnafu)?;
    let right_predicate = kernel.ty_arr(right, bool_ty).context(KernelSnafu)?;
    let carrier_tail = kernel
        .ty_arr(right_predicate, bool_ty)
        .context(KernelSnafu)?;
    let carrier = kernel
        .ty_arr(left_predicate, carrier_tail)
        .context(KernelSnafu)?;
    let base = kernel
        .fresh_name(&[bool_ty, left, right, carrier])
        .context(KernelSnafu)?;
    let mut offset = 0;
    let left_church = church_injection(
        kernel,
        &mut offset,
        base,
        left,
        left_predicate,
        right_predicate,
        carrier_tail,
        carrier,
        true,
    )?;
    let right_church = church_injection(
        kernel,
        &mut offset,
        base,
        right,
        left_predicate,
        right_predicate,
        carrier_tail,
        carrier,
        false,
    )?;
    let candidate = variable(kernel, base, &mut offset, carrier)?;
    let left_witness = variable(kernel, base, &mut offset, left)?;
    let left_image = kernel.app(left_church, left_witness).context(KernelSnafu)?;
    let left_equality = kernel
        .eq(bool_ty, candidate, left_image)
        .context(KernelSnafu)?;
    let left_exists = kernel
        .exists_tm(left_witness, left_equality)
        .context(KernelSnafu)?;
    let right_witness = variable(kernel, base, &mut offset, right)?;
    let right_image = kernel
        .app(right_church, right_witness)
        .context(KernelSnafu)?;
    let right_equality = kernel
        .eq(bool_ty, candidate, right_image)
        .context(KernelSnafu)?;
    let right_exists = kernel
        .exists_tm(right_witness, right_equality)
        .context(KernelSnafu)?;
    let image = kernel
        .op2(Op2::Or, left_exists, right_exists)
        .context(KernelSnafu)?;
    let predicate_ty = kernel.ty_arr(carrier, bool_ty).context(KernelSnafu)?;
    let predicate = kernel
        .lam_at(predicate_ty, candidate, image)
        .context(KernelSnafu)?;
    let subtype = construct_subtype(kernel, bool_ty, carrier, predicate, guarded)?;
    let ty = subtype.sub;
    let left_injection_ty = kernel.ty_arr(left, ty).context(KernelSnafu)?;
    let right_injection_ty = kernel.ty_arr(right, ty).context(KernelSnafu)?;
    let inl = lifted_injection(
        kernel,
        base,
        &mut offset,
        left,
        left_injection_ty,
        left_church,
        subtype.abs,
    )?;
    let inr = lifted_injection(
        kernel,
        base,
        &mut offset,
        right,
        right_injection_ty,
        right_church,
        subtype.abs,
    )?;
    Ok(Coproduct {
        left,
        right,
        carrier,
        left_predicate_ty: left_predicate,
        right_predicate_ty: right_predicate,
        carrier_tail,
        left_church,
        right_church,
        predicate,
        subtype,
        ty,
        inl,
        inl_ty: left_injection_ty,
        inr,
        inr_ty: right_injection_ty,
    })
}

fn construct_subtype(
    kernel: &mut Kernel,
    bool_ty: Ref,
    carrier: Ref,
    predicate: Ref,
    guarded: bool,
) -> Result<Subtype, CoproductError> {
    if guarded {
        kernel.guarded_subtype(bool_ty, carrier, predicate)
    } else {
        kernel.subtype_terms(bool_ty, carrier, predicate)
    }
    .context(SubtypeSnafu)
}

#[allow(clippy::too_many_arguments)]
fn church_injection(
    kernel: &mut Kernel,
    offset: &mut u64,
    base: u64,
    summand: Ref,
    left_predicate: Ref,
    right_predicate: Ref,
    carrier_tail: Ref,
    carrier: Ref,
    is_left: bool,
) -> Result<Ref, CoproductError> {
    let value = variable(kernel, base, offset, summand)?;
    let left = variable(kernel, base, offset, left_predicate)?;
    let right = variable(kernel, base, offset, right_predicate)?;
    let selected = if is_left { left } else { right };
    let result = kernel.app(selected, value).context(KernelSnafu)?;
    let result = kernel
        .lam_at(carrier_tail, right, result)
        .context(KernelSnafu)?;
    let result = kernel.lam_at(carrier, left, result).context(KernelSnafu)?;
    let injection_ty = kernel.ty_arr(summand, carrier).context(KernelSnafu)?;
    kernel
        .lam_at(injection_ty, value, result)
        .context(KernelSnafu)
}

fn lifted_injection(
    kernel: &mut Kernel,
    base: u64,
    offset: &mut u64,
    summand: Ref,
    injection_ty: Ref,
    church: Ref,
    abstraction: Ref,
) -> Result<Ref, CoproductError> {
    let value = variable(kernel, base, offset, summand)?;
    let represented = kernel.app(church, value).context(KernelSnafu)?;
    let abstracted = kernel.app(abstraction, represented).context(KernelSnafu)?;
    kernel
        .lam_at(injection_ty, value, abstracted)
        .context(KernelSnafu)
}

fn variable(
    kernel: &mut Kernel,
    base: u64,
    offset: &mut u64,
    ty: Ref,
) -> Result<Ref, CoproductError> {
    let name = base
        .checked_add(*offset)
        .ok_or(CoproductError::NameExhausted)?;
    *offset = offset.checked_add(1).ok_or(CoproductError::NameExhausted)?;
    kernel.tm_fv(name, ty).context(KernelSnafu)
}

/// An open universal-property predicate for coproducts.
///
/// This descriptor groups three free type variables with the checked Boolean
/// term that mentions them. A source compiler may populate it, but neither the
/// descriptor nor future derivations depend on a particular surface language.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductSchema {
    /// Open left summand type variable.
    pub left: Ref,
    /// Open right summand type variable.
    pub right: Ref,
    /// Open candidate coproduct type variable.
    pub coproduct: Ref,
    /// `IsCoprod left right coproduct`, encoded as an open Boolean term.
    pub predicate: Ref,
}

impl CoproductSchema {
    /// Iterates the schema's complete checked syntax interface.
    #[must_use]
    pub fn references(&self) -> impl ExactSizeIterator<Item = Ref> {
        [self.left, self.right, self.coproduct, self.predicate].into_iter()
    }

    /// Remaps every checked reference while preserving the schema roles.
    ///
    /// # Errors
    ///
    /// Returns the first error produced by `map`.
    pub fn try_map<E>(self, mut map: impl FnMut(Ref) -> Result<Ref, E>) -> Result<Self, E> {
        Ok(Self {
            left: map(self.left)?,
            right: map(self.right)?,
            coproduct: map(self.coproduct)?,
            predicate: map(self.predicate)?,
        })
    }

    /// Specializes the three open type variables to checked resident types.
    ///
    /// The operation is transactional: a rejected schema or type leaves
    /// `kernel` unchanged. The returned term is checked Boolean syntax, but no
    /// theorem asserting it is introduced.
    ///
    /// # Errors
    ///
    /// Returns an error if any checked substitution fails, a resulting row is
    /// malformed, or the fully specialized expression is not Boolean.
    pub fn specialize(
        self,
        kernel: &mut Kernel,
        left: Ref,
        right: Ref,
        coproduct: Ref,
    ) -> Result<Ref, CoproductError> {
        let mut staged = kernel.fork();
        let predicate = substitute(&mut staged, self.left, left, self.predicate)
            .context(SubstitutionSnafu)?
            .output;
        let predicate = substitute(&mut staged, self.right, right, predicate)
            .context(SubstitutionSnafu)?
            .output;
        let predicate = substitute(&mut staged, self.coproduct, coproduct, predicate)
            .context(SubstitutionSnafu)?
            .output;
        let classifier = staged.classifier(predicate).context(KernelSnafu)?;
        if staged.category(predicate).context(KernelSnafu)? != Sort::Tm
            || staged.arena().tag(classifier) != Some(Tag::Ty(TyTag::Bool))
        {
            return Err(CoproductError::NotBoolean);
        }
        *kernel = staged;
        Ok(predicate)
    }
}
