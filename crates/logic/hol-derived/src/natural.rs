//! Natural-number syntax carved from the chosen infinite carrier.
//!
//! This is the first userspace layer of the standard HOL construction.  It
//! chooses the carrier supplied by `ax.inf`, defines the induction-closure
//! predicate on that carrier, and uses the guarded subtype package to carve
//! out the naturals.  No constructor here is trusted: authority remains in
//! the two small kernel capabilities consumed by [`InfinityExt`] and
//! [`SubtypeExt`].

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{AX_INF, AX_SUB, Kernel, KernelError, Ref};

use crate::{
    Infinity, InfinityError, InfinityExt, ModelError, Subtype, SubtypeError, SubtypeExt,
    eta_expand_at, substitute,
};

/// The first object-language natural-number package.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Naturals {
    /// Chosen infinite carrier, successor candidate, and missed point.
    pub infinity: Infinity,
    /// `ind → bool`: membership in every successor-closed predicate containing zero.
    pub member: Ref,
    /// The guarded subtype carved out by [`member`](Self::member).
    pub subtype: Subtype,
    /// The object-language natural-number type.
    pub ty: Ref,
    /// Zero, obtained by abstracting the missed point.
    pub zero: Ref,
    /// Successor on the subtype: `λn. abs (ind.succ (rep n))`.
    pub succ: Ref,
    /// The standard induction-principle statement over [`ty`](Self::ty).
    ///
    /// This row is not yet projected as its own theorem.  The next proof
    /// layer derives it from the subtype and Infinity package theorems.
    pub induction: Ref,
}

impl Naturals {
    /// Resolves one stable init-library name in this package.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Ref> {
        self.symbols()
            .find_map(|(candidate, reference)| (candidate == name).then_some(reference))
    }

    /// Iterates the stable external dictionary for the package.
    ///
    /// Names are userspace metadata; they are not stored in or interpreted by
    /// the trusted arena.
    #[must_use]
    pub fn symbols(&self) -> impl ExactSizeIterator<Item = (&'static str, Ref)> {
        [
            ("ind", self.infinity.carrier),
            ("ind.zero", self.infinity.missed),
            ("ind.succ", self.infinity.map),
            ("nat.member", self.member),
            ("nat", self.ty),
            ("nat.rep", self.subtype.rep),
            ("nat.abs", self.subtype.abs),
            ("nat.zero", self.zero),
            ("nat.succ", self.succ),
            ("nat.induction", self.induction),
        ]
        .into_iter()
    }
}

/// A failure while constructing the natural-number package.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum NaturalError {
    /// A checked kernel constructor rejected the derived syntax.
    #[snafu(display("natural-number construction was rejected: {source}"))]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Selection of the infinite carrier failed.
    #[snafu(display("natural-number carrier selection failed: {source}"))]
    Infinity {
        /// Underlying userspace failure.
        source: InfinityError,
    },
    /// Carving the guarded subtype failed.
    #[snafu(display("natural-number subtype construction failed: {source}"))]
    Subtype {
        /// Underlying userspace failure.
        source: SubtypeError,
    },
    /// Specializing a userspace membership schema failed.
    #[snafu(display("natural-number membership specialization failed: {source}"))]
    Substitution {
        /// Underlying checked userspace substitution failure.
        source: ModelError,
    },
}

impl From<KernelError> for NaturalError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source }
    }
}

impl From<InfinityError> for NaturalError {
    fn from(source: InfinityError) -> Self {
        Self::Infinity { source }
    }
}

impl From<SubtypeError> for NaturalError {
    fn from(source: SubtypeError) -> Self {
        Self::Subtype { source }
    }
}

impl From<ModelError> for NaturalError {
    fn from(source: ModelError) -> Self {
        Self::Substitution { source }
    }
}

/// Derived natural-number operations over a checked kernel.
pub trait NaturalExt {
    /// Chooses and carves the standard natural-number package.
    ///
    /// The kernel must already carry exactly the capabilities needed by the
    /// called constructions (`ax.inf` and `ax.sub`).  This method does not add
    /// assumptions itself.
    ///
    /// # Errors
    ///
    /// Returns an error if either capability is absent, `bool_ty` is not the
    /// kernel's Boolean type, or any checked intermediate construction fails.
    fn choose_naturals(&mut self, bool_ty: Ref) -> Result<Naturals, NaturalError>;

    /// Chooses and carves naturals using an open userspace membership schema.
    ///
    /// `member_schema` must denote the definition
    /// `'a → ('a → 'a) → 'a → bool`, with `type_parameter` as its free `'a`.
    /// The implementation substitutes the chosen infinite carrier through the
    /// public checked substitution API, then applies the chosen zero and
    /// successor. This is the bridge used by the S-expression init source: the
    /// language and schema remain outside the TCB.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`choose_naturals`], or
    /// if the schema cannot be checked, specialized, or applied at the chosen
    /// carrier.
    fn choose_naturals_from_member_schema(
        &mut self,
        bool_ty: Ref,
        type_parameter: Ref,
        member_schema: Ref,
    ) -> Result<Naturals, NaturalError>;
}

impl NaturalExt for Kernel {
    fn choose_naturals(&mut self, bool_ty: Ref) -> Result<Naturals, NaturalError> {
        // Check both capabilities before appending any package syntax, so a
        // missing second capability cannot leave a half-built construction.
        require_natural_capabilities(self)?;
        let infinity = self.choose_infinity(bool_ty)?;
        let member = induction_member(self, bool_ty, &infinity)?;
        finish_naturals(self, bool_ty, infinity, member)
    }

    fn choose_naturals_from_member_schema(
        &mut self,
        bool_ty: Ref,
        type_parameter: Ref,
        member_schema: Ref,
    ) -> Result<Naturals, NaturalError> {
        require_natural_capabilities(self)?;
        let infinity = self.choose_infinity(bool_ty)?;
        let specialized = substitute(self, type_parameter, infinity.carrier, member_schema)?;
        let at_zero = self.app(specialized.output, infinity.missed)?;
        // Substitution deliberately rebuilds syntax rather than hash-consing
        // it. Its expected `carrier → carrier` row can therefore be a distinct
        // reference from the chosen map's extensionally identical classifier.
        // Eta expansion checks the bridge using ordinary applications and
        // gives the argument the exact classifier expected by the schema.
        let at_zero_ty = self.classifier(at_zero)?;
        let actual = self
            .arena()
            .tag(at_zero_ty)
            .ok_or(KernelError::MissingDefinition {
                reference: at_zero_ty,
            })?;
        let expected_map_ty = self
            .arena()
            .children(at_zero_ty)
            .and_then(|mut children| children.next())
            .ok_or(KernelError::WrongForm {
                reference: at_zero_ty,
                expected: "a function accepting the successor map",
                actual,
            })?;
        let map = eta_expand_at(self, expected_map_ty, infinity.map)?;
        let member = self.app(at_zero, map)?;
        finish_naturals(self, bool_ty, infinity, member)
    }
}

fn require_natural_capabilities(kernel: &Kernel) -> Result<(), KernelError> {
    if !kernel.arena().axioms().any(|name| name == AX_INF) {
        return Err(KernelError::MissingAxiom { name: AX_INF });
    }
    if !kernel.arena().axioms().any(|name| name == AX_SUB) {
        return Err(KernelError::MissingAxiom { name: AX_SUB });
    }
    Ok(())
}

fn finish_naturals(
    kernel: &mut Kernel,
    bool_ty: Ref,
    infinity: Infinity,
    member: Ref,
) -> Result<Naturals, NaturalError> {
    let subtype = kernel.guarded_subtype(bool_ty, infinity.carrier, member)?;
    let zero = kernel.app(subtype.abs, infinity.missed)?;

    let n = kernel.tm_fv(
        kernel.fresh_name(&[subtype.sub, subtype.rep, subtype.abs])?,
        subtype.sub,
    )?;
    let represented = kernel.app(subtype.rep, n)?;
    let next_ind = kernel.app(infinity.map, represented)?;
    let next_nat = kernel.app(subtype.abs, next_ind)?;
    let succ = kernel.lam(n, next_nat)?;
    let induction = induction_statement(kernel, bool_ty, subtype.sub, zero, succ)?;

    Ok(Naturals {
        infinity,
        member,
        subtype,
        ty: subtype.sub,
        zero,
        succ,
        induction,
    })
}

fn induction_member(
    kernel: &mut Kernel,
    bool_ty: Ref,
    infinity: &Infinity,
) -> Result<Ref, KernelError> {
    let predicate_ty = kernel.ty_arr(infinity.carrier, bool_ty)?;
    let predicate = kernel.tm_fv(
        kernel.fresh_name(&[infinity.carrier, infinity.map])?,
        predicate_ty,
    )?;
    let n = kernel.tm_fv(kernel.fresh_name(&[predicate])?, infinity.carrier)?;
    let k = kernel.tm_fv(kernel.fresh_name(&[predicate, n])?, infinity.carrier)?;

    let at_zero = kernel.app(predicate, infinity.missed)?;
    let at_k = kernel.app(predicate, k)?;
    let next_k = kernel.app(infinity.map, k)?;
    let at_next = kernel.app(predicate, next_k)?;
    let closed_step = imp(kernel, bool_ty, at_k, at_next)?;
    let closed = kernel.forall_tm(bool_ty, k, closed_step)?;
    let base_and_closed = and(kernel, bool_ty, at_zero, closed)?;
    let at_n = kernel.app(predicate, n)?;
    let entails_n = imp(kernel, bool_ty, base_and_closed, at_n)?;
    let every_predicate = kernel.forall_tm(bool_ty, predicate, entails_n)?;
    kernel.lam(n, every_predicate)
}

fn induction_statement(
    kernel: &mut Kernel,
    bool_ty: Ref,
    nat: Ref,
    zero: Ref,
    succ: Ref,
) -> Result<Ref, KernelError> {
    let predicate_ty = kernel.ty_arr(nat, bool_ty)?;
    let predicate = kernel.tm_fv(kernel.fresh_name(&[nat, zero, succ])?, predicate_ty)?;
    let n = kernel.tm_fv(kernel.fresh_name(&[predicate])?, nat)?;
    let at_zero = kernel.app(predicate, zero)?;
    let at_n = kernel.app(predicate, n)?;
    let next = kernel.app(succ, n)?;
    let at_next = kernel.app(predicate, next)?;
    let step = imp(kernel, bool_ty, at_n, at_next)?;
    let every_step = kernel.forall_tm(bool_ty, n, step)?;
    let premises = and(kernel, bool_ty, at_zero, every_step)?;
    let conclusion = kernel.forall_tm(bool_ty, n, at_n)?;
    let principle = imp(kernel, bool_ty, premises, conclusion)?;
    kernel.forall_tm(bool_ty, predicate, principle)
}

fn and(kernel: &mut Kernel, bool_ty: Ref, left: Ref, right: Ref) -> Result<Ref, KernelError> {
    let unary = kernel.ty_arr(bool_ty, bool_ty)?;
    let binary = kernel.ty_arr(bool_ty, unary)?;
    let binder = kernel.tm_fv(kernel.fresh_name(&[left, right])?, binary)?;
    kernel.and_tm(bool_ty, binder, left, right)
}

fn imp(kernel: &mut Kernel, bool_ty: Ref, left: Ref, right: Ref) -> Result<Ref, KernelError> {
    let unary = kernel.ty_arr(bool_ty, bool_ty)?;
    let binary = kernel.ty_arr(bool_ty, unary)?;
    let binder = kernel.tm_fv(kernel.fresh_name(&[left, right])?, binary)?;
    kernel.imp_tm(bool_ty, binder, left, right)
}
