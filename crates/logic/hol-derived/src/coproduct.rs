//! Language-independent userspace interfaces for coproduct construction.

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, Sort, SynFactId, SynRel, Tag, ThmId, TmTag, TyTag, builtin::Op2,
};

use crate::{
    EqualityError, ExistsError, ForallError, ModelError, Subtype, SubtypeError, SubtypeExt,
    SyntaxError, equality_symmetry, equality_transitivity, forall_elim, function_extensionality,
    join_alpha_equivalent, join_same_syntax, open_exists, substitute,
};

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
    /// Universal elimination rejected a subtype law.
    #[snafu(display("could not specialize coproduct law: {source}"))]
    Forall {
        /// Underlying userspace universal-elimination failure.
        source: ForallError,
    },
    /// Equality symmetry rejected an intermediate theorem.
    #[snafu(display("could not orient coproduct equality: {source}"))]
    Equality {
        /// Underlying userspace equality failure.
        source: EqualityError,
    },
    /// Opening an encoded existential image branch failed.
    #[snafu(display("could not open coproduct image branch: {source}"))]
    Exists {
        /// Underlying userspace existential-opening failure.
        source: ExistsError,
    },
    /// Structural or conversion syntax could not be certified.
    #[snafu(display("could not certify coproduct syntax: {source}"))]
    Syntax {
        /// Underlying userspace syntax failure.
        source: SyntaxError,
    },
    /// The supplied schema did not specialize to a Boolean term.
    #[snafu(display("coproduct schema did not specialize to a Boolean term"))]
    NotBoolean,
    /// Temporary binder names exhausted the unsigned name space.
    #[snafu(display("coproduct construction exhausted variable names"))]
    NameExhausted,
    /// A checked row did not have the shape required by the derivation.
    #[snafu(display("coproduct proof expected {expected}"))]
    WrongForm {
        /// Expected checked shape.
        expected: &'static str,
    },
}

/// A checked binary coproduct representation assembled outside the TCB.
#[derive(Debug)]
pub struct Coproduct {
    /// Exact Boolean type used by predicates and equality.
    pub bool_ty: Ref,
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

/// A Hilbert-choice eliminator for one coproduct codomain.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductEliminator {
    /// Result type.
    pub codomain: Ref,
    /// Exact type `left → codomain`.
    pub left_map_ty: Ref,
    /// Exact type `right → codomain`.
    pub right_map_ty: Ref,
    /// Exact type `coproduct → codomain`.
    pub value_map_ty: Ref,
    /// Exact curried classifier of [`function`](Self::function).
    pub function_ty: Ref,
    /// Curried eliminator `(left → C) → (right → C) → coproduct → C`.
    pub function: Ref,
}

/// One exact coproduct computation theorem.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductComputation {
    /// Equality proposition proved by [`theorem`](Self::theorem).
    pub proposition: Ref,
    /// Exact premise-free theorem of [`proposition`](Self::proposition).
    pub theorem: ThmId,
}

/// The two universally quantified computation laws for one mediator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductLaws {
    /// Choice-based mediator whose laws were proved.
    pub eliminator: CoproductEliminator,
    /// Universal left-injection computation proposition.
    pub left: Ref,
    /// Premise-free theorem of [`left`](Self::left).
    pub left_theorem: ThmId,
    /// Universal right-injection computation proposition.
    pub right: Ref,
    /// Premise-free theorem of [`right`](Self::right).
    pub right_theorem: ThmId,
    /// Conjunction of [`left`](Self::left) and [`right`](Self::right).
    pub conjunction: Ref,
    /// Premise-free theorem of [`conjunction`](Self::conjunction).
    pub theorem: ThmId,
}

/// Premise-free evidence that every coproduct representation lies in an
/// injection image.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductExhaustiveness {
    /// Existential proposition `∃x : carrier. predicate x`.
    pub inhabited: Ref,
    /// Premise-free theorem of [`inhabited`](Self::inhabited).
    pub inhabited_theorem: ThmId,
    /// Universal proposition `∀t : coproduct. predicate (rep t)`.
    pub image_of_rep: Ref,
    /// Premise-free theorem of [`image_of_rep`](Self::image_of_rep).
    pub theorem: ThmId,
}

/// One specialized coproduct image split.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductCases {
    /// Specialized coproduct value.
    pub value: Ref,
    /// Left image existential.
    pub left: Ref,
    /// Right image existential.
    pub right: Ref,
    /// Disjunction of [`left`](Self::left) and [`right`](Self::right).
    pub disjunction: Ref,
    /// Premise-free theorem of [`disjunction`](Self::disjunction).
    pub theorem: ThmId,
}

/// One opened injection-image branch for a coproduct value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductBranch {
    /// Hilbert witness selected by the encoded existential.
    pub witness: Ref,
    /// Opened carrier equality `rep value = church witness`.
    pub image_equality: Ref,
    /// Injection application `inl witness` or `inr witness`.
    pub injected: Ref,
    /// Equality `value = injected` recovered through the subtype laws.
    pub value_equality: Ref,
    /// Theorem from the original existential branch to [`value_equality`](Self::value_equality).
    pub theorem: ThmId,
}

/// Both opened branches of one specialized coproduct image split.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductOpenedCases {
    /// Specialized image split from which the branches were opened.
    pub cases: CoproductCases,
    /// Left injection branch.
    pub left: CoproductBranch,
    /// Right injection branch.
    pub right: CoproductBranch,
}

/// Proof that a candidate mediator obeys both coproduct computation laws.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductCandidateLaws {
    /// Candidate function `coproduct → codomain`.
    pub function: Ref,
    /// Universal law `∀a. function (inl a) = left_map a`.
    pub left: Ref,
    /// Theorem of [`left`](Self::left).
    pub left_theorem: ThmId,
    /// Universal law `∀b. function (inr b) = right_map b`.
    pub right: Ref,
    /// Theorem of [`right`](Self::right).
    pub right_theorem: ThmId,
}

/// Extensional uniqueness of the choice-based coproduct mediator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CoproductUniqueness {
    /// Candidate mediator proved equal to the canonical mediator.
    pub candidate: Ref,
    /// Canonical partially applied mediator `case left_map right_map`.
    pub canonical: Ref,
    /// Universal pointwise equality between the two mediators.
    pub pointwise: Ref,
    /// Premise-free theorem of [`pointwise`](Self::pointwise).
    pub pointwise_theorem: ThmId,
    /// Function equality `candidate = canonical`.
    pub equality: Ref,
    /// Premise-free theorem of [`equality`](Self::equality).
    pub theorem: ThmId,
}

impl Coproduct {
    /// Constructs the choice-based eliminator at one checked result type.
    ///
    /// Construction is transactional and introduces no theorem. Its
    /// computation laws are a separate userspace derivation over the subtype
    /// package's checked laws.
    ///
    /// # Errors
    ///
    /// Returns an error unless this package is resident in `kernel` and
    /// `codomain` is a checked type of kind `star`.
    pub fn eliminator(
        &self,
        kernel: &mut Kernel,
        codomain: Ref,
    ) -> Result<CoproductEliminator, CoproductError> {
        let mut staged = kernel.fork();
        let eliminator = build_eliminator(&mut staged, self, codomain)?;
        *kernel = staged;
        Ok(eliminator)
    }

    /// Proves one left-injection computation instance.
    ///
    /// Given checked `f : left → C`, `g : right → C`, and `a : left`, derives
    /// the exact premise-free theorem `case f g (inl a) = f a`. The operation
    /// is transactional.
    ///
    /// # Errors
    ///
    /// Returns an error unless the eliminator belongs to this package, all
    /// arguments have its exact checked types, and the guarded subtype carries
    /// its proved representation law.
    pub fn prove_case_inl(
        &self,
        kernel: &mut Kernel,
        eliminator: CoproductEliminator,
        left_map: Ref,
        right_map: Ref,
        value: Ref,
    ) -> Result<CoproductComputation, CoproductError> {
        let mut staged = kernel.fork();
        let proof = prove_case_inner(
            &mut staged,
            self,
            eliminator,
            left_map,
            right_map,
            value,
            true,
        )?;
        *kernel = staged;
        Ok(proof)
    }

    /// Proves one right-injection computation instance.
    ///
    /// Given checked `f : left → C`, `g : right → C`, and `b : right`, derives
    /// the exact premise-free theorem `case f g (inr b) = g b`. The operation
    /// is transactional.
    ///
    /// # Errors
    ///
    /// Returns an error unless the eliminator belongs to this package, all
    /// arguments have its exact checked types, and the guarded subtype carries
    /// its proved representation law.
    pub fn prove_case_inr(
        &self,
        kernel: &mut Kernel,
        eliminator: CoproductEliminator,
        left_map: Ref,
        right_map: Ref,
        value: Ref,
    ) -> Result<CoproductComputation, CoproductError> {
        let mut staged = kernel.fork();
        let proof = prove_case_inner(
            &mut staged,
            self,
            eliminator,
            left_map,
            right_map,
            value,
            false,
        )?;
        *kernel = staged;
        Ok(proof)
    }

    /// Constructs a mediator and proves both of its universal computation laws.
    ///
    /// Given checked `f : left → C` and `g : right → C`, this derives the
    /// premise-free conjunction
    /// `(∀a. case f g (inl a) = f a) ∧ (∀b. case f g (inr b) = g b)`.
    /// The temporary quantified variables are allocated independently of the
    /// caller's existing free-variable names, and the operation is
    /// transactional.
    ///
    /// # Errors
    ///
    /// Returns an error unless the supplied eliminator belongs to this package,
    /// both maps have its required checked types, the subtype representation
    /// law is available, and every ordinary HOL derivation step succeeds.
    pub fn prove_case_laws(
        &self,
        kernel: &mut Kernel,
        eliminator: CoproductEliminator,
        left_map: Ref,
        right_map: Ref,
    ) -> Result<CoproductLaws, CoproductError> {
        let mut staged = kernel.fork();
        let proof = prove_case_laws_inner(&mut staged, self, eliminator, left_map, right_map)?;
        *kernel = staged;
        Ok(proof)
    }

    /// Proves that every represented coproduct value is in one injection image.
    ///
    /// This first proves the image predicate inhabited, then eliminates the
    /// guarded subtype's empty-predicate fallback and universally generalizes
    /// the resulting `predicate (rep t)` theorem. The operation is
    /// transactional and uses only ordinary userspace HOL rules.
    ///
    /// # Errors
    ///
    /// Returns an error unless the guarded subtype representation theorem is
    /// available and each checked equality, existential, Gentzen, beta, and
    /// universal-introduction step succeeds.
    pub fn prove_exhaustiveness(
        &self,
        kernel: &mut Kernel,
    ) -> Result<CoproductExhaustiveness, CoproductError> {
        let mut staged = kernel.fork();
        let proof = prove_exhaustiveness_inner(&mut staged, self)?;
        *kernel = staged;
        Ok(proof)
    }

    /// Specializes exhaustiveness at one value and exposes its image cases.
    ///
    /// # Errors
    ///
    /// Returns an error unless `exhaustiveness` belongs to this package,
    /// `value` has the coproduct type, and universal elimination plus checked
    /// beta conversion yield the expected binary image disjunction. Rejection
    /// is transactional.
    pub fn cases(
        &self,
        kernel: &mut Kernel,
        exhaustiveness: CoproductExhaustiveness,
        value: Ref,
    ) -> Result<CoproductCases, CoproductError> {
        let mut staged = kernel.fork();
        let cases = specialize_exhaustiveness(&mut staged, exhaustiveness, value)?;
        *kernel = staged;
        Ok(cases)
    }

    /// Opens both image existentials and recovers equality with an injection.
    ///
    /// Each returned branch theorem retains the corresponding existential as
    /// its sole premise. This is the useful sequent-calculus form for a later
    /// `or_left`: opening the Hilbert encoding itself adds no trusted rule.
    ///
    /// # Errors
    ///
    /// Returns an error unless the case split belongs to this package, both
    /// encoded existentials have their expected equality shape, and the
    /// checked subtype, equality, beta, and theorem-conversion rules recover
    /// `value = inl witness` and `value = inr witness`. Rejection is
    /// transactional.
    pub fn open_cases(
        &self,
        kernel: &mut Kernel,
        cases: CoproductCases,
    ) -> Result<CoproductOpenedCases, CoproductError> {
        let mut staged = kernel.fork();
        let left = open_case_branch(&mut staged, self, cases.value, cases.left, true)?;
        let right = open_case_branch(&mut staged, self, cases.value, cases.right, false)?;
        *kernel = staged;
        Ok(CoproductOpenedCases { cases, left, right })
    }

    /// Eliminates a proved case split through two branch theorems.
    ///
    /// `left_theorem` must use the left image existential as a premise and
    /// `right_theorem` the right image existential. Any other branch premises
    /// and conclusions are preserved, duplicate rows are contracted, and the
    /// premise-free case split is cut away. Thus callers can derive one common
    /// conclusion in both branches without adding an existential-elimination
    /// primitive to the kernel.
    ///
    /// # Errors
    ///
    /// Returns an error unless `cases` is resident, its theorem concludes the
    /// exact disjunction, and both branch theorems contain their corresponding
    /// existential premises. Rejection is transactional.
    pub fn eliminate_cases(
        &self,
        kernel: &mut Kernel,
        cases: CoproductCases,
        left_theorem: ThmId,
        right_theorem: ThmId,
    ) -> Result<ThmId, CoproductError> {
        let mut staged = kernel.fork();
        let branched = staged
            .or_left(left_theorem, right_theorem, positive(cases.disjunction))
            .context(KernelSnafu)?;
        staged.contract_theorem(branched).context(KernelSnafu)?;
        let theorem = staged
            .cut(cases.theorem, branched, positive(cases.disjunction))
            .context(KernelSnafu)?;
        *kernel = staged;
        Ok(theorem)
    }

    /// Proves that any mediator satisfying both computation laws is canonical.
    ///
    /// The proof specializes exhaustiveness at a fresh value, opens both image
    /// branches, transports the candidate and canonical functions across the
    /// recovered injection equalities, eliminates the split, generalizes the
    /// pointwise result, and invokes userspace function extensionality.
    ///
    /// # Errors
    ///
    /// Returns an error unless all functions and laws have the exact checked
    /// coproduct shapes, both candidate laws are usable universal theorems,
    /// and the ordinary derived equality and case rules prove the result.
    /// Rejection is transactional.
    pub fn prove_unique_mediator(
        &self,
        kernel: &mut Kernel,
        eliminator: CoproductEliminator,
        left_map: Ref,
        right_map: Ref,
        candidate: CoproductCandidateLaws,
    ) -> Result<CoproductUniqueness, CoproductError> {
        let mut staged = kernel.fork();
        let proof = prove_unique_mediator_inner(
            &mut staged,
            self,
            eliminator,
            left_map,
            right_map,
            candidate,
        )?;
        *kernel = staged;
        Ok(proof)
    }
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
        bool_ty,
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

fn build_eliminator(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
    codomain: Ref,
) -> Result<CoproductEliminator, CoproductError> {
    let left_map_ty = kernel
        .ty_arr(coproduct.left, codomain)
        .context(KernelSnafu)?;
    let right_map_ty = kernel
        .ty_arr(coproduct.right, codomain)
        .context(KernelSnafu)?;
    let value_map_ty = kernel.ty_arr(coproduct.ty, codomain).context(KernelSnafu)?;
    let right_tail = kernel
        .ty_arr(right_map_ty, value_map_ty)
        .context(KernelSnafu)?;
    let function_ty = kernel
        .ty_arr(left_map_ty, right_tail)
        .context(KernelSnafu)?;
    let base = kernel
        .fresh_name(&coproduct_references(coproduct, codomain))
        .context(KernelSnafu)?;
    let mut offset = 0;
    let left_map = variable(kernel, base, &mut offset, left_map_ty)?;
    let right_map = variable(kernel, base, &mut offset, right_map_ty)?;
    let value = variable(kernel, base, &mut offset, coproduct.ty)?;
    let candidate = variable(kernel, base, &mut offset, codomain)?;
    let left_value = variable(kernel, base, &mut offset, coproduct.left)?;
    let left_result = kernel.app(left_map, left_value).context(KernelSnafu)?;
    let left_equality = kernel
        .eq(coproduct.bool_ty, candidate, left_result)
        .context(KernelSnafu)?;
    let left_predicate = kernel
        .lam_at(coproduct.left_predicate_ty, left_value, left_equality)
        .context(KernelSnafu)?;
    let right_value = variable(kernel, base, &mut offset, coproduct.right)?;
    let right_result = kernel.app(right_map, right_value).context(KernelSnafu)?;
    let right_equality = kernel
        .eq(coproduct.bool_ty, candidate, right_result)
        .context(KernelSnafu)?;
    let right_predicate = kernel
        .lam_at(coproduct.right_predicate_ty, right_value, right_equality)
        .context(KernelSnafu)?;
    let represented = kernel
        .app(coproduct.subtype.rep, value)
        .context(KernelSnafu)?;
    let selects_left = kernel
        .app(represented, left_predicate)
        .context(KernelSnafu)?;
    let selects_result = kernel
        .app(selects_left, right_predicate)
        .context(KernelSnafu)?;
    let result_predicate_ty = kernel
        .ty_arr(codomain, coproduct.bool_ty)
        .context(KernelSnafu)?;
    let result_predicate = kernel
        .lam_at(result_predicate_ty, candidate, selects_result)
        .context(KernelSnafu)?;
    let chosen = kernel
        .eps(codomain, result_predicate)
        .context(KernelSnafu)?;
    let function = kernel
        .lam_at(value_map_ty, value, chosen)
        .context(KernelSnafu)?;
    let function = kernel
        .lam_at(right_tail, right_map, function)
        .context(KernelSnafu)?;
    let function = kernel
        .lam_at(function_ty, left_map, function)
        .context(KernelSnafu)?;
    Ok(CoproductEliminator {
        codomain,
        left_map_ty,
        right_map_ty,
        value_map_ty,
        function_ty,
        function,
    })
}

fn prove_exhaustiveness_inner(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
) -> Result<CoproductExhaustiveness, CoproductError> {
    let inhabited = prove_image_inhabited(kernel, coproduct)?;
    let rep_guarded_theorem =
        coproduct
            .subtype
            .rep_guarded_theorem
            .ok_or(CoproductError::WrongForm {
                expected: "a proved guarded-subtype representation guard",
            })?;
    let mut references = coproduct_references(coproduct, coproduct.ty);
    references.extend([inhabited.proposition, coproduct.subtype.rep_guarded]);
    let base = kernel.fresh_name(&references).context(KernelSnafu)?;
    let value = kernel.tm_fv(base, coproduct.ty).context(KernelSnafu)?;
    let guarded = forall_elim(kernel, rep_guarded_theorem, value).context(ForallSnafu)?;
    let [holds_representation, empty_fallback] = exact_op2(kernel, guarded.proposition, Op2::Or)?;

    let image_branch = kernel
        .identity(positive(holds_representation))
        .context(KernelSnafu)?;
    let empty_branch = kernel
        .copy_theorem(inhabited.theorem)
        .context(KernelSnafu)?;
    kernel
        .not_left(empty_branch, positive(inhabited.proposition))
        .context(KernelSnafu)?;
    let [fallback_inhabited] = exact_children(kernel, empty_fallback, Tag::Tm(TmTag::Op1))?;
    let inhabited_same = join_alpha_equivalent(kernel, inhabited.proposition, fallback_inhabited)
        .context(SyntaxSnafu)?;
    let inhabited_same = kernel
        .syn_refine(None, inhabited_same, SynRel::Conv)
        .context(KernelSnafu)?;
    kernel.union_syn_fact(inhabited_same).context(KernelSnafu)?;
    kernel
        .convert_theorem(empty_branch, inhabited.proposition, fallback_inhabited)
        .context(KernelSnafu)?;
    let empty_branch = kernel
        .fold_premise(empty_branch, positive(empty_fallback))
        .context(KernelSnafu)?;
    kernel
        .weaken(empty_branch, &[], &[positive(holds_representation)])
        .context(KernelSnafu)?;
    let guarded_elimination = kernel
        .or_left(image_branch, empty_branch, positive(guarded.proposition))
        .context(KernelSnafu)?;
    kernel
        .contract_theorem(guarded_elimination)
        .context(KernelSnafu)?;
    let represented_image = kernel
        .cut(
            guarded.theorem,
            guarded_elimination,
            positive(guarded.proposition),
        )
        .context(KernelSnafu)?;

    let universal = kernel
        .forall_intro(represented_image, value)
        .context(KernelSnafu)?;
    Ok(CoproductExhaustiveness {
        inhabited: inhabited.proposition,
        inhabited_theorem: inhabited.theorem,
        image_of_rep: universal.universal,
        theorem: universal.theorem,
    })
}

fn prove_image_inhabited(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
) -> Result<CoproductComputation, CoproductError> {
    let references = coproduct_references(coproduct, coproduct.carrier);
    let base = kernel.fresh_name(&references).context(KernelSnafu)?;
    let left_value = kernel.tm_fv(base, coproduct.left).context(KernelSnafu)?;
    let truth = kernel.bool(coproduct.bool_ty, true).context(KernelSnafu)?;
    let left_choice_predicate = kernel.lam(left_value, truth).context(KernelSnafu)?;
    let chosen_left = kernel
        .eps(coproduct.left, left_choice_predicate)
        .context(KernelSnafu)?;
    let church_value = kernel
        .app(coproduct.left_church, chosen_left)
        .context(KernelSnafu)?;
    let holds = kernel
        .app(coproduct.predicate, church_value)
        .context(KernelSnafu)?;
    let (predicate_application, image, predicate_beta) =
        beta_apply(kernel, coproduct.predicate, church_value)?;
    let holds_same = join_same_syntax(kernel, holds, predicate_application).context(SyntaxSnafu)?;
    let holds_same = kernel
        .syn_refine(None, holds_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let holds_reduction = kernel
        .syn_trans(None, holds_same, predicate_beta)
        .context(KernelSnafu)?;
    kernel
        .union_syn_fact(holds_reduction)
        .context(KernelSnafu)?;
    let image_proof = prove_injection_image(kernel, coproduct, image, chosen_left, true)?;
    kernel
        .convert_conclusions(image_proof.theorem, image, holds)
        .context(KernelSnafu)?;

    let carrier_name = base.checked_add(1).ok_or(CoproductError::NameExhausted)?;
    let carrier_value = kernel
        .tm_fv(carrier_name, coproduct.carrier)
        .context(KernelSnafu)?;
    let carrier_holds = kernel
        .app(coproduct.predicate, carrier_value)
        .context(KernelSnafu)?;
    let inhabited = kernel
        .exists_tm(carrier_value, carrier_holds)
        .context(KernelSnafu)?;
    let [existential_predicate, _existential_witness] =
        exact_children(kernel, inhabited, Tag::Tm(TmTag::App))?;
    let (witness_application, witness_holds, witness_beta) =
        beta_apply(kernel, existential_predicate, church_value)?;
    kernel.union_syn_fact(witness_beta).context(KernelSnafu)?;
    let holds_conversion = join_same_syntax(kernel, witness_holds, holds).context(SyntaxSnafu)?;
    let holds_conversion = kernel
        .syn_refine(None, holds_conversion, SynRel::Conv)
        .context(KernelSnafu)?;
    let witness_reduction = kernel
        .syn_trans(None, witness_beta, holds_conversion)
        .context(KernelSnafu)?;
    kernel
        .union_syn_fact(witness_reduction)
        .context(KernelSnafu)?;
    kernel
        .convert_conclusions(image_proof.theorem, holds, witness_application)
        .context(KernelSnafu)?;
    let theorem = kernel
        .choice_intro_at(image_proof.theorem, inhabited)
        .context(KernelSnafu)?;
    Ok(CoproductComputation {
        proposition: inhabited,
        theorem,
    })
}

fn specialize_exhaustiveness(
    kernel: &mut Kernel,
    exhaustiveness: CoproductExhaustiveness,
    value: Ref,
) -> Result<CoproductCases, CoproductError> {
    let specialized = forall_elim(kernel, exhaustiveness.theorem, value).context(ForallSnafu)?;
    let [predicate, represented] =
        exact_children(kernel, specialized.proposition, Tag::Tm(TmTag::App))?;
    let (predicate_application, disjunction, predicate_beta) =
        beta_apply(kernel, predicate, represented)?;
    let same_application = join_same_syntax(kernel, specialized.proposition, predicate_application)
        .context(SyntaxSnafu)?;
    let same_application = kernel
        .syn_refine(None, same_application, SynRel::Conv)
        .context(KernelSnafu)?;
    let reduction = kernel
        .syn_trans(None, same_application, predicate_beta)
        .context(KernelSnafu)?;
    kernel.union_syn_fact(reduction).context(KernelSnafu)?;
    kernel
        .convert_conclusions(specialized.theorem, specialized.proposition, disjunction)
        .context(KernelSnafu)?;
    let [left, right] = exact_op2(kernel, disjunction, Op2::Or)?;
    Ok(CoproductCases {
        value,
        left,
        right,
        disjunction,
        theorem: specialized.theorem,
    })
}

fn open_case_branch(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
    value: Ref,
    existential: Ref,
    is_left: bool,
) -> Result<CoproductBranch, CoproductError> {
    let opened = open_exists(kernel, existential).context(ExistsSnafu)?;
    let [carrier, represented, church_value] =
        exact_children(kernel, opened.body, Tag::Tm(TmTag::Eq))?;
    join_same_syntax(kernel, carrier, coproduct.carrier).context(SyntaxSnafu)?;

    let represented_expected = kernel
        .app(coproduct.subtype.rep, value)
        .context(KernelSnafu)?;
    join_same_syntax(kernel, represented, represented_expected).context(SyntaxSnafu)?;
    let church = if is_left {
        coproduct.left_church
    } else {
        coproduct.right_church
    };
    let church_expected = kernel.app(church, opened.witness).context(KernelSnafu)?;
    join_same_syntax(kernel, church_value, church_expected).context(SyntaxSnafu)?;

    let image_theorem = kernel
        .identity(positive(opened.body))
        .context(KernelSnafu)?;
    let lifted = kernel
        .ap_term(image_theorem, coproduct.subtype.abs)
        .context(KernelSnafu)?;
    let abs_rep = coproduct
        .subtype
        .abs_rep_theorem
        .ok_or(CoproductError::WrongForm {
            expected: "a proved subtype abstraction-representation law",
        })?;
    let round_trip = forall_elim(kernel, abs_rep, value).context(ForallSnafu)?;
    let value_to_rep =
        equality_symmetry(kernel, coproduct.bool_ty, round_trip.theorem).context(EqualitySnafu)?;
    let value_to_church = equality_transitivity(
        kernel,
        coproduct.bool_ty,
        value_to_rep.theorem,
        lifted.theorem,
    )
    .context(EqualitySnafu)?;

    let injection = if is_left {
        coproduct.inl
    } else {
        coproduct.inr
    };
    let (injected, abstracted_church, injection_beta) =
        beta_apply(kernel, injection, opened.witness)?;
    let existing_children =
        exact_children::<3>(kernel, value_to_church.equality, Tag::Tm(TmTag::Eq))?;
    let target = kernel
        .eq_at(coproduct.bool_ty, coproduct.ty, value, injected)
        .context(KernelSnafu)?;
    let target_children = exact_children::<3>(kernel, target, Tag::Tm(TmTag::Eq))?;
    let domain_fact =
        join_same_syntax(kernel, existing_children[0], target_children[0]).context(SyntaxSnafu)?;
    let left_fact =
        join_same_syntax(kernel, existing_children[1], target_children[1]).context(SyntaxSnafu)?;
    let same_abstracted =
        join_same_syntax(kernel, existing_children[2], abstracted_church).context(SyntaxSnafu)?;
    let same_abstracted = kernel
        .syn_refine(None, same_abstracted, SynRel::Conv)
        .context(KernelSnafu)?;
    let injection_expansion = kernel.syn_symm(None, injection_beta).context(KernelSnafu)?;
    let right_fact = kernel
        .syn_trans(None, same_abstracted, injection_expansion)
        .context(KernelSnafu)?;
    let equality_fact = kernel
        .syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            value_to_church.equality,
            target,
            &[domain_fact, left_fact, right_fact],
        )
        .context(KernelSnafu)?;
    kernel.union_syn_fact(equality_fact).context(KernelSnafu)?;
    kernel
        .convert_conclusions(value_to_church.theorem, value_to_church.equality, target)
        .context(KernelSnafu)?;
    kernel
        .convert_theorem(value_to_church.theorem, opened.body, existential)
        .context(KernelSnafu)?;
    Ok(CoproductBranch {
        witness: opened.witness,
        image_equality: opened.body,
        injected,
        value_equality: target,
        theorem: value_to_church.theorem,
    })
}

fn prove_unique_mediator_inner(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
    eliminator: CoproductEliminator,
    left_map: Ref,
    right_map: Ref,
    candidate: CoproductCandidateLaws,
) -> Result<CoproductUniqueness, CoproductError> {
    join_same_syntax(
        kernel,
        sole_conclusion(kernel, candidate.left_theorem)?,
        candidate.left,
    )
    .context(SyntaxSnafu)?;
    join_same_syntax(
        kernel,
        sole_conclusion(kernel, candidate.right_theorem)?,
        candidate.right,
    )
    .context(SyntaxSnafu)?;
    let candidate_ty = kernel.classifier(candidate.function).context(KernelSnafu)?;
    join_same_syntax(kernel, candidate_ty, eliminator.value_map_ty).context(SyntaxSnafu)?;

    let canonical_laws = prove_case_laws_inner(kernel, coproduct, eliminator, left_map, right_map)?;
    let canonical_left = kernel
        .app(eliminator.function, left_map)
        .context(KernelSnafu)?;
    let canonical = kernel.app(canonical_left, right_map).context(KernelSnafu)?;
    let base = kernel
        .fresh_name(&coproduct_references(coproduct, eliminator.codomain))
        .context(KernelSnafu)?;
    let value = kernel.tm_fv(base, coproduct.ty).context(KernelSnafu)?;
    let candidate_at = kernel.app(candidate.function, value).context(KernelSnafu)?;
    let canonical_at = kernel.app(canonical, value).context(KernelSnafu)?;
    let pointwise_instance = kernel
        .eq(coproduct.bool_ty, candidate_at, canonical_at)
        .context(KernelSnafu)?;

    let exhaustive = prove_exhaustiveness_inner(kernel, coproduct)?;
    let cases = specialize_exhaustiveness(kernel, exhaustive, value)?;
    let left_branch = open_case_branch(kernel, coproduct, value, cases.left, true)?;
    let right_branch = open_case_branch(kernel, coproduct, value, cases.right, false)?;
    let left_theorem = prove_unique_branch(
        kernel,
        coproduct,
        left_branch,
        candidate.function,
        canonical,
        candidate.left_theorem,
        canonical_laws.left_theorem,
        pointwise_instance,
    )?;
    let right_theorem = prove_unique_branch(
        kernel,
        coproduct,
        right_branch,
        candidate.function,
        canonical,
        candidate.right_theorem,
        canonical_laws.right_theorem,
        pointwise_instance,
    )?;
    kernel.contract_theorem(left_theorem).context(KernelSnafu)?;
    kernel
        .contract_theorem(right_theorem)
        .context(KernelSnafu)?;
    let branched = kernel
        .or_left(left_theorem, right_theorem, positive(cases.disjunction))
        .context(KernelSnafu)?;
    kernel.contract_theorem(branched).context(KernelSnafu)?;
    let pointwise_instance_theorem = kernel
        .cut(cases.theorem, branched, positive(cases.disjunction))
        .context(KernelSnafu)?;
    let pointwise = kernel
        .forall_intro(pointwise_instance_theorem, value)
        .context(KernelSnafu)?;
    let extensional = function_extensionality(kernel, coproduct.bool_ty, pointwise.theorem, value)
        .context(EqualitySnafu)?;
    Ok(CoproductUniqueness {
        candidate: candidate.function,
        canonical,
        pointwise: pointwise.universal,
        pointwise_theorem: pointwise.theorem,
        equality: extensional.equality,
        theorem: extensional.theorem,
    })
}

#[allow(clippy::too_many_arguments)]
fn prove_unique_branch(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
    branch: CoproductBranch,
    candidate: Ref,
    canonical: Ref,
    candidate_law: ThmId,
    canonical_law: ThmId,
    target: Ref,
) -> Result<ThmId, CoproductError> {
    let candidate_transport = kernel
        .ap_term(branch.theorem, candidate)
        .context(KernelSnafu)?;
    let candidate_computation =
        forall_elim(kernel, candidate_law, branch.witness).context(ForallSnafu)?;
    let candidate_to_result = equality_transitivity(
        kernel,
        coproduct.bool_ty,
        candidate_transport.theorem,
        candidate_computation.theorem,
    )
    .context(EqualitySnafu)?;

    let canonical_computation =
        forall_elim(kernel, canonical_law, branch.witness).context(ForallSnafu)?;
    let result_to_canonical =
        equality_symmetry(kernel, coproduct.bool_ty, canonical_computation.theorem)
            .context(EqualitySnafu)?;
    let canonical_transport = kernel
        .ap_term(branch.theorem, canonical)
        .context(KernelSnafu)?;
    let canonical_transport =
        equality_symmetry(kernel, coproduct.bool_ty, canonical_transport.theorem)
            .context(EqualitySnafu)?;
    let result_to_value = equality_transitivity(
        kernel,
        coproduct.bool_ty,
        result_to_canonical.theorem,
        canonical_transport.theorem,
    )
    .context(EqualitySnafu)?;
    let pointwise = equality_transitivity(
        kernel,
        coproduct.bool_ty,
        candidate_to_result.theorem,
        result_to_value.theorem,
    )
    .context(EqualitySnafu)?;
    let target_fact = join_same_syntax(kernel, pointwise.equality, target).context(SyntaxSnafu)?;
    kernel.union_syn_fact(target_fact).context(KernelSnafu)?;
    kernel
        .convert_conclusions(pointwise.theorem, pointwise.equality, target)
        .context(KernelSnafu)?;
    Ok(pointwise.theorem)
}

fn prove_case_laws_inner(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
    eliminator: CoproductEliminator,
    left_map: Ref,
    right_map: Ref,
) -> Result<CoproductLaws, CoproductError> {
    let mut references = coproduct_references(coproduct, eliminator.codomain);
    references.extend([left_map, right_map, eliminator.function]);
    let base = kernel.fresh_name(&references).context(KernelSnafu)?;
    let mut offset = 0;
    let left_value = variable(kernel, base, &mut offset, coproduct.left)?;
    let right_value = variable(kernel, base, &mut offset, coproduct.right)?;

    let left_instance = prove_case_inner(
        kernel, coproduct, eliminator, left_map, right_map, left_value, true,
    )?;
    let left = kernel
        .forall_intro(left_instance.theorem, left_value)
        .context(KernelSnafu)?;
    let right_instance = prove_case_inner(
        kernel,
        coproduct,
        eliminator,
        left_map,
        right_map,
        right_value,
        false,
    )?;
    let right = kernel
        .forall_intro(right_instance.theorem, right_value)
        .context(KernelSnafu)?;
    let conjunction = kernel
        .op2(Op2::And, left.universal, right.universal)
        .context(KernelSnafu)?;
    let theorem = kernel
        .and_right(left.theorem, right.theorem, positive(conjunction))
        .context(KernelSnafu)?;
    Ok(CoproductLaws {
        eliminator,
        left: left.universal,
        left_theorem: left.theorem,
        right: right.universal,
        right_theorem: right.theorem,
        conjunction,
        theorem,
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_case_inner(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
    eliminator: CoproductEliminator,
    left_map: Ref,
    right_map: Ref,
    value: Ref,
    is_left: bool,
) -> Result<CoproductComputation, CoproductError> {
    let injection = if is_left {
        coproduct.inl
    } else {
        coproduct.inr
    };
    let branch_church = if is_left {
        coproduct.left_church
    } else {
        coproduct.right_church
    };
    let injected = kernel.app(injection, value).context(KernelSnafu)?;
    let (at_left, after_left, left_beta) = beta_apply(kernel, eliminator.function, left_map)?;
    kernel.union_syn_fact(left_beta).context(KernelSnafu)?;
    let (at_right, after_right, right_beta) = beta_apply(kernel, after_left, right_map)?;
    kernel.union_syn_fact(right_beta).context(KernelSnafu)?;
    let (at_value, chosen, value_beta) = beta_apply(kernel, after_right, injected)?;
    kernel.union_syn_fact(value_beta).context(KernelSnafu)?;
    let direct_left = at_left;
    let direct_right = kernel.app(direct_left, right_map).context(KernelSnafu)?;
    let right_congr = application_congruence(kernel, direct_right, at_right, left_beta, right_map)?;
    let direct_right_beta = kernel
        .syn_trans(None, right_congr, right_beta)
        .context(KernelSnafu)?;
    kernel
        .union_syn_fact(direct_right_beta)
        .context(KernelSnafu)?;
    let direct_case = kernel.app(direct_right, injected).context(KernelSnafu)?;
    let value_congr =
        application_congruence(kernel, direct_case, at_value, direct_right_beta, injected)?;
    let direct_value_beta = kernel
        .syn_trans(None, value_congr, value_beta)
        .context(KernelSnafu)?;
    kernel
        .union_syn_fact(direct_value_beta)
        .context(KernelSnafu)?;
    let [_chosen_ty, result_predicate] = exact_children(kernel, chosen, Tag::Tm(TmTag::Eps))?;

    let branch_map = if is_left { left_map } else { right_map };
    let expected = kernel.app(branch_map, value).context(KernelSnafu)?;
    let (at_expected, selected, expected_beta) = beta_apply(kernel, result_predicate, expected)?;
    kernel.union_syn_fact(expected_beta).context(KernelSnafu)?;
    let [selected_left, right_predicate] = exact_children(kernel, selected, Tag::Tm(TmTag::App))?;
    let [represented, left_predicate] = exact_children(kernel, selected_left, Tag::Tm(TmTag::App))?;

    let branch_church_value = kernel.app(branch_church, value).context(KernelSnafu)?;
    let rep_abs_theorem = coproduct
        .subtype
        .rep_abs_theorem
        .ok_or(CoproductError::WrongForm {
            expected: "a proved guarded-subtype representation law",
        })?;
    let rep_abs = forall_elim(kernel, rep_abs_theorem, branch_church_value).context(ForallSnafu)?;
    let [guard_antecedent, _rep_abs_equality] = exact_op2(kernel, rep_abs.proposition, Op2::Imp)?;
    let guard = prove_injection_guard(kernel, coproduct, guard_antecedent, value, is_left)?;
    let rep_abs_equality =
        modus_ponens(kernel, rep_abs.theorem, guard.theorem, rep_abs.proposition)?;

    let (injected_application, abstracted, injected_beta) = beta_apply(kernel, injection, value)?;
    kernel.union_syn_fact(injected_beta).context(KernelSnafu)?;
    let represented_abstract = kernel
        .app(coproduct.subtype.rep, abstracted)
        .context(KernelSnafu)?;
    let [represented_function, represented_argument] =
        exact_children(kernel, represented, Tag::Tm(TmTag::App))?;
    let same_injected = join_same_syntax(kernel, represented_argument, injected_application)
        .context(SyntaxSnafu)?;
    let same_injected = kernel
        .syn_refine(None, same_injected, SynRel::Conv)
        .context(KernelSnafu)?;
    let argument_beta = kernel
        .syn_trans(None, same_injected, injected_beta)
        .context(KernelSnafu)?;
    let function_refl = kernel
        .syn_refl(None, SynRel::Conv, represented_function)
        .context(KernelSnafu)?;
    let represented_beta = kernel
        .syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            represented,
            represented_abstract,
            &[function_refl, argument_beta],
        )
        .context(KernelSnafu)?;
    kernel
        .union_syn_fact(represented_beta)
        .context(KernelSnafu)?;
    let represented_equality = kernel
        .eq_at(
            coproduct.bool_ty,
            coproduct.carrier,
            represented,
            branch_church_value,
        )
        .context(KernelSnafu)?;
    let law_equality = sole_conclusion(kernel, rep_abs_equality)?;
    let [law_domain, law_left, law_right] =
        exact_children(kernel, law_equality, Tag::Tm(TmTag::Eq))?;
    let same_law_left =
        join_same_syntax(kernel, represented_abstract, law_left).context(SyntaxSnafu)?;
    let same_law_left = kernel
        .syn_refine(None, same_law_left, SynRel::Conv)
        .context(KernelSnafu)?;
    let law_left_fact = kernel
        .syn_trans(None, represented_beta, same_law_left)
        .context(KernelSnafu)?;
    let domain_fact = kernel
        .syn_refl(None, SynRel::Conv, law_domain)
        .context(KernelSnafu)?;
    let right_fact =
        join_same_syntax(kernel, branch_church_value, law_right).context(SyntaxSnafu)?;
    let right_fact = kernel
        .syn_refine(None, right_fact, SynRel::Conv)
        .context(KernelSnafu)?;
    let equality_fact = kernel
        .syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            represented_equality,
            law_equality,
            &[domain_fact, law_left_fact, right_fact],
        )
        .context(KernelSnafu)?;
    kernel.union_syn_fact(equality_fact).context(KernelSnafu)?;
    kernel
        .convert_conclusions(rep_abs_equality, law_equality, represented_equality)
        .context(KernelSnafu)?;

    let selected_left_equality = kernel
        .ap_thm(rep_abs_equality, left_predicate)
        .context(KernelSnafu)?;
    let selected_equality = kernel
        .ap_thm(selected_left_equality.theorem, right_predicate)
        .context(KernelSnafu)?;
    let selected_symmetry = equality_symmetry(kernel, coproduct.bool_ty, selected_equality.theorem)
        .context(EqualitySnafu)?;

    let (reflexive_equality, selected_reduction) = reduce_branch_selection(
        kernel,
        selected_symmetry.left,
        branch_church,
        value,
        left_predicate,
        right_predicate,
        is_left,
    )?;
    let reflexive = kernel
        .refl(coproduct.bool_ty, expected)
        .context(KernelSnafu)?;
    let [predicate_domain, predicate_left, predicate_right] =
        exact_children(kernel, reflexive_equality, Tag::Tm(TmTag::Eq))?;
    let [reflexive_domain, reflexive_left, reflexive_right] =
        exact_children(kernel, reflexive.equality, Tag::Tm(TmTag::Eq))?;
    let domain_same =
        join_same_syntax(kernel, predicate_domain, reflexive_domain).context(SyntaxSnafu)?;
    let domain_same = kernel
        .syn_refine(None, domain_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let left_same =
        join_same_syntax(kernel, predicate_left, reflexive_left).context(SyntaxSnafu)?;
    let left_same = kernel
        .syn_refine(None, left_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let right_same =
        join_same_syntax(kernel, predicate_right, reflexive_right).context(SyntaxSnafu)?;
    let right_same = kernel
        .syn_refine(None, right_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let predicate_to_reflexive = kernel
        .syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            reflexive_equality,
            reflexive.equality,
            &[domain_same, left_same, right_same],
        )
        .context(KernelSnafu)?;
    let selected_reduction = kernel
        .syn_trans(None, selected_reduction, predicate_to_reflexive)
        .context(KernelSnafu)?;
    kernel
        .union_syn_fact(selected_reduction)
        .context(KernelSnafu)?;
    kernel
        .convert_conclusions(
            reflexive.theorem,
            reflexive.equality,
            selected_symmetry.left,
        )
        .context(KernelSnafu)?;
    let selected_theorem = kernel
        .eq_mp(selected_symmetry.theorem, reflexive.theorem)
        .context(KernelSnafu)?;
    let [selected_right_function, selected_right_argument] =
        exact_children(kernel, selected_symmetry.right, Tag::Tm(TmTag::App))?;
    let [selected_right_represented, selected_right_left] =
        exact_children(kernel, selected_right_function, Tag::Tm(TmTag::App))?;
    let represented_reduction =
        join_same_syntax(kernel, selected_right_represented, represented).context(SyntaxSnafu)?;
    let represented_reduction = kernel
        .syn_refine(None, represented_reduction, SynRel::Conv)
        .context(KernelSnafu)?;
    let selected_left_same =
        join_same_syntax(kernel, selected_right_left, left_predicate).context(SyntaxSnafu)?;
    let selected_left_same = kernel
        .syn_refine(None, selected_left_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let selected_function_reduction = application_congruence_with(
        kernel,
        selected_right_function,
        selected_left,
        represented_reduction,
        selected_left_same,
    )?;
    let selected_right_same =
        join_same_syntax(kernel, selected_right_argument, right_predicate).context(SyntaxSnafu)?;
    let selected_right_same = kernel
        .syn_refine(None, selected_right_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let selected_reduction = application_congruence_with(
        kernel,
        selected_symmetry.right,
        selected,
        selected_function_reduction,
        selected_right_same,
    )?;
    kernel
        .union_syn_fact(selected_reduction)
        .context(KernelSnafu)?;
    kernel
        .convert_conclusions(selected_theorem, selected_symmetry.right, selected)
        .context(KernelSnafu)?;
    kernel
        .convert_conclusions(selected_theorem, selected, at_expected)
        .context(KernelSnafu)?;

    let at_choice = kernel.app(result_predicate, chosen).context(KernelSnafu)?;
    let choice_theorem = kernel
        .choice_intro_at(selected_theorem, at_choice)
        .context(KernelSnafu)?;
    let (choice_application, choice_selected, choice_beta) =
        beta_apply(kernel, result_predicate, chosen)?;
    let same_choice_application =
        join_same_syntax(kernel, at_choice, choice_application).context(SyntaxSnafu)?;
    let same_choice_application = kernel
        .syn_refine(None, same_choice_application, SynRel::Conv)
        .context(KernelSnafu)?;
    let choice_reduction = kernel
        .syn_trans(None, same_choice_application, choice_beta)
        .context(KernelSnafu)?;
    kernel
        .union_syn_fact(choice_reduction)
        .context(KernelSnafu)?;
    kernel
        .convert_conclusions(choice_theorem, at_choice, choice_selected)
        .context(KernelSnafu)?;
    let [choice_selected_left, choice_right_predicate] =
        exact_children(kernel, choice_selected, Tag::Tm(TmTag::App))?;
    let [_choice_represented, choice_left_predicate] =
        exact_children(kernel, choice_selected_left, Tag::Tm(TmTag::App))?;
    let choice_left_equality = kernel
        .ap_thm(rep_abs_equality, choice_left_predicate)
        .context(KernelSnafu)?;
    let choice_equality = kernel
        .ap_thm(choice_left_equality.theorem, choice_right_predicate)
        .context(KernelSnafu)?;
    let choice_selected_same =
        join_same_syntax(kernel, choice_selected, choice_equality.left).context(SyntaxSnafu)?;
    let choice_selected_same = kernel
        .syn_refine(None, choice_selected_same, SynRel::Conv)
        .context(KernelSnafu)?;
    kernel
        .union_syn_fact(choice_selected_same)
        .context(KernelSnafu)?;
    kernel
        .convert_conclusions(choice_theorem, choice_selected, choice_equality.left)
        .context(KernelSnafu)?;
    let choice_theorem = kernel
        .eq_mp(choice_equality.theorem, choice_theorem)
        .context(KernelSnafu)?;

    let (choice_result_equality, choice_church_reduction) = reduce_branch_selection(
        kernel,
        choice_equality.right,
        branch_church,
        value,
        choice_left_predicate,
        choice_right_predicate,
        is_left,
    )?;
    kernel
        .union_syn_fact(choice_church_reduction)
        .context(KernelSnafu)?;
    kernel
        .convert_conclusions(
            choice_theorem,
            choice_equality.right,
            choice_result_equality,
        )
        .context(KernelSnafu)?;
    let proposition = kernel
        .eq(coproduct.bool_ty, direct_case, expected)
        .context(KernelSnafu)?;
    let [proposition_domain, proposition_left, proposition_right] =
        exact_children(kernel, proposition, Tag::Tm(TmTag::Eq))?;
    let [choice_domain, choice_left, choice_right] =
        exact_children(kernel, choice_result_equality, Tag::Tm(TmTag::Eq))?;
    let proposition_domain_same =
        join_same_syntax(kernel, proposition_domain, choice_domain).context(SyntaxSnafu)?;
    let proposition_domain_same = kernel
        .syn_refine(None, proposition_domain_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let direct_case_same =
        join_same_syntax(kernel, proposition_left, direct_case).context(SyntaxSnafu)?;
    let direct_case_same = kernel
        .syn_refine(None, direct_case_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let proposition_left_reduction = kernel
        .syn_trans(None, direct_case_same, direct_value_beta)
        .context(KernelSnafu)?;
    let chosen_same = join_same_syntax(kernel, chosen, choice_left).context(SyntaxSnafu)?;
    let chosen_same = kernel
        .syn_refine(None, chosen_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let proposition_left_reduction = kernel
        .syn_trans(None, proposition_left_reduction, chosen_same)
        .context(KernelSnafu)?;
    let proposition_right_same =
        join_same_syntax(kernel, proposition_right, choice_right).context(SyntaxSnafu)?;
    let proposition_right_same = kernel
        .syn_refine(None, proposition_right_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let proposition_reduction = kernel
        .syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            proposition,
            choice_result_equality,
            &[
                proposition_domain_same,
                proposition_left_reduction,
                proposition_right_same,
            ],
        )
        .context(KernelSnafu)?;
    kernel
        .union_syn_fact(proposition_reduction)
        .context(KernelSnafu)?;
    kernel
        .convert_conclusions(choice_theorem, choice_result_equality, proposition)
        .context(KernelSnafu)?;
    Ok(CoproductComputation {
        proposition,
        theorem: choice_theorem,
    })
}

#[allow(clippy::too_many_arguments)]
fn reduce_branch_selection(
    kernel: &mut Kernel,
    selection: Ref,
    branch_church: Ref,
    value: Ref,
    left_predicate: Ref,
    right_predicate: Ref,
    is_left: bool,
) -> Result<(Ref, SynFactId), CoproductError> {
    let [selection_function, selection_right] =
        exact_children(kernel, selection, Tag::Tm(TmTag::App))?;
    let [selection_church, selection_left] =
        exact_children(kernel, selection_function, Tag::Tm(TmTag::App))?;

    let (church_application, church_body, church_beta) = beta_apply(kernel, branch_church, value)?;
    let church_same =
        join_same_syntax(kernel, selection_church, church_application).context(SyntaxSnafu)?;
    let church_same = kernel
        .syn_refine(None, church_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let church_reduction = kernel
        .syn_trans(None, church_same, church_beta)
        .context(KernelSnafu)?;

    let left_same =
        join_same_syntax(kernel, selection_left, left_predicate).context(SyntaxSnafu)?;
    let left_same = kernel
        .syn_refine(None, left_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let reduced_function = kernel
        .app(church_body, left_predicate)
        .context(KernelSnafu)?;
    let function_reduction = application_congruence_with(
        kernel,
        selection_function,
        reduced_function,
        church_reduction,
        left_same,
    )?;
    let (left_application, church_tail, left_beta) =
        beta_apply(kernel, church_body, left_predicate)?;
    let left_application_same =
        join_same_syntax(kernel, reduced_function, left_application).context(SyntaxSnafu)?;
    let left_application_same = kernel
        .syn_refine(None, left_application_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let left_reduction = kernel
        .syn_trans(None, left_application_same, left_beta)
        .context(KernelSnafu)?;
    let function_reduction = kernel
        .syn_trans(None, function_reduction, left_reduction)
        .context(KernelSnafu)?;

    let right_same =
        join_same_syntax(kernel, selection_right, right_predicate).context(SyntaxSnafu)?;
    let right_same = kernel
        .syn_refine(None, right_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let reduced_selection = kernel
        .app(church_tail, right_predicate)
        .context(KernelSnafu)?;
    let selection_reduction = application_congruence_with(
        kernel,
        selection,
        reduced_selection,
        function_reduction,
        right_same,
    )?;
    let (right_application, selected_at_value, right_beta) =
        beta_apply(kernel, church_tail, right_predicate)?;
    let right_application_same =
        join_same_syntax(kernel, reduced_selection, right_application).context(SyntaxSnafu)?;
    let right_application_same = kernel
        .syn_refine(None, right_application_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let right_reduction = kernel
        .syn_trans(None, right_application_same, right_beta)
        .context(KernelSnafu)?;
    let selection_reduction = kernel
        .syn_trans(None, selection_reduction, right_reduction)
        .context(KernelSnafu)?;

    let selected_predicate = if is_left {
        left_predicate
    } else {
        right_predicate
    };
    let (predicate_application, result, predicate_beta) =
        beta_apply(kernel, selected_predicate, value)?;
    let predicate_same =
        join_same_syntax(kernel, selected_at_value, predicate_application).context(SyntaxSnafu)?;
    let predicate_same = kernel
        .syn_refine(None, predicate_same, SynRel::Conv)
        .context(KernelSnafu)?;
    let predicate_reduction = kernel
        .syn_trans(None, predicate_same, predicate_beta)
        .context(KernelSnafu)?;
    let reduction = kernel
        .syn_trans(None, selection_reduction, predicate_reduction)
        .context(KernelSnafu)?;
    Ok((result, reduction))
}

fn prove_injection_guard(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
    expanded: Ref,
    value: Ref,
    is_left: bool,
) -> Result<CoproductComputation, CoproductError> {
    let [holds_value, empty_fallback] = exact_op2(kernel, expanded, Op2::Or)?;
    let [predicate, church_value] = exact_children(kernel, holds_value, Tag::Tm(TmTag::App))?;
    let (predicate_application, image, predicate_beta) =
        beta_apply(kernel, predicate, church_value)?;
    let same_application =
        join_same_syntax(kernel, holds_value, predicate_application).context(SyntaxSnafu)?;
    let same_application = kernel
        .syn_refine(None, same_application, SynRel::Conv)
        .context(KernelSnafu)?;
    let holds_beta = kernel
        .syn_trans(None, same_application, predicate_beta)
        .context(KernelSnafu)?;
    kernel.union_syn_fact(predicate_beta).context(KernelSnafu)?;
    kernel.union_syn_fact(holds_beta).context(KernelSnafu)?;
    let image_proof = prove_injection_image(kernel, coproduct, image, value, is_left)?;
    kernel
        .convert_conclusions(image_proof.theorem, image, holds_value)
        .context(KernelSnafu)?;
    kernel
        .weaken(image_proof.theorem, &[], &[positive(empty_fallback)])
        .context(KernelSnafu)?;
    let guard_theorem = kernel
        .or_right(image_proof.theorem, positive(expanded))
        .context(KernelSnafu)?;
    Ok(CoproductComputation {
        proposition: expanded,
        theorem: guard_theorem,
    })
}

fn prove_injection_image(
    kernel: &mut Kernel,
    coproduct: &Coproduct,
    image: Ref,
    value: Ref,
    is_left: bool,
) -> Result<CoproductComputation, CoproductError> {
    let [left_exists, right_exists] = exact_op2(kernel, image, Op2::Or)?;
    let selected_exists = if is_left { left_exists } else { right_exists };
    let other_exists = if is_left { right_exists } else { left_exists };
    let [selected_predicate, _choice] =
        exact_children(kernel, selected_exists, Tag::Tm(TmTag::App))?;
    let (witness, witness_equality, witness_beta) = beta_apply(kernel, selected_predicate, value)?;
    kernel.union_syn_fact(witness_beta).context(KernelSnafu)?;
    let [domain, witness_left, witness_right] =
        exact_children(kernel, witness_equality, Tag::Tm(TmTag::Eq))?;
    let reflexive = kernel
        .refl(coproduct.bool_ty, witness_left)
        .context(KernelSnafu)?;
    let right_fact = join_same_syntax(kernel, witness_left, witness_right).context(SyntaxSnafu)?;
    let domain_fact = kernel
        .syn_refl(None, SynRel::Syn, domain)
        .context(KernelSnafu)?;
    let left_fact = kernel
        .syn_refl(None, SynRel::Syn, witness_left)
        .context(KernelSnafu)?;
    let equality_fact = kernel
        .syn_congr(
            None,
            SynRel::Syn,
            None,
            None,
            reflexive.equality,
            witness_equality,
            &[domain_fact, left_fact, right_fact],
        )
        .context(KernelSnafu)?;
    kernel.union_syn_fact(equality_fact).context(KernelSnafu)?;
    kernel
        .convert_conclusions(reflexive.theorem, reflexive.equality, witness)
        .context(KernelSnafu)?;
    let selected = kernel
        .choice_intro_at(reflexive.theorem, selected_exists)
        .context(KernelSnafu)?;
    kernel
        .weaken(selected, &[], &[positive(other_exists)])
        .context(KernelSnafu)?;
    let image_theorem = kernel
        .or_right(selected, positive(image))
        .context(KernelSnafu)?;
    Ok(CoproductComputation {
        proposition: image,
        theorem: image_theorem,
    })
}

fn beta_apply(
    kernel: &mut Kernel,
    function: Ref,
    argument: Ref,
) -> Result<(Ref, Ref, SynFactId), CoproductError> {
    let application = kernel.app(function, argument).context(KernelSnafu)?;
    let [binder, body] = exact_children(kernel, function, Tag::Tm(TmTag::Lam))?;
    let substitution = substitute(kernel, binder, argument, body).context(SubstitutionSnafu)?;
    let beta = kernel
        .tm_beta_fact(None, application, substitution.fact)
        .context(KernelSnafu)?;
    Ok((application, substitution.output, beta))
}

fn application_congruence(
    kernel: &mut Kernel,
    left: Ref,
    right: Ref,
    function: SynFactId,
    argument: Ref,
) -> Result<SynFactId, CoproductError> {
    let argument = kernel
        .syn_refl(None, SynRel::Conv, argument)
        .context(KernelSnafu)?;
    application_congruence_with(kernel, left, right, function, argument)
}

fn application_congruence_with(
    kernel: &mut Kernel,
    left: Ref,
    right: Ref,
    function: SynFactId,
    argument: SynFactId,
) -> Result<SynFactId, CoproductError> {
    kernel
        .syn_congr(
            None,
            SynRel::Conv,
            None,
            None,
            left,
            right,
            &[function, argument],
        )
        .context(KernelSnafu)
}

fn modus_ponens(
    kernel: &mut Kernel,
    implication_theorem: ThmId,
    antecedent_theorem: ThmId,
    implication: Ref,
) -> Result<ThmId, CoproductError> {
    let [_antecedent, consequent] = exact_op2(kernel, implication, Op2::Imp)?;
    let consequence = kernel.identity(positive(consequent)).context(KernelSnafu)?;
    let use_implication = kernel
        .imp_left(antecedent_theorem, consequence, positive(implication))
        .context(KernelSnafu)?;
    kernel
        .cut(implication_theorem, use_implication, positive(implication))
        .context(KernelSnafu)
}

fn sole_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, CoproductError> {
    let theorem = kernel.thm().get(theorem).ok_or(CoproductError::WrongForm {
        expected: "a resident coproduct theorem",
    })?;
    let mut rows = theorem.rhs.rows();
    let row = rows.next().ok_or(CoproductError::WrongForm {
        expected: "one positive coproduct theorem conclusion",
    })?;
    if rows.next().is_some() || row.len() != 1 || !row[0].is_positive() {
        return Err(CoproductError::WrongForm {
            expected: "one positive coproduct theorem conclusion",
        });
    }
    let reference = i32::try_from(row[0].magnitude()).map_err(|_| CoproductError::WrongForm {
        expected: "an in-range coproduct proposition",
    })?;
    Ref::new(reference).ok_or(CoproductError::WrongForm {
        expected: "a nonzero coproduct proposition",
    })
}

fn exact_op2(kernel: &Kernel, reference: Ref, op: Op2) -> Result<[Ref; 2], CoproductError> {
    if kernel.arena().op2(reference) != Some(op) {
        return Err(CoproductError::WrongForm {
            expected: "a compact logical binary opcode",
        });
    }
    exact_children(kernel, reference, Tag::Tm(TmTag::Op2))
}

fn exact_children<const N: usize>(
    kernel: &Kernel,
    reference: Ref,
    tag: Tag,
) -> Result<[Ref; N], CoproductError> {
    if kernel.arena().tag(reference) != Some(tag) {
        return Err(CoproductError::WrongForm {
            expected: "a checked coproduct syntax node",
        });
    }
    kernel
        .arena()
        .children(reference)
        .ok_or(CoproductError::WrongForm {
            expected: "resident coproduct syntax children",
        })?
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| CoproductError::WrongForm {
            expected: "the exact coproduct syntax arity",
        })
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

fn coproduct_references(coproduct: &Coproduct, codomain: Ref) -> Vec<Ref> {
    vec![
        coproduct.bool_ty,
        coproduct.left,
        coproduct.right,
        coproduct.carrier,
        coproduct.left_church,
        coproduct.right_church,
        coproduct.predicate,
        coproduct.ty,
        coproduct.inl,
        coproduct.inr,
        codomain,
    ]
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
