//! Language-independent userspace interfaces for coproduct construction.

use covalence_lib_error::snafu::{ResultExt, Snafu};
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, Sort, SynFactId, SynRel, Tag, ThmId, TmTag, TyTag, builtin::Op2,
};

use crate::{
    EqualityError, ForallError, ModelError, Subtype, SubtypeError, SubtypeExt, SyntaxError,
    equality_symmetry, forall_elim, join_same_syntax, substitute,
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
    kernel
        .convert_conclusions(image_theorem, image, holds_value)
        .context(KernelSnafu)?;
    kernel
        .weaken(image_theorem, &[], &[positive(empty_fallback)])
        .context(KernelSnafu)?;
    let guard_theorem = kernel
        .or_right(image_theorem, positive(expanded))
        .context(KernelSnafu)?;
    Ok(CoproductComputation {
        proposition: expanded,
        theorem: guard_theorem,
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
