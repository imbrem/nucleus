//! Natural-number syntax carved from the chosen infinite carrier.
//!
//! This is the first userspace layer of the standard HOL construction.  It
//! chooses the carrier supplied by `ax.inf`, defines the induction-closure
//! predicate on that carrier, and uses the guarded subtype package to carve
//! out the naturals.  No constructor here is trusted: authority remains in
//! the two small kernel capabilities consumed by [`InfinityExt`] and
//! [`SubtypeExt`].

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    AX_INF, AX_SUB, Kernel, KernelError, Lit, Ref, SynRel, Tag, ThmId, TmTag, builtin::Op2,
};

use crate::{
    EqualityError, ForallError, Infinity, InfinityError, InfinityExt, ModelError, ProvedEquality,
    Subtype, SubtypeError, SubtypeExt, SyntaxError, equality_symmetry, equality_transitivity,
    forall_elim, join_same_syntax, substitute,
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
    /// The carrier-level proposition `member ind.zero`.
    pub zero_member: Ref,
    /// Exact theorem `⊢ member ind.zero`, derived entirely in userspace.
    pub zero_member_theorem: ThmId,
    /// The existential encoded by the subtype guard: `∃a. member a`.
    pub member_inhabited: Ref,
    /// Exact theorem of [`member_inhabited`](Self::member_inhabited).
    pub member_inhabited_theorem: ThmId,
    /// `∀n : nat. member (rep n)`.
    pub rep_member: Ref,
    /// Exact theorem of [`rep_member`](Self::rep_member).
    pub rep_member_theorem: ThmId,
    /// `∀a : ind. member a → member (ind.succ a)`.
    pub member_succ: Ref,
    /// Exact theorem of [`member_succ`](Self::member_succ).
    pub member_succ_theorem: ThmId,
    /// Successor on the subtype: `λn. abs (ind.succ (rep n))`.
    pub succ: Ref,
    /// The standard induction-principle statement over [`ty`](Self::ty).
    pub induction: Ref,
    /// Exact theorem `⊢ nat.induction`.
    pub induction_theorem: ThmId,
    /// `∀m n : nat. nat.succ m = nat.succ n → m = n`.
    pub succ_injective: Ref,
    /// Exact theorem `⊢ nat.succ.injective`.
    pub succ_injective_theorem: ThmId,
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
            ("nat.zero_member", self.zero_member),
            ("nat.member_inhabited", self.member_inhabited),
            ("nat.rep_member", self.rep_member),
            ("nat.member_succ", self.member_succ),
            ("nat.succ", self.succ),
            ("nat.induction", self.induction),
            ("nat.succ.injective", self.succ_injective),
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
    /// A compiled or derived schema did not have the expected logical shape.
    #[snafu(display("natural-number proof expected {expected}"))]
    WrongForm {
        /// Expected checked syntax shape.
        expected: &'static str,
    },
    /// Universal specialization needed by the proof layer failed.
    #[snafu(display("natural-number universal specialization failed: {source}"))]
    Forall {
        /// Underlying checked derived failure.
        source: ForallError,
    },
    /// Structural syntax certification failed.
    #[snafu(display("natural-number syntax certification failed: {source}"))]
    Syntax {
        /// Underlying userspace certification failure.
        source: SyntaxError,
    },
    /// A derived equality rule failed.
    #[snafu(display("natural-number equality derivation failed: {source}"))]
    Equality {
        /// Underlying userspace equality failure.
        source: EqualityError,
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

impl From<ForallError> for NaturalError {
    fn from(source: ForallError) -> Self {
        Self::Forall { source }
    }
}

impl From<SyntaxError> for NaturalError {
    fn from(source: SyntaxError) -> Self {
        Self::Syntax { source }
    }
}

impl From<EqualityError> for NaturalError {
    fn from(source: EqualityError) -> Self {
        Self::Equality { source }
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
        let [zero_binder, zero_body] =
            exact_children(self, specialized.output, Tag::Tm(TmTag::Lam))?;
        let at_zero = substitute(self, zero_binder, infinity.missed, zero_body)?.output;
        // Substitution deliberately rebuilds syntax rather than hash-consing
        // it. Its expected `carrier → carrier` row can therefore be a distinct
        // reference from the chosen map's syntactically identical classifier.
        // Certify and join those rows before substituting the map itself. This
        // preserves the schema's source-independent meaning without baking
        // any knowledge of the S-expression language into the kernel.
        let [map_binder, member_body] = exact_children(self, at_zero, Tag::Tm(TmTag::Lam))?;
        let expected_map_ty = self.classifier(map_binder)?;
        let actual_map_ty = self.classifier(infinity.map)?;
        join_same_syntax(self, expected_map_ty, actual_map_ty)?;
        let member = substitute(self, map_binder, infinity.map, member_body)?.output;
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
    let (zero_member, zero_member_theorem) = prove_member_zero(kernel, member, infinity.missed)?;

    let n = kernel.tm_fv(
        kernel.fresh_name(&[subtype.sub, subtype.rep, subtype.abs])?,
        subtype.sub,
    )?;
    let represented = kernel.app(subtype.rep, n)?;
    let (member_inhabited, member_inhabited_theorem, rep_member, rep_member_theorem) =
        prove_representations_are_members(
            kernel,
            &subtype,
            infinity.missed,
            zero_member,
            zero_member_theorem,
            n,
        )?;
    let (member_succ, member_succ_theorem) =
        prove_member_successor(kernel, member, infinity.carrier, infinity.map)?;
    let next_ind = kernel.app(infinity.map, represented)?;
    let next_nat = kernel.app(subtype.abs, next_ind)?;
    let succ = kernel.lam(n, next_nat)?;
    let induction = induction_statement(kernel, bool_ty, subtype.sub, zero, succ)?;
    let induction_theorem = prove_induction(
        kernel,
        member,
        &subtype,
        infinity.map,
        zero_member,
        zero_member_theorem,
        rep_member_theorem,
        member_succ_theorem,
        succ,
        induction,
    )?;
    let (succ_injective, succ_injective_theorem) = prove_successor_injective(
        kernel,
        bool_ty,
        &infinity,
        &subtype,
        rep_member_theorem,
        member_succ_theorem,
        succ,
    )?;

    Ok(Naturals {
        infinity,
        member,
        subtype,
        ty: subtype.sub,
        zero,
        zero_member,
        zero_member_theorem,
        member_inhabited,
        member_inhabited_theorem,
        rep_member,
        rep_member_theorem,
        member_succ,
        member_succ_theorem,
        succ,
        induction,
        induction_theorem,
        succ_injective,
        succ_injective_theorem,
    })
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_successor_injective(
    kernel: &mut Kernel,
    bool_ty: Ref,
    infinity: &Infinity,
    subtype: &Subtype,
    rep_member_theorem: ThmId,
    member_succ_theorem: ThmId,
    successor: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let left = kernel.tm_fv(kernel.fresh_name(&[subtype.sub, successor])?, subtype.sub)?;
    let right = kernel.tm_fv(kernel.fresh_name(&[left])?, subtype.sub)?;
    let successor_left = kernel.app(successor, left)?;
    let successor_right = kernel.app(successor, right)?;
    let successor_equality = kernel.eq(bool_ty, successor_left, successor_right)?;
    let source = kernel.identity(positive(successor_equality))?;
    let represented_successors = kernel.ap_term(source, subtype.rep)?;

    let represented_left = kernel.app(subtype.rep, left)?;
    let represented_right = kernel.app(subtype.rep, right)?;
    let mapped_left = kernel.app(infinity.map, represented_left)?;
    let mapped_right = kernel.app(infinity.map, represented_right)?;
    let left_member = prove_mapped_rep_member(
        kernel,
        represented_left,
        mapped_left,
        left,
        rep_member_theorem,
        member_succ_theorem,
    )?;
    let right_member = prove_mapped_rep_member(
        kernel,
        represented_right,
        mapped_right,
        right,
        rep_member_theorem,
        member_succ_theorem,
    )?;
    let left_round_trip = prove_guarded_round_trip(kernel, subtype, mapped_left, left_member)?;
    let right_round_trip = prove_guarded_round_trip(kernel, subtype, mapped_right, right_member)?;

    let (represented_successor_left, left_expansion) = expand_represented_successor(
        kernel,
        subtype.rep,
        successor,
        left,
        represented_successors.left,
    )?;
    let (represented_successor_right, right_expansion) = expand_represented_successor(
        kernel,
        subtype.rep,
        successor,
        right,
        represented_successors.right,
    )?;
    let left_shape = join_same_syntax(kernel, left_round_trip.left, represented_successor_left)?;
    let right_shape = join_same_syntax(kernel, right_round_trip.left, represented_successor_right)?;
    let left_expansion = kernel.syn_symm(None, left_expansion)?;
    let right_expansion = kernel.syn_symm(None, right_expansion)?;
    let left_endpoint = kernel.syn_trans(None, left_shape, left_expansion)?;
    let right_endpoint = kernel.syn_trans(None, right_shape, right_expansion)?;
    let left_round_trip_theorem = kernel.copy_theorem(left_round_trip.theorem)?;
    let left_round_trip_target = kernel.eq(bool_ty, represented_successors.left, mapped_left)?;
    certify_equality_conversion(
        kernel,
        left_round_trip.equality,
        left_round_trip_target,
        left_endpoint,
    )?;
    kernel.convert_conclusions(
        left_round_trip_theorem,
        left_round_trip.equality,
        left_round_trip_target,
    )?;
    let left_round_trip = proved_equality(kernel, left_round_trip_theorem)?;
    let right_round_trip_theorem = kernel.copy_theorem(right_round_trip.theorem)?;
    let right_round_trip_target = kernel.eq(bool_ty, represented_successors.right, mapped_right)?;
    certify_equality_conversion(
        kernel,
        right_round_trip.equality,
        right_round_trip_target,
        right_endpoint,
    )?;
    kernel.convert_conclusions(
        right_round_trip_theorem,
        right_round_trip.equality,
        right_round_trip_target,
    )?;
    let right_round_trip = proved_equality(kernel, right_round_trip_theorem)?;

    let left_inverse = equality_symmetry(kernel, bool_ty, left_round_trip.theorem)?;
    let through_successors = equality_transitivity(
        kernel,
        bool_ty,
        left_inverse.theorem,
        represented_successors.theorem,
    )?;
    let mapped_equality = equality_transitivity(
        kernel,
        bool_ty,
        through_successors.theorem,
        right_round_trip.theorem,
    )?;

    let reflected_left = forall_elim(kernel, infinity.reflects_equality_theorem, represented_left)?;
    let reflected = forall_elim(kernel, reflected_left.theorem, represented_right)?;
    let [_bool_ty, images_equal, _arguments_equal] =
        exact_children(kernel, reflected.proposition, Tag::Tm(TmTag::Eq))?;
    join_same_syntax(kernel, mapped_equality.equality, images_equal)?;
    kernel.convert_conclusions(
        mapped_equality.theorem,
        mapped_equality.equality,
        images_equal,
    )?;
    let represented_equality = kernel.eq_mp(reflected.theorem, mapped_equality.theorem)?;

    let abstracted_equality = kernel.ap_term(represented_equality, subtype.abs)?;
    let left_abs_rep = forall_elim(
        kernel,
        subtype.abs_rep_theorem.ok_or(NaturalError::WrongForm {
            expected: "the proved subtype abs-rep law",
        })?,
        left,
    )?;
    let right_abs_rep = forall_elim(
        kernel,
        subtype.abs_rep_theorem.ok_or(NaturalError::WrongForm {
            expected: "the proved subtype abs-rep law",
        })?,
        right,
    )?;
    let left_abs_rep = proved_equality(kernel, left_abs_rep.theorem)?;
    let right_abs_rep = proved_equality(kernel, right_abs_rep.theorem)?;
    let abstracted_left = join_same_syntax(kernel, abstracted_equality.left, left_abs_rep.left)?;
    let abstracted_right = join_same_syntax(kernel, abstracted_equality.right, right_abs_rep.left)?;
    let abstracted_target = kernel.eq(bool_ty, left_abs_rep.left, right_abs_rep.left)?;
    certify_equality_conversion_both(
        kernel,
        abstracted_equality.equality,
        abstracted_target,
        abstracted_left,
        abstracted_right,
    )?;
    kernel.convert_conclusions(
        abstracted_equality.theorem,
        abstracted_equality.equality,
        abstracted_target,
    )?;
    let abstracted_equality = proved_equality(kernel, abstracted_equality.theorem)?;
    let left_inverse = equality_symmetry(kernel, bool_ty, left_abs_rep.theorem)?;
    let through_abstraction = equality_transitivity(
        kernel,
        bool_ty,
        left_inverse.theorem,
        abstracted_equality.theorem,
    )?;
    let natural_equality = equality_transitivity(
        kernel,
        bool_ty,
        through_abstraction.theorem,
        right_abs_rep.theorem,
    )?;

    let implication = kernel.op2(Op2::Imp, successor_equality, natural_equality.equality)?;
    let implication_theorem = kernel.imp_right(natural_equality.theorem, positive(implication))?;
    kernel.contract_theorem(implication_theorem)?;
    let inner = kernel.forall_intro(implication_theorem, right)?;
    let outer = kernel.forall_intro(inner.theorem, left)?;
    Ok((outer.universal, outer.theorem))
}

fn prove_mapped_rep_member(
    kernel: &mut Kernel,
    represented: Ref,
    mapped: Ref,
    natural: Ref,
    rep_member_theorem: ThmId,
    member_succ_theorem: ThmId,
) -> Result<ThmId, NaturalError> {
    let represented_member = forall_elim(kernel, rep_member_theorem, natural)?;
    let closure = forall_elim(kernel, member_succ_theorem, represented)?;
    let [source, target] = exact_op2(kernel, closure.proposition, Op2::Imp)?;
    join_same_syntax(kernel, represented_member.proposition, source)?;
    let represented_member_theorem = kernel.copy_theorem(represented_member.theorem)?;
    kernel.convert_conclusions(
        represented_member_theorem,
        represented_member.proposition,
        source,
    )?;
    let result = modus_ponens(
        kernel,
        closure.theorem,
        represented_member_theorem,
        closure.proposition,
    )?;
    let proposition = sole_conclusion(kernel, result)?;
    let [_predicate, target_value] = exact_children(kernel, target, Tag::Tm(TmTag::App))?;
    join_same_syntax(kernel, target_value, mapped)?;
    join_same_syntax(kernel, proposition, target)?;
    Ok(result)
}

fn prove_guarded_round_trip(
    kernel: &mut Kernel,
    subtype: &Subtype,
    value: Ref,
    member_theorem: ThmId,
) -> Result<ProvedEquality, NaturalError> {
    let specialized = forall_elim(
        kernel,
        subtype.rep_abs_theorem.ok_or(NaturalError::WrongForm {
            expected: "the proved subtype rep-abs law",
        })?,
        value,
    )?;
    let [guard, _equality] = exact_op2(kernel, specialized.proposition, Op2::Imp)?;
    let [member, empty] = exact_op2(kernel, guard, Op2::Or)?;
    let source_member = sole_conclusion(kernel, member_theorem)?;
    join_same_syntax(kernel, source_member, member)?;
    let guard_theorem = kernel.copy_theorem(member_theorem)?;
    kernel.convert_conclusions(guard_theorem, source_member, member)?;
    kernel.weaken(guard_theorem, &[], &[positive(empty)])?;
    let guard_theorem = kernel.or_right(guard_theorem, positive(guard))?;
    let equality = modus_ponens(
        kernel,
        specialized.theorem,
        guard_theorem,
        specialized.proposition,
    )?;
    proved_equality(kernel, equality)
}

fn expand_represented_successor(
    kernel: &mut Kernel,
    representation: Ref,
    successor: Ref,
    argument: Ref,
    represented_successor: Ref,
) -> Result<(Ref, covalence_logic_hol::SynFactId), NaturalError> {
    let [actual_representation, successor_application] =
        exact_children(kernel, represented_successor, Tag::Tm(TmTag::App))?;
    if actual_representation != representation {
        return Err(NaturalError::WrongForm {
            expected: "the representation of a natural successor",
        });
    }
    let [actual_successor, actual_argument] =
        exact_children(kernel, successor_application, Tag::Tm(TmTag::App))?;
    if actual_successor != successor || actual_argument != argument {
        return Err(NaturalError::WrongForm {
            expected: "the expected natural successor application",
        });
    }
    let [binder, body] = exact_children(kernel, successor, Tag::Tm(TmTag::Lam))?;
    let substitution = substitute(kernel, binder, argument, body)?;
    let beta = kernel.tm_beta_fact(None, successor_application, substitution.fact)?;
    kernel.union_syn_fact(beta)?;
    let expanded = kernel.app(representation, substitution.output)?;
    let representation_refl = kernel.syn_refl(None, SynRel::Syn, representation)?;
    let congruence = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        represented_successor,
        expanded,
        &[representation_refl, beta],
    )?;
    kernel.union_syn_fact(congruence)?;
    Ok((expanded, congruence))
}

fn certify_equality_conversion(
    kernel: &mut Kernel,
    source: Ref,
    target: Ref,
    left: covalence_logic_hol::SynFactId,
) -> Result<(), NaturalError> {
    let [_source_domain, _source_left, source_right] =
        exact_children(kernel, source, Tag::Tm(TmTag::Eq))?;
    let [_target_domain, _target_left, target_right] =
        exact_children(kernel, target, Tag::Tm(TmTag::Eq))?;
    let right = join_same_syntax(kernel, source_right, target_right)?;
    certify_equality_conversion_both(kernel, source, target, left, right)
}

fn certify_equality_conversion_both(
    kernel: &mut Kernel,
    source: Ref,
    target: Ref,
    left: covalence_logic_hol::SynFactId,
    right: covalence_logic_hol::SynFactId,
) -> Result<(), NaturalError> {
    let [source_domain, _source_left, _source_right] =
        exact_children(kernel, source, Tag::Tm(TmTag::Eq))?;
    let [target_domain, _target_left, _target_right] =
        exact_children(kernel, target, Tag::Tm(TmTag::Eq))?;
    let domain = join_same_syntax(kernel, source_domain, target_domain)?;
    let fact = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        source,
        target,
        &[domain, left, right],
    )?;
    kernel.union_syn_fact(fact)?;
    Ok(())
}

fn proved_equality(kernel: &Kernel, theorem: ThmId) -> Result<ProvedEquality, NaturalError> {
    let equality = sole_conclusion(kernel, theorem)?;
    let [_domain, left, right] = exact_children(kernel, equality, Tag::Tm(TmTag::Eq))?;
    Ok(ProvedEquality {
        left,
        right,
        equality,
        theorem,
    })
}

#[allow(clippy::too_many_arguments)]
fn prove_induction(
    kernel: &mut Kernel,
    member: Ref,
    subtype: &Subtype,
    carrier_successor: Ref,
    zero_member: Ref,
    zero_member_theorem: ThmId,
    rep_member_theorem: ThmId,
    member_succ_theorem: ThmId,
    natural_successor: Ref,
    induction: Ref,
) -> Result<ThmId, NaturalError> {
    let (predicate, principle) = universal_parts(kernel, induction)?;
    let [premises, conclusion] = exact_op2(kernel, principle, Op2::Imp)?;
    let [base, _natural_step] = exact_op2(kernel, premises, Op2::And)?;
    let (natural, at_n) = universal_parts(kernel, conclusion)?;
    let represented = kernel.app(subtype.rep, natural)?;

    // Open `member (rep n)` and instantiate its quantified predicate with
    // `λa. member a ∧ P (abs a)`.
    let represented_member =
        forall_elim(kernel, rep_member_theorem, natural).map_err(|_| NaturalError::WrongForm {
            expected: "specializable representation membership",
        })?;
    let (represented_application, represented_universal) =
        beta_application(kernel, member, represented)?;
    join_same_syntax(
        kernel,
        represented_application,
        represented_member.proposition,
    )?;
    kernel.convert_conclusions(
        represented_member.theorem,
        represented_member.proposition,
        represented_universal,
    )?;
    let (member_predicate, _member_body) = universal_parts(kernel, represented_universal)?;
    let carrier_value = kernel.tm_fv(
        kernel.fresh_name(&[predicate, member_predicate, represented])?,
        subtype.carrier,
    )?;
    let member_at_value = kernel.app(member, carrier_value)?;
    let abstracted_value = kernel.app(subtype.abs, carrier_value)?;
    let property_at_value = kernel.app(predicate, abstracted_value)?;
    let strengthened_body = kernel.op2(Op2::And, member_at_value, property_at_value)?;
    let strengthened = kernel.lam_at(
        kernel.classifier(member_predicate)?,
        carrier_value,
        strengthened_body,
    )?;
    let represented_closed = forall_elim(kernel, represented_member.theorem, strengthened)
        .map_err(|_| NaturalError::WrongForm {
            expected: "membership specialized at the strengthened predicate",
        })?;
    let [strengthened_closure, strengthened_at_rep] =
        exact_op2(kernel, represented_closed.proposition, Op2::Imp)?;
    let [strengthened_base, strengthened_step] = exact_op2(kernel, strengthened_closure, Op2::And)?;

    // Base: zero membership is already exact, while the user's base premise
    // supplies `P (abs ind.zero)`.
    let [base_function, carrier_zero] =
        exact_children(kernel, strengthened_base, Tag::Tm(TmTag::App))?;
    if base_function != strengthened {
        return Err(NaturalError::WrongForm {
            expected: "the strengthened predicate at carrier zero",
        });
    }
    let (strengthened_base_application, expanded_strengthened_base) =
        beta_application(kernel, strengthened, carrier_zero)?;
    join_same_syntax(kernel, strengthened_base_application, strengthened_base)?;
    let [target_zero_member, target_zero_property] =
        exact_op2(kernel, expanded_strengthened_base, Op2::And)?;
    join_same_syntax(kernel, zero_member, target_zero_member)?;
    let zero_membership = kernel.copy_theorem(zero_member_theorem)?;
    kernel.convert_conclusions(zero_membership, zero_member, target_zero_member)?;
    let base_property = project_and_left(kernel, premises)?;
    join_same_syntax(kernel, base, target_zero_property)?;
    kernel.convert_conclusions(base_property, base, target_zero_property)?;
    let strengthened_base_proof = kernel.and_right(
        zero_membership,
        base_property,
        positive(expanded_strengthened_base),
    )?;
    kernel.convert_conclusions(
        strengthened_base_proof,
        expanded_strengthened_base,
        strengthened_base,
    )?;

    let strengthened_step_proof = prove_strengthened_step(
        kernel,
        subtype,
        predicate,
        premises,
        member_succ_theorem,
        carrier_successor,
        natural_successor,
        strengthened,
        strengthened_step,
    )?;

    finish_induction(
        kernel,
        subtype,
        predicate,
        natural,
        at_n,
        conclusion,
        principle,
        induction,
        strengthened,
        strengthened_closure,
        strengthened_at_rep,
        represented_closed.proposition,
        represented_closed.theorem,
        strengthened_base_proof,
        strengthened_step_proof,
    )
}

#[allow(clippy::too_many_arguments)]
fn finish_induction(
    kernel: &mut Kernel,
    subtype: &Subtype,
    predicate: Ref,
    natural: Ref,
    at_n: Ref,
    conclusion: Ref,
    principle: Ref,
    induction: Ref,
    strengthened: Ref,
    strengthened_closure: Ref,
    strengthened_at_rep: Ref,
    represented_closed: Ref,
    represented_closed_theorem: ThmId,
    strengthened_base_theorem: ThmId,
    strengthened_step_theorem: ThmId,
) -> Result<ThmId, NaturalError> {
    let closure = kernel.and_right(
        strengthened_base_theorem,
        strengthened_step_theorem,
        positive(strengthened_closure),
    )?;
    kernel.contract_theorem(closure)?;
    let at_rep_theorem = modus_ponens(
        kernel,
        represented_closed_theorem,
        closure,
        represented_closed,
    )?;
    let [_rep_function, represented_argument] =
        exact_children(kernel, strengthened_at_rep, Tag::Tm(TmTag::App))?;
    let (at_rep_application, expanded_at_rep) =
        beta_application(kernel, strengthened, represented_argument)?;
    join_same_syntax(kernel, at_rep_application, strengthened_at_rep)?;
    kernel.convert_conclusions(at_rep_theorem, strengthened_at_rep, expanded_at_rep)?;
    let property_at_rep = project_and_right(kernel, expanded_at_rep)?;
    let property_at_rep = kernel.cut(at_rep_theorem, property_at_rep, positive(expanded_at_rep))?;

    let abs_rep = forall_elim(
        kernel,
        subtype.abs_rep_theorem.ok_or(NaturalError::WrongForm {
            expected: "the subtype abstraction-representation theorem",
        })?,
        natural,
    )
    .map_err(|_| NaturalError::WrongForm {
        expected: "specializable subtype abs-rep theorem",
    })?;
    let final_equality = kernel.ap_term(abs_rep.theorem, predicate)?;
    let property_at_rep_term = sole_conclusion(kernel, property_at_rep)?;
    join_same_syntax(kernel, final_equality.left, property_at_rep_term)?;
    join_same_syntax(kernel, final_equality.right, at_n)?;
    kernel.convert_conclusions(property_at_rep, property_at_rep_term, final_equality.left)?;
    let at_n_proof = kernel.eq_mp(final_equality.theorem, property_at_rep)?;
    kernel.convert_conclusions(at_n_proof, final_equality.right, at_n)?;
    let conclusion_proof = kernel.forall_intro_at(at_n_proof, natural, conclusion)?;
    kernel.contract_theorem(conclusion_proof)?;
    let principle_proof = kernel.imp_right(conclusion_proof, positive(principle))?;
    Ok(kernel.forall_intro_at(principle_proof, predicate, induction)?)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn prove_strengthened_step(
    kernel: &mut Kernel,
    subtype: &Subtype,
    predicate: Ref,
    premises: Ref,
    member_succ_theorem: ThmId,
    carrier_successor: Ref,
    natural_successor: Ref,
    strengthened: Ref,
    strengthened_step: Ref,
) -> Result<ThmId, NaturalError> {
    let (carrier_value, step_body) = universal_parts(kernel, strengthened_step)?;
    let [at_value, at_next] = exact_op2(kernel, step_body, Op2::Imp)?;
    let (at_value_application, expanded_at_value) =
        beta_application(kernel, strengthened, carrier_value)?;
    join_same_syntax(kernel, at_value_application, at_value)?;
    let [_next_function, carrier_next] = exact_children(kernel, at_next, Tag::Tm(TmTag::App))?;
    let (at_next_application, expanded_at_next) =
        beta_application(kernel, strengthened, carrier_next)?;
    join_same_syntax(kernel, at_next_application, at_next)?;
    let [member_at_value, property_at_value] = exact_op2(kernel, expanded_at_value, Op2::And)?;
    let [member_at_next, property_at_next] = exact_op2(kernel, expanded_at_next, Op2::And)?;

    let membership_assumption = project_and_left(kernel, expanded_at_value)?;
    let member_step = forall_elim(kernel, member_succ_theorem, carrier_value).map_err(|_| {
        NaturalError::WrongForm {
            expected: "specializable membership successor theorem",
        }
    })?;
    let [member_step_source, member_step_target] =
        exact_op2(kernel, member_step.proposition, Op2::Imp)?;
    join_same_syntax(kernel, member_at_value, member_step_source)?;
    join_same_syntax(kernel, member_at_next, member_step_target)?;
    kernel.convert_conclusions(membership_assumption, member_at_value, member_step_source)?;
    let next_membership = modus_ponens(
        kernel,
        member_step.theorem,
        membership_assumption,
        member_step.proposition,
    )?;
    kernel.convert_conclusions(next_membership, member_step_target, member_at_next)?;

    let property_assumption = project_and_right(kernel, expanded_at_value)?;
    let natural_step_proof = project_and_right(kernel, premises)?;
    let abstracted_value = kernel.app(subtype.abs, carrier_value)?;
    let natural_step_at =
        forall_elim(kernel, natural_step_proof, abstracted_value).map_err(|_| {
            NaturalError::WrongForm {
                expected: "specializable natural successor premise",
            }
        })?;
    let [natural_step_source, natural_step_target] =
        exact_op2(kernel, natural_step_at.proposition, Op2::Imp)?;
    join_same_syntax(kernel, property_at_value, natural_step_source)?;
    kernel.convert_conclusions(property_assumption, property_at_value, natural_step_source)?;
    let property_of_natural_successor = modus_ponens(
        kernel,
        natural_step_at.theorem,
        property_assumption,
        natural_step_at.proposition,
    )?;

    let rep_abs = forall_elim(
        kernel,
        subtype.rep_abs_theorem.ok_or(NaturalError::WrongForm {
            expected: "the subtype representation-abstraction theorem",
        })?,
        carrier_value,
    )
    .map_err(|_| NaturalError::WrongForm {
        expected: "specializable subtype rep-abs theorem",
    })?;
    let [guard, _representation_equality] = exact_op2(kernel, rep_abs.proposition, Op2::Imp)?;
    let [guard_member, guard_empty] = exact_op2(kernel, guard, Op2::Or)?;
    join_same_syntax(kernel, member_at_value, guard_member)?;
    let guard_proof = project_and_left(kernel, expanded_at_value)?;
    kernel.convert_conclusions(guard_proof, member_at_value, guard_member)?;
    kernel.weaken(guard_proof, &[], &[positive(guard_empty)])?;
    let guard_proof = kernel.or_right(guard_proof, positive(guard))?;
    let representation_equality =
        modus_ponens(kernel, rep_abs.theorem, guard_proof, rep_abs.proposition)?;
    let successor_equality = kernel.ap_term(representation_equality, carrier_successor)?;
    let abstraction_equality = kernel.ap_term(successor_equality.theorem, subtype.abs)?;

    let natural_successor_application = kernel.app(natural_successor, abstracted_value)?;
    let [successor_binder, successor_body] =
        exact_children(kernel, natural_successor, Tag::Tm(TmTag::Lam))?;
    let successor_beta = substitute(kernel, successor_binder, abstracted_value, successor_body)?;
    let successor_beta_fact =
        kernel.tm_beta_fact(None, natural_successor_application, successor_beta.fact)?;
    kernel.union_syn_fact(successor_beta_fact)?;
    join_same_syntax(kernel, abstraction_equality.left, successor_beta.output)?;
    let property_equality = kernel.ap_term(abstraction_equality.theorem, predicate)?;

    let property_of_expanded_successor = kernel.app(predicate, successor_beta.output)?;
    let [step_predicate, step_argument] =
        exact_children(kernel, natural_step_target, Tag::Tm(TmTag::App))?;
    let predicate_fact = join_same_syntax(kernel, step_predicate, predicate)?;
    let argument_shape = join_same_syntax(kernel, step_argument, natural_successor_application)?;
    let argument_beta = kernel.syn_trans(None, argument_shape, successor_beta_fact)?;
    let lifted_beta = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        natural_step_target,
        property_of_expanded_successor,
        &[predicate_fact, argument_beta],
    )?;
    kernel.union_syn_fact(lifted_beta)?;
    kernel.convert_conclusions(
        property_of_natural_successor,
        natural_step_target,
        property_of_expanded_successor,
    )?;
    join_same_syntax(
        kernel,
        property_equality.left,
        property_of_expanded_successor,
    )?;
    join_same_syntax(kernel, property_equality.right, property_at_next)?;
    kernel.convert_conclusions(
        property_of_natural_successor,
        property_of_expanded_successor,
        property_equality.left,
    )?;
    let next_property = kernel.eq_mp(property_equality.theorem, property_of_natural_successor)?;
    kernel.convert_conclusions(next_property, property_equality.right, property_at_next)?;

    let next = kernel.and_right(next_membership, next_property, positive(expanded_at_next))?;
    kernel.contract_theorem(next)?;
    kernel.convert_conclusions(next, expanded_at_next, at_next)?;
    kernel.convert_theorem(next, expanded_at_value, at_value)?;
    let body_proof = kernel.imp_right(next, positive(step_body))?;
    kernel.contract_theorem(body_proof)?;
    Ok(kernel.forall_intro_at(body_proof, carrier_value, strengthened_step)?)
}

fn prove_member_successor(
    kernel: &mut Kernel,
    member: Ref,
    carrier: Ref,
    successor: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let value = kernel.tm_fv(kernel.fresh_name(&[member, successor])?, carrier)?;
    let member_at_value = kernel.app(member, value)?;
    let next = kernel.app(successor, value)?;
    let member_at_next = kernel.app(member, next)?;
    let implication = kernel.op2(Op2::Imp, member_at_value, member_at_next)?;
    let statement = kernel.forall_tm(kernel.classifier(member_at_value)?, value, implication)?;

    let (next_application, expanded_next) = beta_application(kernel, member, next)?;
    join_same_syntax(kernel, next_application, member_at_next)?;
    let [_forall_ty, predicate_function, truth_function] =
        exact_children(kernel, expanded_next, Tag::Tm(TmTag::Eq))?;
    let [predicate, closure_implication] =
        exact_children(kernel, predicate_function, Tag::Tm(TmTag::Lam))?;
    let [truth_binder, truth_body] = exact_children(kernel, truth_function, Tag::Tm(TmTag::Lam))?;
    if truth_binder != predicate || kernel.arena().bool_value(truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "the successor membership universal",
        });
    }
    let [closure, at_next] = exact_op2(kernel, closure_implication, Op2::Imp)?;

    let member_assumption = kernel.identity(positive(member_at_value))?;
    let (value_application, expanded_value) = beta_application(kernel, member, value)?;
    join_same_syntax(kernel, value_application, member_at_value)?;
    kernel.convert_conclusions(member_assumption, member_at_value, expanded_value)?;
    let specialized_member =
        forall_elim(kernel, member_assumption, predicate).map_err(|_| NaturalError::WrongForm {
            expected: "specializable membership at the predecessor",
        })?;
    let [specialized_closure, at_value] =
        exact_op2(kernel, specialized_member.proposition, Op2::Imp)?;
    join_same_syntax(kernel, closure, specialized_closure)?;
    let closure_proof = kernel.identity(positive(closure))?;
    kernel.convert_conclusions(closure_proof, closure, specialized_closure)?;
    let at_value_proof = modus_ponens(
        kernel,
        specialized_member.theorem,
        closure_proof,
        specialized_member.proposition,
    )?;

    let step_proof = project_and_right(kernel, closure)?;
    let step_at_value =
        forall_elim(kernel, step_proof, value).map_err(|_| NaturalError::WrongForm {
            expected: "specializable successor-closure premise",
        })?;
    let [step_at, step_next] = exact_op2(kernel, step_at_value.proposition, Op2::Imp)?;
    join_same_syntax(kernel, at_value, step_at)?;
    join_same_syntax(kernel, step_next, at_next)?;
    kernel.convert_conclusions(at_value_proof, at_value, step_at)?;
    let next_proof = modus_ponens(
        kernel,
        step_at_value.theorem,
        at_value_proof,
        step_at_value.proposition,
    )?;
    kernel.contract_theorem(next_proof)?;
    kernel.convert_conclusions(next_proof, step_next, at_next)?;
    let closure_to_next = kernel.imp_right(next_proof, positive(closure_implication))?;
    kernel.contract_theorem(closure_to_next)?;
    let generalized_predicate =
        kernel.forall_intro_at(closure_to_next, predicate, expanded_next)?;
    kernel.convert_theorem(generalized_predicate, expanded_next, member_at_next)?;
    let membership_implication = kernel.imp_right(generalized_predicate, positive(implication))?;
    let generalized = kernel.forall_intro_at(membership_implication, value, statement)?;
    Ok((statement, generalized))
}

fn modus_ponens(
    kernel: &mut Kernel,
    implication_theorem: ThmId,
    antecedent_theorem: ThmId,
    implication: Ref,
) -> Result<ThmId, NaturalError> {
    let [_antecedent, consequent] = exact_op2(kernel, implication, Op2::Imp)?;
    let consequence = kernel.identity(positive(consequent))?;
    let use_implication =
        kernel.imp_left(antecedent_theorem, consequence, positive(implication))?;
    Ok(kernel.cut(implication_theorem, use_implication, positive(implication))?)
}

fn project_and_right(kernel: &mut Kernel, conjunction: Ref) -> Result<ThmId, NaturalError> {
    let [left, right] = exact_op2(kernel, conjunction, Op2::And)?;
    let theorem = kernel.identity(positive(right))?;
    kernel.weaken(theorem, &[positive(left)], &[])?;
    Ok(kernel.and_left(theorem, positive(conjunction))?)
}

fn project_and_left(kernel: &mut Kernel, conjunction: Ref) -> Result<ThmId, NaturalError> {
    let [left, right] = exact_op2(kernel, conjunction, Op2::And)?;
    let theorem = kernel.identity(positive(left))?;
    kernel.weaken(theorem, &[positive(right)], &[])?;
    Ok(kernel.and_left(theorem, positive(conjunction))?)
}

fn beta_application(
    kernel: &mut Kernel,
    function: Ref,
    argument: Ref,
) -> Result<(Ref, Ref), NaturalError> {
    let application = kernel.app(function, argument)?;
    let [binder, body] = exact_children(kernel, function, Tag::Tm(TmTag::Lam))?;
    let substitution = substitute(kernel, binder, argument, body)?;
    let beta = kernel.tm_beta_fact(None, application, substitution.fact)?;
    kernel.union_syn_fact(beta)?;
    Ok((application, substitution.output))
}

#[allow(clippy::too_many_arguments)]
fn prove_representations_are_members(
    kernel: &mut Kernel,
    subtype: &Subtype,
    zero: Ref,
    zero_member: Ref,
    zero_member_theorem: ThmId,
    natural: Ref,
) -> Result<(Ref, ThmId, Ref, ThmId), NaturalError> {
    let guarded = forall_elim(
        kernel,
        subtype.rep_guarded_theorem.ok_or(NaturalError::WrongForm {
            expected: "the proved subtype representation guard",
        })?,
        natural,
    )?;
    let [represented_member, empty] = exact_op2(kernel, guarded.proposition, Op2::Or)?;
    let [inhabited] = exact_op1(kernel, empty, covalence_logic_hol::builtin::Op1::Not)?;

    // Prove the exact existential already embedded in the guard, rather than
    // constructing a parallel choice term and relying on hash-consing.
    let [predicate, _choice] = exact_children(kernel, inhabited, Tag::Tm(TmTag::App))?;
    let [witness, body] = exact_children(kernel, predicate, Tag::Tm(TmTag::Lam))?;
    let at_zero = kernel.app(predicate, zero)?;
    let beta = substitute(kernel, witness, zero, body)?;
    let beta_fact = kernel.tm_beta_fact(None, at_zero, beta.fact)?;
    kernel.union_syn_fact(beta_fact)?;
    join_same_syntax(kernel, beta.output, zero_member)?;
    let witness_theorem = kernel.copy_theorem(zero_member_theorem)?;
    kernel.convert_theorem(witness_theorem, zero_member, at_zero)?;
    let inhabited_theorem = kernel.choice_intro_at(witness_theorem, inhabited)?;

    // `guard (rep n)` is `member (rep n) ∨ ¬ inhabited`. The second branch
    // contradicts the witness above, so ordinary Gentzen rules remove it.
    let member_branch = kernel.identity(positive(represented_member))?;
    let impossible_branch = kernel.identity(positive(inhabited))?;
    kernel.not_left(impossible_branch, positive(inhabited))?;
    let impossible_branch = kernel.fold_premise(impossible_branch, positive(empty))?;
    let cases = kernel.or_left(
        member_branch,
        impossible_branch,
        positive(guarded.proposition),
    )?;
    let without_guard = kernel.cut(guarded.theorem, cases, positive(guarded.proposition))?;
    let represented_member_theorem =
        kernel.cut(inhabited_theorem, without_guard, positive(inhabited))?;
    let generalized = kernel.forall_intro(represented_member_theorem, natural)?;
    Ok((
        inhabited,
        inhabited_theorem,
        generalized.universal,
        generalized.theorem,
    ))
}

/// Proves that the designated zero belongs to the intersection of all
/// successor-closed predicates containing zero.
fn prove_member_zero(
    kernel: &mut Kernel,
    member: Ref,
    zero: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let member_at_zero = kernel.app(member, zero)?;
    let [member_binder, member_body] = exact_children(kernel, member, Tag::Tm(TmTag::Lam))?;
    let beta = substitute(kernel, member_binder, zero, member_body)?;
    let beta_fact = kernel.tm_beta_fact(None, member_at_zero, beta.fact)?;
    kernel.union_syn_fact(beta_fact)?;

    let [_forall_ty, predicate_function, truth_function] =
        exact_children(kernel, beta.output, Tag::Tm(TmTag::Eq))?;
    let [predicate, implication] = exact_children(kernel, predicate_function, Tag::Tm(TmTag::Lam))?;
    let [truth_binder, truth_body] = exact_children(kernel, truth_function, Tag::Tm(TmTag::Lam))?;
    if truth_binder != predicate || kernel.arena().bool_value(truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "an equality-encoded universal",
        });
    }
    let [premises, consequence] = exact_op2(kernel, implication, Op2::Imp)?;
    let [base, step] = exact_op2(kernel, premises, Op2::And)?;

    // `base` and `consequence` are separately elaborated applications of the
    // same predicate to zero. Certify that fact instead of assuming physical
    // hash-consing in the userspace compiler.
    join_same_syntax(kernel, base, consequence)?;
    let theorem = kernel.identity(positive(base))?;
    kernel.convert_conclusions(theorem, base, consequence)?;
    kernel.weaken(theorem, &[positive(step)], &[])?;
    let theorem = kernel.and_left(theorem, positive(premises))?;
    let theorem = kernel.imp_right(theorem, positive(implication))?;
    let theorem = kernel.forall_intro_at(theorem, predicate, beta.output)?;
    kernel.convert_theorem(theorem, beta.output, member_at_zero)?;
    Ok((member_at_zero, theorem))
}

fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}

fn exact_op2(kernel: &Kernel, reference: Ref, op: Op2) -> Result<[Ref; 2], NaturalError> {
    if kernel.arena().op2(reference) != Some(op) {
        return Err(NaturalError::WrongForm {
            expected: "a compact logical opcode",
        });
    }
    exact_children(kernel, reference, Tag::Tm(TmTag::Op2))
}

fn exact_op1(
    kernel: &Kernel,
    reference: Ref,
    op: covalence_logic_hol::builtin::Op1,
) -> Result<[Ref; 1], NaturalError> {
    if kernel.arena().op1(reference) != Some(op) {
        return Err(NaturalError::WrongForm {
            expected: "a compact unary logical opcode",
        });
    }
    exact_children(kernel, reference, Tag::Tm(TmTag::Op1))
}

fn universal_parts(kernel: &Kernel, universal: Ref) -> Result<(Ref, Ref), NaturalError> {
    let [_ty, predicate, truth] = exact_children(kernel, universal, Tag::Tm(TmTag::Eq))?;
    let [binder, body] = exact_children(kernel, predicate, Tag::Tm(TmTag::Lam))?;
    let [truth_binder, truth_body] = exact_children(kernel, truth, Tag::Tm(TmTag::Lam))?;
    if truth_binder != binder || kernel.arena().bool_value(truth_body) != Some(true) {
        return Err(NaturalError::WrongForm {
            expected: "an equality-encoded universal",
        });
    }
    Ok((binder, body))
}

fn sole_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, NaturalError> {
    let theorem = kernel.thm().get(theorem).ok_or(NaturalError::WrongForm {
        expected: "a resident theorem",
    })?;
    let mut rows = theorem.rhs.rows();
    let row = rows.next().ok_or(NaturalError::WrongForm {
        expected: "one theorem conclusion",
    })?;
    if rows.next().is_some() || row.len() != 1 || !row[0].is_positive() {
        return Err(NaturalError::WrongForm {
            expected: "one positive theorem conclusion",
        });
    }
    Ref::new(
        i32::try_from(row[0].magnitude()).map_err(|_| NaturalError::WrongForm {
            expected: "a local theorem proposition",
        })?,
    )
    .ok_or(NaturalError::WrongForm {
        expected: "a nonzero theorem proposition",
    })
}

fn exact_children<const N: usize>(
    kernel: &Kernel,
    reference: Ref,
    tag: Tag,
) -> Result<[Ref; N], NaturalError> {
    if kernel.arena().tag(reference) != Some(tag) {
        return Err(NaturalError::WrongForm {
            expected: "the natural schema's checked syntax",
        });
    }
    kernel
        .arena()
        .children(reference)
        .ok_or(NaturalError::WrongForm {
            expected: "resident natural schema syntax",
        })?
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| NaturalError::WrongForm {
            expected: "the natural schema's exact arity",
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
    let closed_step = kernel.op2(Op2::Imp, at_k, at_next)?;
    let closed = kernel.forall_tm(bool_ty, k, closed_step)?;
    let base_and_closed = kernel.op2(Op2::And, at_zero, closed)?;
    let at_n = kernel.app(predicate, n)?;
    let entails_n = kernel.op2(Op2::Imp, base_and_closed, at_n)?;
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
    let step = kernel.op2(Op2::Imp, at_n, at_next)?;
    let every_step = kernel.forall_tm(bool_ty, n, step)?;
    let premises = kernel.op2(Op2::And, at_zero, every_step)?;
    let conclusion = kernel.forall_tm(bool_ty, n, at_n)?;
    let principle = kernel.op2(Op2::Imp, premises, conclusion)?;
    kernel.forall_tm(bool_ty, predicate, principle)
}
