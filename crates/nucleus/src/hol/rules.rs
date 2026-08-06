//! The sealed primitive rules and `proof_step`.
//!
//! Each rule struct's fields are exactly the inputs fixed by
//! `hol/semantics.txt`; `proof_step` authorizes the rule, revalidates
//! every premise in this store, checks the side conditions, interns the
//! conclusion syntax, and inserts-or-finds the canonical theorem row in
//! one transaction. A failing step persists nothing; repeating a step
//! returns the existing handle. The omega rules (`TY_ABS`, `TY_BETA`,
//! `TY_ETA`) land as a strictly additive follow-up.

use covalence_lib_error::snafu::ResultExt;
use covalence_lib_sqlite::OptionalExtension;

use super::syntax::{HypsId, Kind, KindsId, TermId, TheoremId, Tm, Ty, TypeId, VarsId};
use super::typing::{
    DeepTm, lift_tm_in_tm, lift_ty_in_tm, lift_ty_in_ty, open_tm_in_tm, strengthen_tm_in_tm,
    subst_tm_in_tm, subst_ty_in_tm, subst_ty_in_ty,
};
use super::view::{
    ArityMismatchSnafu, ContextMismatchSnafu, HolError, HolView, HypothesisNotStrengthenableSnafu,
    NotAnApplicationSnafu, NotAnEqualitySnafu, NotBooleanSnafu, StorageSnafu, TypeMismatchSnafu,
    UnknownIdSnafu,
};
use super::{Operation, Policy};

mod sealed {
    pub trait Sealed {}
}

/// A primitive proof step: sealed, with typed inputs and output.
pub trait Rule<'v>: sealed::Sealed {
    /// The typed persistent result of the step.
    type Output;

    /// The policy operation this step requires.
    fn operation(&self) -> Operation;

    /// Applies the rule; called inside `proof_step`'s transaction.
    ///
    /// # Errors
    ///
    /// Fails when a premise or side condition does not hold.
    fn apply<P: Policy>(self, view: &HolView<'v, P>) -> Result<Self::Output, HolError>;
}

macro_rules! rule {
    ($(#[$doc:meta])* $name:ident<'v> { $($(#[$fdoc:meta])* $field:ident : $ty:ty),* $(,)? }) => {
        $(#[$doc])*
        pub struct $name<'v> {
            $($(#[$fdoc])* pub $field: $ty,)*
        }
        impl<'v> sealed::Sealed for $name<'v> {}
    };
}

rule!(
    /// `ASSUME`: `Delta; Gamma; {p} |- p`.
    Assume<'v> {
        /// Kind context.
        kinds: KindsId<'v>,
        /// Variable context.
        vars: VarsId<'v>,
        /// The Boolean proposition to assume.
        prop: TermId<'v>,
    }
);
rule!(
    /// `WEAKEN_HYP`: add a hypothesis.
    WeakenHyp<'v> {
        /// The premise theorem.
        thm: TheoremId<'v>,
        /// The Boolean hypothesis to add.
        prop: TermId<'v>,
    }
);
rule!(
    /// `WEAKEN_VAR`: push a variable, lifting term indices.
    WeakenVar<'v> {
        /// The premise theorem.
        thm: TheoremId<'v>,
        /// The type of the new innermost variable.
        ty: TypeId<'v>,
    }
);
rule!(
    /// `WEAKEN_KIND`: push a kind, lifting type indices.
    WeakenKind<'v> {
        /// The premise theorem.
        thm: TheoremId<'v>,
        /// The new innermost kind.
        kind: super::syntax::KindId<'v>,
    }
);
rule!(
    /// `INST_TM`: simultaneous term-variable instantiation.
    InstTm<'v> {
        /// The premise theorem.
        thm: TheoremId<'v>,
        /// The target variable context.
        vars: VarsId<'v>,
        /// One value per premise variable, innermost first.
        values: Vec<TermId<'v>>,
    }
);
rule!(
    /// `INST_TY`: simultaneous type-variable instantiation.
    InstTy<'v> {
        /// The premise theorem.
        thm: TheoremId<'v>,
        /// The target kind context.
        kinds: KindsId<'v>,
        /// One type per premise kind variable, innermost first.
        values: Vec<TypeId<'v>>,
    }
);
rule!(
    /// `TRUTH`: `|- true`.
    Truth<'v> {
        /// Kind context.
        kinds: KindsId<'v>,
        /// Variable context.
        vars: VarsId<'v>,
    }
);
rule!(
    /// `REFL`: `|- EQ t t`.
    Refl<'v> {
        /// Kind context.
        kinds: KindsId<'v>,
        /// Variable context.
        vars: VarsId<'v>,
        /// The well-typed term.
        term: TermId<'v>,
    }
);
rule!(
    /// `SYM`: from `|- EQ x y`, `|- EQ y x`.
    Sym<'v> {
        /// The equality premise.
        premise: TheoremId<'v>,
    }
);
rule!(
    /// `TRANS`: from `|- EQ x y` and `|- EQ y z`, `|- EQ x z`.
    Trans<'v> {
        /// The left equality.
        left: TheoremId<'v>,
        /// The right equality.
        right: TheoremId<'v>,
    }
);
rule!(
    /// `EQ_MP`: from `|- EQ p q` and `|- p`, `|- q`.
    EqMp<'v> {
        /// The Boolean equality.
        equality: TheoremId<'v>,
        /// The premise `p`.
        premise: TheoremId<'v>,
    }
);
rule!(
    /// `MK_COMB`: application congruence.
    MkComb<'v> {
        /// Equality of functions.
        function: TheoremId<'v>,
        /// Equality of arguments.
        argument: TheoremId<'v>,
    }
);
rule!(
    /// `ABS`: lambda congruence; hypotheses must not use the variable.
    Abs<'v> {
        /// Equality under the innermost variable.
        premise: TheoremId<'v>,
    }
);
rule!(
    /// `BETA`: `|- EQ (APP (LAM A t) s) (t[s])`.
    Beta<'v> {
        /// Kind context.
        kinds: KindsId<'v>,
        /// Variable context.
        vars: VarsId<'v>,
        /// The lambda abstraction.
        lam: TermId<'v>,
        /// The argument.
        arg: TermId<'v>,
    }
);
rule!(
    /// `ETA`: `|- EQ (LAM A (APP f' (BV 0))) f`.
    Eta<'v> {
        /// Kind context.
        kinds: KindsId<'v>,
        /// Variable context.
        vars: VarsId<'v>,
        /// The function term of arrow type.
        function: TermId<'v>,
    }
);
rule!(
    /// `CHOICE`: from `|- APP p x`, `|- APP p (EPS p)`.
    Choice<'v> {
        /// The applied-predicate premise.
        premise: TheoremId<'v>,
    }
);
rule!(
    /// `DEDUCT_ANTISYM`: Boolean antisymmetry of deduction.
    DeductAntisym<'v> {
        /// The left premise.
        left: TheoremId<'v>,
        /// The right premise.
        right: TheoremId<'v>,
    }
);
rule!(
    /// `ABS_REP`: `|- EQ (ABS p (REP p x)) x`.
    AbsRep<'v> {
        /// Kind context.
        kinds: KindsId<'v>,
        /// Variable context.
        vars: VarsId<'v>,
        /// A value of subtype type.
        value: TermId<'v>,
    }
);
rule!(
    /// `REP_ABS`: from `|- p[x]`, `|- EQ (REP p (ABS p x)) x`.
    RepAbs<'v> {
        /// The satisfaction premise `|- p[x]`.
        premise: TheoremId<'v>,
        /// The subtype predicate (typed in its own one-variable context).
        pred: TermId<'v>,
        /// The value.
        value: TermId<'v>,
    }
);

/// `INFINITY`: the fixed closed axiom over the individuals type.
pub struct Infinity;
impl sealed::Sealed for Infinity {}

impl<'v, P: Policy> HolView<'v, P> {
    /// Applies one primitive proof step atomically.
    ///
    /// # Errors
    ///
    /// Fails when the policy refuses the rule or a premise or side
    /// condition does not hold; nothing is persisted on failure.
    pub fn proof_step<R: Rule<'v>>(&self, rule: R) -> Result<R::Output, HolError> {
        self.authorize(rule.operation())?;
        let transaction = self
            .raw_sqlite()
            .unchecked_transaction()
            .context(StorageSnafu)?;
        let output = rule.apply(self)?;
        transaction.commit().context(StorageSnafu)?;
        Ok(output)
    }

    /// Reads a theorem's components.
    ///
    /// # Errors
    ///
    /// Fails if the handle does not name a theorem row.
    pub fn theorem(
        &self,
        theorem: TheoremId<'v>,
    ) -> Result<(KindsId<'v>, VarsId<'v>, HypsId<'v>, TermId<'v>), HolError> {
        self.authorize(Operation::ReadSyntax)?;
        self.theorem_parts(theorem.raw())
    }

    /// Revalidates a raw theorem handle.
    ///
    /// # Errors
    ///
    /// Fails if the id does not name a theorem row.
    pub fn theorem_from_raw(&self, raw: i64) -> Result<TheoremId<'v>, HolError> {
        self.authorize(Operation::ReadSyntax)?;
        self.theorem_parts(raw)?;
        Ok(TheoremId::new(raw))
    }

    fn theorem_parts(
        &self,
        raw: i64,
    ) -> Result<(KindsId<'v>, VarsId<'v>, HypsId<'v>, TermId<'v>), HolError> {
        self.raw_sqlite()
            .prepare_cached(
                "SELECT kinds, vars, hyps, concl FROM hol_theorem WHERE theorem_id = ?1",
            )
            .and_then(|mut statement| {
                statement
                    .query_row((raw,), |row| {
                        Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?))
                    })
                    .optional()
            })
            .context(StorageSnafu)?
            .map(|(kinds, vars, hyps, concl): (i64, i64, i64, i64)| {
                (
                    KindsId::new(kinds),
                    VarsId::new(vars),
                    HypsId::new(hyps),
                    TermId::new(concl),
                )
            })
            .ok_or_else(|| UnknownIdSnafu { raw }.build())
    }

    fn insert_theorem(
        &self,
        kinds: KindsId<'v>,
        vars: VarsId<'v>,
        hyps: HypsId<'v>,
        concl: TermId<'v>,
    ) -> Result<TheoremId<'v>, HolError> {
        self.raw_sqlite()
            .prepare_cached(
                "INSERT INTO hol_theorem(kinds, vars, hyps, concl)
                 VALUES (?1, ?2, ?3, ?4)
                 ON CONFLICT(kinds, vars, hyps, concl) DO UPDATE SET concl = concl
                 RETURNING theorem_id",
            )
            .and_then(|mut statement| {
                statement.query_row((kinds.raw(), vars.raw(), hyps.raw(), concl.raw()), |row| {
                    row.get::<_, i64>(0)
                })
            })
            .context(StorageSnafu)
            .map(TheoremId::new)
    }

    fn require_bool(
        &self,
        kinds: KindsId<'v>,
        vars: VarsId<'v>,
        term: TermId<'v>,
    ) -> Result<(), HolError> {
        let bool_ty = self.ty(Ty::Bool)?;
        if self.type_of(kinds, vars, term)? == bool_ty {
            Ok(())
        } else {
            NotBooleanSnafu.fail()
        }
    }

    fn require_valid_ctx(&self, kinds: KindsId<'v>, vars: VarsId<'v>) -> Result<(), HolError> {
        let star = self.kind(Kind::Star)?;
        for entry in self.vars_entries(vars)? {
            if self.kind_of(kinds, entry)? != star {
                return TypeMismatchSnafu.fail();
            }
        }
        Ok(())
    }

    /// Splits an equality conclusion into its sides.
    fn equality_sides(&self, concl: TermId<'v>) -> Result<(TermId<'v>, TermId<'v>), HolError> {
        match self.tm_node(concl)? {
            Tm::Eq(left, right) => Ok((left, right)),
            _ => NotAnEqualitySnafu.fail(),
        }
    }

    fn union_hyps(&self, left: HypsId<'v>, right: HypsId<'v>) -> Result<HypsId<'v>, HolError> {
        let mut entries = self.hyps_entries(left)?;
        entries.extend(self.hyps_entries(right)?);
        self.hyps(&entries)
    }

    fn map_theorem_terms(
        &self,
        hyps: HypsId<'v>,
        concl: TermId<'v>,
        mut transform: impl FnMut(&DeepTm) -> Result<DeepTm, HolError>,
    ) -> Result<(Vec<TermId<'v>>, TermId<'v>), HolError> {
        let mut mapped = Vec::new();
        for hyp in self.hyps_entries(hyps)? {
            let tree = self.load_tm(hyp)?;
            let transformed = transform(&tree)?;
            mapped.push(self.intern_tm(&transformed)?);
        }
        let concl_tree = self.load_tm(concl)?;
        let transformed = transform(&concl_tree)?;
        let concl = self.intern_tm(&transformed)?;
        Ok((mapped, concl))
    }
}

macro_rules! impl_rule {
    ($name:ident, $operation:ident, |$self:ident, $view:ident| $body:block) => {
        impl<'v> Rule<'v> for $name<'v> {
            type Output = TheoremId<'v>;

            fn operation(&self) -> Operation {
                Operation::$operation
            }

            fn apply<P: Policy>($self, $view: &HolView<'v, P>) -> Result<Self::Output, HolError> {
                $body
            }
        }
    };
}

impl_rule!(Assume, Assume, |self, view| {
    view.require_valid_ctx(self.kinds, self.vars)?;
    view.require_bool(self.kinds, self.vars, self.prop)?;
    let hyps = view.hyps(&[self.prop])?;
    view.insert_theorem(self.kinds, self.vars, hyps, self.prop)
});

impl_rule!(WeakenHyp, WeakenHyp, |self, view| {
    let (kinds, vars, hyps, concl) = view.theorem_parts(self.thm.raw())?;
    view.require_bool(kinds, vars, self.prop)?;
    let mut entries = view.hyps_entries(hyps)?;
    entries.push(self.prop);
    let hyps = view.hyps(&entries)?;
    view.insert_theorem(kinds, vars, hyps, concl)
});

impl_rule!(WeakenVar, WeakenVar, |self, view| {
    let (kinds, vars, hyps, concl) = view.theorem_parts(self.thm.raw())?;
    let star = view.kind(Kind::Star)?;
    if view.kind_of(kinds, self.ty)? != star {
        return TypeMismatchSnafu.fail();
    }
    let mut entries = vec![self.ty];
    entries.extend(view.vars_entries(vars)?);
    let vars = view.vars(&entries)?;
    let (hyp_terms, concl) =
        view.map_theorem_terms(hyps, concl, |tree| Ok(Box::new(lift_tm_in_tm(tree, 1, 0))))?;
    let hyps = view.hyps(&hyp_terms)?;
    view.insert_theorem(kinds, vars, hyps, concl)
});

impl_rule!(WeakenKind, WeakenKind, |self, view| {
    let (kinds, vars, hyps, concl) = view.theorem_parts(self.thm.raw())?;
    let mut kind_entries = vec![self.kind];
    kind_entries.extend(view.kinds_entries(kinds)?);
    let kinds = view.kinds(&kind_entries)?;
    let mut var_entries = Vec::new();
    for entry in view.vars_entries(vars)? {
        let tree = view.load_ty(entry)?;
        var_entries.push(view.intern_ty(&lift_ty_in_ty(&tree, 1, 0))?);
    }
    let vars = view.vars(&var_entries)?;
    let (hyp_terms, concl) =
        view.map_theorem_terms(hyps, concl, |tree| Ok(Box::new(lift_ty_in_tm(tree, 1, 0))))?;
    let hyps = view.hyps(&hyp_terms)?;
    view.insert_theorem(kinds, vars, hyps, concl)
});

impl_rule!(InstTm, InstTm, |self, view| {
    let (kinds, vars, hyps, concl) = view.theorem_parts(self.thm.raw())?;
    let premise_vars = view.vars_entries(vars)?;
    if premise_vars.len() != self.values.len() {
        return ArityMismatchSnafu {
            expected: premise_vars.len(),
            found: self.values.len(),
        }
        .fail();
    }
    for (variable_ty, value) in premise_vars.iter().zip(&self.values) {
        if view.type_of(kinds, self.vars, *value)? != *variable_ty {
            return TypeMismatchSnafu.fail();
        }
    }
    let mut value_trees = Vec::new();
    for value in &self.values {
        value_trees.push(view.load_tm(*value)?);
    }
    let (hyp_terms, concl) = view.map_theorem_terms(hyps, concl, |tree| {
        subst_tm_in_tm(tree, &value_trees, 0, 0).map(Box::new)
    })?;
    let hyps = view.hyps(&hyp_terms)?;
    view.insert_theorem(kinds, self.vars, hyps, concl)
});

impl_rule!(InstTy, InstTy, |self, view| {
    let (kinds, vars, hyps, concl) = view.theorem_parts(self.thm.raw())?;
    let premise_kinds = view.kinds_entries(kinds)?;
    if premise_kinds.len() != self.values.len() {
        return ArityMismatchSnafu {
            expected: premise_kinds.len(),
            found: self.values.len(),
        }
        .fail();
    }
    for (kind, value) in premise_kinds.iter().zip(&self.values) {
        if view.kind_of(self.kinds, *value)? != *kind {
            return TypeMismatchSnafu.fail();
        }
    }
    let mut value_trees = Vec::new();
    for value in &self.values {
        value_trees.push(view.load_ty(*value)?);
    }
    let mut var_entries = Vec::new();
    for entry in view.vars_entries(vars)? {
        let tree = view.load_ty(entry)?;
        var_entries.push(view.intern_ty(&subst_ty_in_ty(&tree, &value_trees, 0)?)?);
    }
    let vars = view.vars(&var_entries)?;
    let (hyp_terms, concl) = view.map_theorem_terms(hyps, concl, |tree| {
        subst_ty_in_tm(tree, &value_trees, 0).map(Box::new)
    })?;
    let hyps = view.hyps(&hyp_terms)?;
    view.insert_theorem(self.kinds, vars, hyps, concl)
});

impl_rule!(Truth, Truth, |self, view| {
    view.require_valid_ctx(self.kinds, self.vars)?;
    let truth = view.tm(Tm::Bool(true))?;
    view.insert_theorem(self.kinds, self.vars, view.empty_hyps(), truth)
});

impl_rule!(Refl, Refl, |self, view| {
    view.require_valid_ctx(self.kinds, self.vars)?;
    view.type_of(self.kinds, self.vars, self.term)?;
    let concl = view.tm(Tm::Eq(self.term, self.term))?;
    view.insert_theorem(self.kinds, self.vars, view.empty_hyps(), concl)
});

impl_rule!(Sym, Sym, |self, view| {
    let (kinds, vars, hyps, concl) = view.theorem_parts(self.premise.raw())?;
    let (left, right) = view.equality_sides(concl)?;
    let concl = view.tm(Tm::Eq(right, left))?;
    view.insert_theorem(kinds, vars, hyps, concl)
});

impl_rule!(Trans, Trans, |self, view| {
    let (kinds, vars, left_hyps, left_concl) = view.theorem_parts(self.left.raw())?;
    let (right_kinds, right_vars, right_hyps, right_concl) =
        view.theorem_parts(self.right.raw())?;
    if kinds != right_kinds || vars != right_vars {
        return ContextMismatchSnafu.fail();
    }
    let (x, y_left) = view.equality_sides(left_concl)?;
    let (y_right, z) = view.equality_sides(right_concl)?;
    if y_left != y_right {
        return TypeMismatchSnafu.fail();
    }
    let hyps = view.union_hyps(left_hyps, right_hyps)?;
    let concl = view.tm(Tm::Eq(x, z))?;
    view.insert_theorem(kinds, vars, hyps, concl)
});

impl_rule!(EqMp, EqMp, |self, view| {
    let (kinds, vars, eq_hyps, eq_concl) = view.theorem_parts(self.equality.raw())?;
    let (premise_kinds, premise_vars, premise_hyps, premise_concl) =
        view.theorem_parts(self.premise.raw())?;
    if kinds != premise_kinds || vars != premise_vars {
        return ContextMismatchSnafu.fail();
    }
    let (p, q) = view.equality_sides(eq_concl)?;
    if p != premise_concl {
        return TypeMismatchSnafu.fail();
    }
    view.require_bool(kinds, vars, p)?;
    let hyps = view.union_hyps(eq_hyps, premise_hyps)?;
    view.insert_theorem(kinds, vars, hyps, q)
});

impl_rule!(MkComb, MkComb, |self, view| {
    let (kinds, vars, function_hyps, function_concl) = view.theorem_parts(self.function.raw())?;
    let (argument_kinds, argument_vars, argument_hyps, argument_concl) =
        view.theorem_parts(self.argument.raw())?;
    if kinds != argument_kinds || vars != argument_vars {
        return ContextMismatchSnafu.fail();
    }
    let (f, g) = view.equality_sides(function_concl)?;
    let (x, y) = view.equality_sides(argument_concl)?;
    let Ty::Arr(domain, _) = view.ty_node(view.type_of(kinds, vars, f)?)? else {
        return TypeMismatchSnafu.fail();
    };
    if view.type_of(kinds, vars, x)? != domain {
        return TypeMismatchSnafu.fail();
    }
    let hyps = view.union_hyps(function_hyps, argument_hyps)?;
    let left = view.tm(Tm::App(f, x))?;
    let right = view.tm(Tm::App(g, y))?;
    let concl = view.tm(Tm::Eq(left, right))?;
    view.insert_theorem(kinds, vars, hyps, concl)
});

impl_rule!(Abs, Abs, |self, view| {
    let (kinds, vars, hyps, concl) = view.theorem_parts(self.premise.raw())?;
    let entries = view.vars_entries(vars)?;
    let Some((domain, outer)) = entries.split_first() else {
        return ContextMismatchSnafu.fail();
    };
    let vars = view.vars(outer)?;
    let mut strengthened = Vec::new();
    for hyp in view.hyps_entries(hyps)? {
        let tree = view.load_tm(hyp)?;
        let Some(lowered) = strengthen_tm_in_tm(&tree) else {
            return HypothesisNotStrengthenableSnafu.fail();
        };
        strengthened.push(view.intern_tm(&lowered)?);
    }
    let hyps = view.hyps(&strengthened)?;
    let (x, y) = view.equality_sides(concl)?;
    let left = view.tm(Tm::Lam(*domain, x))?;
    let right = view.tm(Tm::Lam(*domain, y))?;
    let concl = view.tm(Tm::Eq(left, right))?;
    view.insert_theorem(kinds, vars, hyps, concl)
});

impl_rule!(Beta, Beta, |self, view| {
    view.require_valid_ctx(self.kinds, self.vars)?;
    let Tm::Lam(domain, body) = view.tm_node(self.lam)? else {
        return NotAnApplicationSnafu.fail();
    };
    view.type_of(self.kinds, self.vars, self.lam)?;
    if view.type_of(self.kinds, self.vars, self.arg)? != domain {
        return TypeMismatchSnafu.fail();
    }
    let body_tree = view.load_tm(body)?;
    let arg_tree = view.load_tm(self.arg)?;
    let reduct = open_tm_in_tm(&body_tree, &arg_tree);
    let reduct = view.intern_tm(&reduct)?;
    let redex = view.tm(Tm::App(self.lam, self.arg))?;
    let concl = view.tm(Tm::Eq(redex, reduct))?;
    view.insert_theorem(self.kinds, self.vars, view.empty_hyps(), concl)
});

impl_rule!(Eta, Eta, |self, view| {
    view.require_valid_ctx(self.kinds, self.vars)?;
    let Ty::Arr(domain, _) = view.ty_node(view.type_of(self.kinds, self.vars, self.function)?)?
    else {
        return TypeMismatchSnafu.fail();
    };
    let function_tree = view.load_tm(self.function)?;
    let lifted = view.intern_tm(&lift_tm_in_tm(&function_tree, 1, 0))?;
    let variable = view.tm(Tm::Bv(0))?;
    let applied = view.tm(Tm::App(lifted, variable))?;
    let expansion = view.tm(Tm::Lam(domain, applied))?;
    let concl = view.tm(Tm::Eq(expansion, self.function))?;
    view.insert_theorem(self.kinds, self.vars, view.empty_hyps(), concl)
});

impl_rule!(Choice, Choice, |self, view| {
    let (kinds, vars, hyps, concl) = view.theorem_parts(self.premise.raw())?;
    let Tm::App(predicate, _) = view.tm_node(concl)? else {
        return NotAnApplicationSnafu.fail();
    };
    let epsilon = view.tm(Tm::Eps(predicate))?;
    let concl = view.tm(Tm::App(predicate, epsilon))?;
    view.insert_theorem(kinds, vars, hyps, concl)
});

impl_rule!(DeductAntisym, DeductAntisym, |self, view| {
    let (kinds, vars, left_hyps, left_concl) = view.theorem_parts(self.left.raw())?;
    let (right_kinds, right_vars, right_hyps, right_concl) =
        view.theorem_parts(self.right.raw())?;
    if kinds != right_kinds || vars != right_vars {
        return ContextMismatchSnafu.fail();
    }
    let left_entries: Vec<TermId<'v>> = view
        .hyps_entries(left_hyps)?
        .into_iter()
        .filter(|hyp| *hyp != right_concl)
        .collect();
    let mut entries: Vec<TermId<'v>> = view
        .hyps_entries(right_hyps)?
        .into_iter()
        .filter(|hyp| *hyp != left_concl)
        .collect();
    entries.extend(left_entries);
    let hyps = view.hyps(&entries)?;
    let concl = view.tm(Tm::Eq(left_concl, right_concl))?;
    view.insert_theorem(kinds, vars, hyps, concl)
});

impl_rule!(AbsRep, AbsRep, |self, view| {
    view.require_valid_ctx(self.kinds, self.vars)?;
    let value_ty = view.type_of(self.kinds, self.vars, self.value)?;
    let Ty::Sub(_, predicate) = view.ty_node(value_ty)? else {
        return TypeMismatchSnafu.fail();
    };
    let rep = view.tm(Tm::Rep(predicate, self.value))?;
    let abs = view.tm(Tm::Abs(predicate, rep))?;
    let concl = view.tm(Tm::Eq(abs, self.value))?;
    view.insert_theorem(self.kinds, self.vars, view.empty_hyps(), concl)
});

impl_rule!(RepAbs, RepAbs, |self, view| {
    let (kinds, vars, hyps, concl) = view.theorem_parts(self.premise.raw())?;
    let value_ty = view.type_of(kinds, vars, self.value)?;
    let local = view.vars(&[value_ty])?;
    view.require_bool(kinds, local, self.pred)?;
    let pred_tree = view.load_tm(self.pred)?;
    let value_tree = view.load_tm(self.value)?;
    let expected = open_tm_in_tm(&pred_tree, &value_tree);
    if view.intern_tm(&expected)? != concl {
        return TypeMismatchSnafu.fail();
    }
    let abs = view.tm(Tm::Abs(self.pred, self.value))?;
    let rep = view.tm(Tm::Rep(self.pred, abs))?;
    let eq = view.tm(Tm::Eq(rep, self.value))?;
    view.insert_theorem(kinds, vars, hyps, eq)
});

impl<'v> Rule<'v> for Infinity {
    type Output = TheoremId<'v>;

    fn operation(&self) -> Operation {
        Operation::Infinity
    }

    fn apply<P: Policy>(self, view: &HolView<'v, P>) -> Result<Self::Output, HolError> {
        let concl = build_infinity(view)?;
        view.insert_theorem(
            view.empty_kinds(),
            view.empty_vars(),
            view.empty_hyps(),
            concl,
        )
    }
}

/// Builds the fixed `INFINITY` conclusion from the abbreviations in
/// `hol/semantics.txt`.
fn build_infinity<'v, P: Policy>(view: &HolView<'v, P>) -> Result<TermId<'v>, HolError> {
    let bool_ty = view.ty(Ty::Bool)?;
    let ind = view.ty(Ty::Ind)?;
    let arrow = |a: TypeId<'v>, b: TypeId<'v>| view.ty(Ty::Arr(a, b));
    let ind_to_ind = arrow(ind, ind)?;
    let bool_bool = arrow(bool_ty, bool_ty)?;
    let conj_carrier = arrow(bool_ty, bool_bool)?;
    let truth = view.tm(Tm::Bool(true))?;
    let falsity = view.tm(Tm::Bool(false))?;

    let not = |term: TermId<'v>| view.tm(Tm::Eq(term, falsity));
    let forall = |ty: TypeId<'v>, predicate: TermId<'v>| -> Result<TermId<'v>, HolError> {
        let constant_true = view.tm(Tm::Lam(ty, truth))?;
        view.tm(Tm::Eq(predicate, constant_true))
    };
    let lift = |term: TermId<'v>| -> Result<TermId<'v>, HolError> {
        let tree = view.load_tm(term)?;
        view.intern_tm(&lift_tm_in_tm(&tree, 1, 0))
    };
    let exists = |ty: TypeId<'v>, predicate: TermId<'v>| -> Result<TermId<'v>, HolError> {
        let inner = view.tm(Tm::App(lift(predicate)?, view.tm(Tm::Bv(0))?))?;
        let negated = not(inner)?;
        let all = forall(ty, view.tm(Tm::Lam(ty, negated))?)?;
        not(all)
    };
    let conj = |left: TermId<'v>, right: TermId<'v>| -> Result<TermId<'v>, HolError> {
        let selector = view.tm(Tm::Bv(0))?;
        let applied = view.tm(Tm::App(
            view.tm(Tm::App(selector, lift(left)?))?,
            lift(right)?,
        ))?;
        let pair = view.tm(Tm::Lam(conj_carrier, applied))?;
        let applied_true = view.tm(Tm::App(view.tm(Tm::App(selector, truth))?, truth))?;
        let pair_true = view.tm(Tm::Lam(conj_carrier, applied_true))?;
        view.tm(Tm::Eq(pair, pair_true))
    };

    // one_one f: forall x1 x2. (f x1 = f x2) = (x1 = x2); f enters at
    // de Bruijn depth 2.
    let f2 = view.tm(Tm::Bv(2))?;
    let x1 = view.tm(Tm::Bv(1))?;
    let x2 = view.tm(Tm::Bv(0))?;
    let images = view.tm(Tm::Eq(view.tm(Tm::App(f2, x1))?, view.tm(Tm::App(f2, x2))?))?;
    let points = view.tm(Tm::Eq(x1, x2))?;
    let one_one_body = view.tm(Tm::Eq(images, points))?;
    let one_one = forall(
        ind,
        view.tm(Tm::Lam(
            ind,
            forall(ind, view.tm(Tm::Lam(ind, one_one_body))?)?,
        ))?,
    )?;

    // onto f: forall y. exists x. y = f x; f enters at depth 2.
    let y = view.tm(Tm::Bv(1))?;
    let x = view.tm(Tm::Bv(0))?;
    let image = view.tm(Tm::App(f2, x))?;
    let onto_body = view.tm(Tm::Eq(y, image))?;
    let onto = forall(
        ind,
        view.tm(Tm::Lam(
            ind,
            exists(ind, view.tm(Tm::Lam(ind, onto_body))?)?,
        ))?,
    )?;

    // INF = exists f : ind -> ind. one_one f /\ not (onto f).
    let body = conj(one_one, not(onto)?)?;
    exists(ind_to_ind, view.tm(Tm::Lam(ind_to_ind, body))?)
}

#[cfg(test)]
mod tests {
    use super::super::{AllowAll, Hol};
    use super::*;
    use crate::Connection;

    fn open() -> Connection<Hol<AllowAll>> {
        Connection::open_hol_in_memory(AllowAll).expect("open kernel-state database")
    }

    #[test]
    fn beta_transports_truth_through_eq_mp() {
        // |- (\x:bool. x) true = true, then EQ_MP carries |- true across
        // the symmetric equality: the conversions-are-theorems pipeline.
        let connection = open();
        let hol = connection.view();
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        let body = hol.tm(Tm::Bv(0)).expect("bv0");
        let identity = hol.tm(Tm::Lam(bool_ty, body)).expect("identity");
        let truth = hol.tm(Tm::Bool(true)).expect("true");
        let beta = hol
            .proof_step(Beta {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
                lam: identity,
                arg: truth,
            })
            .expect("beta");
        let truth_thm = hol
            .proof_step(Truth {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
            })
            .expect("truth");
        let symmetric = hol.proof_step(Sym { premise: beta }).expect("sym");
        let transported = hol
            .proof_step(EqMp {
                equality: symmetric,
                premise: truth_thm,
            })
            .expect("eq_mp");
        let (_, _, hyps, concl) = hol.theorem(transported).expect("parts");
        assert_eq!(hyps, hol.empty_hyps());
        let redex = hol.tm(Tm::App(identity, truth)).expect("redex");
        assert_eq!(concl, redex);
    }

    #[test]
    fn proof_steps_are_idempotent_at_the_fact_layer() {
        let connection = open();
        let hol = connection.view();
        let first = hol
            .proof_step(Truth {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
            })
            .expect("first");
        let second = hol
            .proof_step(Truth {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
            })
            .expect("second");
        assert_eq!(first.raw(), second.raw());
    }

    #[test]
    fn assume_weaken_and_deduct_antisym_manage_hypotheses() {
        let connection = open();
        let hol = connection.view();
        let p = hol.tm(Tm::Bool(true)).expect("p");
        let q = hol.tm(Tm::Bool(false)).expect("q");
        let assume_p = hol
            .proof_step(Assume {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
                prop: p,
            })
            .expect("assume p");
        let weakened = hol
            .proof_step(WeakenHyp {
                thm: assume_p,
                prop: q,
            })
            .expect("weaken");
        let (_, _, hyps, _) = hol.theorem(weakened).expect("parts");
        assert_eq!(hol.hyps_entries(hyps).expect("entries").len(), 2);

        let assume_q = hol
            .proof_step(Assume {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
                prop: q,
            })
            .expect("assume q");
        // DEDUCT_ANTISYM: {p} |- p and {q} |- q gives {} |- ... after
        // discharging each other's conclusion? Here hypotheses do not
        // match conclusions crosswise, so both survive minus the
        // crosswise removals.
        let antisym = hol
            .proof_step(DeductAntisym {
                left: assume_p,
                right: assume_q,
            })
            .expect("deduct");
        let (_, _, hyps, concl) = hol.theorem(antisym).expect("parts");
        // left hyps {p} minus right concl q = {p}; right hyps {q} minus
        // left concl p = {q}: both remain.
        assert_eq!(hol.hyps_entries(hyps).expect("entries").len(), 2);
        assert_eq!(hol.tm_node(concl).expect("node"), Tm::Eq(p, q));
    }

    #[test]
    fn abs_discharges_only_unused_hypotheses() {
        let connection = open();
        let hol = connection.view();
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        let vars = hol.vars(&[bool_ty]).expect("vars");
        let variable = hol.tm(Tm::Bv(0)).expect("bv0");
        let reflexive = hol
            .proof_step(Refl {
                kinds: hol.empty_kinds(),
                vars,
                term: variable,
            })
            .expect("refl under binder");
        let lambda_eq = hol.proof_step(Abs { premise: reflexive }).expect("abs");
        let (_, out_vars, _, concl) = hol.theorem(lambda_eq).expect("parts");
        assert_eq!(out_vars, hol.empty_vars());
        let identity = hol.tm(Tm::Lam(bool_ty, variable)).expect("identity");
        assert_eq!(
            hol.tm_node(concl).expect("node"),
            Tm::Eq(identity, identity)
        );

        // A hypothesis mentioning the variable blocks ABS.
        let hyp = hol.tm(Tm::Eq(variable, variable)).expect("var hyp");
        let assumed = hol
            .proof_step(Assume {
                kinds: hol.empty_kinds(),
                vars,
                prop: hyp,
            })
            .expect("assume");
        let under = hol
            .proof_step(WeakenHyp {
                thm: reflexive,
                prop: hyp,
            })
            .expect("weaken");
        let _ = assumed;
        assert!(matches!(
            hol.proof_step(Abs { premise: under }),
            Err(HolError::HypothesisNotStrengthenable)
        ));
    }

    #[test]
    fn instantiation_substitutes_terms_and_types() {
        let connection = open();
        let hol = connection.view();
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        let vars = hol.vars(&[bool_ty]).expect("vars");
        let variable = hol.tm(Tm::Bv(0)).expect("bv0");
        let schematic = hol
            .proof_step(Refl {
                kinds: hol.empty_kinds(),
                vars,
                term: variable,
            })
            .expect("schematic");
        let truth = hol.tm(Tm::Bool(true)).expect("true");
        let instantiated = hol
            .proof_step(InstTm {
                thm: schematic,
                vars: hol.empty_vars(),
                values: vec![truth],
            })
            .expect("instantiate");
        let (_, out_vars, _, concl) = hol.theorem(instantiated).expect("parts");
        assert_eq!(out_vars, hol.empty_vars());
        assert_eq!(hol.tm_node(concl).expect("node"), Tm::Eq(truth, truth));

        let star = hol.kind(Kind::Star).expect("star");
        let kinds = hol.kinds(&[star]).expect("kinds");
        let tyvar = hol.ty(Ty::Bv(0)).expect("tyvar");
        let poly_vars = hol.vars(&[tyvar]).expect("poly vars");
        let poly = hol
            .proof_step(Refl {
                kinds,
                vars: poly_vars,
                term: variable,
            })
            .expect("poly refl");
        let mono = hol
            .proof_step(InstTy {
                thm: poly,
                kinds: hol.empty_kinds(),
                values: vec![bool_ty],
            })
            .expect("inst type");
        let (out_kinds, out_vars, _, _) = hol.theorem(mono).expect("parts");
        assert_eq!(out_kinds, hol.empty_kinds());
        assert_eq!(hol.vars_entries(out_vars).expect("entries"), vec![bool_ty]);
    }

    #[test]
    fn choice_selects_and_subtypes_round_trip() {
        let connection = open();
        let hol = connection.view();
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        // p := \x:bool. x ; |- p true via BETA + SYM + EQ_MP on |- true.
        let body = hol.tm(Tm::Bv(0)).expect("bv0");
        let predicate = hol.tm(Tm::Lam(bool_ty, body)).expect("predicate");
        let truth = hol.tm(Tm::Bool(true)).expect("true");
        let beta = hol
            .proof_step(Beta {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
                lam: predicate,
                arg: truth,
            })
            .expect("beta");
        let truth_thm = hol
            .proof_step(Truth {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
            })
            .expect("truth");
        let symmetric = hol.proof_step(Sym { premise: beta }).expect("sym");
        let applied = hol
            .proof_step(EqMp {
                equality: symmetric,
                premise: truth_thm,
            })
            .expect("p true");
        let chosen = hol.proof_step(Choice { premise: applied }).expect("choice");
        let (.., concl) = hol.theorem(chosen).expect("parts");
        let epsilon = hol.tm(Tm::Eps(predicate)).expect("eps");
        assert_eq!(
            hol.tm_node(concl).expect("node"),
            Tm::App(predicate, epsilon)
        );

        // REP_ABS: |- p[true] gives the representation equation.
        let bv_pred = hol.tm(Tm::Bv(0)).expect("subtype predicate");
        let sat = applied;
        // p[x] for pred BV0 and value true is APP-free: open(BV0, true) =
        // true, and |- true is exactly the premise required.
        let rep_abs = hol
            .proof_step(RepAbs {
                premise: truth_thm,
                pred: bv_pred,
                value: truth,
            })
            .expect("rep_abs");
        let (.., concl) = hol.theorem(rep_abs).expect("parts");
        let abs = hol.tm(Tm::Abs(bv_pred, truth)).expect("abs");
        let rep = hol.tm(Tm::Rep(bv_pred, abs)).expect("rep");
        assert_eq!(hol.tm_node(concl).expect("node"), Tm::Eq(rep, truth));
        let _ = sat;
    }

    #[test]
    fn infinity_is_closed_boolean_and_stable() {
        let connection = open();
        let hol = connection.view();
        let first = hol.proof_step(Infinity).expect("infinity");
        let second = hol.proof_step(Infinity).expect("again");
        assert_eq!(first.raw(), second.raw());
        let (kinds, vars, hyps, concl) = hol.theorem(first).expect("parts");
        assert_eq!(kinds, hol.empty_kinds());
        assert_eq!(vars, hol.empty_vars());
        assert_eq!(hyps, hol.empty_hyps());
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        assert_eq!(
            hol.type_of(hol.empty_kinds(), hol.empty_vars(), concl)
                .expect("type"),
            bool_ty
        );
    }

    #[test]
    fn eq_former_congruence_derives_from_the_wrapper_trick() {
        // EPS congruence via \q. EPS q: MK_COMB + BETA + SYM + TRANS —
        // the derivation that justifies keeping former congruences out
        // of the primitive set.
        let connection = open();
        let hol = connection.view();
        let bool_ty = hol.ty(Ty::Bool).expect("bool");
        let pred_ty = hol.ty(Ty::Arr(bool_ty, bool_ty)).expect("bool->bool");
        let id_body = hol.tm(Tm::Bv(0)).expect("bv0");
        let p1 = hol.tm(Tm::Lam(bool_ty, id_body)).expect("p1 = id");
        // p2 = \x. (\y. y) x, eta-expanded id; equal to p1 by BETA-based
        // reasoning; here we take p1 = p2 from ETA directly.
        let inner = hol
            .tm(Tm::App(hol.tm(Tm::Bv(1)).expect("bv1"), id_body))
            .expect("app");
        let _ = inner;
        let eta = hol
            .proof_step(Eta {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
                function: p1,
            })
            .expect("eta");
        // eta: |- (\x. p1' x) = p1. Wrap with F := \q. EPS q.
        let wrapper_body = hol.tm(Tm::Eps(id_body)).expect("eps bv0");
        let wrapper = hol.tm(Tm::Lam(pred_ty, wrapper_body)).expect("wrapper");
        let wrapper_eq = hol
            .proof_step(Refl {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
                term: wrapper,
            })
            .expect("refl wrapper");
        let combined = hol
            .proof_step(MkComb {
                function: wrapper_eq,
                argument: eta,
            })
            .expect("mk_comb");
        // BETA both sides and chain: EPS (\x. p1' x) = EPS p1.
        let (.., combined_concl) = hol.theorem(combined).expect("parts");
        let (left_app, right_app) = match hol.tm_node(combined_concl).expect("node") {
            Tm::Eq(left, right) => (left, right),
            other => panic!("unexpected conclusion {other:?}"),
        };
        let Tm::App(_, eta_expansion) = hol.tm_node(left_app).expect("left") else {
            panic!("expected application");
        };
        let beta_left = hol
            .proof_step(Beta {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
                lam: wrapper,
                arg: eta_expansion,
            })
            .expect("beta left");
        let beta_right = hol
            .proof_step(Beta {
                kinds: hol.empty_kinds(),
                vars: hol.empty_vars(),
                lam: wrapper,
                arg: p1,
            })
            .expect("beta right");
        let left_sym = hol.proof_step(Sym { premise: beta_left }).expect("sym");
        let chain = hol
            .proof_step(Trans {
                left: left_sym,
                right: combined,
            })
            .expect("trans 1");
        let full = hol
            .proof_step(Trans {
                left: chain,
                right: beta_right,
            })
            .expect("trans 2");
        let (.., concl) = hol.theorem(full).expect("parts");
        let eps_left = hol.tm(Tm::Eps(eta_expansion)).expect("eps lhs");
        let eps_right = hol.tm(Tm::Eps(p1)).expect("eps rhs");
        assert_eq!(
            hol.tm_node(concl).expect("node"),
            Tm::Eq(eps_left, eps_right)
        );
        let _ = right_app;
    }
}
