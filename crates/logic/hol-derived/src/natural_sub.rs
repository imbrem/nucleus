//! Predecessor and truncated subtraction for the natural numbers.
//!
//! `nat` has no additive inverse, so subtraction is truncated: `a - b` is zero
//! whenever `b` is at least `a`. Both operations are ordinary primitive
//! recursions over the same recursor machinery as addition and multiplication,
//! and everything here is untrusted userspace.
//!
//! Recursion runs on the subtrahend, so the recursor is `minus b a = a - b`.
//! `sub` wraps it as `λa b. minus b a`, which puts the arguments in the usual
//! order. Only the two equations below mention `minus`; every later proof uses
//! `sub` and never unfolds it.

use covalence_logic_hol::{Kernel, Ref, SynFactId, SynRel, ThmId};

use crate::{
    NaturalArithmetic, NaturalError, NaturalNameSupply, NaturalRecExt, NaturalRecSchemas,
    NaturalRecursor, Naturals,
    natural_arithmetic::{
        apply2, bridge_normal_forms, exact_equality, next_global_name, normalize_application,
        pointwise_successor, pointwise_zero, retarget_equality, sole_conclusion,
    },
    natural_calc::{Calc, Law, on_left, quantify, under},
    natural_ring::NaturalRing,
};

/// Predecessor and subtraction statements.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalSubtractionDecl {
    /// First name reserved for this package's temporary binders.
    pub base_name: u64,
    /// `nat.pred`.
    pub pred: Ref,
    /// `pred 0 = 0`.
    pub pred_zero: Ref,
    /// `∀a. pred (succ a) = a`.
    pub pred_successor: Ref,
    /// `nat.sub`.
    pub sub: Ref,
    /// `∀a. a - 0 = a`.
    pub sub_zero: Ref,
    /// `∀a b. a - succ b = pred (a - b)`.
    pub sub_successor: Ref,
    /// `∀a b. succ a - succ b = a - b`.
    pub sub_successor_both: Ref,
    /// `∀a b. (a + b) - b = a`.
    pub sub_add_cancel: Ref,
}

/// Exact theorem handles certifying a [`NaturalSubtractionDecl`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalSubtractionProof {
    /// Exact theorem `⊢ pred_zero`.
    pub pred_zero: ThmId,
    /// Exact theorem `⊢ pred_successor`.
    pub pred_successor: ThmId,
    /// Exact theorem `⊢ sub_zero`.
    pub sub_zero: ThmId,
    /// Exact theorem `⊢ sub_successor`.
    pub sub_successor: ThmId,
    /// Exact theorem `⊢ sub_successor_both`.
    pub sub_successor_both: ThmId,
    /// Exact theorem `⊢ sub_add_cancel`.
    pub sub_add_cancel: ThmId,
}

/// A subtraction package certified in one checked kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalSubtraction {
    /// Statements.
    pub declaration: NaturalSubtractionDecl,
    /// Kernel-local exact theorem handles.
    pub proof: NaturalSubtractionProof,
}

impl NaturalSubtraction {
    /// Resolves one name to its statement.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Ref> {
        self.symbols()
            .find_map(|(candidate, reference, _)| (candidate == name).then_some(reference))
    }

    /// Resolves one law name to its exact theorem.
    #[must_use]
    pub fn theorem(&self, name: &str) -> Option<ThmId> {
        self.symbols()
            .find_map(|(candidate, _, theorem)| (candidate == name).then_some(theorem))
    }

    /// Iterates every law as `(name, statement, theorem)`.
    #[must_use]
    pub fn symbols(&self) -> impl ExactSizeIterator<Item = (&'static str, Ref, ThmId)> {
        let declaration = self.declaration;
        let proof = self.proof;
        [
            ("nat.pred.zero", declaration.pred_zero, proof.pred_zero),
            (
                "nat.pred.successor",
                declaration.pred_successor,
                proof.pred_successor,
            ),
            ("nat.sub.zero", declaration.sub_zero, proof.sub_zero),
            (
                "nat.sub.successor",
                declaration.sub_successor,
                proof.sub_successor,
            ),
            (
                "nat.sub.successor_both",
                declaration.sub_successor_both,
                proof.sub_successor_both,
            ),
            (
                "nat.sub.add_cancel",
                declaration.sub_add_cancel,
                proof.sub_add_cancel,
            ),
        ]
        .into_iter()
    }
}

/// Userspace derivation of truncated natural subtraction.
pub trait NaturalSubtractionExt {
    /// Builds `pred` and `sub` and proves their equations.
    ///
    /// # Errors
    ///
    /// Returns an error if a supplied schema has the wrong checked shape or any
    /// ordinary kernel operation rejects the derivation.
    fn natural_subtraction(
        &mut self,
        naturals: &Naturals,
        arithmetic: &NaturalArithmetic,
        ring: &NaturalRing,
        schemas: NaturalRecSchemas,
    ) -> Result<NaturalSubtraction, NaturalError>;

    /// Builds subtraction using an explicit binder-name block.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as
    /// [`natural_subtraction`](Self::natural_subtraction), or when `base_name`
    /// is not above every name reachable from the inputs.
    fn natural_subtraction_at(
        &mut self,
        naturals: &Naturals,
        arithmetic: &NaturalArithmetic,
        ring: &NaturalRing,
        schemas: NaturalRecSchemas,
        base_name: u64,
    ) -> Result<NaturalSubtraction, NaturalError>;
}

impl NaturalSubtractionExt for Kernel {
    fn natural_subtraction(
        &mut self,
        naturals: &Naturals,
        arithmetic: &NaturalArithmetic,
        ring: &NaturalRing,
        schemas: NaturalRecSchemas,
    ) -> Result<NaturalSubtraction, NaturalError> {
        let base_name = next_global_name(self)?;
        self.natural_subtraction_at(naturals, arithmetic, ring, schemas, base_name)
    }

    fn natural_subtraction_at(
        &mut self,
        naturals: &Naturals,
        arithmetic: &NaturalArithmetic,
        ring: &NaturalRing,
        schemas: NaturalRecSchemas,
        base_name: u64,
    ) -> Result<NaturalSubtraction, NaturalError> {
        let minimum = self.fresh_name(
            &naturals
                .declaration
                .references()
                .chain(arithmetic.declaration.references())
                .chain(schemas.references())
                .collect::<Vec<_>>(),
        )?;
        if base_name < minimum {
            return Err(NaturalError::WrongForm {
                expected: "a hygienic subtraction binder-name block",
            });
        }
        let mut staged = self.fork();
        let subtraction = derive(&mut staged, naturals, ring, schemas, base_name)?;
        *self = staged;
        Ok(subtraction)
    }
}

fn derive(
    kernel: &mut Kernel,
    naturals: &Naturals,
    ring: &NaturalRing,
    schemas: NaturalRecSchemas,
    base_name: u64,
) -> Result<NaturalSubtraction, NaturalError> {
    let mut names = NaturalNameSupply::new(base_name);
    let signature = ring.signature;
    let zero = signature.zero;

    let predecessor = derive_predecessor(kernel, &mut names, naturals, schemas)?;
    let minus = derive_minus(kernel, &mut names, naturals, schemas, predecessor.function)?;

    // `sub a b` is `minus b a`, so the arguments read in the usual order.
    let minuend = names.variable(kernel, naturals.ty)?;
    let subtrahend = names.variable(kernel, naturals.ty)?;
    let swapped = {
        let at_subtrahend = kernel.app(minus.function, subtrahend)?;
        kernel.app(at_subtrahend, minuend)?
    };
    let at_subtrahend = kernel.lam(subtrahend, swapped)?;
    let sub = kernel.lam(minuend, at_subtrahend)?;

    // Unfolding `sub` is how its two equations are read off `minus`; every
    // later step keeps it folded.
    let unfold = [minus.function, predecessor.function, signature.succ];
    let calc = Calc {
        naturals,
        bool_ty: signature.bool_ty,
        opaque: vec![
            signature.add,
            signature.mul,
            signature.succ,
            sub,
            predecessor.function,
            minus.function,
        ],
    };

    let a = calc.variable(kernel, &mut names)?;
    let b = calc.variable(kernel, &mut names)?;

    let sub_zero = {
        let source = calc.at(kernel, minus.zero_theorem, &[a])?;
        let left = apply2(kernel, sub, a, zero)?;
        let theorem = retarget(kernel, source, left, a, &unfold)?;
        quantify(kernel, theorem, &[a])?
    };
    let sub_successor = {
        let source = calc.at(kernel, minus.successor_theorem, &[b, a])?;
        let next_b = calc.next(kernel, b)?;
        let left = apply2(kernel, sub, a, next_b)?;
        let inner = apply2(kernel, sub, a, b)?;
        let right = kernel.app(predecessor.function, inner)?;
        let theorem = retarget(kernel, source, left, right, &unfold)?;
        quantify(kernel, theorem, &[a, b])?
    };

    let sub_successor_both = prove_sub_successor_both(
        kernel,
        &calc,
        &mut names,
        sub,
        predecessor.function,
        predecessor.successor_theorem,
        sub_zero.1,
        sub_successor.1,
    )?;
    let sub_add_cancel = prove_sub_add_cancel(
        kernel,
        &calc,
        &mut names,
        signature.add,
        sub,
        ring.proof.add_right_zero,
        ring.proof.add_right_successor,
        sub_zero.1,
        sub_successor_both.1,
    )?;

    Ok(NaturalSubtraction {
        declaration: NaturalSubtractionDecl {
            base_name,
            pred: predecessor.function,
            pred_zero: predecessor.zero,
            pred_successor: predecessor.successor,
            sub,
            sub_zero: sub_zero.0,
            sub_successor: sub_successor.0,
            sub_successor_both: sub_successor_both.0,
            sub_add_cancel: sub_add_cancel.0,
        },
        proof: NaturalSubtractionProof {
            pred_zero: predecessor.zero_theorem,
            pred_successor: predecessor.successor_theorem,
            sub_zero: sub_zero.1,
            sub_successor: sub_successor.1,
            sub_successor_both: sub_successor_both.1,
            sub_add_cancel: sub_add_cancel.1,
        },
    })
}

struct Predecessor {
    function: Ref,
    zero: Ref,
    zero_theorem: ThmId,
    successor: Ref,
    successor_theorem: ThmId,
}

struct Minus {
    zero_theorem: ThmId,
    successor_theorem: ThmId,
    function: Ref,
}

/// `pred 0 = 0` and `pred (succ a) = a`, by recursion with codomain `nat`.
fn derive_predecessor(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    schemas: NaturalRecSchemas,
) -> Result<Predecessor, NaturalError> {
    let index = names.variable(kernel, naturals.ty)?;
    let previous = names.variable(kernel, naturals.ty)?;
    let at_previous = kernel.lam(previous, index)?;
    let step = kernel.lam(index, at_previous)?;
    let recursor = kernel.natural_rec_from_schemata_with_names(
        names,
        naturals,
        schemas,
        naturals.ty,
        naturals.zero,
        step,
    )?;

    let value = names.variable(kernel, naturals.ty)?;
    let (successor, successor_theorem) = read_off(kernel, &recursor, value, |_, _| Ok(value))?;
    Ok(Predecessor {
        function: recursor.graph.rec,
        zero: recursor.graph.rec_zero,
        zero_theorem: recursor.graph.rec_zero_theorem,
        successor,
        successor_theorem,
    })
}

/// `minus 0 = λa. a` and `minus (succ b) a = pred (minus b a)`.
fn derive_minus(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    schemas: NaturalRecSchemas,
    pred: Ref,
) -> Result<Minus, NaturalError> {
    let function_ty = kernel.classifier(naturals.succ)?;
    let argument = names.variable(kernel, naturals.ty)?;
    let base = kernel.lam(argument, argument)?;

    let index = names.variable(kernel, naturals.ty)?;
    let previous = names.variable(kernel, function_ty)?;
    let value = names.variable(kernel, naturals.ty)?;
    let applied = kernel.app(previous, value)?;
    let decreased = kernel.app(pred, applied)?;
    let at_value = kernel.lam(value, decreased)?;
    let at_previous = kernel.lam(previous, at_value)?;
    let step = kernel.lam(index, at_previous)?;

    let recursor = kernel.natural_rec_from_schemata_with_names(
        names,
        naturals,
        schemas,
        function_ty,
        base,
        step,
    )?;
    let (_, zero_theorem) =
        pointwise_zero(kernel, names, naturals, &recursor, |_, value| Ok(value))?;
    let (_, successor_theorem) = pointwise_successor(
        kernel,
        names,
        naturals,
        &recursor,
        |kernel, recursive, value| {
            let inner = kernel.app(recursive, value)?;
            Ok(kernel.app(pred, inner)?)
        },
        &[pred],
    )?;
    Ok(Minus {
        zero_theorem,
        successor_theorem,
        function: recursor.graph.rec,
    })
}

/// Reads `rec (succ i) = <target>` off a recursor whose codomain is `nat`.
fn read_off(
    kernel: &mut Kernel,
    recursor: &NaturalRecursor,
    index: Ref,
    target: impl FnOnce(&mut Kernel, Ref) -> Result<Ref, NaturalError>,
) -> Result<(Ref, ThmId), NaturalError> {
    let specialized = crate::forall_elim(kernel, recursor.graph.rec_successor_theorem, index)?;
    let source = sole_conclusion(kernel, specialized.theorem)?;
    let [_, left, right] = exact_equality(kernel, source)?;
    let expected = target(kernel, index)?;
    let (normal, fact) = normalize_application(kernel, right, &[])?;
    let right_fact = bridge_normal_forms(kernel, normal, fact, expected, &[])?;
    let left_fact = kernel.syn_refl(None, SynRel::Syn, left)?;
    let theorem = retarget_equality(
        kernel,
        specialized.theorem,
        None,
        left,
        expected,
        left_fact,
        right_fact,
    )?;
    let generalized = kernel.forall_intro(theorem, index)?;
    Ok((generalized.universal, generalized.theorem))
}

/// Rewrites a proved equality onto endpoints that agree with it after
/// unfolding the definitions in `unfold`.
fn retarget(
    kernel: &mut Kernel,
    theorem: ThmId,
    left: Ref,
    right: Ref,
    unfold: &[Ref],
) -> Result<ThmId, NaturalError> {
    let source = sole_conclusion(kernel, theorem)?;
    let [_, source_left, source_right] = exact_equality(kernel, source)?;
    let left_fact = unfold_bridge(kernel, source_left, left, unfold)?;
    let right_fact = unfold_bridge(kernel, source_right, right, unfold)?;
    retarget_equality(kernel, theorem, None, left, right, left_fact, right_fact)
}

/// Certifies `source ~ target` when the two have the same normal form.
fn unfold_bridge(
    kernel: &mut Kernel,
    source: Ref,
    target: Ref,
    unfold: &[Ref],
) -> Result<SynFactId, NaturalError> {
    let (normal, fact) = normalize_application(kernel, source, unfold)?;
    bridge_normal_forms(kernel, normal, fact, target, unfold)
}

/// `∀a b. succ a - succ b = a - b`, by induction on `b`.
#[allow(clippy::too_many_arguments)]
fn prove_sub_successor_both(
    kernel: &mut Kernel,
    calc: &Calc<'_>,
    names: &mut NaturalNameSupply,
    sub: Ref,
    pred: Ref,
    pred_successor: ThmId,
    sub_zero: ThmId,
    sub_successor: ThmId,
) -> Result<Law, NaturalError> {
    let a = calc.variable(kernel, names)?;
    let b = calc.variable(kernel, names)?;
    let next_a = calc.next(kernel, a)?;
    let next_b = calc.next(kernel, b)?;
    let left = apply2(kernel, sub, next_a, next_b)?;
    let right = apply2(kernel, sub, a, b)?;
    let body = calc.equation(kernel, left, right)?;
    calc.by_induction(
        kernel,
        names,
        b,
        body,
        &[a, b],
        |kernel| {
            let zero = calc.naturals.zero;
            let unfold = calc.at(kernel, sub_successor, &[next_a, zero])?; // pred (succ a - 0)
            let inner = calc.at(kernel, sub_zero, &[next_a])?;
            let folded = under(kernel, pred, inner)?; // pred (succ a)
            let collapse = calc.at(kernel, pred_successor, &[a])?; // a
            let target = calc.at(kernel, sub_zero, &[a])?;
            let target = calc.symm(kernel, target)?; // a - 0
            calc.chain(kernel, &[unfold, folded, collapse, target])
        },
        |kernel, hypothesis| {
            let unfold = calc.at(kernel, sub_successor, &[next_a, next_b])?; // pred (succ a - succ b)
            let rewritten = under(kernel, pred, hypothesis)?; // pred (a - b)
            let target = calc.at(kernel, sub_successor, &[a, b])?;
            let target = calc.symm(kernel, target)?; // a - succ b
            calc.chain(kernel, &[unfold, rewritten, target])
        },
    )
}

/// `∀a b. (a + b) - b = a`, by induction on `b`.
#[allow(clippy::too_many_arguments)]
fn prove_sub_add_cancel(
    kernel: &mut Kernel,
    calc: &Calc<'_>,
    names: &mut NaturalNameSupply,
    add: Ref,
    sub: Ref,
    add_right_zero: ThmId,
    add_right_successor: ThmId,
    sub_zero: ThmId,
    sub_successor_both: ThmId,
) -> Result<Law, NaturalError> {
    let a = calc.variable(kernel, names)?;
    let b = calc.variable(kernel, names)?;
    let sum = apply2(kernel, add, a, b)?;
    let left = apply2(kernel, sub, sum, b)?;
    let body = calc.equation(kernel, left, a)?;
    calc.by_induction(
        kernel,
        names,
        b,
        body,
        &[a, b],
        |kernel| {
            let zero = calc.naturals.zero;
            let with_zero = apply2(kernel, add, a, zero)?;
            let unfold = calc.at(kernel, sub_zero, &[with_zero])?; // a + 0
            let collapse = calc.at(kernel, add_right_zero, &[a])?; // a
            calc.chain(kernel, &[unfold, collapse])
        },
        |kernel, hypothesis| {
            let shift = calc.at(kernel, add_right_successor, &[a, b])?; // succ (a + b)
            let next_b = calc.next(kernel, b)?;
            let folded = on_left(kernel, sub, shift, next_b)?; // succ (a + b) - succ b
            let cancel = calc.at(kernel, sub_successor_both, &[sum, b])?; // (a + b) - b
            calc.chain(kernel, &[folded, cancel, hypothesis])
        },
    )
}
