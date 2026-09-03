//! Primitive-recursive natural arithmetic assembled outside the TCB.
//!
//! Addition and multiplication are closed function-valued recursors.  This
//! avoids ambient parameters and leaves the kernel to check only ordinary HOL
//! construction, conversion, equality, and universal rules.

use covalence_logic_hol::{Kernel, Lit, Ref, SynFactId, SynRel, Tag, ThmId, TmTag, builtin::Op2};

use crate::{
    NaturalError, NaturalInduction, NaturalNameSupply, NaturalRecExt, NaturalRecSchemas,
    NaturalRecursor, NaturalRecursorDecl, NaturalRecursorProof, Naturals, equality_symmetry,
    equality_transitivity, forall_elim, join_same_syntax, substitute,
};

/// Stable natural-arithmetic definitions and law statements.
///
/// This descriptor contains syntax references only. It can therefore be
/// remapped into a projected init slice without carrying theorem-slot identity
/// from the kernel in which the package was first proved.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalArithmeticDecl {
    /// First name reserved for arithmetic's temporary binders.
    pub base_name: u64,
    /// Private recursion package from which addition is selected.
    pub add_rec: NaturalRecursorDecl,
    /// Addition, with its recursive argument first.
    pub add: Ref,
    /// `∀m. add zero m = m`.
    pub add_zero: Ref,
    /// `∀n m. add (succ n) m = succ (add n m)`.
    pub add_successor: Ref,
    /// `∀n. add n zero = n`.
    pub add_right_zero: Ref,
    /// `∀m n. add n (succ m) = succ (add n m)`.
    pub add_right_successor: Ref,
    /// `∀m n. add n m = add m n`.
    pub add_commutative: Ref,
    /// Private recursion package from which multiplication is selected.
    pub mul_rec: NaturalRecursorDecl,
    /// Multiplication, with its recursive argument first.
    pub mul: Ref,
    /// `∀m. mul zero m = zero`.
    pub mul_zero: Ref,
    /// `∀n m. mul (succ n) m = add (mul n m) m`.
    pub mul_successor: Ref,
    /// `succ zero`.
    pub one: Ref,
    /// `succ one`.
    pub two: Ref,
    /// `add one one = two`.
    pub one_plus_one: Ref,
}

impl NaturalArithmeticDecl {
    /// Iterates every public and private syntax reference needed for replay.
    pub fn references(&self) -> impl Iterator<Item = Ref> + '_ {
        self.add_rec
            .references()
            .chain(self.mul_rec.references())
            .chain(self.symbols().map(|(_, reference)| reference))
    }

    /// Resolves one stable external name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Ref> {
        self.symbols()
            .find_map(|(candidate, reference)| (candidate == name).then_some(reference))
    }

    /// Iterates the external arithmetic dictionary.
    #[must_use]
    pub fn symbols(&self) -> impl ExactSizeIterator<Item = (&'static str, Ref)> {
        [
            ("nat.add", self.add),
            ("nat.add.zero", self.add_zero),
            ("nat.add.successor", self.add_successor),
            ("nat.add.right_zero", self.add_right_zero),
            ("nat.add.right_successor", self.add_right_successor),
            ("nat.add.commutative", self.add_commutative),
            ("nat.mul", self.mul),
            ("nat.mul.zero", self.mul_zero),
            ("nat.mul.successor", self.mul_successor),
            ("nat.one", self.one),
            ("nat.two", self.two),
            ("nat.one_plus_one", self.one_plus_one),
        ]
        .into_iter()
    }

    /// Remaps every syntax reference while preserving the package shape.
    ///
    /// # Errors
    ///
    /// Returns the first error produced by `map`.
    pub fn try_map<E>(self, mut map: impl FnMut(Ref) -> Result<Ref, E>) -> Result<Self, E> {
        Ok(Self {
            base_name: self.base_name,
            add_rec: self.add_rec.try_map(&mut map)?,
            add: map(self.add)?,
            add_zero: map(self.add_zero)?,
            add_successor: map(self.add_successor)?,
            add_right_zero: map(self.add_right_zero)?,
            add_right_successor: map(self.add_right_successor)?,
            add_commutative: map(self.add_commutative)?,
            mul_rec: self.mul_rec.try_map(&mut map)?,
            mul: map(self.mul)?,
            mul_zero: map(self.mul_zero)?,
            mul_successor: map(self.mul_successor)?,
            one: map(self.one)?,
            two: map(self.two)?,
            one_plus_one: map(self.one_plus_one)?,
        })
    }
}

/// Exact theorem handles certifying a [`NaturalArithmeticDecl`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalArithmeticProof {
    /// Exact theorem handles for the addition recursor package.
    pub add_rec: NaturalRecursorProof,
    /// Exact theorem `⊢ add_zero`.
    pub add_zero: ThmId,
    /// Exact theorem `⊢ add_successor`.
    pub add_successor: ThmId,
    /// Exact theorem `⊢ add_right_zero`.
    pub add_right_zero: ThmId,
    /// Exact theorem `⊢ add_right_successor`.
    pub add_right_successor: ThmId,
    /// Exact theorem `⊢ add_commutative`.
    pub add_commutative: ThmId,
    /// Exact theorem handles for the multiplication recursor package.
    pub mul_rec: NaturalRecursorProof,
    /// Exact theorem `⊢ mul_zero`.
    pub mul_zero: ThmId,
    /// Exact theorem `⊢ mul_successor`.
    pub mul_successor: ThmId,
    /// Exact theorem `⊢ add one one = two`.
    pub one_plus_one: ThmId,
}

/// A natural-arithmetic declaration certified in one checked kernel.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalArithmetic {
    /// Stable definitions and theorem statements.
    pub declaration: NaturalArithmeticDecl,
    /// Kernel-local exact theorem handles.
    pub proof: NaturalArithmeticProof,
}

struct Addition {
    recursor: NaturalRecursor,
    function: Ref,
    zero: Ref,
    zero_theorem: ThmId,
    successor: Ref,
    successor_theorem: ThmId,
}

struct Multiplication {
    recursor: NaturalRecursor,
    function: Ref,
    zero: Ref,
    zero_theorem: ThmId,
    successor: Ref,
    successor_theorem: ThmId,
}

impl NaturalArithmetic {
    /// Resolves one stable external name in the declaration.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<Ref> {
        self.declaration.get(name)
    }

    /// Iterates the declaration's external dictionary.
    #[must_use]
    pub fn symbols(&self) -> impl ExactSizeIterator<Item = (&'static str, Ref)> {
        self.declaration.symbols()
    }
}

/// Userspace derivation of primitive-recursive natural arithmetic.
pub trait NaturalArithmeticExt {
    /// Constructs closed addition and multiplication recursors and proves
    /// their defining equations and `1 + 1 = 2`.
    ///
    /// # Errors
    ///
    /// Returns an error if a supplied schema has the wrong checked shape or
    /// any ordinary kernel operation rejects the derivation.
    fn natural_arithmetic(
        &mut self,
        naturals: &Naturals,
        schemas: NaturalRecSchemas,
    ) -> Result<NaturalArithmetic, NaturalError>;

    /// Constructs arithmetic using an explicit hygienic temporary-name block.
    ///
    /// # Errors
    ///
    /// Returns an error under the same conditions as [`natural_arithmetic`](Self::natural_arithmetic),
    /// or when `base_name` is not above every name reachable from the inputs.
    fn natural_arithmetic_at(
        &mut self,
        naturals: &Naturals,
        schemas: NaturalRecSchemas,
        base_name: u64,
    ) -> Result<NaturalArithmetic, NaturalError>;
}

impl NaturalArithmeticExt for Kernel {
    fn natural_arithmetic(
        &mut self,
        naturals: &Naturals,
        schemas: NaturalRecSchemas,
    ) -> Result<NaturalArithmetic, NaturalError> {
        let base_name = next_global_name(self)?;
        self.natural_arithmetic_at(naturals, schemas, base_name)
    }

    fn natural_arithmetic_at(
        &mut self,
        naturals: &Naturals,
        schemas: NaturalRecSchemas,
        base_name: u64,
    ) -> Result<NaturalArithmetic, NaturalError> {
        let minimum = self.fresh_name(
            &naturals
                .declaration
                .references()
                .chain(schemas.references())
                .collect::<Vec<_>>(),
        )?;
        if base_name < minimum {
            return Err(NaturalError::WrongForm {
                expected: "a hygienic arithmetic binder-name block",
            });
        }
        let mut names = NaturalNameSupply::new(base_name);
        let bool_ty = self.classifier(naturals.zero_ne_succ)?;
        let function_ty = self.classifier(naturals.succ)?;
        let add = derive_addition(self, &mut names, naturals, schemas, function_ty)?;
        let mul = derive_multiplication(
            self,
            &mut names,
            naturals,
            schemas,
            function_ty,
            add.function,
        )?;

        let (one, two, one_plus_one, one_plus_one_theorem) = prove_one_plus_one(
            self,
            naturals,
            bool_ty,
            add.function,
            add.zero_theorem,
            add.successor_theorem,
        )?;
        let (add_right_zero, add_right_zero_theorem) = prove_add_right_zero(
            self,
            &mut names,
            naturals,
            bool_ty,
            add.function,
            add.zero_theorem,
            add.successor_theorem,
        )?;
        let (add_right_successor, add_right_successor_theorem) = prove_add_right_successor(
            self,
            &mut names,
            naturals,
            bool_ty,
            add.function,
            add.zero_theorem,
            add.successor_theorem,
        )?;
        let (add_commutative, add_commutative_theorem) = prove_add_commutative(
            self,
            &mut names,
            naturals,
            bool_ty,
            &add,
            add_right_zero_theorem,
            add_right_successor_theorem,
        )?;

        Ok(NaturalArithmetic {
            declaration: NaturalArithmeticDecl {
                base_name,
                add_rec: add.recursor.declaration(),
                add: add.function,
                add_zero: add.zero,
                add_successor: add.successor,
                add_right_zero,
                add_right_successor,
                add_commutative,
                mul_rec: mul.recursor.declaration(),
                mul: mul.function,
                mul_zero: mul.zero,
                mul_successor: mul.successor,
                one,
                two,
                one_plus_one,
            },
            proof: NaturalArithmeticProof {
                add_rec: add.recursor.proof(),
                add_zero: add.zero_theorem,
                add_successor: add.successor_theorem,
                add_right_zero: add_right_zero_theorem,
                add_right_successor: add_right_successor_theorem,
                add_commutative: add_commutative_theorem,
                mul_rec: mul.recursor.proof(),
                mul_zero: mul.zero_theorem,
                mul_successor: mul.successor_theorem,
                one_plus_one: one_plus_one_theorem,
            },
        })
    }
}

fn derive_addition(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    schemas: NaturalRecSchemas,
    function_ty: Ref,
) -> Result<Addition, NaturalError> {
    let argument = names.variable(kernel, naturals.ty)?;
    let base = kernel.lam(argument, argument)?;
    let step = successor_step(kernel, names, naturals)?;
    let recursor = kernel.natural_rec_from_schemata_with_names(
        names,
        naturals,
        schemas,
        function_ty,
        base,
        step,
    )?;
    let function = recursor.graph.rec;
    let (zero, zero_theorem) =
        pointwise_zero(kernel, names, naturals, &recursor, |_, value| Ok(value))?;
    let (successor, successor_theorem) = pointwise_successor(
        kernel,
        names,
        naturals,
        &recursor,
        |kernel, recursive, value| {
            let previous = kernel.app(recursive, value)?;
            Ok(kernel.app(naturals.succ, previous)?)
        },
        &[naturals.succ],
    )?;
    Ok(Addition {
        recursor,
        function,
        zero,
        zero_theorem,
        successor,
        successor_theorem,
    })
}

fn derive_multiplication(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    schemas: NaturalRecSchemas,
    function_ty: Ref,
    add: Ref,
) -> Result<Multiplication, NaturalError> {
    let add_type = kernel.classifier(add)?;
    let add_parameter = names.variable(kernel, add_type)?;
    let argument = names.variable(kernel, naturals.ty)?;
    let base = kernel.lam(argument, naturals.zero)?;
    let step = multiplication_step(kernel, names, naturals, add_parameter)?;
    let recursor = kernel.natural_rec_from_schemata_with_names(
        names,
        naturals,
        schemas,
        function_ty,
        base,
        step,
    )?;
    let (_, raw_zero_theorem) =
        pointwise_zero(kernel, names, naturals, &recursor, |_, _| Ok(naturals.zero))?;
    let (_, raw_successor_theorem) = pointwise_successor(
        kernel,
        names,
        naturals,
        &recursor,
        |kernel, recursive, value| {
            let previous = kernel.app(recursive, value)?;
            apply2(kernel, add_parameter, previous, value)
        },
        &[add_parameter],
    )?;
    let generalized_zero = kernel.forall_intro(raw_zero_theorem, add_parameter)?;
    let specialized_zero = forall_elim(kernel, generalized_zero.theorem, add)?;
    let (function, zero, zero_theorem) =
        specialize_mul_zero(kernel, names, naturals, specialized_zero.theorem)?;
    let generalized_successor = kernel.forall_intro(raw_successor_theorem, add_parameter)?;
    let specialized_successor = forall_elim(kernel, generalized_successor.theorem, add)?;
    let (successor, successor_theorem) = specialize_mul_successor(
        kernel,
        names,
        naturals,
        specialized_successor.theorem,
        function,
        add,
    )?;
    Ok(Multiplication {
        recursor,
        function,
        zero,
        zero_theorem,
        successor,
        successor_theorem,
    })
}

fn prove_one_plus_one(
    kernel: &mut Kernel,
    naturals: &Naturals,
    bool_ty: Ref,
    add: Ref,
    add_zero_theorem: ThmId,
    add_successor_theorem: ThmId,
) -> Result<(Ref, Ref, Ref, ThmId), NaturalError> {
    let one = kernel.app(naturals.succ, naturals.zero)?;
    let two = kernel.app(naturals.succ, one)?;
    let successor_at_zero = forall_elim(kernel, add_successor_theorem, naturals.zero)?;
    let successor_at_one = forall_elim(kernel, successor_at_zero.theorem, one)?;
    let zero_at_one = forall_elim(kernel, add_zero_theorem, one)?;
    let lifted_zero = kernel.ap_term(zero_at_one.theorem, naturals.succ)?;
    let successor_equality = sole_conclusion(kernel, successor_at_one.theorem)?;
    let [successor_domain, _successor_left, middle] = exact_equality(kernel, successor_equality)?;
    let lifted_equality = sole_conclusion(kernel, lifted_zero.theorem)?;
    let [_lifted_domain, lifted_left, lifted_right] = exact_equality(kernel, lifted_equality)?;
    let middle_fact = join_same_syntax(kernel, lifted_left, middle)?;
    let right_fact = kernel.syn_refl(None, SynRel::Syn, lifted_right)?;
    retarget_equality(
        kernel,
        lifted_zero.theorem,
        Some(successor_domain),
        middle,
        lifted_right,
        middle_fact,
        right_fact,
    )?;
    let proof = equality_transitivity(
        // Keep this derivation intentionally explicit: the equality helper
        // requires literal agreement at the shared endpoint.
        kernel,
        bool_ty,
        successor_at_one.theorem,
        lifted_zero.theorem,
    )?;
    let left = apply2(kernel, add, one, one)?;
    let proposition = kernel.eq(bool_ty, left, two)?;
    join_same_syntax(kernel, proof.equality, proposition)?;
    kernel.convert_conclusions(proof.theorem, proof.equality, proposition)?;
    Ok((one, two, proposition, proof.theorem))
}

fn prove_add_right_zero(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    bool_ty: Ref,
    add: Ref,
    add_zero_theorem: ThmId,
    add_successor_theorem: ThmId,
) -> Result<(Ref, ThmId), NaturalError> {
    let natural = names.variable(kernel, naturals.ty)?;
    let left = apply2(kernel, add, natural, naturals.zero)?;
    let body = kernel.eq(bool_ty, left, natural)?;
    let induction = prove_by_induction(
        kernel,
        naturals,
        natural,
        body,
        // 0 + 0 = 0.
        |kernel| Ok(forall_elim(kernel, add_zero_theorem, naturals.zero)?.theorem),
        // succ n + 0 = succ (n + 0) = succ n.
        |kernel, hypothesis| {
            let lifted = kernel.ap_term(hypothesis, naturals.succ)?;
            let at_natural = forall_elim(kernel, add_successor_theorem, natural)?;
            let at_zero = forall_elim(kernel, at_natural.theorem, naturals.zero)?;
            Ok(equality_transitivity(kernel, bool_ty, at_zero.theorem, lifted.theorem)?.theorem)
        },
    )?;
    Ok((induction.universal, induction.theorem))
}

fn prove_add_right_successor(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    bool_ty: Ref,
    add: Ref,
    add_zero_theorem: ThmId,
    add_successor_theorem: ThmId,
) -> Result<(Ref, ThmId), NaturalError> {
    let parameter = names.variable(kernel, naturals.ty)?;
    let natural = names.variable(kernel, naturals.ty)?;
    let next_parameter = kernel.app(naturals.succ, parameter)?;
    let left = apply2(kernel, add, natural, next_parameter)?;
    let at_parameter = apply2(kernel, add, natural, parameter)?;
    let right = kernel.app(naturals.succ, at_parameter)?;
    let body = kernel.eq(bool_ty, left, right)?;
    let induction = prove_by_induction(
        kernel,
        naturals,
        natural,
        body,
        // 0 + succ m = succ m = succ (0 + m).
        |kernel| {
            let at_next = forall_elim(kernel, add_zero_theorem, next_parameter)?;
            let at_parameter = forall_elim(kernel, add_zero_theorem, parameter)?;
            let lifted = kernel.ap_term(at_parameter.theorem, naturals.succ)?;
            let reversed = equality_symmetry(kernel, bool_ty, lifted.theorem)?;
            Ok(equality_transitivity(kernel, bool_ty, at_next.theorem, reversed.theorem)?.theorem)
        },
        // succ n + succ m = succ (n + succ m) = succ (succ (n + m)) = succ (succ n + m).
        |kernel, hypothesis| {
            let lifted = kernel.ap_term(hypothesis, naturals.succ)?;
            let at_natural = forall_elim(kernel, add_successor_theorem, natural)?;
            let at_next = forall_elim(kernel, at_natural.theorem, next_parameter)?;
            let first = equality_transitivity(kernel, bool_ty, at_next.theorem, lifted.theorem)?;
            let at_parameter = forall_elim(kernel, at_natural.theorem, parameter)?;
            let lifted_law = kernel.ap_term(at_parameter.theorem, naturals.succ)?;
            let reversed = equality_symmetry(kernel, bool_ty, lifted_law.theorem)?;
            Ok(equality_transitivity(kernel, bool_ty, first.theorem, reversed.theorem)?.theorem)
        },
    )?;
    let generalized = kernel.forall_intro(induction.theorem, parameter)?;
    Ok((generalized.universal, generalized.theorem))
}

fn prove_add_commutative(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    bool_ty: Ref,
    add: &Addition,
    add_right_zero_theorem: ThmId,
    add_right_successor_theorem: ThmId,
) -> Result<(Ref, ThmId), NaturalError> {
    let parameter = names.variable(kernel, naturals.ty)?;
    let natural = names.variable(kernel, naturals.ty)?;
    let left = apply2(kernel, add.function, natural, parameter)?;
    let right = apply2(kernel, add.function, parameter, natural)?;
    let body = kernel.eq(bool_ty, left, right)?;
    let opaque = [add.function, naturals.succ];
    let induction = prove_by_induction(
        kernel,
        naturals,
        natural,
        body,
        // 0 + m = m = m + 0.
        |kernel| {
            let at_parameter = forall_elim(kernel, add.zero_theorem, parameter)?;
            let (_, right_zero) =
                forall_elim_normalized(kernel, add_right_zero_theorem, parameter, &opaque)?;
            let reversed = equality_symmetry(kernel, bool_ty, right_zero)?;
            Ok(
                equality_transitivity(kernel, bool_ty, at_parameter.theorem, reversed.theorem)?
                    .theorem,
            )
        },
        // succ n + m = succ (n + m) = succ (m + n) = m + succ n.
        |kernel, hypothesis| {
            let lifted = kernel.ap_term(hypothesis, naturals.succ)?;
            let at_natural = forall_elim(kernel, add.successor_theorem, natural)?;
            let at_parameter = forall_elim(kernel, at_natural.theorem, parameter)?;
            let first =
                equality_transitivity(kernel, bool_ty, at_parameter.theorem, lifted.theorem)?;
            let right_successor = forall_elim(kernel, add_right_successor_theorem, natural)?;
            let (_, right_successor) =
                forall_elim_normalized(kernel, right_successor.theorem, parameter, &opaque)?;
            let reversed = equality_symmetry(kernel, bool_ty, right_successor)?;
            Ok(equality_transitivity(kernel, bool_ty, first.theorem, reversed.theorem)?.theorem)
        },
    )?;
    let generalized = kernel.forall_intro(induction.theorem, parameter)?;
    Ok((generalized.universal, generalized.theorem))
}

/// Proves `∀binder. body` by induction on `binder`.
///
/// `base` proves `body` with `binder` replaced by zero. `step` proves it with
/// `binder` replaced by `succ binder`, and is handed the hypothesis theorem
/// `body ⊢ body`. Both may conclude any syntactically equal proposition; this
/// function transports the result onto the exact induction predicate.
pub(crate) fn prove_by_induction(
    kernel: &mut Kernel,
    naturals: &Naturals,
    binder: Ref,
    body: Ref,
    base: impl FnOnce(&mut Kernel) -> Result<ThmId, NaturalError>,
    step: impl FnOnce(&mut Kernel, ThmId) -> Result<ThmId, NaturalError>,
) -> Result<NaturalInduction, NaturalError> {
    let predicate = kernel.lam_at(naturals.predicate_ty(kernel)?, binder, body)?;

    let base_body = substitute(kernel, binder, naturals.zero, body)?.output;
    let at_zero = predicate_application(kernel, binder, predicate, body, naturals.zero, base_body)?;
    let base_theorem = base(kernel)?;
    retarget_conclusion(kernel, base_theorem, base_body)?;
    kernel.convert_conclusions(base_theorem, base_body, at_zero)?;

    let next = kernel.app(naturals.succ, binder)?;
    let step_body = substitute(kernel, binder, next, body)?.output;
    let at_next = predicate_application(kernel, binder, predicate, body, next, step_body)?;
    let hypothesis = kernel.identity(positive(body))?;
    let step_theorem = step(kernel, hypothesis)?;
    retarget_conclusion(kernel, step_theorem, step_body)?;
    kernel.convert_conclusions(step_theorem, step_body, at_next)?;

    let at_binder = predicate_application(kernel, binder, predicate, body, binder, body)?;
    kernel.convert_theorem(step_theorem, body, at_binder)?;
    let implication = kernel.op2(Op2::Imp, at_binder, at_next)?;
    let discharged = kernel.imp_right(step_theorem, positive(implication))?;
    let generalized = kernel.forall_intro(discharged, binder)?;
    naturals.induct(kernel, predicate, base_theorem, generalized.theorem)
}

/// Rewrites a theorem's single conclusion onto a syntactically equal target.
pub(crate) fn retarget_conclusion(
    kernel: &mut Kernel,
    theorem: ThmId,
    target: Ref,
) -> Result<(), NaturalError> {
    let conclusion = sole_conclusion(kernel, theorem)?;
    if conclusion == target {
        return Ok(());
    }
    join_same_syntax(kernel, conclusion, target)?;
    kernel.convert_conclusions(theorem, conclusion, target)?;
    Ok(())
}

fn predicate_application(
    kernel: &mut Kernel,
    binder: Ref,
    predicate: Ref,
    body: Ref,
    argument: Ref,
    target: Ref,
) -> Result<Ref, NaturalError> {
    let application = kernel.app(predicate, argument)?;
    let substitution = substitute(kernel, binder, argument, body)?;
    let beta = kernel.tm_beta_fact(None, application, substitution.fact)?;
    let same = join_same_syntax(kernel, substitution.output, target)?;
    let conversion = kernel.syn_trans(None, beta, same)?;
    kernel.union_syn_fact(conversion)?;
    Ok(application)
}

fn successor_step(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
) -> Result<Ref, NaturalError> {
    let function_ty = kernel.classifier(naturals.succ)?;
    let index = names.variable(kernel, naturals.ty)?;
    let previous = names.variable(kernel, function_ty)?;
    let value = names.variable(kernel, naturals.ty)?;
    let previous_value = kernel.app(previous, value)?;
    let next = kernel.app(naturals.succ, previous_value)?;
    let at_value = kernel.lam(value, next)?;
    let at_previous = kernel.lam(previous, at_value)?;
    Ok(kernel.lam(index, at_previous)?)
}

fn multiplication_step(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    add: Ref,
) -> Result<Ref, NaturalError> {
    let function_ty = kernel.classifier(naturals.succ)?;
    let index = names.variable(kernel, naturals.ty)?;
    let previous = names.variable(kernel, function_ty)?;
    let value = names.variable(kernel, naturals.ty)?;
    let previous_value = kernel.app(previous, value)?;
    let product = apply2(kernel, add, previous_value, value)?;
    let at_value = kernel.lam(value, product)?;
    let at_previous = kernel.lam(previous, at_value)?;
    Ok(kernel.lam(index, at_previous)?)
}

fn specialize_mul_zero(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    theorem: ThmId,
) -> Result<(Ref, Ref, ThmId), NaturalError> {
    let value = names.variable(kernel, naturals.ty)?;
    let specialized = forall_elim(kernel, theorem, value)?;
    let equality = sole_conclusion(kernel, specialized.theorem)?;
    let [_domain, left, right] = exact_equality(kernel, equality)?;
    let [at_zero, argument] = exact_children(kernel, left, Tag::Tm(TmTag::App))?;
    let [mul, zero] = exact_children(kernel, at_zero, Tag::Tm(TmTag::App))?;
    join_same_syntax(kernel, argument, value)?;
    join_same_syntax(kernel, zero, naturals.zero)?;
    join_same_syntax(kernel, right, naturals.zero)?;
    let generalized = kernel.forall_intro(specialized.theorem, value)?;
    Ok((mul, generalized.universal, generalized.theorem))
}

fn specialize_mul_successor(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    theorem: ThmId,
    mul: Ref,
    add: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let index = names.variable(kernel, naturals.ty)?;
    let value = names.variable(kernel, naturals.ty)?;
    let at_index = forall_elim(kernel, theorem, index)?;
    let at_value = forall_elim(kernel, at_index.theorem, value)?;
    let source = sole_conclusion(kernel, at_value.theorem)?;
    let [domain, source_left, source_right] = exact_equality(kernel, source)?;
    let successor = kernel.app(naturals.succ, index)?;
    let target_left = apply2(kernel, mul, successor, value)?;
    let previous = apply2(kernel, mul, index, value)?;
    let target_right = apply2(kernel, add, previous, value)?;
    let left_fact = join_same_syntax(kernel, source_left, target_left)?;
    let right_fact = join_same_syntax(kernel, source_right, target_right)?;
    let theorem = retarget_equality(
        kernel,
        at_value.theorem,
        Some(domain),
        target_left,
        target_right,
        left_fact,
        right_fact,
    )?;
    let at_value = kernel.forall_intro(theorem, value)?;
    let generalized = kernel.forall_intro(at_value.theorem, index)?;
    Ok((generalized.universal, generalized.theorem))
}

pub(crate) fn pointwise_zero(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    recursor: &NaturalRecursor,
    target: impl FnOnce(&mut Kernel, Ref) -> Result<Ref, NaturalError>,
) -> Result<(Ref, ThmId), NaturalError> {
    let value = names.variable(kernel, naturals.ty)?;
    let applied = kernel.ap_thm(recursor.graph.rec_zero_theorem, value)?;
    let (right, right_fact) = normalize_application(kernel, applied.right, &[])?;
    let target_right = target(kernel, value)?;
    let right_fact = bridge_normal_forms(kernel, right, right_fact, target_right, &[])?;
    let left_fact = kernel.syn_refl(None, SynRel::Syn, applied.left)?;
    let theorem = retarget_equality(
        kernel,
        applied.theorem,
        None,
        applied.left,
        target_right,
        left_fact,
        right_fact,
    )?;
    let generalized = kernel.forall_intro(theorem, value)?;
    Ok((generalized.universal, generalized.theorem))
}

pub(crate) fn pointwise_successor(
    kernel: &mut Kernel,
    names: &mut NaturalNameSupply,
    naturals: &Naturals,
    recursor: &NaturalRecursor,
    target: impl FnOnce(&mut Kernel, Ref, Ref) -> Result<Ref, NaturalError>,
    opaque: &[Ref],
) -> Result<(Ref, ThmId), NaturalError> {
    let index = names.variable(kernel, naturals.ty)?;
    let value = names.variable(kernel, naturals.ty)?;
    let specialized = forall_elim(kernel, recursor.graph.rec_successor_theorem, index)?;
    let applied = kernel.ap_thm(specialized.theorem, value)?;
    let (right, right_fact) = normalize_application(kernel, applied.right, opaque)?;
    let recursive = kernel.app(recursor.graph.rec, index)?;
    let target_right = target(kernel, recursive, value)?;
    let right_fact = bridge_normal_forms(kernel, right, right_fact, target_right, opaque)?;
    let left_fact = kernel.syn_refl(None, SynRel::Syn, applied.left)?;
    let theorem = retarget_equality(
        kernel,
        applied.theorem,
        None,
        applied.left,
        target_right,
        left_fact,
        right_fact,
    )?;
    let at_value = kernel.forall_intro(theorem, value)?;
    let generalized = kernel.forall_intro(at_value.theorem, index)?;
    Ok((generalized.universal, generalized.theorem))
}

pub(crate) fn retarget_equality(
    kernel: &mut Kernel,
    theorem: ThmId,
    target_domain: Option<Ref>,
    left: Ref,
    right: Ref,
    left_fact: SynFactId,
    right_fact: SynFactId,
) -> Result<ThmId, NaturalError> {
    let source = sole_conclusion(kernel, theorem)?;
    let [source_domain, source_left, source_right] = exact_equality(kernel, source)?;
    let domain = target_domain.unwrap_or(source_domain);
    let bool_ty = kernel.classifier(source)?;
    let target = kernel.eq_at(bool_ty, domain, left, right)?;
    require_fact(kernel, left_fact, source_left, left)?;
    require_fact(kernel, right_fact, source_right, right)?;
    let domain_fact = join_same_syntax(kernel, source_domain, domain)?;
    let equality_fact = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        source,
        target,
        &[domain_fact, left_fact, right_fact],
    )?;
    kernel.union_syn_fact(equality_fact)?;
    kernel.convert_conclusions(theorem, source, target)?;
    Ok(theorem)
}

pub(crate) fn bridge_normal_forms(
    kernel: &mut Kernel,
    source_normal: Ref,
    source_fact: SynFactId,
    target: Ref,
    opaque: &[Ref],
) -> Result<SynFactId, NaturalError> {
    let (target_normal, target_fact) = normalize_application(kernel, target, opaque)?;
    let middle = join_same_syntax(kernel, source_normal, target_normal)?;
    let source_to_normal = kernel.syn_trans(None, source_fact, middle)?;
    let normal_to_target = kernel.syn_symm(None, target_fact)?;
    let fact = kernel.syn_trans(None, source_to_normal, normal_to_target)?;
    kernel.union_syn_fact(fact)?;
    Ok(fact)
}

pub(crate) fn normalize_application(
    kernel: &mut Kernel,
    input: Ref,
    opaque: &[Ref],
) -> Result<(Ref, SynFactId), NaturalError> {
    if kernel.arena().tag(input) != Some(Tag::Tm(TmTag::App)) {
        return Ok((input, kernel.syn_refl(None, SynRel::Syn, input)?));
    }
    let [function, argument] = exact_children(kernel, input, Tag::Tm(TmTag::App))?;
    let (function, function_fact) = normalize_application(kernel, function, opaque)?;
    let (argument, argument_fact) = normalize_application(kernel, argument, opaque)?;
    let rebuilt = kernel.app(function, argument)?;
    let rebuilt_fact = kernel.syn_congr(
        None,
        SynRel::Conv,
        None,
        None,
        input,
        rebuilt,
        &[function_fact, argument_fact],
    )?;
    kernel.union_syn_fact(rebuilt_fact)?;
    if opaque.contains(&function) || kernel.arena().tag(function) != Some(Tag::Tm(TmTag::Lam)) {
        return Ok((rebuilt, rebuilt_fact));
    }
    let [binder, body] = exact_children(kernel, function, Tag::Tm(TmTag::Lam))?;
    let substitution = crate::substitute(kernel, binder, argument, body)?;
    let beta = kernel.tm_beta_fact(None, rebuilt, substitution.fact)?;
    kernel.union_syn_fact(beta)?;
    let (output, tail) = normalize_application(kernel, substitution.output, opaque)?;
    let head = kernel.syn_trans(None, rebuilt_fact, beta)?;
    let fact = kernel.syn_trans(None, head, tail)?;
    kernel.union_syn_fact(fact)?;
    Ok((output, fact))
}

pub(crate) fn forall_elim_normalized(
    kernel: &mut Kernel,
    theorem: ThmId,
    argument: Ref,
    opaque: &[Ref],
) -> Result<(Ref, ThmId), NaturalError> {
    let specialized = forall_elim(kernel, theorem, argument)?;
    let (normal, _) = normalize_application(kernel, specialized.proposition, opaque)?;
    kernel.convert_conclusions(specialized.theorem, specialized.proposition, normal)?;
    Ok((normal, specialized.theorem))
}

fn require_fact(
    kernel: &Kernel,
    fact: SynFactId,
    input: Ref,
    output: Ref,
) -> Result<(), NaturalError> {
    let fact = kernel.syn_fact(fact)?;
    if fact.input() != input || fact.output() != output {
        return Err(NaturalError::WrongForm {
            expected: "an arithmetic endpoint conversion",
        });
    }
    Ok(())
}

pub(crate) fn sole_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, NaturalError> {
    let theorem = kernel.thm().get(theorem).ok_or(NaturalError::WrongForm {
        expected: "a resident arithmetic theorem",
    })?;
    let mut rows = theorem.rhs.rows();
    let row = rows.next().ok_or(NaturalError::WrongForm {
        expected: "one arithmetic conclusion",
    })?;
    if rows.next().is_some() || row.len() != 1 || !row[0].is_positive() {
        return Err(NaturalError::WrongForm {
            expected: "one positive arithmetic conclusion",
        });
    }
    Ref::new(
        i32::try_from(row[0].magnitude()).map_err(|_| NaturalError::WrongForm {
            expected: "a local arithmetic proposition",
        })?,
    )
    .ok_or(NaturalError::WrongForm {
        expected: "a nonzero arithmetic proposition",
    })
}

pub(crate) fn exact_equality(kernel: &Kernel, equality: Ref) -> Result<[Ref; 3], NaturalError> {
    exact_children(kernel, equality, Tag::Tm(TmTag::Eq))
}

pub(crate) fn exact_children<const N: usize>(
    kernel: &Kernel,
    reference: Ref,
    tag: Tag,
) -> Result<[Ref; N], NaturalError> {
    if kernel.arena().tag(reference) != Some(tag) {
        return Err(NaturalError::WrongForm {
            expected: "the arithmetic schema shape",
        });
    }
    kernel
        .arena()
        .children(reference)
        .ok_or(NaturalError::WrongForm {
            expected: "resident arithmetic syntax",
        })?
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| NaturalError::WrongForm {
            expected: "the arithmetic schema arity",
        })
}

pub(crate) fn next_global_name(kernel: &Kernel) -> Result<u64, NaturalError> {
    let mut greatest = None;
    for raw in 1..=kernel.arena().len() {
        let reference = Ref::new(i32::try_from(raw).map_err(|_| NaturalError::WrongForm {
            expected: "an i32-sized arithmetic arena",
        })?)
        .ok_or(NaturalError::WrongForm {
            expected: "a nonzero arithmetic row",
        })?;
        if let Some(name) = kernel.arena().name(reference) {
            greatest = Some(greatest.map_or(name, |current: u64| current.max(name)));
        }
    }
    greatest
        .unwrap_or(0)
        .checked_add(1)
        .ok_or(NaturalError::WrongForm {
            expected: "an available arithmetic binder name",
        })
}

pub(crate) fn apply2(
    kernel: &mut Kernel,
    function: Ref,
    left: Ref,
    right: Ref,
) -> Result<Ref, NaturalError> {
    let at_left = kernel.app(function, left)?;
    Ok(kernel.app(at_left, right)?)
}

pub(crate) fn positive(reference: Ref) -> Lit {
    Lit::positive(reference.get())
}
