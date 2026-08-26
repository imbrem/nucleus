//! Primitive-recursive natural arithmetic assembled outside the TCB.
//!
//! Addition and multiplication are closed function-valued recursors.  This
//! avoids ambient parameters and leaves the kernel to check only ordinary HOL
//! construction, conversion, equality, and universal rules.

use covalence_logic_hol::{Kernel, Ref, SynFactId, SynRel, Tag, ThmId, TmTag};

use crate::{
    NaturalError, NaturalRecExt, NaturalRecSchemas, NaturalRecursor, Naturals,
    equality_transitivity, forall_elim, join_same_syntax,
};

/// Checked addition, multiplication, recursion equations, and small numerals.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NaturalArithmetic {
    /// Addition, with its recursive argument first.
    pub add: Ref,
    /// `∀m. add zero m = m`.
    pub add_zero: Ref,
    /// Exact theorem `⊢ add_zero`.
    pub add_zero_theorem: ThmId,
    /// `∀n m. add (succ n) m = succ (add n m)`.
    pub add_successor: Ref,
    /// Exact theorem `⊢ add_successor`.
    pub add_successor_theorem: ThmId,
    /// Multiplication, with its recursive argument first.
    pub mul: Ref,
    /// `∀m. mul zero m = zero`.
    pub mul_zero: Ref,
    /// Exact theorem `⊢ mul_zero`.
    pub mul_zero_theorem: ThmId,
    /// `∀n m. mul (succ n) m = add (mul n m) m`.
    pub mul_successor: Ref,
    /// Exact theorem `⊢ mul_successor`.
    pub mul_successor_theorem: ThmId,
    /// `succ zero`.
    pub one: Ref,
    /// `succ one`.
    pub two: Ref,
    /// `add one one = two`.
    pub one_plus_one: Ref,
    /// Exact theorem `⊢ add one one = two`.
    pub one_plus_one_theorem: ThmId,
}

impl NaturalArithmetic {
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
            ("nat.mul", self.mul),
            ("nat.mul.zero", self.mul_zero),
            ("nat.mul.successor", self.mul_successor),
            ("nat.one", self.one),
            ("nat.two", self.two),
            ("nat.one_plus_one", self.one_plus_one),
        ]
        .into_iter()
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
}

impl NaturalArithmeticExt for Kernel {
    fn natural_arithmetic(
        &mut self,
        naturals: &Naturals,
        schemas: NaturalRecSchemas,
    ) -> Result<NaturalArithmetic, NaturalError> {
        let bool_ty = self.classifier(naturals.zero_ne_succ)?;
        let function_ty = self.classifier(naturals.succ)?;

        let base_argument = fresh_global(self, naturals.ty)?;
        let add_base = self.lam(base_argument, base_argument)?;
        let add_step = successor_step(self, naturals)?;
        let add_rec =
            self.natural_rec_from_schemata(naturals, schemas, function_ty, add_base, add_step)?;
        let add = add_rec.graph.rec;
        let (add_zero, add_zero_theorem) =
            pointwise_zero(self, naturals, &add_rec, |_, value| Ok(value))?;
        let (add_successor, add_successor_theorem) = pointwise_successor(
            self,
            naturals,
            &add_rec,
            |kernel, recursive, value| {
                let previous = kernel.app(recursive, value)?;
                Ok(kernel.app(naturals.succ, previous)?)
            },
            &[naturals.succ],
        )?;
        let add_type = self.classifier(add)?;
        let add_parameter = fresh_global(self, add_type)?;
        let mul_argument = fresh_global(self, naturals.ty)?;
        let mul_base = self.lam(mul_argument, naturals.zero)?;
        let mul_step = multiplication_step(self, naturals, add_parameter)?;
        let mul_rec =
            self.natural_rec_from_schemata(naturals, schemas, function_ty, mul_base, mul_step)?;
        let (raw_mul_zero, raw_mul_zero_theorem) =
            pointwise_zero(self, naturals, &mul_rec, |_, _| Ok(naturals.zero))?;
        let (raw_mul_successor, raw_mul_successor_theorem) = pointwise_successor(
            self,
            naturals,
            &mul_rec,
            |kernel, recursive, value| {
                let previous = kernel.app(recursive, value)?;
                apply2(kernel, add_parameter, previous, value)
            },
            &[add_parameter],
        )?;
        let _ = (raw_mul_zero, raw_mul_successor);
        let generalized_zero = self.forall_intro(raw_mul_zero_theorem, add_parameter)?;
        let specialized_zero = forall_elim(self, generalized_zero.theorem, add)?;
        let (mul, mul_zero, mul_zero_theorem) =
            specialize_mul_zero(self, naturals, specialized_zero.theorem)?;
        let generalized_successor = self.forall_intro(raw_mul_successor_theorem, add_parameter)?;
        let specialized_successor = forall_elim(self, generalized_successor.theorem, add)?;
        let (mul_successor, mul_successor_theorem) =
            specialize_mul_successor(self, naturals, specialized_successor.theorem, mul, add)?;

        let one = self.app(naturals.succ, naturals.zero)?;
        let two = self.app(naturals.succ, one)?;
        let successor_at_zero = forall_elim(self, add_successor_theorem, naturals.zero)?;
        let successor_at_one = forall_elim(self, successor_at_zero.theorem, one)?;
        let zero_at_one = forall_elim(self, add_zero_theorem, one)?;
        let lifted_zero = self.ap_term(zero_at_one.theorem, naturals.succ)?;
        let successor_equality = sole_conclusion(self, successor_at_one.theorem)?;
        let [successor_domain, _successor_left, middle] = exact_equality(self, successor_equality)?;
        let lifted_equality = sole_conclusion(self, lifted_zero.theorem)?;
        let [_lifted_domain, lifted_left, lifted_right] = exact_equality(self, lifted_equality)?;
        let middle_fact = join_same_syntax(self, lifted_left, middle)?;
        let right_fact = self.syn_refl(None, SynRel::Syn, lifted_right)?;
        retarget_equality(
            self,
            lifted_zero.theorem,
            Some(successor_domain),
            middle,
            lifted_right,
            middle_fact,
            right_fact,
        )?;
        let one_plus_one_proof = equality_transitivity(
            // Keep this derivation intentionally explicit: the equality
            // helper requires literal agreement at the shared endpoint.
            self,
            bool_ty,
            successor_at_one.theorem,
            lifted_zero.theorem,
        )?;
        let one_plus_one_left = apply2(self, add, one, one)?;
        let one_plus_one = self.eq(bool_ty, one_plus_one_left, two)?;
        join_same_syntax(self, one_plus_one_proof.equality, one_plus_one)?;
        self.convert_conclusions(
            one_plus_one_proof.theorem,
            one_plus_one_proof.equality,
            one_plus_one,
        )?;

        Ok(NaturalArithmetic {
            add,
            add_zero,
            add_zero_theorem,
            add_successor,
            add_successor_theorem,
            mul,
            mul_zero,
            mul_zero_theorem,
            mul_successor,
            mul_successor_theorem,
            one,
            two,
            one_plus_one,
            one_plus_one_theorem: one_plus_one_proof.theorem,
        })
    }
}

fn successor_step(kernel: &mut Kernel, naturals: &Naturals) -> Result<Ref, NaturalError> {
    let function_ty = kernel.classifier(naturals.succ)?;
    let index = fresh_global(kernel, naturals.ty)?;
    let previous = fresh_global(kernel, function_ty)?;
    let value = fresh_global(kernel, naturals.ty)?;
    let previous_value = kernel.app(previous, value)?;
    let next = kernel.app(naturals.succ, previous_value)?;
    let at_value = kernel.lam(value, next)?;
    let at_previous = kernel.lam(previous, at_value)?;
    Ok(kernel.lam(index, at_previous)?)
}

fn multiplication_step(
    kernel: &mut Kernel,
    naturals: &Naturals,
    add: Ref,
) -> Result<Ref, NaturalError> {
    let function_ty = kernel.classifier(naturals.succ)?;
    let index = fresh_global(kernel, naturals.ty)?;
    let previous = fresh_global(kernel, function_ty)?;
    let value = fresh_global(kernel, naturals.ty)?;
    let previous_value = kernel.app(previous, value)?;
    let product = apply2(kernel, add, previous_value, value)?;
    let at_value = kernel.lam(value, product)?;
    let at_previous = kernel.lam(previous, at_value)?;
    Ok(kernel.lam(index, at_previous)?)
}

fn specialize_mul_zero(
    kernel: &mut Kernel,
    naturals: &Naturals,
    theorem: ThmId,
) -> Result<(Ref, Ref, ThmId), NaturalError> {
    let value = fresh_global(kernel, naturals.ty)?;
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
    naturals: &Naturals,
    theorem: ThmId,
    mul: Ref,
    add: Ref,
) -> Result<(Ref, ThmId), NaturalError> {
    let index = fresh_global(kernel, naturals.ty)?;
    let value = fresh_global(kernel, naturals.ty)?;
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

fn pointwise_zero(
    kernel: &mut Kernel,
    naturals: &Naturals,
    recursor: &NaturalRecursor,
    target: impl FnOnce(&mut Kernel, Ref) -> Result<Ref, NaturalError>,
) -> Result<(Ref, ThmId), NaturalError> {
    let value = fresh_global(kernel, naturals.ty)?;
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

fn pointwise_successor(
    kernel: &mut Kernel,
    naturals: &Naturals,
    recursor: &NaturalRecursor,
    target: impl FnOnce(&mut Kernel, Ref, Ref) -> Result<Ref, NaturalError>,
    opaque: &[Ref],
) -> Result<(Ref, ThmId), NaturalError> {
    let index = fresh_global(kernel, naturals.ty)?;
    let value = fresh_global(kernel, naturals.ty)?;
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

fn retarget_equality(
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

fn bridge_normal_forms(
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

fn normalize_application(
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

fn sole_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, NaturalError> {
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

fn exact_equality(kernel: &Kernel, equality: Ref) -> Result<[Ref; 3], NaturalError> {
    exact_children(kernel, equality, Tag::Tm(TmTag::Eq))
}

fn exact_children<const N: usize>(
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

fn fresh_global(kernel: &mut Kernel, ty: Ref) -> Result<Ref, NaturalError> {
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
    let name = greatest
        .unwrap_or(0)
        .checked_add(1)
        .ok_or(NaturalError::WrongForm {
            expected: "an available arithmetic binder name",
        })?;
    Ok(kernel.tm_fv(name, ty)?)
}

fn apply2(kernel: &mut Kernel, function: Ref, left: Ref, right: Ref) -> Result<Ref, NaturalError> {
    let at_left = kernel.app(function, left)?;
    Ok(kernel.app(at_left, right)?)
}
