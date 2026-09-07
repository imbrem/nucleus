//! Trusted literal extension: concrete carriers and successful evaluation.
//!
//! This is an explicit addition to the trusted rules under ax.inf. It does
//! not claim opcode-free syntactic lowering. Raw rows never enter this rule:
//! every reachable row and classifier is checked first.
use super::{AX_INF, Kernel, KernelError, Node};
use crate::{
    Ref, Sort, ThmId,
    literals::{Builtin, EvalError, EvalLimits, LiteralType, LiteralValue},
};
use std::{collections::BTreeMap, convert::Infallible};

impl Kernel {
    pub(super) fn require_literal_capability(&self) -> Result<(), KernelError> {
        if self.arena.axioms().any(|a| a == AX_INF) {
            Ok(())
        } else {
            Err(KernelError::MissingAxiom { name: AX_INF })
        }
    }
    /// Returns a concrete literal carrier, creating it on first use.
    /// # Errors
    /// Non-Boolean carriers require ax.inf; capacity failures leave no change.
    pub fn literal_ty(&mut self, ty: LiteralType) -> Result<Ref, KernelError> {
        let reference = crate::global::ty(ty);
        self.row::<Infallible>(reference)?;
        Ok(reference)
    }
    /// Constructs a canonical checked literal.
    /// # Errors
    /// Requires its carrier capability, a bounded value, and arena capacity.
    /// Failure leaves the kernel unchanged.
    pub fn literal(&mut self, value: LiteralValue) -> Result<Ref, KernelError> {
        let ty = self.literal_ty(value.ty())?;
        if let Some(reference) = crate::global::literal(&value) {
            return Ok(reference);
        }
        super::super::literals::check_size(&value, EvalLimits::default())?;
        if !self.arena.can_push_literal(&value) {
            return Err(EvalError::Resource.into());
        }
        let result = self
            .arena
            .push_literal(value)
            .ok_or(KernelError::TooManyDefinitions)?;
        self.arena
            .set_eq_column(crate::EqColumn::Conv, result, Some(ty));
        Ok(result)
    }
    /// Inspects the concrete carrier of a checked term.
    /// # Errors
    /// Rejects missing, non-term, or nonliteral classifiers.
    pub fn literal_type(&self, term: Ref) -> Result<LiteralType, KernelError> {
        self.require_category::<Infallible>(term, Sort::Tm)?;
        let ty = self.classifier(term)?;
        self.arena
            .literal_type(ty)
            .or(self.arena.literal_type(self.find(ty)?))
            .ok_or(KernelError::Literal {
                source: EvalError::Signature,
            })
    }
    /// Inspects a resident literal; symbolic expressions return None.
    /// # Errors
    /// Rejects malformed or nonliteral-typed terms.
    pub fn literal_value(&self, term: Ref) -> Result<Option<LiteralValue>, KernelError> {
        self.literal_type(term)?;
        Ok(self.arena.literal_value(term))
    }
    /// Constructs a first-class builtin constant with its curried function type.
    ///
    /// Use ordinary application for partial applications. Bytes.empty is a
    /// zero-argument constant whose type is Bytes.
    /// # Errors
    /// Rejects invalid descriptors, missing ax.inf, or exhausted row capacity.
    pub fn builtin_const(&mut self, op: Builtin) -> Result<Ref, KernelError> {
        let reference = crate::global::builtin(op).ok_or(EvalError::Signature)?;
        self.row::<Infallible>(reference)?;
        Ok(reference)
    }
    /// Constructs a fully applied builtin using ordinary application rows.
    /// # Errors
    /// Rejects wrong signatures, missing capabilities, or exhausted capacity.
    pub fn builtin(&mut self, op: Builtin, args: &[Ref]) -> Result<Ref, KernelError> {
        let (inputs, _) = op.signature()?;
        if inputs.len() != args.len() {
            return Err(EvalError::Signature.into());
        }
        let mut function = self.builtin_const(op)?;
        for (&argument, input) in args.iter().zip(inputs) {
            if self.literal_type(argument)? != input
                || !self.equivalent(self.classifier(argument)?, crate::global::ty(input))?
            {
                return Err(EvalError::Signature.into());
            }
        }
        if let Builtin::Cast(crate::literals::CastOp::WordWrap(from, to)) =
            crate::global::canonical(op)
            && from == to
        {
            return Ok(args[0]);
        }
        self.literal_capacity(args.len())?;
        for &argument in args {
            function = self.app(function, argument)?;
        }
        Ok(function)
    }
    /// Computes a closed literal expression and proves its exact equality.
    ///
    /// The returned pair is the result literal and a premise-free theorem
    /// whose sole conclusion equates the original expression with that result.
    /// This is the trusted concrete-literal evaluation rule under ax.inf.
    /// # Errors
    /// Rejects symbolic/imported/invalid terms, undefined operations and resource
    /// exhaustion. Every failure is atomic and creates no theorem.
    pub fn reduce_builtin(
        &mut self,
        term: Ref,
        limits: EvalLimits,
    ) -> Result<(Ref, ThmId), KernelError> {
        self.literal_type(term)?;
        let mut staged = self.fork();
        let result = staged.reduce_literal_value(term, limits)?;
        let bool_ty = staged.literal_ty(LiteralType::Bool)?;
        let ty = staged.classifier(term)?;
        let equality = staged.eq_at(bool_ty, ty, term, result)?;
        let theorem = staged.push_axiom(equality)?;
        *self = staged;
        Ok((result, theorem))
    }

    fn reduce_literal_value(&mut self, term: Ref, limits: EvalLimits) -> Result<Ref, KernelError> {
        let mut todo = vec![(term, false)];
        let mut values = BTreeMap::new();
        let mut active = std::collections::BTreeSet::new();
        let mut steps = 0u32;
        while let Some((r, visited)) = todo.pop() {
            if values.contains_key(&r) {
                continue;
            }
            steps = steps
                .checked_add(1)
                .filter(|n| *n <= limits.max_steps)
                .ok_or(EvalError::Resource)?;
            self.validate_copy_row(r)?;
            let root = self.find(r)?;
            if let Some(value) = self.arena.literal_value(root) {
                self.validate_copy_row(root)?;
                super::super::literals::check_size(&value, limits)?;
                values.insert(r, (root, value));
                continue;
            }
            let node = *self.row::<Infallible>(r)?.expr();
            let (operation, operands) = match node {
                Node::Builtin(_) | Node::App(..) => {
                    let (op, args) = self.literal_call(r, &mut steps, limits)?;
                    (Some(op), args)
                }
                Node::Eq(_, left, right) => (None, vec![left, right]),
                _ => return Err(EvalError::Undefined.into()),
            };
            if visited {
                let arguments = operands
                    .iter()
                    .map(|child| {
                        values
                            .get(child)
                            .map(|(_, value)| value.clone())
                            .ok_or(EvalError::Undefined)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let result = if let Some(op) = operation {
                    op.evaluate(&arguments, limits)?
                } else {
                    LiteralValue::Bool(arguments[0] == arguments[1])
                };
                let result_ref = self.literal(result.clone())?;
                self.union::<Infallible>(r, result_ref)?;
                values.insert(r, (result_ref, result));
                active.remove(&r);
            } else {
                if !active.insert(r) {
                    return Err(KernelError::CyclicSyntax { reference: r });
                }
                todo.push((r, true));
                for child in operands.into_iter().rev() {
                    todo.push((child, false));
                }
            }
        }
        values
            .remove(&term)
            .map(|(reference, _)| reference)
            .ok_or_else(|| EvalError::Undefined.into())
    }
    pub(super) fn validate_literal_row(&self, r: Ref) -> Result<Ref, KernelError> {
        let declared = self.literal_type(r)?;
        if declared != LiteralType::Bool {
            self.require_literal_capability()?;
        }
        let actual = match *self.row::<Infallible>(r)?.expr() {
            Node::ConstRef(id) => self
                .arena
                .constants
                .get(id)
                .ok_or(EvalError::Signature)?
                .literal_type(),
            _ => self
                .arena
                .literal_type_of_ref(r)
                .ok_or(EvalError::Signature)?,
        };
        if declared != actual {
            return Err(EvalError::Signature.into());
        }
        self.classifier(r)
    }

    pub(super) fn validate_builtin_const(&self, r: Ref, op: Builtin) -> Result<Ref, KernelError> {
        self.row::<Infallible>(r)?;
        let (inputs, output) = op.signature()?;
        let original = self.classifier(r)?;
        let mut ty = original;
        for input in inputs {
            self.require_star_type::<Infallible>(ty)?;
            let (domain, codomain) = self.type_arrow_member::<Infallible>(ty)?;
            self.require_star_type::<Infallible>(domain)?;
            if self.arena.literal_type(domain) != Some(input) {
                return Err(EvalError::Signature.into());
            }
            ty = codomain;
        }
        self.require_star_type::<Infallible>(ty)?;
        if self.arena.literal_type(ty) != Some(output) {
            return Err(EvalError::Signature.into());
        }
        Ok(original)
    }
    fn literal_call(
        &self,
        root: Ref,
        steps: &mut u32,
        limits: EvalLimits,
    ) -> Result<(Builtin, Vec<Ref>), KernelError> {
        let mut function = root;
        let mut arguments = Vec::new();
        loop {
            *steps = steps
                .checked_add(1)
                .filter(|n| *n <= limits.max_steps)
                .ok_or(EvalError::Resource)?;
            self.validate_copy_row(function)?;
            match *self.row::<Infallible>(function)?.expr() {
                Node::App(head, arg) => {
                    arguments.push(arg);
                    if arguments.len() > 4 {
                        return Err(EvalError::Signature.into());
                    }
                    function = head;
                }
                Node::Builtin(op) => {
                    arguments.reverse();
                    let (inputs, _) = op.signature()?;
                    if inputs.len() != arguments.len() {
                        return Err(EvalError::Signature.into());
                    }
                    return Ok((op, arguments));
                }
                _ => return Err(EvalError::Undefined.into()),
            }
        }
    }
    fn literal_capacity(&self, additional: usize) -> Result<(), KernelError> {
        if additional == 0 {
            return Ok(());
        }
        let last = self
            .arena
            .len()
            .checked_add(additional)
            .and_then(|n| i32::try_from(n).ok())
            .and_then(Ref::new);
        last.ok_or(KernelError::TooManyDefinitions).map(|_| ())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Row;
    use crate::literals::{BytesOp, CastOp, Endian, IntOp, NatOp, WordOp, WordWidth};
    use covalence_data_num::{Int, Num};

    fn kernel() -> Kernel {
        let mut k = Kernel::new();
        k.add_axiom(AX_INF).unwrap();
        k
    }
    #[test]
    fn builtin_constants_are_first_class_curried_functions() {
        let mut k = kernel();
        let add = k
            .builtin_const(Builtin::Word(WordWidth::W32, WordOp::Add))
            .unwrap();
        assert_eq!(k.arena.children(add).unwrap().count(), 0);
        let one = k.literal(LiteralValue::I32(1)).unwrap();
        let partial = k.app(add, one).unwrap();
        let before = k.arena.clone();
        assert!(k.reduce_builtin(partial, EvalLimits::default()).is_err());
        assert_eq!(k.arena, before);
        let complete = k.app(partial, one).unwrap();
        let (result, _) = k.reduce_builtin(complete, EvalLimits::default()).unwrap();
        assert_eq!(k.literal_value(result).unwrap(), Some(LiteralValue::I32(2)));
        let empty = k.builtin_const(Builtin::Bytes(BytesOp::Empty)).unwrap();
        let (result, _) = k.reduce_builtin(empty, EvalLimits::default()).unwrap();
        assert_eq!(
            k.literal_value(result).unwrap(),
            Some(LiteralValue::Bytes(bytes::Bytes::new()))
        );
        let wrong = k.literal_ty(LiteralType::Nat).unwrap();
        k.arena
            .set_eq_column(crate::EqColumn::Conv, partial, Some(wrong));
        let before = k.arena.clone();
        assert!(k.reduce_builtin(complete, EvalLimits::default()).is_err());
        assert_eq!(k.arena, before);
    }
    #[test]
    fn corrupted_builtin_function_signature_is_rejected_atomically() {
        for corrupt_domain in [true, false] {
            let mut k = kernel();
            let successor = k
                .arena
                .push_row(Row::new(Node::Builtin(Builtin::Nat(NatOp::Succ))), None)
                .unwrap();
            let nat_ty = k.literal_ty(LiteralType::Nat).unwrap();
            let int_ty = k.literal_ty(LiteralType::Int).unwrap();
            let (domain, result) = if corrupt_domain {
                (int_ty, nat_ty)
            } else {
                (nat_ty, int_ty)
            };
            let forged_ty = k.ty_arr(domain, result).unwrap();
            k.arena
                .set_eq_column(crate::EqColumn::Conv, successor, Some(forged_ty));
            let argument = k
                .literal(if corrupt_domain {
                    LiteralValue::Int(Int::from(7))
                } else {
                    LiteralValue::Nat(Num::from(7u8))
                })
                .unwrap();
            // The application itself matches the forged arrow; rejection must
            // inspect the builtin descriptor's domain and result contract.
            let application = k.app(successor, argument).unwrap();
            let before = k.arena.clone();
            assert!(matches!(
                k.reduce_builtin(application, EvalLimits::default()),
                Err(KernelError::Literal {
                    source: EvalError::Signature
                })
            ));
            assert_eq!(k.arena, before);
        }
    }
    fn compute(k: &mut Kernel, op: Builtin, args: Vec<LiteralValue>) -> LiteralValue {
        let args = args
            .into_iter()
            .map(|v| k.literal(v).unwrap())
            .collect::<Vec<_>>();
        let term = k.builtin(op, &args).unwrap();
        let (result, theorem) = k.reduce_builtin(term, EvalLimits::default()).unwrap();
        let thm = k.theorems().get(theorem).unwrap();
        assert_eq!(thm.lhs.rows().count(), 0);
        let rows = thm.rhs.to_rows();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].len(), 1);
        let equality = Ref::new(i32::try_from(rows[0][0].magnitude()).unwrap()).unwrap();
        assert_eq!(
            k.arena
                .children(equality)
                .unwrap()
                .skip(1)
                .collect::<Vec<_>>(),
            [term, result]
        );
        k.literal_value(result).unwrap().unwrap()
    }
    #[test]
    fn checked_nested_arithmetic_has_exact_conclusion() {
        let mut k = kernel();
        let a = k.literal(LiteralValue::I32(20)).unwrap();
        let b = k.literal(LiteralValue::I32(22)).unwrap();
        let sum = k
            .builtin(Builtin::Word(WordWidth::W32, WordOp::Add), &[a, b])
            .unwrap();
        let product = k
            .builtin(Builtin::Word(WordWidth::W32, WordOp::Mul), &[sum, b])
            .unwrap();
        let (value, thm) = k.reduce_builtin(product, EvalLimits::default()).unwrap();
        assert_eq!(
            k.literal_value(value).unwrap(),
            Some(LiteralValue::I32(924))
        );
        assert!(k.theorems().get(thm).is_some());
    }

    #[test]
    fn reduction_accepts_only_checked_equivalent_application_classifiers() {
        let mut k = Kernel::new();
        let star = k.star().unwrap();
        let bool_ty = k.bool_ty(star).unwrap();
        let parameter = k.ty_fv(77, star).unwrap();
        let identity = k.ty_lam(parameter, parameter).unwrap();
        let alias = k.ty_app(identity, bool_ty).unwrap();
        let truth = k.bool(bool_ty, true).unwrap();
        assert!(k.eq(alias, truth, truth).is_err());
        let substitution = k.syn_sub_var(None, parameter, bool_ty).unwrap();
        let beta = k.ty_beta_fact(None, alias, substitution).unwrap();
        k.union_syn_fact(beta).unwrap();
        let equality = k.eq(alias, truth, truth).unwrap();
        assert_eq!(k.classifier(equality).unwrap(), alias);
        let negated = k.not(equality).unwrap();
        let (result, theorem) = k.reduce_builtin(negated, EvalLimits::default()).unwrap();
        assert_eq!(
            k.literal_value(result).unwrap(),
            Some(LiteralValue::Bool(false))
        );
        assert!(k.theorems().get(theorem).is_some());

        // Merely assigning an unrelated type is not evidence of equivalence.
        let unrelated = k.ty_fv(78, star).unwrap();
        k.arena
            .set_eq_column(crate::EqColumn::Conv, equality, Some(unrelated));
        let before = k.arena.clone();
        assert!(k.reduce_builtin(negated, EvalLimits::default()).is_err());
        assert_eq!(k.arena, before);
    }
    #[test]
    fn resident_results_are_cached_without_an_auxiliary_value_table() {
        let mut k = kernel();
        let bytes = k
            .literal(LiteralValue::Bytes(vec![1, 2, 3].into()))
            .unwrap();
        let doubled = k
            .builtin(Builtin::Bytes(BytesOp::Append), &[bytes, bytes])
            .unwrap();
        let (result, _) = k.reduce_builtin(doubled, EvalLimits::default()).unwrap();
        assert!(result.get() > 0);
        assert_eq!(k.find(doubled).unwrap(), result);
        let before = k.len();
        let (again, _) = k
            .reduce_builtin(
                doubled,
                EvalLimits {
                    max_steps: 1,
                    ..Default::default()
                },
            )
            .unwrap();
        assert_eq!(again, result);
        assert_eq!(
            k.len(),
            before + 1,
            "only the requested theorem proposition is appended"
        );
    }
    #[test]
    fn arithmetic_and_bytes_produce_real_theorems() {
        let mut k = kernel();
        assert_eq!(
            compute(
                &mut k,
                Builtin::Int(IntOp::Div),
                vec![
                    LiteralValue::Int(Int::from(-7)),
                    LiteralValue::Int(Int::from(3))
                ]
            ),
            LiteralValue::Int(Int::from(-2))
        );
        assert_eq!(
            compute(
                &mut k,
                Builtin::Nat(NatOp::Sub),
                vec![
                    LiteralValue::Nat(Num::from(1u8)),
                    LiteralValue::Nat(Num::from(3u8))
                ]
            ),
            LiteralValue::Nat(Num::ZERO)
        );
        assert_eq!(
            compute(
                &mut k,
                Builtin::Bytes(BytesOp::Read(WordWidth::W16, Endian::Little)),
                vec![
                    LiteralValue::Bytes(vec![0x34, 0x12].into()),
                    LiteralValue::Nat(Num::ZERO)
                ]
            ),
            LiteralValue::I16(0x1234)
        );
    }
    #[test]
    fn failures_are_atomic_and_terms_are_separate_from_reduction() {
        let mut k = kernel();
        let a = k.literal(LiteralValue::I8(1)).unwrap();
        let zero = k.literal(LiteralValue::I8(0)).unwrap();
        let div = k
            .builtin(Builtin::Word(WordWidth::W8, WordOp::DivU), &[a, zero])
            .unwrap();
        let before = k.arena.clone();
        assert!(matches!(
            k.reduce_builtin(div, EvalLimits::default()),
            Err(KernelError::Literal {
                source: EvalError::Undefined
            })
        ));
        assert_eq!(k.arena, before);
        assert!(k.builtin(Builtin::Nat(NatOp::Add), &[a, a]).is_err());
        assert_eq!(k.arena, before);
        assert!(
            k.reduce_builtin(
                a,
                EvalLimits {
                    max_bytes: 1,
                    max_steps: 0
                }
            )
            .is_err()
        );
        assert_eq!(k.arena, before);
        let nat_ty = k.literal_ty(LiteralType::Nat).unwrap();
        let symbolic = k.tm_fv(900, nat_ty).unwrap();
        let expression = k.builtin(Builtin::Nat(NatOp::Succ), &[symbolic]).unwrap();
        let before = k.arena.clone();
        assert!(k.reduce_builtin(expression, EvalLimits::default()).is_err());
        assert_eq!(k.arena, before);
    }
    #[test]
    fn capability_and_wrong_literal_classifier_are_checked() {
        let mut k = Kernel::new();
        assert!(k.literal(LiteralValue::Nat(Num::ZERO)).is_err());
        assert!(k.arena.is_empty());
        let mut k = kernel();
        let value = k
            .arena
            .push_row(Row::new(Node::Word(WordWidth::W8, 7)), None)
            .unwrap();
        let wrong = k.literal_ty(LiteralType::Int).unwrap();
        k.arena
            .set_eq_column(crate::EqColumn::Conv, value, Some(wrong));
        let before = k.arena.clone();
        assert!(k.reduce_builtin(value, EvalLimits::default()).is_err());
        assert_eq!(k.arena, before);
    }
    #[test]
    fn constant_copy_remaps_table_and_preserves_value() {
        let mut source = kernel();
        let value = source
            .literal(LiteralValue::Bytes(vec![1, 2, 3].into()))
            .unwrap();
        let mut dest = kernel();
        dest.literal(LiteralValue::Bytes(vec![9].into())).unwrap();
        let copy = dest.copy_terms_from(&source, &[value]).unwrap();
        let copied = copy.roots()[0];
        assert_eq!(
            dest.literal_value(copied).unwrap(),
            Some(LiteralValue::Bytes(vec![1, 2, 3].into()))
        );
        let (result, _) = dest.reduce_builtin(copied, EvalLimits::default()).unwrap();
        assert_eq!(
            dest.literal_value(result).unwrap(),
            Some(LiteralValue::Bytes(vec![1, 2, 3].into()))
        );
    }
    #[test]
    fn copied_builtin_application_uses_its_carriers_with_populated_destination_cache() {
        let mut source = kernel();
        let big = Num::from_canonical_bytes(&[0x81; 9]).unwrap();
        let left = source.literal(LiteralValue::Nat(big.clone())).unwrap();
        let right = source.literal(LiteralValue::Nat(Num::from(5u8))).unwrap();
        let sum = source
            .builtin(Builtin::Nat(NatOp::Add), &[left, right])
            .unwrap();
        let mut destination = kernel();
        destination
            .literal(LiteralValue::Int(Int::from(-1)))
            .unwrap();
        destination
            .literal(LiteralValue::Bytes(vec![9, 8, 7].into()))
            .unwrap();
        destination.literal(LiteralValue::I32(1)).unwrap();
        let cached_nat = destination.literal_ty(LiteralType::Nat).unwrap();
        destination
            .literal(LiteralValue::Nat(Num::from(100u8)))
            .unwrap();
        assert_eq!(source.classifier(sum).unwrap(), cached_nat);
        let copy = destination.copy_terms_from(&source, &[sum]).unwrap();
        let copied = copy.roots()[0];
        let copied_type = destination.classifier(copied).unwrap();
        assert_eq!(copied_type, cached_nat);
        let (result, theorem) = destination
            .reduce_builtin(copied, EvalLimits::default())
            .unwrap();
        assert_eq!(
            destination.literal_value(result).unwrap(),
            Some(LiteralValue::Nat(&big + &Num::from(5u8)))
        );
        assert_eq!(destination.classifier(result).unwrap(), copied_type);
        assert_eq!(
            destination.literal_ty(LiteralType::Nat).unwrap(),
            cached_nat
        );
        assert_eq!(
            destination
                .theorems()
                .get(theorem)
                .unwrap()
                .lhs
                .rows()
                .count(),
            0
        );
    }
    #[test]
    fn negative_cast_and_big_integer_boundaries() {
        let mut k = kernel();
        let value = k.literal(LiteralValue::Int(Int::from(-1))).unwrap();
        let term = k
            .builtin(Builtin::Cast(CastOp::IntToNat), &[value])
            .unwrap();
        let before = k.arena.clone();
        assert!(k.reduce_builtin(term, EvalLimits::default()).is_err());
        assert_eq!(k.arena, before);
        let big = Num::from_canonical_bytes(&[1; 33]).unwrap();
        assert_eq!(
            compute(
                &mut k,
                Builtin::Nat(NatOp::Add),
                vec![LiteralValue::Nat(big.clone()), LiteralValue::Nat(Num::ZERO)]
            ),
            LiteralValue::Nat(big)
        );
    }
    #[test]
    fn equality_ignores_inline_or_constant_storage() {
        let mut k = kernel();
        let inline = k.literal(LiteralValue::Nat(Num::from(7u8))).unwrap();
        let id = k
            .arena
            .constants
            .push(crate::constants::Constant::Nat(Num::from(7u8)))
            .unwrap();
        let referenced = k
            .push::<Infallible>(
                Row::new(Node::ConstRef(id)),
                Some(k.classifier(inline).unwrap()),
            )
            .unwrap();
        let bool_ty = k.literal_ty(LiteralType::Bool).unwrap();
        let eq = k.eq(bool_ty, inline, referenced).unwrap();
        let (value, _) = k.reduce_builtin(eq, EvalLimits::default()).unwrap();
        assert_eq!(
            k.literal_value(value).unwrap(),
            Some(LiteralValue::Bool(true))
        );
        let truth = k.literal(LiteralValue::Bool(true)).unwrap();
        let falsehood = k.literal(LiteralValue::Bool(false)).unwrap();
        let eq = k.eq(bool_ty, truth, falsehood).unwrap();
        let (value, _) = k.reduce_builtin(eq, EvalLimits::default()).unwrap();
        assert_eq!(
            k.literal_value(value).unwrap(),
            Some(LiteralValue::Bool(false))
        );
        let inline = k.literal(LiteralValue::Int(Int::from(-7))).unwrap();
        let id = k
            .arena
            .constants
            .push(crate::constants::Constant::Int(Int::from(-7)))
            .unwrap();
        let referenced = k
            .push::<Infallible>(
                Row::new(Node::ConstRef(id)),
                Some(k.classifier(inline).unwrap()),
            )
            .unwrap();
        let eq = k.eq(bool_ty, inline, referenced).unwrap();
        let (value, _) = k.reduce_builtin(eq, EvalLimits::default()).unwrap();
        assert_eq!(
            k.literal_value(value).unwrap(),
            Some(LiteralValue::Bool(true))
        );
    }
}
