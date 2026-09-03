//! Generic checked propositions for faithful structural-value interpretations.
//!
//! `SpecTec` lowering may initially interpret every structural value in one
//! erased HOL carrier. This module states the constructor injectivity and
//! disjointness obligations needed to make such an interpretation faithful.
//! It constructs syntax only: callers must supply checked proofs or retain the
//! propositions as explicit semantic premises.

use std::sync::Arc;

use covalence_logic_hol::{
    Kernel, KernelError, Ref,
    builtin::{Op1, Op2},
};
use covalence_logic_hol_derived::join_same_syntax;

/// One validated constructor in an erased structural-value algebra.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StructuralConstructor {
    operation: Ref,
    arity: usize,
}

impl StructuralConstructor {
    /// Returns the checked curried constructor operation.
    #[must_use]
    pub const fn operation(self) -> Ref {
        self.operation
    }

    /// Returns the number of structural children.
    #[must_use]
    pub const fn arity(self) -> usize {
        self.arity
    }
}

/// Classifiers shared by a single-carrier structural-value interpretation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StructuralValueAlgebra {
    /// Classifier of erased structural values.
    pub value_ty: Ref,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
}

/// Immutable obligations for one finite structural-constructor vocabulary.
///
/// The propositions contain every constructor's injectivity law followed by
/// disjointness for every unordered pair, in input order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StructuralConstructorLaws {
    constructors: Arc<[StructuralConstructor]>,
    propositions: Arc<[Ref]>,
}

impl StructuralConstructorLaws {
    /// Returns the exact constructor vocabulary covered by these laws.
    #[must_use]
    pub fn constructors(&self) -> &[StructuralConstructor] {
        &self.constructors
    }

    /// Returns the injectivity and pairwise-disjointness propositions.
    #[must_use]
    pub fn propositions(&self) -> &[Ref] {
        &self.propositions
    }
}

impl StructuralValueAlgebra {
    /// Constructs the complete constructor-separation obligations for a finite
    /// vocabulary.
    ///
    /// The result contains one injectivity proposition per constructor and one
    /// disjointness proposition per unordered constructor pair. It does not
    /// claim exhaustiveness, sequence-operation laws, or that any proposition
    /// has been proved.
    ///
    /// # Errors
    ///
    /// Returns an error if a constructor is duplicated or invalid for this
    /// algebra, or any checked proposition construction fails. `kernel` is
    /// unchanged on failure.
    pub fn constructor_laws(
        self,
        kernel: &mut Kernel,
        constructors: &[StructuralConstructor],
    ) -> Result<StructuralConstructorLaws, KernelError> {
        let mut staged = kernel.fork();
        for (index, &constructor) in constructors.iter().enumerate() {
            self.require_constructor(&mut staged, constructor)?;
            if constructors[..index].contains(&constructor) {
                return Err(KernelError::InvalidTheoremRule {
                    rule: "duplicate structural constructor law",
                });
            }
        }
        let pair_count = constructors
            .len()
            .checked_mul(constructors.len().saturating_sub(1))
            .and_then(|count| count.checked_div(2))
            .ok_or(KernelError::TooManyNames)?;
        let mut propositions = Vec::with_capacity(
            constructors
                .len()
                .checked_add(pair_count)
                .ok_or(KernelError::TooManyNames)?,
        );
        for (index, &constructor) in constructors.iter().enumerate() {
            propositions.push(self.injective(&mut staged, constructor)?);
            for &other in &constructors[index + 1..] {
                propositions.push(self.disjoint(&mut staged, constructor, other)?);
            }
        }
        let laws = StructuralConstructorLaws {
            constructors: Arc::from(constructors),
            propositions: Arc::from(propositions),
        };
        *kernel = staged;
        Ok(laws)
    }

    /// Validates a curried `value^arity -> value` constructor.
    ///
    /// # Errors
    ///
    /// Returns an error unless `operation` has the exact classifier induced by
    /// `arity`. `kernel` is unchanged on failure.
    pub fn constructor(
        self,
        kernel: &mut Kernel,
        operation: Ref,
        arity: usize,
    ) -> Result<StructuralConstructor, KernelError> {
        let mut staged = kernel.fork();
        let mut expected = self.value_ty;
        for _ in 0..arity {
            expected = staged.ty_arr(self.value_ty, expected)?;
        }
        let actual = staged.classifier(operation)?;
        join_same_syntax(&mut staged, actual, expected)
            .map_err(|_| KernelError::ClassifierMismatch { expected, actual })?;
        *kernel = staged;
        Ok(StructuralConstructor { operation, arity })
    }

    /// Constructs the injectivity proposition for one constructor.
    ///
    /// For arity `n`, the result is
    /// `forall xs ys. constructor(xs) = constructor(ys) -> and_i xs[i] = ys[i]`.
    /// Nullary constructor injectivity reduces to an implication with `true`
    /// consequent.
    ///
    /// # Errors
    ///
    /// Returns an error if `constructor` is not valid for this algebra, fresh
    /// variables cannot be allocated, or a checked HOL constructor fails.
    /// `kernel` is unchanged on failure.
    pub fn injective(
        self,
        kernel: &mut Kernel,
        constructor: StructuralConstructor,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        self.require_constructor(&mut staged, constructor)?;
        let (left, right) = self.arguments(&mut staged, constructor, constructor)?;
        let left_value = apply(&mut staged, constructor.operation, &left)?;
        let right_value = apply(&mut staged, constructor.operation, &right)?;
        let equal_values = staged.eq(self.bool_ty, left_value, right_value)?;
        let mut equal_fields = staged.bool(self.bool_ty, true)?;
        for (&left, &right) in left.iter().zip(&right).rev() {
            let equal = staged.eq(self.bool_ty, left, right)?;
            equal_fields = staged.op2(Op2::And, equal, equal_fields)?;
        }
        let body = staged.op2(Op2::Imp, equal_values, equal_fields)?;
        let proposition = quantify(&mut staged, self.bool_ty, &left, &right, body)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs disjointness of two structural constructors.
    ///
    /// The result is `forall xs ys. not (left(xs) = right(ys))` and supports
    /// independently chosen arities.
    ///
    /// # Errors
    ///
    /// Returns an error if either constructor belongs to another algebra,
    /// fresh variables cannot be allocated, or checked construction fails.
    /// `kernel` is unchanged on failure.
    pub fn disjoint(
        self,
        kernel: &mut Kernel,
        left_constructor: StructuralConstructor,
        right_constructor: StructuralConstructor,
    ) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        self.require_constructor(&mut staged, left_constructor)?;
        self.require_constructor(&mut staged, right_constructor)?;
        let (left, right) = self.arguments(&mut staged, left_constructor, right_constructor)?;
        let left_value = apply(&mut staged, left_constructor.operation, &left)?;
        let right_value = apply(&mut staged, right_constructor.operation, &right)?;
        let equality = staged.eq(self.bool_ty, left_value, right_value)?;
        let body = staged.op1(Op1::Not, equality)?;
        let proposition = quantify(&mut staged, self.bool_ty, &left, &right, body)?;
        *kernel = staged;
        Ok(proposition)
    }

    fn require_constructor(
        self,
        kernel: &mut Kernel,
        constructor: StructuralConstructor,
    ) -> Result<(), KernelError> {
        self.constructor(kernel, constructor.operation, constructor.arity)?;
        Ok(())
    }

    fn arguments(
        self,
        kernel: &mut Kernel,
        left: StructuralConstructor,
        right: StructuralConstructor,
    ) -> Result<(Vec<Ref>, Vec<Ref>), KernelError> {
        let first =
            kernel.fresh_name(&[self.value_ty, self.bool_ty, left.operation, right.operation])?;
        let count = left
            .arity
            .checked_add(right.arity)
            .ok_or(KernelError::TooManyNames)?;
        let mut variables = Vec::with_capacity(count);
        for offset in 0..count {
            let offset = u64::try_from(offset).map_err(|_| KernelError::TooManyNames)?;
            variables.push(kernel.tm_fv(
                first.checked_add(offset).ok_or(KernelError::TooManyNames)?,
                self.value_ty,
            )?);
        }
        let right = variables.split_off(left.arity);
        Ok((variables, right))
    }
}

fn apply(kernel: &mut Kernel, function: Ref, arguments: &[Ref]) -> Result<Ref, KernelError> {
    arguments.iter().try_fold(function, |function, &argument| {
        kernel.app(function, argument)
    })
}

fn quantify(
    kernel: &mut Kernel,
    bool_ty: Ref,
    left: &[Ref],
    right: &[Ref],
    mut body: Ref,
) -> Result<Ref, KernelError> {
    for &variable in right.iter().rev().chain(left.iter().rev()) {
        body = kernel.forall_tm(bool_ty, variable, body)?;
    }
    Ok(body)
}

#[cfg(test)]
mod tests {
    use super::{StructuralValueAlgebra, apply};
    use covalence_logic_hol::Kernel;

    #[test]
    fn structural_faithfulness_laws_are_generic_checked_and_transactional() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let value_ty = kernel.ty_fv(1, star).unwrap();
        let unary_ty = kernel.ty_arr(value_ty, value_ty).unwrap();
        let binary_tail = kernel.ty_arr(value_ty, value_ty).unwrap();
        let binary_ty = kernel.ty_arr(value_ty, binary_tail).unwrap();
        let unary = kernel.tm_fv(10, unary_ty).unwrap();
        let binary = kernel.tm_fv(11, binary_ty).unwrap();
        let algebra = StructuralValueAlgebra { value_ty, bool_ty };
        let unary = algebra.constructor(&mut kernel, unary, 1).unwrap();
        let binary = algebra.constructor(&mut kernel, binary, 2).unwrap();
        let injective = algebra.injective(&mut kernel, binary).unwrap();
        let disjoint = algebra.disjoint(&mut kernel, unary, binary).unwrap();
        assert_eq!(kernel.classifier(injective).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(disjoint).unwrap(), bool_ty);

        let laws = algebra
            .constructor_laws(&mut kernel, &[unary, binary])
            .unwrap();
        assert_eq!(laws.constructors(), &[unary, binary]);
        assert_eq!(laws.propositions().len(), 3);
        assert!(
            laws.propositions()
                .iter()
                .all(|&law| kernel.classifier(law).unwrap() == bool_ty)
        );

        let value = kernel.tm_fv(12, value_ty).unwrap();
        let applied = apply(&mut kernel, unary.operation(), &[value]).unwrap();
        assert_eq!(kernel.classifier(applied).unwrap(), value_ty);

        let before = kernel.arena().clone();
        assert!(
            algebra
                .constructor(&mut kernel, unary.operation(), 2)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert!(
            algebra
                .constructor_laws(&mut kernel, &[unary, unary])
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
    }
}
