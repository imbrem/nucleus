//! Generic checked propositions for faithful structural-value interpretations.
//!
//! `SpecTec` lowering may initially interpret every structural value in one
//! erased HOL carrier. This module states the constructor injectivity and
//! disjointness obligations needed to make such an interpretation faithful.
//! It constructs syntax only: callers must supply checked proofs or retain the
//! propositions as explicit semantic premises.

use std::sync::Arc;

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{
    Kernel, KernelError, Lit, Ref, ThmId,
    builtin::{Op1, Op2},
};
use covalence_logic_hol_derived::{
    ForallError, SyntaxError, forall_elim, join_alpha_equivalent, join_same_syntax,
};

use crate::Evidence;

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

/// One finite structural sequence and its exact membership-law proposition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FiniteSequenceLaw {
    list: Ref,
    elements: Arc<[Ref]>,
    binder: Ref,
    proposition: Ref,
}

impl FiniteSequenceLaw {
    /// Returns the structural list term.
    #[must_use]
    pub const fn list(&self) -> Ref {
        self.list
    }

    /// Returns the elements in semantic order.
    #[must_use]
    pub fn elements(&self) -> &[Ref] {
        &self.elements
    }

    /// Returns `forall x. member x list = (x=e0 or ...)`.
    #[must_use]
    pub const fn proposition(&self) -> Ref {
        self.proposition
    }
}

/// A checked membership operation over one structural-value carrier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct StructuralSequenceAlgebra {
    values: StructuralValueAlgebra,
    member: Ref,
}

impl StructuralSequenceAlgebra {
    /// Validates `member : value -> value -> bool`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `member` has the exact required classifier.
    /// `kernel` is unchanged on failure.
    pub fn new(
        kernel: &mut Kernel,
        values: StructuralValueAlgebra,
        member: Ref,
    ) -> Result<Self, KernelError> {
        let mut staged = kernel.fork();
        let tail = staged.ty_arr(values.value_ty, values.bool_ty)?;
        let expected = staged.ty_arr(values.value_ty, tail)?;
        let actual = staged.classifier(member)?;
        join_same_syntax(&mut staged, actual, expected)
            .map_err(|_| KernelError::ClassifierMismatch { expected, actual })?;
        *kernel = staged;
        Ok(Self { values, member })
    }

    /// Returns the checked membership predicate.
    #[must_use]
    pub const fn member(self) -> Ref {
        self.member
    }

    /// Constructs exact finite membership semantics for one list constructor.
    ///
    /// For elements `[e0, ...]`, the proposition is
    /// `forall x. member x (list e0 ...) = (x=e0 or ...)`. The empty
    /// disjunction is false. This creates no theorem fact.
    ///
    /// # Errors
    ///
    /// Returns an error unless `list_constructor` belongs to this value
    /// algebra with arity equal to `elements.len()`, every element has the
    /// value classifier, and checked construction succeeds. `kernel` is
    /// unchanged on failure.
    pub fn membership_law(
        self,
        kernel: &mut Kernel,
        list_constructor: StructuralConstructor,
        elements: &[Ref],
    ) -> Result<FiniteSequenceLaw, KernelError> {
        let mut staged = kernel.fork();
        self.values
            .require_constructor(&mut staged, list_constructor)?;
        if list_constructor.arity != elements.len() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "finite sequence constructor arity",
            });
        }
        for &element in elements {
            let actual = staged.classifier(element)?;
            join_same_syntax(&mut staged, actual, self.values.value_ty).map_err(|_| {
                KernelError::ClassifierMismatch {
                    expected: self.values.value_ty,
                    actual,
                }
            })?;
        }
        let list = apply(&mut staged, list_constructor.operation, elements)?;
        let mut roots = vec![
            self.values.value_ty,
            self.values.bool_ty,
            self.member,
            list_constructor.operation,
            list,
        ];
        roots.extend_from_slice(elements);
        let candidate = staged.tm_fv(staged.fresh_name(&roots)?, self.values.value_ty)?;
        let contains = apply(&mut staged, self.member, &[candidate, list])?;
        let mut enumerated = staged.bool(self.values.bool_ty, false)?;
        for &element in elements.iter().rev() {
            let equal = staged.eq(self.values.bool_ty, candidate, element)?;
            enumerated = staged.op2(Op2::Or, equal, enumerated)?;
        }
        let exact = staged.eq(self.values.bool_ty, contains, enumerated)?;
        let proposition = staged.forall_tm(self.values.bool_ty, candidate, exact)?;
        let law = FiniteSequenceLaw {
            list,
            elements: Arc::from(elements),
            binder: candidate,
            proposition,
        };
        *kernel = staged;
        Ok(law)
    }

    /// Constructs `forall x. not (member x list)`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `list` has the value classifier or checked
    /// construction fails. `kernel` is unchanged on failure.
    pub fn no_members(self, kernel: &mut Kernel, list: Ref) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let actual = staged.classifier(list)?;
        join_same_syntax(&mut staged, actual, self.values.value_ty).map_err(|_| {
            KernelError::ClassifierMismatch {
                expected: self.values.value_ty,
                actual,
            }
        })?;
        let candidate = staged.tm_fv(
            staged.fresh_name(&[self.values.value_ty, self.values.bool_ty, self.member, list])?,
            self.values.value_ty,
        )?;
        let contains = apply(&mut staged, self.member, &[candidate, list])?;
        let absent = staged.op1(Op1::Not, contains)?;
        let proposition = staged.forall_tm(self.values.bool_ty, candidate, absent)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Derives absence of members from checked exact membership semantics for
    /// an empty finite sequence.
    ///
    /// Every premise of `membership_fact` remains visible. No property of the
    /// membership operation is assumed beyond the supplied checked theorem.
    ///
    /// # Errors
    ///
    /// Returns an error unless `law` has no elements and `membership_fact`
    /// positively proves its exact proposition, or a checked specialization,
    /// equality, contradiction, universal, or alignment step fails. `kernel`
    /// is unchanged on failure.
    pub fn prove_empty_has_no_members(
        self,
        kernel: &mut Kernel,
        law: &FiniteSequenceLaw,
        membership_fact: ThmId,
    ) -> Result<Evidence, StructuralValueProofError> {
        if !law.elements.is_empty() {
            return Err(StructuralValueProofError::NonemptySequence);
        }
        let mut staged = kernel.fork();
        let source = positive_conclusion(&staged, membership_fact)?;
        let membership_fact = staged.copy_theorem(membership_fact)?;
        if source != law.proposition {
            join_alpha_equivalent(&mut staged, source, law.proposition)?;
            staged.convert_conclusions(membership_fact, source, law.proposition)?;
        }
        let candidate = staged.tm_fv(
            staged.fresh_name(&[
                self.values.value_ty,
                self.values.bool_ty,
                self.member,
                law.list,
                law.binder,
                law.proposition,
            ])?,
            self.values.value_ty,
        )?;
        let specialized = forall_elim(&mut staged, membership_fact, candidate)?;
        let contains = apply(&mut staged, self.member, &[candidate, law.list])?;
        let falsehood = staged.bool(self.values.bool_ty, false)?;
        let equality = staged.eq(self.values.bool_ty, contains, falsehood)?;
        join_alpha_equivalent(&mut staged, specialized.proposition, equality)?;
        staged.convert_conclusions(specialized.theorem, specialized.proposition, equality)?;
        let assumed = staged.identity(positive(contains))?;
        let impossible = staged.eq_mp(specialized.theorem, assumed)?;
        let false_left = staged.false_left(positive(falsehood))?;
        let contradiction = staged.cut(impossible, false_left, positive(falsehood))?;
        staged.not_right(contradiction, positive(contains))?;
        let absent = staged.op1(Op1::Not, contains)?;
        let flattened = staged.flatten_conclusion(contradiction, positive(contains).negated())?;
        let absent_fact = staged.fold_conclusion(flattened, positive(absent))?;
        let direct = staged.forall_tm(self.values.bool_ty, candidate, absent)?;
        let theorem = staged.forall_intro_at(absent_fact, candidate, direct)?;
        let canonical = self.no_members(&mut staged, law.list)?;
        join_alpha_equivalent(&mut staged, direct, canonical)?;
        staged.convert_conclusions(theorem, direct, canonical)?;
        *kernel = staged;
        Ok(Evidence {
            proposition: canonical,
            theorem,
            holds: true,
        })
    }
}

/// Failure to derive a checked structural-value algebra law.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum StructuralValueProofError {
    /// Empty-sequence elimination was requested for a nonempty law.
    #[snafu(display("expected an empty finite-sequence law"))]
    NonemptySequence,
    /// A checked kernel operation failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Universal specialization failed.
    #[snafu(transparent)]
    Forall {
        /// Underlying derived universal-elimination failure.
        source: ForallError,
    },
    /// Checked formulas could not be aligned.
    #[snafu(transparent)]
    Syntax {
        /// Underlying alpha-equivalence failure.
        source: SyntaxError,
    },
}

fn positive(proposition: Ref) -> Lit {
    Lit::positive(proposition.get())
}

fn positive_conclusion(kernel: &Kernel, theorem: ThmId) -> Result<Ref, KernelError> {
    let theorem = kernel
        .thm()
        .get(theorem)
        .ok_or(KernelError::MissingTheorem { id: theorem })?;
    let mut conclusions = theorem.rhs.rows();
    let Some([literal]) = conclusions.next() else {
        return Err(KernelError::InvalidTheoremRule {
            rule: "structural value proof unit conclusion",
        });
    };
    if conclusions.next().is_some() || !literal.is_positive() {
        return Err(KernelError::InvalidTheoremRule {
            rule: "structural value proof positive conclusion",
        });
    }
    Ref::new(literal.magnitude().cast_signed()).ok_or(KernelError::InvalidTheoremRule {
        rule: "structural value proof conclusion reference",
    })
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
    use super::{StructuralSequenceAlgebra, StructuralValueAlgebra, apply};
    use crate::EvidenceScope;
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
        let member_tail = kernel.ty_arr(value_ty, bool_ty).unwrap();
        let member_ty = kernel.ty_arr(value_ty, member_tail).unwrap();
        let empty = kernel.tm_fv(9, value_ty).unwrap();
        let unary = kernel.tm_fv(10, unary_ty).unwrap();
        let binary = kernel.tm_fv(11, binary_ty).unwrap();
        let member = kernel.tm_fv(13, member_ty).unwrap();
        let algebra = StructuralValueAlgebra { value_ty, bool_ty };
        let empty = algebra.constructor(&mut kernel, empty, 0).unwrap();
        let unary = algebra.constructor(&mut kernel, unary, 1).unwrap();
        let binary = algebra.constructor(&mut kernel, binary, 2).unwrap();
        let injective = algebra.injective(&mut kernel, binary).unwrap();
        let disjoint = algebra.disjoint(&mut kernel, unary, binary).unwrap();
        assert_eq!(kernel.classifier(injective).unwrap(), bool_ty);
        assert_eq!(kernel.classifier(disjoint).unwrap(), bool_ty);

        let sequences = StructuralSequenceAlgebra::new(&mut kernel, algebra, member).unwrap();
        let empty_law = sequences.membership_law(&mut kernel, empty, &[]).unwrap();
        let element = kernel.tm_fv(12, value_ty).unwrap();
        let singleton_law = sequences
            .membership_law(&mut kernel, unary, &[element])
            .unwrap();
        assert!(empty_law.elements().is_empty());
        assert_eq!(singleton_law.elements(), &[element]);
        assert_eq!(kernel.classifier(empty_law.proposition()).unwrap(), bool_ty);
        assert_eq!(
            kernel.classifier(singleton_law.proposition()).unwrap(),
            bool_ty
        );
        let empty_fact = kernel
            .identity(super::positive(empty_law.proposition()))
            .unwrap();
        let no_members = sequences
            .prove_empty_has_no_members(&mut kernel, &empty_law, empty_fact)
            .unwrap();
        EvidenceScope::positive(&[empty_law.proposition()])
            .check(&kernel, no_members)
            .unwrap();

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

        let applied = apply(&mut kernel, unary.operation(), &[element]).unwrap();
        assert_eq!(kernel.classifier(applied).unwrap(), value_ty);

        let before = kernel.arena().clone();
        assert!(
            algebra
                .constructor(&mut kernel, unary.operation(), 2)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert!(
            sequences
                .prove_empty_has_no_members(&mut kernel, &singleton_law, empty_fact)
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
        assert!(sequences.membership_law(&mut kernel, unary, &[]).is_err());
        assert_eq!(kernel.arena(), &before);
        assert!(
            algebra
                .constructor_laws(&mut kernel, &[unary, unary])
                .is_err()
        );
        assert_eq!(kernel.arena(), &before);
    }
}
