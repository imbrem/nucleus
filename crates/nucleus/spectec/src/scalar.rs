//! Typed handles and algebraic goal schemas for WebAssembly scalar values.
//!
//! The types and operations here are checked HOL terms supplied by a semantic
//! interpretation. Rust never evaluates an operation or turns a host result
//! into theorem evidence.

use covalence_lib_error::snafu::Snafu;
use covalence_logic_hol::{Kernel, KernelError, Ref, ThmId};
use covalence_logic_hol_derived::{
    ForallError, SyntaxError, forall_elim, join_alpha_equivalent, join_same_syntax,
};

use crate::Evidence;

/// One WebAssembly scalar type.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum WasmScalarKind {
    /// A 32-bit integer bit vector.
    I32,
    /// A 64-bit integer bit vector.
    I64,
    /// An IEEE-754 binary32 value.
    F32,
    /// An IEEE-754 binary64 value.
    F64,
    /// A 128-bit SIMD vector.
    V128,
}

/// Checked HOL classifiers for all WebAssembly scalar kinds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WasmScalarTypes {
    /// `i32` classifier.
    pub i32: Ref,
    /// `i64` classifier.
    pub i64: Ref,
    /// `f32` classifier.
    pub f32: Ref,
    /// `f64` classifier.
    pub f64: Ref,
    /// `v128` classifier.
    pub v128: Ref,
}

impl WasmScalarTypes {
    /// Returns the classifier for `kind`.
    #[must_use]
    pub const fn get(self, kind: WasmScalarKind) -> Ref {
        match kind {
            WasmScalarKind::I32 => self.i32,
            WasmScalarKind::I64 => self.i64,
            WasmScalarKind::F32 => self.f32,
            WasmScalarKind::F64 => self.f64,
            WasmScalarKind::V128 => self.v128,
        }
    }
}

/// A checked scalar term paired with its WebAssembly kind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WasmScalar {
    kind: WasmScalarKind,
    term: Ref,
}

impl WasmScalar {
    pub(crate) const fn from_checked(kind: WasmScalarKind, term: Ref) -> Self {
        Self { kind, term }
    }

    /// Returns the scalar kind.
    #[must_use]
    pub const fn kind(self) -> WasmScalarKind {
        self.kind
    }

    /// Returns the underlying HOL term.
    #[must_use]
    pub const fn term(self) -> Ref {
        self.term
    }
}

/// One checked, kind-preserving WebAssembly binary scalar operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WasmScalarBinary {
    kind: WasmScalarKind,
    scalar_ty: Ref,
    bool_ty: Ref,
    operation: Ref,
}

impl WasmScalarBinary {
    /// Returns the scalar kind consumed and produced by this operation.
    #[must_use]
    pub const fn kind(self) -> WasmScalarKind {
        self.kind
    }

    /// Applies the operation to two same-kind scalar terms.
    ///
    /// # Errors
    ///
    /// Returns an error unless both operands have this operation's scalar
    /// classifier. `kernel` is unchanged on failure.
    pub fn apply(
        self,
        kernel: &mut Kernel,
        left: WasmScalar,
        right: WasmScalar,
    ) -> Result<WasmScalar, KernelError> {
        let mut staged = kernel.fork();
        require_kind(left, self.kind)?;
        require_kind(right, self.kind)?;
        let partial = staged.app(self.operation, left.term)?;
        let term = staged.app(partial, right.term)?;
        require_classifier(&staged, term, self.scalar_ty)?;
        *kernel = staged;
        Ok(WasmScalar::from_checked(self.kind, term))
    }

    /// Constructs the universally quantified commutativity proposition.
    ///
    /// This states an obligation; it does not assume or prove that the
    /// operation is commutative.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application, equality, or quantification
    /// fails. `kernel` is unchanged on failure.
    pub fn commutative(self, kernel: &mut Kernel) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let first = staged.fresh_name(&[self.scalar_ty, self.bool_ty, self.operation])?;
        let left = staged.tm_fv(first, self.scalar_ty)?;
        let right = staged.tm_fv(
            first.checked_add(1).ok_or(KernelError::TooManyNames)?,
            self.scalar_ty,
        )?;
        let partial = staged.app(self.operation, left)?;
        let left_right = staged.app(partial, right)?;
        let partial = staged.app(self.operation, right)?;
        let right_left = staged.app(partial, left)?;
        let equality = staged.eq(self.bool_ty, left_right, right_left)?;
        let right_closed = staged.forall_tm(self.bool_ty, right, equality)?;
        let proposition = staged.forall_tm(self.bool_ty, left, right_closed)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Constructs the universally quantified associativity proposition.
    ///
    /// This states `(x op y) op z = x op (y op z)` as an obligation; it does
    /// not assert that every Wasm operation is associative. In particular,
    /// callers must supply appropriate checked evidence for the selected
    /// integer, floating-point, or SIMD operation.
    ///
    /// # Errors
    ///
    /// Returns an error if checked application, equality, or quantification
    /// fails. `kernel` is unchanged on failure.
    pub fn associative(self, kernel: &mut Kernel) -> Result<Ref, KernelError> {
        let mut staged = kernel.fork();
        let first = staged.fresh_name(&[self.scalar_ty, self.bool_ty, self.operation])?;
        let x = WasmScalar::from_checked(self.kind, staged.tm_fv(first, self.scalar_ty)?);
        let y = WasmScalar::from_checked(
            self.kind,
            staged.tm_fv(
                first.checked_add(1).ok_or(KernelError::TooManyNames)?,
                self.scalar_ty,
            )?,
        );
        let z = WasmScalar::from_checked(
            self.kind,
            staged.tm_fv(
                first.checked_add(2).ok_or(KernelError::TooManyNames)?,
                self.scalar_ty,
            )?,
        );
        let xy = self.apply(&mut staged, x, y)?;
        let xy_z = self.apply(&mut staged, xy, z)?;
        let yz = self.apply(&mut staged, y, z)?;
        let x_yz = self.apply(&mut staged, x, yz)?;
        let equality = staged.eq(self.bool_ty, xy_z.term, x_yz.term)?;
        let by_z = staged.forall_tm(self.bool_ty, z.term, equality)?;
        let by_y = staged.forall_tm(self.bool_ty, y.term, by_z)?;
        let proposition = staged.forall_tm(self.bool_ty, x.term, by_y)?;
        *kernel = staged;
        Ok(proposition)
    }

    /// Specializes a checked commutativity theorem to two scalar operands.
    ///
    /// Every premise of `commutativity` remains visible in the result. This
    /// method does not claim that an operation is commutative merely because
    /// it is packaged as a WebAssembly scalar operation.
    ///
    /// # Errors
    ///
    /// Returns an error unless `commutativity` proves this operation's exact
    /// universally quantified law, both operands have the configured kind, or
    /// a checked specialization step fails. `kernel` is unchanged on failure.
    pub fn prove_commutes(
        self,
        kernel: &mut Kernel,
        commutativity: ThmId,
        left: WasmScalar,
        right: WasmScalar,
    ) -> Result<Evidence, WasmScalarProofError> {
        require_kind(left, self.kind)?;
        require_kind(right, self.kind)?;
        let mut staged = kernel.fork();
        let law = self.commutative(&mut staged)?;
        let law = align_positive(&mut staged, commutativity, law)?;
        let at_left = forall_elim(&mut staged, law, left.term)?;
        let at_right = forall_elim(&mut staged, at_left.theorem, right.term)?;
        let left_right = self.apply(&mut staged, left, right)?;
        let right_left = self.apply(&mut staged, right, left)?;
        let proposition = staged.eq(self.bool_ty, left_right.term, right_left.term)?;
        join_alpha_equivalent(&mut staged, at_right.proposition, proposition)?;
        staged.convert_conclusions(at_right.theorem, at_right.proposition, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem: at_right.theorem,
            holds: true,
        })
    }

    /// Specializes a checked associativity theorem to three scalar operands.
    ///
    /// Every premise of `associativity` remains visible in the result.
    ///
    /// # Errors
    ///
    /// Returns an error unless `associativity` proves this operation's exact
    /// universally quantified law, all operands have the configured kind, or
    /// checked specialization fails. `kernel` is unchanged on failure.
    pub fn prove_associates(
        self,
        kernel: &mut Kernel,
        associativity: ThmId,
        x: WasmScalar,
        y: WasmScalar,
        z: WasmScalar,
    ) -> Result<Evidence, WasmScalarProofError> {
        require_kind(x, self.kind)?;
        require_kind(y, self.kind)?;
        require_kind(z, self.kind)?;
        let mut staged = kernel.fork();
        let law = self.associative(&mut staged)?;
        let law = align_positive(&mut staged, associativity, law)?;
        let at_x = forall_elim(&mut staged, law, x.term)?;
        let at_y = forall_elim(&mut staged, at_x.theorem, y.term)?;
        let at_z = forall_elim(&mut staged, at_y.theorem, z.term)?;
        let xy = self.apply(&mut staged, x, y)?;
        let xy_z = self.apply(&mut staged, xy, z)?;
        let yz = self.apply(&mut staged, y, z)?;
        let x_yz = self.apply(&mut staged, x, yz)?;
        let proposition = staged.eq(self.bool_ty, xy_z.term, x_yz.term)?;
        join_alpha_equivalent(&mut staged, at_z.proposition, proposition)?;
        staged.convert_conclusions(at_z.theorem, at_z.proposition, proposition)?;
        *kernel = staged;
        Ok(Evidence {
            proposition,
            theorem: at_z.theorem,
            holds: true,
        })
    }
}

/// Failure to specialize a checked scalar-operation law.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum WasmScalarProofError {
    /// A checked HOL construction failed.
    #[snafu(transparent)]
    Kernel {
        /// Underlying checked failure.
        source: KernelError,
    },
    /// Universal specialization failed.
    #[snafu(transparent)]
    Forall {
        /// Underlying specialization failure.
        source: ForallError,
    },
    /// Formula alignment failed.
    #[snafu(transparent)]
    Syntax {
        /// Underlying syntax-certification failure.
        source: SyntaxError,
    },
}

/// Checked scalar vocabulary for one Wasm semantic interpretation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WasmScalars {
    /// Scalar classifiers.
    pub types: WasmScalarTypes,
    /// HOL Boolean classifier.
    pub bool_ty: Ref,
}

impl WasmScalars {
    /// Checks and wraps one scalar term.
    ///
    /// # Errors
    ///
    /// Returns an error unless `term` has the classifier selected by `kind`.
    pub fn scalar(
        self,
        kernel: &Kernel,
        kind: WasmScalarKind,
        term: Ref,
    ) -> Result<WasmScalar, KernelError> {
        require_classifier(kernel, term, self.types.get(kind))?;
        Ok(WasmScalar::from_checked(kind, term))
    }

    /// Checks and wraps one kind-preserving binary operation.
    ///
    /// # Errors
    ///
    /// Returns an error unless `operation` has classifier
    /// `scalar -> scalar -> scalar` for the selected kind. `kernel` is
    /// unchanged on failure.
    pub fn binary(
        self,
        kernel: &mut Kernel,
        kind: WasmScalarKind,
        operation: Ref,
    ) -> Result<WasmScalarBinary, KernelError> {
        let mut staged = kernel.fork();
        let scalar_ty = self.types.get(kind);
        let tail = staged.ty_arr(scalar_ty, scalar_ty)?;
        let expected = staged.ty_arr(scalar_ty, tail)?;
        require_classifier_mut(&mut staged, operation, expected)?;
        *kernel = staged;
        Ok(WasmScalarBinary {
            kind,
            scalar_ty,
            bool_ty: self.bool_ty,
            operation,
        })
    }
}

fn require_kind(value: WasmScalar, expected: WasmScalarKind) -> Result<(), KernelError> {
    if value.kind == expected {
        Ok(())
    } else {
        Err(KernelError::InvalidTheoremRule {
            rule: "Wasm scalar kind",
        })
    }
}

fn require_classifier(kernel: &Kernel, term: Ref, expected: Ref) -> Result<(), KernelError> {
    let actual = kernel.classifier(term)?;
    if kernel.equivalent(actual, expected)? {
        Ok(())
    } else {
        Err(KernelError::ClassifierMismatch { expected, actual })
    }
}

fn require_classifier_mut(
    kernel: &mut Kernel,
    term: Ref,
    expected: Ref,
) -> Result<(), KernelError> {
    let actual = kernel.classifier(term)?;
    if kernel.equivalent(actual, expected)? || join_same_syntax(kernel, actual, expected).is_ok() {
        Ok(())
    } else {
        Err(KernelError::ClassifierMismatch { expected, actual })
    }
}

fn align_positive(kernel: &mut Kernel, theorem: ThmId, target: Ref) -> Result<ThmId, KernelError> {
    let source = {
        let theorem = kernel
            .thm()
            .get(theorem)
            .ok_or(KernelError::MissingTheorem { id: theorem })?;
        let mut rows = theorem.rhs.rows();
        let Some([literal]) = rows.next() else {
            return Err(KernelError::InvalidTheoremRule {
                rule: "Wasm scalar law unit conclusion",
            });
        };
        if rows.next().is_some() || !literal.is_positive() {
            return Err(KernelError::InvalidTheoremRule {
                rule: "Wasm scalar law positive conclusion",
            });
        }
        Ref::new(literal.magnitude().cast_signed()).ok_or(KernelError::InvalidTheoremRule {
            rule: "Wasm scalar law conclusion reference",
        })?
    };
    join_alpha_equivalent(kernel, source, target).map_err(|_| KernelError::InvalidTheoremRule {
        rule: "Wasm scalar law conclusion alignment",
    })?;
    let aligned = kernel.copy_theorem(theorem)?;
    kernel.convert_conclusions(aligned, source, target)?;
    Ok(aligned)
}

#[cfg(test)]
mod tests {
    use covalence_logic_hol::Lit;

    use super::*;
    use crate::EvidenceScope;

    #[test]
    fn scalar_operations_are_typed_compositional_and_transactional() {
        let mut kernel = Kernel::new();
        let star = kernel.star().unwrap();
        let bool_ty = kernel.bool_ty(star).unwrap();
        let types = WasmScalarTypes {
            i32: kernel.ty_fv(1, star).unwrap(),
            i64: kernel.ty_fv(2, star).unwrap(),
            f32: kernel.ty_fv(3, star).unwrap(),
            f64: kernel.ty_fv(4, star).unwrap(),
            v128: kernel.ty_fv(5, star).unwrap(),
        };
        let scalars = WasmScalars { types, bool_ty };
        let tail = kernel.ty_arr(types.i32, types.i32).unwrap();
        let binary_ty = kernel.ty_arr(types.i32, tail).unwrap();
        let operation = kernel.tm_fv(10, binary_ty).unwrap();
        let operation = scalars
            .binary(&mut kernel, WasmScalarKind::I32, operation)
            .unwrap();
        let left_term = kernel.tm_fv(11, types.i32).unwrap();
        let left = scalars
            .scalar(&kernel, WasmScalarKind::I32, left_term)
            .unwrap();
        let right_term = kernel.tm_fv(12, types.i32).unwrap();
        let right = scalars
            .scalar(&kernel, WasmScalarKind::I32, right_term)
            .unwrap();
        let result = operation.apply(&mut kernel, left, right).unwrap();
        assert_eq!(result.kind(), WasmScalarKind::I32);
        assert!(
            kernel
                .equivalent(kernel.classifier(result.term()).unwrap(), types.i32)
                .unwrap()
        );
        let commutative = operation.commutative(&mut kernel).unwrap();
        assert!(
            kernel
                .equivalent(kernel.classifier(commutative).unwrap(), bool_ty)
                .unwrap()
        );
        let commutativity_fact = kernel.identity(Lit::positive(commutative.get())).unwrap();
        let swapped = operation
            .prove_commutes(&mut kernel, commutativity_fact, left, right)
            .unwrap();
        EvidenceScope::positive(&[commutative])
            .check(&kernel, swapped)
            .unwrap();
        let third_term = kernel.tm_fv(14, types.i32).unwrap();
        let third = scalars
            .scalar(&kernel, WasmScalarKind::I32, third_term)
            .unwrap();
        let associative = operation.associative(&mut kernel).unwrap();
        let associativity_fact = kernel.identity(Lit::positive(associative.get())).unwrap();
        let reassociated = operation
            .prove_associates(&mut kernel, associativity_fact, left, right, third)
            .unwrap();
        EvidenceScope::positive(&[associative])
            .check(&kernel, reassociated)
            .unwrap();

        let wrong_term = kernel.tm_fv(13, types.i64).unwrap();
        let wrong = scalars
            .scalar(&kernel, WasmScalarKind::I64, wrong_term)
            .unwrap();
        let before = kernel.arena().clone();
        assert!(operation.apply(&mut kernel, left, wrong).is_err());
        assert_eq!(kernel.arena(), &before);
    }
}
