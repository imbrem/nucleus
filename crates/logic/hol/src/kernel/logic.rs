//! Derived logical constructions over the Ethane primitives.
//!
//! Ethane's core has equality, lambda, application, choice, and Boolean
//! literals. The connectives and quantifiers are *macros* over those — nothing
//! here appends a new row shape or checks a new rule, and none of it is
//! trusted beyond the primitive constructors it calls.
//!
//! Each definition mirrors `Nucleus.Hol.Ethane.Expr` in
//! `lean/Nucleus/Nucleus/Hol/Ethane/Logic.lean` term for term. That
//! correspondence is load-bearing: the guarded subtype package in
//! [`subtype`](super::subtype) is proved sound in Lean against *these*
//! encodings, so a Rust construction that spells a connective differently is
//! not covered by that proof.
//!
//! ## Why not the `Op1`/`Op2` builtins
//!
//! [`Kernel::op1`](super::Kernel::op1) / [`op2`](super::Kernel::op2) and
//! [`lower_logical`](super::Kernel::lower_logical) are a second, independent
//! Boolean encoding: compact rows whose meaning is supplied by applying the
//! init manifest's `not`/`and`/`or`/`imp` *definitions*. That encoding is not
//! interchangeable with this one — the manifest defines `false` as
//! `(λx. x) = (λy. true)` where this uses the primitive literal — and no
//! lemma yet relates them. The subtype package is built here rather than
//! there because that is where the soundness proof is.
//!
//! ## Binders are rows, not names
//!
//! The Lean encodings take a binder *name*; a checked Ethane binder is a
//! `tm.fv` row instead, so each function here takes the binder's reference and
//! a body already written against it. Choosing a binder that does not capture
//! is therefore the caller's problem, exactly as it is in Lean, and
//! [`subtype`](super::subtype) documents how it discharges that.

use std::convert::Infallible;

use super::{Kernel, KernelError};
use crate::Ref;

impl Kernel {
    /// Appends `¬ proposition`, which is `proposition = false`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `bool_ty` is Boolean and `proposition` is a
    /// Boolean term.
    pub fn not_tm(&mut self, bool_ty: Ref, proposition: Ref) -> Result<Ref, KernelError> {
        let falsehood = self.bool(bool_ty, false)?;
        self.eq(bool_ty, proposition, falsehood)
    }

    /// Appends `∀ binder. body`, which is
    /// `(λ binder. body) = (λ binder. true)`.
    ///
    /// # Errors
    ///
    /// Returns an error unless `bool_ty` is Boolean, `binder` is a `tm.fv`
    /// row, and `body` is a Boolean term.
    pub fn forall_tm(&mut self, bool_ty: Ref, binder: Ref, body: Ref) -> Result<Ref, KernelError> {
        self.require_bool_term::<Infallible>(body)?;
        // Both lambdas must carry the *same* arrow row: Ethane's type equality
        // is the row union-find, so two structurally identical arrows appended
        // separately are not equal and the equality below would be rejected.
        let domain = self.classifier(binder)?;
        let function_ty = self.ty_arr(domain, bool_ty)?;
        let predicate = self.lam_at(function_ty, binder, body)?;
        let truth = self.bool(bool_ty, true)?;
        let constant = self.lam_at(function_ty, binder, truth)?;
        self.eq(bool_ty, predicate, constant)
    }

    /// Appends `∃ binder. body` by Hilbert choice, which is
    /// `(λ binder. body) (ε (λ binder. body))`.
    ///
    /// Both occurrences of the predicate are the same row, as in Lean's
    /// `existsTm`, so the term stays a DAG rather than a tree.
    ///
    /// # Errors
    ///
    /// Returns an error unless `binder` is a `tm.fv` row and `body` is a
    /// Boolean term.
    pub fn exists_tm(&mut self, binder: Ref, body: Ref) -> Result<Ref, KernelError> {
        self.require_bool_term::<Infallible>(body)?;
        let predicate = self.lam(binder, body)?;
        let domain = self.classifier(binder)?;
        let choice = self.eps(domain, predicate)?;
        self.app(predicate, choice)
    }

    /// Appends `left ∧ right`, in the equality-only HOL encoding
    /// `(λf. f left right) = (λf. f true true)`.
    ///
    /// `binder` is the bound function variable and must have type
    /// `bool → bool → bool`. It occurs bound in both operands of the equality,
    /// so it may be the same row for nested conjunctions — Lean's `and` reuses
    /// one name the same way.
    ///
    /// # Errors
    ///
    /// Returns an error unless `bool_ty` is Boolean, `binder` is a `tm.fv` row
    /// of the binary Boolean function type, and both operands are Boolean
    /// terms.
    pub fn and_tm(
        &mut self,
        bool_ty: Ref,
        binder: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        self.require_bool_term::<Infallible>(left)?;
        self.require_bool_term::<Infallible>(right)?;
        // One arrow row for both lambdas; see `forall_tm`.
        let binder_ty = self.classifier(binder)?;
        let function_ty = self.ty_arr(binder_ty, bool_ty)?;
        let applied = self.app(binder, left)?;
        let lhs_body = self.app(applied, right)?;
        let lhs = self.lam_at(function_ty, binder, lhs_body)?;
        let truth = self.bool(bool_ty, true)?;
        let applied_true = self.app(binder, truth)?;
        let rhs_body = self.app(applied_true, truth)?;
        let rhs = self.lam_at(function_ty, binder, rhs_body)?;
        self.eq(bool_ty, lhs, rhs)
    }

    /// Appends `left ∨ right`, which is `¬(¬left ∧ ¬right)`.
    ///
    /// # Errors
    ///
    /// As [`and_tm`](Self::and_tm).
    pub fn or_tm(
        &mut self,
        bool_ty: Ref,
        binder: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        let not_left = self.not_tm(bool_ty, left)?;
        let not_right = self.not_tm(bool_ty, right)?;
        let conjunction = self.and_tm(bool_ty, binder, not_left, not_right)?;
        self.not_tm(bool_ty, conjunction)
    }

    /// Appends `left → right`, which is `¬(left ∧ ¬right)`.
    ///
    /// # Errors
    ///
    /// As [`and_tm`](Self::and_tm).
    pub fn imp_tm(
        &mut self,
        bool_ty: Ref,
        binder: Ref,
        left: Ref,
        right: Ref,
    ) -> Result<Ref, KernelError> {
        let not_right = self.not_tm(bool_ty, right)?;
        let conjunction = self.and_tm(bool_ty, binder, left, not_right)?;
        self.not_tm(bool_ty, conjunction)
    }
}
