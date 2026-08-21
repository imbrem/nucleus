import Nucleus.HolE.EmptyRules

/-!
# Checked derived logic for the empty HolE signature

The connectives are syntax macros over equality, lambda, application, and
choice.  They add no constructors or trusted proof rules.
-/

namespace Nucleus.HolE.Empty

open Nucleus.HolE

set_option relaxedAutoImplicit true

def not {types depth} {Γ : Ctx types depth}
    (proposition : BoolTm Γ) : BoolTm Γ :=
  Term.eq FamK.boolTy proposition (Term.falsehood Γ)

/-- Universal quantification as equality with the constantly true function. -/
def forallTm {types depth} {Γ : Ctx types depth}
    (A : Ty types) (body : BoolTm (Γ.extend A)) : BoolTm Γ :=
  Term.eq (A.arr FamK.boolTy) (Term.lam A body)
    (Term.lam A (Term.truth (Γ.extend A)))

/-- Choice-based existential quantification. -/
def existsTm {types depth} {Γ : Ctx types depth}
    (A : Ty types) (body : BoolTm (Γ.extend A)) : BoolTm Γ :=
  let predicate := Term.lam A body
  Term.app predicate (Term.eps A predicate)

/-- The standard equality-only definition of conjunction. -/
def andLegacy {types depth} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : BoolTm Γ := by
  let functionType : Ty types := FamK.boolTy.arr (FamK.boolTy.arr FamK.boolTy)
  let extended := Γ.extend functionType
  let function : Term extended functionType := Term.bv extended 0
  let lhsBody := Term.app (Term.app function (left.weaken functionType))
    (right.weaken functionType)
  let lhs := Term.lam functionType lhsBody
  let truth : BoolTm extended := Term.truth extended
  let rhsBody := Term.app (Term.app function truth) truth
  let rhs := Term.lam functionType rhsBody
  exact Term.eq (functionType.arr FamK.boolTy) lhs rhs

/-- The Boolean binary-operation type used by conjunction. -/
abbrev andFunctionType {types : List Kind} : Ty types :=
  FamK.boolTy.arr (FamK.boolTy.arr FamK.boolTy)

/-- The body of the left function in the equality definition. -/
def andLhsBody {types depth} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : BoolTm (Γ.extend andFunctionType) :=
  let function : Term (Γ.extend andFunctionType) andFunctionType :=
    Term.bv (Γ.extend andFunctionType) 0
  Term.app (Term.app function (left.weaken andFunctionType))
    (right.weaken andFunctionType)

def andLhs {types depth} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : Term Γ (andFunctionType.arr FamK.boolTy) :=
  Term.lam andFunctionType (andLhsBody left right)

/-- The constantly-true reference function in the equality definition. -/
def andRhs {types depth} {Γ : Ctx types depth} :
    Term Γ (andFunctionType.arr FamK.boolTy) :=
  andLhs (Term.truth Γ) (Term.truth Γ)

/-- A decomposed view of the equality-only definition of conjunction. -/
def andView {types depth} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : BoolTm Γ :=
  Term.eq (andFunctionType.arr FamK.boolTy) (andLhs left right) andRhs

/-- The standard equality-only HOL definition of conjunction. -/
def and {types depth} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : BoolTm Γ :=
  andLegacy left right

theorem and_eq_view {types depth} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : and left right = andView left right := by
  rw [Term.mk.injEq]
  simp [and, andLegacy, andView, andLhs, andLhsBody, andRhs,
    andFunctionType, Term.eq, Term.lam, Term.app, Term.bv, Term.weaken,
    Term.truth, Term.bool, HolE.weaken, HolE.rename]

def or {types depth} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : BoolTm Γ :=
  not (and (not left) (not right))

def imp {types depth} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : BoolTm Γ :=
  not (and left (not right))

end Nucleus.HolE.Empty
