import Nucleus.Finset.Nat
import Nucleus.HolE.Named.Unsorted

/-!
# Derived unsorted named HolE syntax

These are definitions, not additions to the trusted syntax.  The fresh name
used by conjunction is chosen outside every name appearing in its arguments,
so the auxiliary lambda cannot capture user syntax.
-/

namespace Nucleus.HolE.Named.Unsorted

set_option relaxedAutoImplicit true

/-- All names occurring in an expression, including binder names.  This is a
conservative support used only to choose hygienic names for derived syntax. -/
def names : Expr Sig Nat → Finset Nat
  | .boolTy | .bool _ | .primFam .. | .primTm .. => ∅
  | .arr A B | .app A B => names A ∪ names B
  | .tyApp _ _ F A => names F ∪ names A
  | .tyLam _ _ name body | .tyExists name body | .model name body =>
      insert name (names body)
  | .tyFv name _ => {name}
  | .sub A name p | .lam name A p => insert name (names A ∪ names p)
  | .tmFv name A => insert name (names A)
  | .eq A x y => names A ∪ names x ∪ names y
  | .eps A p => names A ∪ names p
  | .abs A name p x | .rep A name p x =>
      insert name (names A ∪ names p ∪ names x)

/-- A name absent from both expressions. -/
def freshName (left right : Expr Sig Nat) : Nat :=
  Finset.freshNat (names left ∪ names right)

/-- A let-binding is lambda application. -/
def letTm (name : Nat) (type value body : Expr Sig Nat) : Expr Sig Nat :=
  .app (.lam name type body) value

/-- Boolean negation, defined by equality with false. -/
def not (proposition : Expr Sig Nat) : Expr Sig Nat :=
  .eq .boolTy proposition (.bool false)

/-- Standard equality-only HOL conjunction. -/
def and (left right : Expr Sig Nat) : Expr Sig Nat :=
  let functionType := .arr .boolTy (.arr .boolTy .boolTy)
  let name := freshName left right
  let function := .tmFv name functionType
  let lhs := .lam name functionType (.app (.app function left) right)
  let rhs := .lam name functionType
    (.app (.app function (.bool true)) (.bool true))
  .eq (.arr functionType .boolTy) lhs rhs

/-- Boolean disjunction by De Morgan's law. -/
def or (left right : Expr Sig Nat) : Expr Sig Nat :=
  not (and (not left) (not right))

/-- Boolean implication, defined as `(left ∧ right) = left`. -/
def imp (left right : Expr Sig Nat) : Expr Sig Nat :=
  .eq .boolTy (and left right) left

@[simp] theorem letTm_eq (name : Nat) (type value body : Expr Sig Nat) :
    letTm name type value body = .app (.lam name type body) value := rfl

@[simp] theorem not_eq (proposition : Expr Sig Nat) :
    not proposition = .eq .boolTy proposition (.bool false) := rfl

@[simp] theorem or_eq (left right : Expr Sig Nat) :
    or left right = not (and (not left) (not right)) := rfl

@[simp] theorem imp_eq (left right : Expr Sig Nat) :
    imp left right = .eq .boolTy (and left right) left := rfl

end Nucleus.HolE.Named.Unsorted
