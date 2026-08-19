import Nucleus.HolE.Named.Syntax

/-!
# Unsorted named HolE syntax

This syntax erases the result sort while retaining the kind annotations needed
to reconstruct type application, type abstraction, type variables, and
signature primitives.  `check` validates a caller-supplied sort.  `infer`
determines the result sort from the outer constructor and uses `check` to
validate every argument.
-/

namespace Nucleus.HolE.Named.Unsorted

universe u
set_option relaxedAutoImplicit true

/-- Named HolE syntax without a sort index. -/
inductive Expr (Sig : Signature.{u}) (Name : Type := Nat) : Type (max u 1) where
  | boolTy
  | arr (domain codomain : Expr Sig Name)
  | tyApp (domain codomain : Kind) (function argument : Expr Sig Name)
  | tyLam (domain codomain : Kind) (name : Name) (body : Expr Sig Name)
  | tyFv (name : Name) (kind : Kind)
  | sub (carrier : Expr Sig Name) (name : Name) (predicate : Expr Sig Name)
  | tyExists (name : Name) (predicate : Expr Sig Name)
  | model (name : Name) (predicate : Expr Sig Name)
  | primFam (kind : Kind) (symbol : Sig (.kind kind))
  | primTm (symbol : Sig .tm)
  | tmFv (name : Name) (type : Expr Sig Name)
  | app (function argument : Expr Sig Name)
  | lam (name : Name) (domain body : Expr Sig Name)
  | bool (value : Bool)
  | eq (type left right : Expr Sig Name)
  | eps (type predicate : Expr Sig Name)
  | abs (carrier : Expr Sig Name) (name : Name) (predicate value : Expr Sig Name)
  | rep (carrier : Expr Sig Name) (name : Name) (predicate value : Expr Sig Name)

/-- A sorted named expression with its sort hidden existentially. -/
structure SortedExpr (Sig : Signature.{u}) (Name : Type := Nat) where
  sort : HolSort
  expression : Named.Expr Sig Name sort

/-- The result sort suggested by the outer constructor.  Argument sorts are
validated separately by `check`. -/
def rootSort : Expr Sig Name → HolSort
  | .boolTy | .arr .. | .sub .. | .model .. => .kind .star
  | .tyApp _ codomain .. => .kind codomain
  | .tyLam domain codomain .. => .kind (.arr domain codomain)
  | .tyFv _ kind | .primFam kind _ => .kind kind
  | .tyExists .. | .primTm .. | .tmFv .. | .app .. | .lam .. | .bool .. |
      .eq .. | .eps .. | .abs .. | .rep .. => .tm

/-- Check an unsorted expression against a supplied result sort. -/
def check : (sort : HolSort) → Expr Sig Name → Option (Named.Expr Sig Name sort)
  | .kind expected, .boolTy =>
      if equality : expected = .star then by
        subst expected
        exact some .boolTy
      else none
  | .kind expected, .arr domain codomain =>
      if equality : expected = .star then by
        subst expected
        exact do return .arr (← check (.kind .star) domain) (← check (.kind .star) codomain)
      else none
  | .kind expected, .tyApp domain codomain function argument =>
      if equality : expected = codomain then by
        subst expected
        exact do
          let checkedFunction ← check (.kind (.arr domain codomain)) function
          let checkedArgument ← check (.kind domain) argument
          return .tyApp checkedFunction checkedArgument
      else none
  | .kind expected, .tyLam domain codomain name body =>
      if equality : expected = .arr domain codomain then by
        subst expected
        exact do return .tyLam name (← check (.kind codomain) body)
      else none
  | .kind expected, .tyFv name actual =>
      if equality : expected = actual then by
        subst expected
        exact some (.tyFv name actual)
      else none
  | .kind expected, .sub carrier name predicate =>
      if equality : expected = .star then by
        subst expected
        exact do return .sub (← check (.kind .star) carrier) name (← check .tm predicate)
      else none
  | .kind expected, .model name predicate =>
      if equality : expected = .star then by
        subst expected
        exact do return .model name (← check .tm predicate)
      else none
  | .kind expected, .primFam actual symbol =>
      if equality : expected = actual then by
        subst expected
        exact some (.primFam symbol)
      else none
  | .tm, .tyExists name predicate => return .tyExists name (← check .tm predicate)
  | .tm, .primTm symbol => some (.primTm symbol)
  | .tm, .tmFv name type => return .tmFv name (← check (.kind .star) type)
  | .tm, .app function argument => return .app (← check .tm function) (← check .tm argument)
  | .tm, .lam name domain body =>
      return .lam name (← check (.kind .star) domain) (← check .tm body)
  | .tm, .bool value => some (.bool value)
  | .tm, .eq type left right =>
      return .eq (← check (.kind .star) type) (← check .tm left) (← check .tm right)
  | .tm, .eps type predicate =>
      return .eps (← check (.kind .star) type) (← check .tm predicate)
  | .tm, .abs carrier name predicate value =>
      return .abs (← check (.kind .star) carrier) name (← check .tm predicate)
        (← check .tm value)
  | .tm, .rep carrier name predicate value =>
      return .rep (← check (.kind .star) carrier) name (← check .tm predicate)
        (← check .tm value)
  | _, _ => none

/-- Infer the result sort and validate all argument sorts. -/
def infer (expression : Expr Sig Name) : Option (SortedExpr Sig Name) := do
  let sort := rootSort expression
  return ⟨sort, ← check sort expression⟩

/-- Erase the sort index of a sorted named expression. -/
def erase : {sort : HolSort} → Named.Expr Sig Name sort → Expr Sig Name
  | _, .boolTy => .boolTy
  | _, .arr domain codomain => .arr (erase domain) (erase codomain)
  | .kind codomain, @Named.Expr.tyApp _ _ domain _ function argument =>
      .tyApp domain codomain (erase function) (erase argument)
  | .kind (.arr domain codomain), .tyLam name body =>
      .tyLam domain codomain name (erase body)
  | .kind kind, .tyFv name _ => .tyFv name kind
  | _, .sub carrier name predicate => .sub (erase carrier) name (erase predicate)
  | _, .tyExists name predicate => .tyExists name (erase predicate)
  | _, .model name predicate => .model name (erase predicate)
  | .kind kind, .primFam symbol => .primFam kind symbol
  | _, .primTm symbol => .primTm symbol
  | _, .tmFv name type => .tmFv name (erase type)
  | _, .app function argument => .app (erase function) (erase argument)
  | _, .lam name domain body => .lam name (erase domain) (erase body)
  | _, .bool value => .bool value
  | _, .eq type left right => .eq (erase type) (erase left) (erase right)
  | _, .eps type predicate => .eps (erase type) (erase predicate)
  | _, .abs carrier name predicate value =>
      .abs (erase carrier) name (erase predicate) (erase value)
  | _, .rep carrier name predicate value =>
      .rep (erase carrier) name (erase predicate) (erase value)

@[simp] theorem rootSort_erase (expression : Named.Expr Sig Name sort) :
    rootSort (erase expression) = sort := by
  cases expression <;> rfl

@[simp] theorem check_erase (expression : Named.Expr Sig Name sort) :
    check sort (erase expression) = some expression := by
  induction expression <;> simp_all [erase, check]

@[simp] theorem infer_erase (expression : Named.Expr Sig Name sort) :
    infer (erase expression) = some ⟨sort, expression⟩ := by
  cases expression <;> simp [infer, erase, rootSort, check]

section Examples

variable (Sig : Signature) (Name : Type)

/-- Checking rejects a correct constructor at the wrong result sort. -/
example : check (Sig := Sig) (Name := Name) .tm .boolTy = none := rfl

/-- Inference rejects a term constructor whose child has the wrong sort. -/
example : infer (Sig := Sig) (Name := Name) (.app .boolTy (.bool true)) = none := rfl

/-- Inference also validates the annotated argument kind of type application. -/
example (name : Name) : infer (Sig := Sig) (Name := Name)
    (.tyApp .star .star .boolTy (.tyFv name (.arr .star .star))) =
    none := by
  simp [infer, rootSort, check]

end Examples

end Nucleus.HolE.Named.Unsorted
