import Nucleus.Hol.Traits
import Nucleus.HolLN.Variants

/-!
# Relationship to the existing natural-number HOL syntax

The new signature presentation has a first-class successor constant.  The old
syntax represents that constant by its eta-expansion `λx : nat. succ x`; an
applied successor translates directly to the old unary successor node.
-/

namespace Nucleus.Hol.Nat

open Nucleus.Hol

def toExistingRaw : {sort : HolSort} → {depth : Nat} →
    Expr NatSig sort depth → HolLN.Tree.Raw Empty
  | _, _, .primFam .natTy => .natTy
  | _, _, .primTm .zero => .zero
  | _, _, .primTm .succ => .lam .natTy (.succ (.bv 0))
  | _, _, .boolTy => .boolTy
  | _, _, .arr A B => .arr (toExistingRaw A) (toExistingRaw B)
  | .kind codomain, _, @Expr.tyApp _ domain _ function argument =>
      .tyApp domain codomain (toExistingRaw function) (toExistingRaw argument)
  | _, _, .sub A p => .sub (toExistingRaw A) (toExistingRaw p)
  | _, _, .bv i => .bv i
  | _, _, .fv name A => .fv name (toExistingRaw A)
  | _, _, .app (.primTm .succ) value => .succ (toExistingRaw value)
  | _, _, .app function argument => .app (toExistingRaw function) (toExistingRaw argument)
  | _, _, .lam A body => .lam (toExistingRaw A) (toExistingRaw body)
  | _, _, .bool value => .bool value
  | _, _, .eq A left right => .eq (toExistingRaw A) (toExistingRaw left) (toExistingRaw right)
  | _, _, .eps A predicate => .eps (toExistingRaw A) (toExistingRaw predicate)
  | _, _, .abs A predicate value =>
      .abs (toExistingRaw A) (toExistingRaw predicate) (toExistingRaw value)
  | _, _, .rep A predicate value =>
      .rep (toExistingRaw A) (toExistingRaw predicate) (toExistingRaw value)

@[simp] theorem toExistingRaw_natTy : toExistingRaw natTy = (.natTy : HolLN.Tree.Raw Empty) :=
  by simp [natTy, toExistingRaw]

@[simp] theorem toExistingRaw_zero {depth : Nat} :
    toExistingRaw (zero (depth := depth)) = (.zero : HolLN.Tree.Raw Empty) := by
  simp [zero, toExistingRaw]

@[simp] theorem toExistingRaw_succConst {depth : Nat} :
    toExistingRaw (succConst (depth := depth)) =
      (.lam .natTy (.succ (.bv 0)) : HolLN.Tree.Raw Empty) := by
  simp [succConst, toExistingRaw]

@[simp] theorem toExistingRaw_succ {depth : Nat} (value : Tm NatSig depth) :
    toExistingRaw (succ value) = .succ (toExistingRaw value) := by
  simp [succ, succConst, toExistingRaw]

end Nucleus.Hol.Nat
