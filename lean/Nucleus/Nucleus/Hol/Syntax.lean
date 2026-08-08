import Nucleus.HolOmega.Syntax

/-! Raw syntax for the monomorphic HOL fragment and its inclusion in HOL-omega. -/

universe u

namespace Nucleus.Hol

inductive ExprSort where | ty | tm

/-- The ordinary HOL trees.  This deliberately has no type variables, type
lambda/application, or universal types. -/
inductive Expr (Base : Type u) : ExprSort → Type u
  | base : Base → Expr Base .ty
  | tyBool : Expr Base .ty
  | tyArr : Expr Base .ty → Expr Base .ty → Expr Base .ty
  | tySub : Expr Base .ty → Expr Base .tm → Expr Base .ty
  | tmVar : Nat → Expr Base .tm
  | tmApp : Expr Base .tm → Expr Base .tm → Expr Base .tm
  | tmLam : Expr Base .ty → Expr Base .tm → Expr Base .tm
  | tmBool : Bool → Expr Base .tm
  | tmEq : Expr Base .ty → Expr Base .tm → Expr Base .tm → Expr Base .tm
  | tmEps : Expr Base .ty → Expr Base .tm → Expr Base .tm
  | tmAbs : Expr Base .ty → Expr Base .tm → Expr Base .tm → Expr Base .tm
  | tmRep : Expr Base .ty → Expr Base .tm → Expr Base .tm → Expr Base .tm

abbrev Ty (Base : Type u) := Expr Base .ty
abbrev Tm (Base : Type u) := Expr Base .tm
abbrev Ctx (Base : Type u) := List (Ty Base)

variable {Base : Type u}

/-- Constructor-for-constructor inclusion of ordinary HOL into HOL-omega. -/
def Expr.toOmega : {s : ExprSort} → Expr Base s → HolOmega.Expr Base (match s with
    | .ty => .ty | .tm => .tm)
  | .ty, .base c => .base c
  | .ty, .tyBool => .tyBool
  | .ty, .tyArr A B => .tyArr A.toOmega B.toOmega
  | .ty, .tySub A p => .tySub A.toOmega p.toOmega
  | .tm, .tmVar n => .tmVar n
  | .tm, .tmApp f x => .tmApp f.toOmega x.toOmega
  | .tm, .tmLam A t => .tmLam A.toOmega t.toOmega
  | .tm, .tmBool b => .tmBool b
  | .tm, .tmEq A x y => .tmEq A.toOmega x.toOmega y.toOmega
  | .tm, .tmEps A p => .tmEps A.toOmega p.toOmega
  | .tm, .tmAbs A p x => .tmAbs A.toOmega p.toOmega x.toOmega
  | .tm, .tmRep A p x => .tmRep A.toOmega p.toOmega x.toOmega

end Nucleus.Hol
