import Nucleus.Hol.Syntax

/-! Higher-kinded type operators without quantification over types. -/

universe u

namespace Nucleus.HolTypeOperators

abbrev Kind := HolOmega.Kind
abbrev RKind := HolOmega.RKind

inductive ExprSort where | ty | tm

inductive Expr (Base : Type u) : ExprSort → Type u
  | base : Base → Expr Base .ty
  | tyVar : Nat → Expr Base .ty
  | tyLam : RKind → Expr Base .ty → Expr Base .ty
  | tyApp : Expr Base .ty → Expr Base .ty → Expr Base .ty
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
abbrev KindCtx := List RKind
abbrev TmCtx (Base : Type u) := List (Ty Base)

variable {Base : Type u}

def Expr.toOmega : {s : ExprSort} → Expr Base s → HolOmega.Expr Base (match s with
    | .ty => .ty | .tm => .tm)
  | .ty, .base c => .base c
  | .ty, .tyVar n => .tyVar n
  | .ty, .tyLam RK A => .tyLam RK A.toOmega
  | .ty, .tyApp F X => .tyApp F.toOmega X.toOmega
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

def Expr.ofHol : {s : Hol.ExprSort} → Hol.Expr Base s → Expr Base (match s with
    | .ty => .ty | .tm => .tm)
  | .ty, .base c => .base c
  | .ty, .tyBool => .tyBool
  | .ty, .tyArr A B => .tyArr (Expr.ofHol A) (Expr.ofHol B)
  | .ty, .tySub A p => .tySub (Expr.ofHol A) (Expr.ofHol p)
  | .tm, .tmVar n => .tmVar n
  | .tm, .tmApp f x => .tmApp (Expr.ofHol f) (Expr.ofHol x)
  | .tm, .tmLam A t => .tmLam (Expr.ofHol A) (Expr.ofHol t)
  | .tm, .tmBool b => .tmBool b
  | .tm, .tmEq A x y => .tmEq (Expr.ofHol A) (Expr.ofHol x) (Expr.ofHol y)
  | .tm, .tmEps A p => .tmEps (Expr.ofHol A) (Expr.ofHol p)
  | .tm, .tmAbs A p x => .tmAbs (Expr.ofHol A) (Expr.ofHol p) (Expr.ofHol x)
  | .tm, .tmRep A p x => .tmRep (Expr.ofHol A) (Expr.ofHol p) (Expr.ofHol x)

end Nucleus.HolTypeOperators
