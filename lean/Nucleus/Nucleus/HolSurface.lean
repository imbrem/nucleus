/-!
# Rust HolE surface syntax

This is the Lean specification of `covalence-logic-hol`'s checked syntax DAG.
Every child is one representation-owned index. Types and terms additionally
carry their checked result kind or type inline.

Links are surface constructors, not logical constructors. A successful link
resolution must produce a closed, checked type or term with the recorded sort.
-/

namespace Nucleus.HolSurface

universe u

structure Repr where
  Ix : Type u
  Name : Type u
  Link : Type u

structure Kind (R : Repr) where
  index : R.Ix

structure Ty (R : Repr) where
  index : R.Ix
  kind : Kind R

structure Tm (R : Repr) where
  index : R.Ix
  ty : Ty R

inductive ExprSort (R : Repr) where
  | tm (type : Ty R)
  | ty (kind : Kind R)
  | kind

structure Variable (R : Repr) where
  name : R.Name
  ty : Ty R

structure TypeVariable (R : Repr) where
  index : UInt64
  kind : Kind R

inductive Format where
  | blob
  | cborTree
  deriving DecidableEq

/-- One node of the Rust checked syntax DAG. Field order specifies CBOR order;
the numeric tag is prepended to these fields. -/
inductive Expr (R : Repr) where
  | kindStar
  | kindArr (domain codomain : Kind R)
  | tyBool (kind : Kind R)
  | tyArr (domain codomain : Ty R) (kind : Kind R)
  | tyApp (function argument : Ty R) (kind : Kind R)
  | tyLam (domain : Kind R) (body : Ty R) (kind : Kind R)
  | tyBv (fv : TypeVariable R)
  | tySub (carrier : Ty R) (predicate : Tm R) (kind : Kind R)
  | tyModel (predicate : Tm R) (kind : Kind R)
  | tyLink (source : R.Link) (format : Format) (kind : Kind R)
  | tyExists (predicate : Tm R) (result : Ty R)
  | tmBv (index : UInt64) (result : Ty R)
  | tmFv (fv : Variable R)
  | tmApp (function argument : Tm R) (result : Ty R)
  | tmLam (domain : Ty R) (body : Tm R) (result : Ty R)
  | tmBool (value : Bool) (result : Ty R)
  | tmEq (left right : Tm R) (result : Ty R)
  | tmEps (predicate : Tm R) (result : Ty R)
  | tmAbs (carrier : Ty R) (predicate value : Tm R) (result : Ty R)
  | tmRep (carrier : Ty R) (predicate value : Tm R)
  | tmLink (source : R.Link) (format : Format) (result : Ty R)
  | tmCast (value : Tm R) (target : Ty R)

inductive Tag where
  | kindStar | kindArr
  | tyBool | tyArr | tyApp | tyLam | tyBv | tySub | tyExists | tyModel | tyLink
  | tmBv | tmFv | tmApp | tmLam | tmBool | tmEq | tmEps | tmAbs | tmRep | tmLink | tmCast
  deriving DecidableEq

def Tag.id : Tag → Nat
  | .kindStar => 0
  | .kindArr => 1
  | .tyBool => 2
  | .tyArr => 3
  | .tyApp => 4
  | .tyLam => 5
  | .tyBv => 6
  | .tySub => 7
  | .tyExists => 8
  | .tyModel => 9
  | .tyLink => 11
  | .tmBv => 13
  | .tmFv => 14
  | .tmApp => 15
  | .tmLam => 16
  | .tmBool => 17
  | .tmEq => 18
  | .tmEps => 19
  | .tmAbs => 20
  | .tmRep => 21
  | .tmLink => 22
  | .tmCast => 23

def Tag.name : Tag → String
  | .kindStar => "KIND_STAR"
  | .kindArr => "KIND_ARR"
  | .tyBool => "TY_BOOL"
  | .tyArr => "TY_ARR"
  | .tyApp => "TY_APP"
  | .tyLam => "TY_LAM"
  | .tyBv => "TY_BV"
  | .tySub => "TY_SUB"
  | .tyExists => "TY_EXISTS"
  | .tyModel => "TY_MODEL"
  | .tyLink => "TY_LINK"
  | .tmBv => "TM_BV"
  | .tmFv => "TM_FV"
  | .tmApp => "TM_APP"
  | .tmLam => "TM_LAM"
  | .tmBool => "TM_BOOL"
  | .tmEq => "TM_EQ"
  | .tmEps => "TM_EPS"
  | .tmAbs => "TM_ABS"
  | .tmRep => "TM_REP"
  | .tmLink => "TM_LINK"
  | .tmCast => "TM_CAST"

def Expr.tag {R : Repr} : Expr R → Tag
  | .kindStar => .kindStar
  | .kindArr .. => .kindArr
  | .tyBool .. => .tyBool
  | .tyArr .. => .tyArr
  | .tyApp .. => .tyApp
  | .tyLam .. => .tyLam
  | .tyBv .. => .tyBv
  | .tySub .. => .tySub
  | .tyModel .. => .tyModel
  | .tyLink .. => .tyLink
  | .tyExists .. => .tyExists
  | .tmBv .. => .tmBv
  | .tmFv .. => .tmFv
  | .tmApp .. => .tmApp
  | .tmLam .. => .tmLam
  | .tmBool .. => .tmBool
  | .tmEq .. => .tmEq
  | .tmEps .. => .tmEps
  | .tmAbs .. => .tmAbs
  | .tmRep .. => .tmRep
  | .tmLink .. => .tmLink
  | .tmCast .. => .tmCast

theorem Tag.id_injective : Function.Injective Tag.id := by
  intro a b h
  cases a <;> cases b <;> simp_all [Tag.id]

end Nucleus.HolSurface
