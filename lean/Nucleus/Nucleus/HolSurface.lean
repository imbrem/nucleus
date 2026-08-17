/-!
# Backend-neutral HOL surface syntax

This is the Lean counterpart of `covalence-logic-hol`'s raw syntax. Children
are supplied by a representation so implementations may choose sharing,
interning, or indices without changing the syntax. In particular, `Link` is
deliberately abstract here: hashes and serialization formats are implementation
details, not logical syntax.
-/

namespace Nucleus.HolSurface

universe u

/-- Storage choices for indices held by surface syntax. -/
structure Repr where
  Kind : Type u
  Ty : Type u
  Tm : Type u
  Var : Type u
  Ctx : Type u
  Link : Type u
  Prim : Type u

inductive Kind (R : Repr) where
  | star
  | arr (domain codomain : R.Kind)

inductive Ty (R : Repr) where
  | bool
  | arr (domain codomain : R.Ty)
  | app (function argument : R.Ty)
  | abs (domain : R.Kind) (body : R.Ty)
  | bv (index : R.Var)
  | sub (carrier : R.Ty) (predicate : R.Tm)
  | model (witness : R.Tm)
  | prim (primitive : R.Prim)
  | link (target : R.Link) (kind : R.Kind)
  | nat

inductive Tm (R : Repr) where
  | tyExists (body : R.Tm)
  | prim (primitive : R.Prim)
  | bv (index : R.Var)
  | fv (index : R.Var)
  | app (function argument : R.Tm)
  | lam (domain : R.Ty) (body : R.Tm)
  | bool (value : Bool)
  | eq (type : R.Ty) (left right : R.Tm)
  | eps (type : R.Ty) (predicate : R.Tm)
  | abs (type : R.Ty) (predicate representation : R.Tm)
  | rep (type : R.Ty) (predicate abstraction : R.Tm)
  | link (target : R.Link) (type : R.Ty)
  | nat (value : UInt64)
  | ctx (premises : R.Ctx)
  | imp (premises : R.Ctx) (conclusion : R.Tm)

/-- An explicit wrapper for heterogeneous storage of the three sorted forms. -/
inductive AnyExpr (R : Repr) where
  | kind (value : Kind R)
  | ty (value : Ty R)
  | tm (value : Tm R)

/-- Canonical tags shared by Lean, Rust, and the CBOR representation. -/
inductive Tag where
  | kindStar | kindArr
  | tyBool | tyArr | tyApp | tyLam | tyBv | tySub | tyExists | tyModel
  | tyPrim | tyLink
  | tmPrim | tmBv | tmFv | tmApp | tmLam | tmBool | tmEq | tmEps | tmAbs | tmRep
  | tmLink | imp | tyNat | ctx | tmLitNat

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
  | .tyPrim => 10
  | .tyLink => 11
  | .tmPrim => 12
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
  | .imp => 64
  | .tyNat => 65
  | .ctx => 66
  | .tmLitNat => 67

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
  | .tyPrim => "TY_PRIM"
  | .tyLink => "TY_LINK"
  | .tmPrim => "TM_PRIM"
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
  | .imp => "IMP"
  | .tyNat => "TY_NAT"
  | .ctx => "CTX"
  | .tmLitNat => "TM_LIT_NAT"

def Kind.tag {R : Repr} : Kind R → Tag
  | .star => .kindStar
  | .arr _ _ => .kindArr

def Ty.tag {R : Repr} : Ty R → Tag
  | .bool => .tyBool
  | .arr _ _ => .tyArr
  | .app _ _ => .tyApp
  | .abs _ _ => .tyLam
  | .bv _ => .tyBv
  | .sub _ _ => .tySub
  | .model _ => .tyModel
  | .prim _ => .tyPrim
  | .link _ _ => .tyLink
  | .nat => .tyNat

def Tm.tag {R : Repr} : Tm R → Tag
  | .tyExists _ => .tyExists
  | .prim _ => .tmPrim
  | .bv _ => .tmBv
  | .fv _ => .tmFv
  | .app _ _ => .tmApp
  | .lam _ _ => .tmLam
  | .bool _ => .tmBool
  | .eq _ _ _ => .tmEq
  | .eps _ _ => .tmEps
  | .abs _ _ _ => .tmAbs
  | .rep _ _ _ => .tmRep
  | .link _ _ => .tmLink
  | .nat _ => .tmLitNat
  | .ctx _ => .ctx
  | .imp _ _ => .imp

def AnyExpr.tag {R : Repr} : AnyExpr R → Tag
  | .kind value => value.tag
  | .ty value => value.tag
  | .tm value => value.tag

end Nucleus.HolSurface
