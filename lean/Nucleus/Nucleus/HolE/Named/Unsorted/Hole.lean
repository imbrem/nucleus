import Nucleus.HolE.Named.Hole
import Nucleus.HolE.Named.Unsorted

/-!
# Single-hole contexts for unsorted named HolE

This is the unindexed counterpart of `Named.OneHole`.  The hole and every
node remain fully named; `fill` performs only structural hole replacement.
-/

namespace Nucleus.HolE.Named.Unsorted

universe u
set_option relaxedAutoImplicit true

/-- An unsorted named HolE expression containing exactly one hole. -/
inductive OneHole (Sig : Signature.{u}) (Name : Type) : Type (max u 1) where
  | hole
  | arrDomain (context : OneHole Sig Name) (codomain : Expr Sig Name)
  | arrCodomain (domain : Expr Sig Name) (context : OneHole Sig Name)
  | tyAppFunction (domain codomain : Kind) (context : OneHole Sig Name)
      (argument : Expr Sig Name)
  | tyAppArgument (domain codomain : Kind) (function : Expr Sig Name)
      (context : OneHole Sig Name)
  | tyLam (domain codomain : Kind) (name : Name) (context : OneHole Sig Name)
  | subCarrier (context : OneHole Sig Name) (name : Name) (predicate : Expr Sig Name)
  | subPredicate (carrier : Expr Sig Name) (name : Name) (context : OneHole Sig Name)
  | tyExists (name : Name) (context : OneHole Sig Name)
  | model (name : Name) (context : OneHole Sig Name)
  | tmFv (name : Name) (context : OneHole Sig Name)
  | appFunction (context : OneHole Sig Name) (argument : Expr Sig Name)
  | appArgument (function : Expr Sig Name) (context : OneHole Sig Name)
  | lamDomain (name : Name) (context : OneHole Sig Name) (body : Expr Sig Name)
  | lamBody (name : Name) (domain : Expr Sig Name) (context : OneHole Sig Name)
  | eqType (context : OneHole Sig Name) (left right : Expr Sig Name)
  | eqLeft (type : Expr Sig Name) (context : OneHole Sig Name) (right : Expr Sig Name)
  | eqRight (type left : Expr Sig Name) (context : OneHole Sig Name)
  | epsType (context : OneHole Sig Name) (predicate : Expr Sig Name)
  | epsPredicate (type : Expr Sig Name) (context : OneHole Sig Name)
  | absCarrier (context : OneHole Sig Name) (name : Name)
      (predicate value : Expr Sig Name)
  | absPredicate (carrier : Expr Sig Name) (name : Name)
      (context : OneHole Sig Name) (value : Expr Sig Name)
  | absValue (carrier : Expr Sig Name) (name : Name) (predicate : Expr Sig Name)
      (context : OneHole Sig Name)
  | repCarrier (context : OneHole Sig Name) (name : Name)
      (predicate value : Expr Sig Name)
  | repPredicate (carrier : Expr Sig Name) (name : Name)
      (context : OneHole Sig Name) (value : Expr Sig Name)
  | repValue (carrier : Expr Sig Name) (name : Name) (predicate : Expr Sig Name)
      (context : OneHole Sig Name)

namespace OneHole

/-- Replace the distinguished hole with an unsorted expression. -/
def fill : OneHole Sig Name → Expr Sig Name → Expr Sig Name
  | .hole, expression => expression
  | .arrDomain context codomain, expression => .arr (context.fill expression) codomain
  | .arrCodomain domain context, expression => .arr domain (context.fill expression)
  | .tyAppFunction domain codomain context argument, expression =>
      .tyApp domain codomain (context.fill expression) argument
  | .tyAppArgument domain codomain function context, expression =>
      .tyApp domain codomain function (context.fill expression)
  | .tyLam domain codomain name context, expression =>
      .tyLam domain codomain name (context.fill expression)
  | .subCarrier context name predicate, expression =>
      .sub (context.fill expression) name predicate
  | .subPredicate carrier name context, expression =>
      .sub carrier name (context.fill expression)
  | .tyExists name context, expression => .tyExists name (context.fill expression)
  | .model name context, expression => .model name (context.fill expression)
  | .tmFv name context, expression => .tmFv name (context.fill expression)
  | .appFunction context argument, expression => .app (context.fill expression) argument
  | .appArgument function context, expression => .app function (context.fill expression)
  | .lamDomain name context body, expression =>
      .lam name (context.fill expression) body
  | .lamBody name domain context, expression => .lam name domain (context.fill expression)
  | .eqType context left right, expression => .eq (context.fill expression) left right
  | .eqLeft type context right, expression => .eq type (context.fill expression) right
  | .eqRight type left context, expression => .eq type left (context.fill expression)
  | .epsType context predicate, expression => .eps (context.fill expression) predicate
  | .epsPredicate type context, expression => .eps type (context.fill expression)
  | .absCarrier context name predicate value, expression =>
      .abs (context.fill expression) name predicate value
  | .absPredicate carrier name context value, expression =>
      .abs carrier name (context.fill expression) value
  | .absValue carrier name predicate context, expression =>
      .abs carrier name predicate (context.fill expression)
  | .repCarrier context name predicate value, expression =>
      .rep (context.fill expression) name predicate value
  | .repPredicate carrier name context value, expression =>
      .rep carrier name (context.fill expression) value
  | .repValue carrier name predicate context, expression =>
      .rep carrier name predicate (context.fill expression)

end OneHole

instance : Cslib.HasContext (Expr Sig Name) where
  Context := OneHole Sig Name
  fill := OneHole.fill

/-- Alpha equivalence generated by sortable alpha-equivalent pairs and
closed under unsorted single-hole contexts. -/
inductive AlphaEquiv {Sig : Signature} : Expr Sig Nat → Expr Sig Nat → Prop where
  | sorted {sort : HolSort} {left right : Expr Sig Nat}
      {sortedLeft sortedRight : Named.Expr Sig Nat sort} :
      check sort left = some sortedLeft →
      check sort right = some sortedRight →
      Named.AlphaEquiv sortedLeft sortedRight →
      AlphaEquiv left right
  | refl (expression : Expr Sig Nat) : AlphaEquiv expression expression
  | symm {left right : Expr Sig Nat} : AlphaEquiv left right → AlphaEquiv right left
  | trans {left middle right : Expr Sig Nat} :
      AlphaEquiv left middle → AlphaEquiv middle right → AlphaEquiv left right
  | context (context : OneHole Sig Nat) {left right : Expr Sig Nat} :
      AlphaEquiv left right →
        AlphaEquiv (context.fill left) (context.fill right)

instance : Cslib.HasAlphaEquiv (Expr Sig Nat) where
  AlphaEquiv := AlphaEquiv

instance : Cslib.Congruence (Expr Sig Nat) AlphaEquiv where
  refl := AlphaEquiv.refl
  symm := fun _ _ equivalent => AlphaEquiv.symm equivalent
  trans := fun _ _ _ leftMiddle middleRight => AlphaEquiv.trans leftMiddle middleRight
  elim context _ _ equivalent := AlphaEquiv.context context equivalent

end Nucleus.HolE.Named.Unsorted
