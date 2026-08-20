import Cslib.Foundations.Syntax.Congruence
import Cslib.Foundations.Syntax.HasAlphaEquiv
import Nucleus.HolE.Named.Alpha

/-!
# Single-hole contexts for sorted named HolE

`OneHole` is the syntax of a named HolE expression with exactly one
distinguished hole.  Its two sort indices record the sort accepted by the
hole and the sort produced after filling it.  Names remain names throughout;
the representation introduces no de Bruijn indices.
-/

namespace Nucleus.HolE.Named

universe u
set_option relaxedAutoImplicit true

/-- A sorted named HolE expression containing exactly one hole. -/
inductive OneHole (Sig : Signature.{u}) (Name : Type) (holeSort : HolSort) :
    HolSort → Type (max u 1) where
  | hole : OneHole Sig Name holeSort holeSort
  | arrDomain (context : OneHole Sig Name holeSort (.kind .star))
      (codomain : Ty Sig Name) : OneHole Sig Name holeSort (.kind .star)
  | arrCodomain (domain : Ty Sig Name)
      (context : OneHole Sig Name holeSort (.kind .star)) :
      OneHole Sig Name holeSort (.kind .star)
  | tyAppFunction {domain codomain : Kind}
      (context : OneHole Sig Name holeSort (.kind (.arr domain codomain)))
      (argument : Fam Sig domain Name) : OneHole Sig Name holeSort (.kind codomain)
  | tyAppArgument {domain codomain : Kind}
      (function : Fam Sig (.arr domain codomain) Name)
      (context : OneHole Sig Name holeSort (.kind domain)) :
      OneHole Sig Name holeSort (.kind codomain)
  | tyLam {domain codomain : Kind} (name : Name)
      (context : OneHole Sig Name holeSort (.kind codomain)) :
      OneHole Sig Name holeSort (.kind (.arr domain codomain))
  | subCarrier (context : OneHole Sig Name holeSort (.kind .star))
      (name : Name) (predicate : Tm Sig Name) :
      OneHole Sig Name holeSort (.kind .star)
  | subPredicate (carrier : Ty Sig Name) (name : Name)
      (context : OneHole Sig Name holeSort .tm) :
      OneHole Sig Name holeSort (.kind .star)
  | tyExists (name : Name) (context : OneHole Sig Name holeSort .tm) :
      OneHole Sig Name holeSort .tm
  | model (name : Name) (context : OneHole Sig Name holeSort .tm) :
      OneHole Sig Name holeSort (.kind .star)
  | tmFv (name : Name) (context : OneHole Sig Name holeSort (.kind .star)) :
      OneHole Sig Name holeSort .tm
  | appFunction (context : OneHole Sig Name holeSort .tm)
      (argument : Tm Sig Name) : OneHole Sig Name holeSort .tm
  | appArgument (function : Tm Sig Name)
      (context : OneHole Sig Name holeSort .tm) : OneHole Sig Name holeSort .tm
  | lamDomain (name : Name) (context : OneHole Sig Name holeSort (.kind .star))
      (body : Tm Sig Name) : OneHole Sig Name holeSort .tm
  | lamBody (name : Name) (domain : Ty Sig Name)
      (context : OneHole Sig Name holeSort .tm) : OneHole Sig Name holeSort .tm
  | eqType (context : OneHole Sig Name holeSort (.kind .star))
      (left right : Tm Sig Name) : OneHole Sig Name holeSort .tm
  | eqLeft (type : Ty Sig Name) (context : OneHole Sig Name holeSort .tm)
      (right : Tm Sig Name) : OneHole Sig Name holeSort .tm
  | eqRight (type : Ty Sig Name) (left : Tm Sig Name)
      (context : OneHole Sig Name holeSort .tm) : OneHole Sig Name holeSort .tm
  | epsType (context : OneHole Sig Name holeSort (.kind .star))
      (predicate : Tm Sig Name) : OneHole Sig Name holeSort .tm
  | epsPredicate (type : Ty Sig Name)
      (context : OneHole Sig Name holeSort .tm) : OneHole Sig Name holeSort .tm
  | absCarrier (context : OneHole Sig Name holeSort (.kind .star))
      (name : Name) (predicate value : Tm Sig Name) : OneHole Sig Name holeSort .tm
  | absPredicate (carrier : Ty Sig Name) (name : Name)
      (context : OneHole Sig Name holeSort .tm) (value : Tm Sig Name) :
      OneHole Sig Name holeSort .tm
  | absValue (carrier : Ty Sig Name) (name : Name) (predicate : Tm Sig Name)
      (context : OneHole Sig Name holeSort .tm) : OneHole Sig Name holeSort .tm
  | repCarrier (context : OneHole Sig Name holeSort (.kind .star))
      (name : Name) (predicate value : Tm Sig Name) : OneHole Sig Name holeSort .tm
  | repPredicate (carrier : Ty Sig Name) (name : Name)
      (context : OneHole Sig Name holeSort .tm) (value : Tm Sig Name) :
      OneHole Sig Name holeSort .tm
  | repValue (carrier : Ty Sig Name) (name : Name) (predicate : Tm Sig Name)
      (context : OneHole Sig Name holeSort .tm) : OneHole Sig Name holeSort .tm

namespace OneHole

/-- Replace the distinguished hole with an expression of the required sort. -/
def fill : OneHole Sig Name holeSort resultSort →
    Expr Sig Name holeSort → Expr Sig Name resultSort
  | .hole, expression => expression
  | .arrDomain context codomain, expression => .arr (context.fill expression) codomain
  | .arrCodomain domain context, expression => .arr domain (context.fill expression)
  | .tyAppFunction context argument, expression =>
      .tyApp (context.fill expression) argument
  | .tyAppArgument function context, expression =>
      .tyApp function (context.fill expression)
  | .tyLam name context, expression => .tyLam name (context.fill expression)
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
  | .eqType context left right, expression =>
      .eq (context.fill expression) left right
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

instance : Cslib.HasHContext (Expr Sig Name resultSort) (Expr Sig Name holeSort) where
  Context := OneHole Sig Name holeSort resultSort
  fill := OneHole.fill

/-- Alpha equivalence generated by scoped HolE alpha conversion and closed
under every sorted single-hole context. -/
inductive AlphaEquiv {Sig : Signature} :
    {sort : HolSort} → Expr Sig Nat sort → Expr Sig Nat sort → Prop where
  | scoped {sort : HolSort} {types : List Kind} {depth : Nat}
      {typeScope : TyScope types} {termScope : TmScope Sig depth}
      {left right : Expr Sig Nat sort} :
      Alpha typeScope termScope left right → AlphaEquiv left right
  | refl {sort : HolSort} (expression : Expr Sig Nat sort) : AlphaEquiv expression expression
  | symm {sort : HolSort} {left right : Expr Sig Nat sort} :
      AlphaEquiv left right → AlphaEquiv right left
  | trans {sort : HolSort} {left middle right : Expr Sig Nat sort} :
      AlphaEquiv left middle → AlphaEquiv middle right → AlphaEquiv left right
  | context {holeSort resultSort : HolSort}
      (context : OneHole Sig Nat holeSort resultSort)
      {left right : Expr Sig Nat holeSort} :
      AlphaEquiv left right →
        AlphaEquiv (context.fill left) (context.fill right)

instance : Cslib.HasAlphaEquiv (Expr Sig Nat sort) where
  AlphaEquiv := AlphaEquiv

instance : Cslib.Congruence (Expr Sig Nat sort) AlphaEquiv where
  refl := AlphaEquiv.refl
  symm := fun _ _ equivalent => AlphaEquiv.symm equivalent
  trans := fun _ _ _ leftMiddle middleRight => AlphaEquiv.trans leftMiddle middleRight
  elim context _ _ equivalent := AlphaEquiv.context context equivalent

end Nucleus.HolE.Named
