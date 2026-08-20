import Nucleus.HolE.Named.Hole
import Nucleus.TypeFormers

/-!
# Affine holes for sorted named HolE

An `AffineHole` is indexed by a code whose denotation names the available
holes.  A hole leaf consumes one label.  Binary syntax combines disjoint label
spaces with `HasCoproduct`, so a label can occur at most once; labels may be
unused.  For the canonical `Nat` codes, the labels are `Fin n` and coproduct
is addition.
-/

namespace Nucleus.HolE.Named

open Nucleus

universe u v w
set_option relaxedAutoImplicit true

/-- Sorted named syntax with an affine, code-indexed family of holes. -/
inductive AffineHole (Sig : Signature.{u}) (Name : Type) (Code : Type w)
    [Denotes.{w, v} Code] [HasEmpty Code] [HasCoproduct Code]
    (holeSort : HolSort) : Code → HolSort → Type (max u v w 1) where
  | hole {code : Code} (index : code) : AffineHole Sig Name Code holeSort code holeSort
  | boolTy : AffineHole Sig Name Code holeSort HasEmpty.empty (.kind .star)
  | arr {leftCode rightCode : Code}
      (domain : AffineHole Sig Name Code holeSort leftCode (.kind .star))
      (codomain : AffineHole Sig Name Code holeSort rightCode (.kind .star)) :
      AffineHole Sig Name Code holeSort
        (HasCoproduct.coproduct leftCode rightCode) (.kind .star)
  | tyApp {domain codomain : Kind} {leftCode rightCode : Code}
      (function : AffineHole Sig Name Code holeSort leftCode
        (.kind (.arr domain codomain)))
      (argument : AffineHole Sig Name Code holeSort rightCode (.kind domain)) :
      AffineHole Sig Name Code holeSort
        (HasCoproduct.coproduct leftCode rightCode) (.kind codomain)
  | tyLam {domain codomain : Kind} {code : Code} (name : Name)
      (body : AffineHole Sig Name Code holeSort code (.kind codomain)) :
      AffineHole Sig Name Code holeSort code (.kind (.arr domain codomain))
  | tyFv (name : Name) (kind : Kind) :
      AffineHole Sig Name Code holeSort HasEmpty.empty (.kind kind)
  | sub {leftCode rightCode : Code}
      (carrier : AffineHole Sig Name Code holeSort leftCode (.kind .star))
      (name : Name) (predicate : AffineHole Sig Name Code holeSort rightCode .tm) :
      AffineHole Sig Name Code holeSort
        (HasCoproduct.coproduct leftCode rightCode) (.kind .star)
  | tyExists {code : Code} (name : Name)
      (predicate : AffineHole Sig Name Code holeSort code .tm) :
      AffineHole Sig Name Code holeSort code .tm
  | model {code : Code} (name : Name)
      (predicate : AffineHole Sig Name Code holeSort code .tm) :
      AffineHole Sig Name Code holeSort code (.kind .star)
  | primFam {kind : Kind} (symbol : Sig (.kind kind)) :
      AffineHole Sig Name Code holeSort HasEmpty.empty (.kind kind)
  | primTm (symbol : Sig .tm) :
      AffineHole Sig Name Code holeSort HasEmpty.empty .tm
  | tmFv {code : Code} (name : Name)
      (type : AffineHole Sig Name Code holeSort code (.kind .star)) :
      AffineHole Sig Name Code holeSort code .tm
  | app {leftCode rightCode : Code}
      (function : AffineHole Sig Name Code holeSort leftCode .tm)
      (argument : AffineHole Sig Name Code holeSort rightCode .tm) :
      AffineHole Sig Name Code holeSort
        (HasCoproduct.coproduct leftCode rightCode) .tm
  | lam {leftCode rightCode : Code} (name : Name)
      (domain : AffineHole Sig Name Code holeSort leftCode (.kind .star))
      (body : AffineHole Sig Name Code holeSort rightCode .tm) :
      AffineHole Sig Name Code holeSort
        (HasCoproduct.coproduct leftCode rightCode) .tm
  | bool (value : Bool) : AffineHole Sig Name Code holeSort HasEmpty.empty .tm
  | eq {typeCode leftCode rightCode : Code}
      (type : AffineHole Sig Name Code holeSort typeCode (.kind .star))
      (left : AffineHole Sig Name Code holeSort leftCode .tm)
      (right : AffineHole Sig Name Code holeSort rightCode .tm) :
      AffineHole Sig Name Code holeSort
        (HasCoproduct.coproduct typeCode
          (HasCoproduct.coproduct leftCode rightCode)) .tm
  | eps {leftCode rightCode : Code}
      (type : AffineHole Sig Name Code holeSort leftCode (.kind .star))
      (predicate : AffineHole Sig Name Code holeSort rightCode .tm) :
      AffineHole Sig Name Code holeSort
        (HasCoproduct.coproduct leftCode rightCode) .tm
  | abs {typeCode predicateCode valueCode : Code}
      (carrier : AffineHole Sig Name Code holeSort typeCode (.kind .star))
      (name : Name)
      (predicate : AffineHole Sig Name Code holeSort predicateCode .tm)
      (value : AffineHole Sig Name Code holeSort valueCode .tm) :
      AffineHole Sig Name Code holeSort
        (HasCoproduct.coproduct typeCode
          (HasCoproduct.coproduct predicateCode valueCode)) .tm
  | rep {typeCode predicateCode valueCode : Code}
      (carrier : AffineHole Sig Name Code holeSort typeCode (.kind .star))
      (name : Name)
      (predicate : AffineHole Sig Name Code holeSort predicateCode .tm)
      (value : AffineHole Sig Name Code holeSort valueCode .tm) :
      AffineHole Sig Name Code holeSort
        (HasCoproduct.coproduct typeCode
          (HasCoproduct.coproduct predicateCode valueCode)) .tm

namespace AffineHole

private def leftReplacement {Code : Type w} [Denotes.{w, v} Code] [HasCoproduct Code]
    {leftCode rightCode : Code} (replacement :
      HasCoproduct.coproduct (Code := Code) leftCode rightCode → Expr Sig Name holeSort) :
    leftCode → Expr Sig Name holeSort :=
  fun index => replacement
    (Nucleus.TypeFormers.inl (Code := Code) (right := rightCode) index)

private def rightReplacement {Code : Type w} [Denotes.{w, v} Code] [HasCoproduct Code]
    {leftCode rightCode : Code} (replacement :
      HasCoproduct.coproduct (Code := Code) leftCode rightCode → Expr Sig Name holeSort) :
    rightCode → Expr Sig Name holeSort :=
  fun index => replacement
    (Nucleus.TypeFormers.inr (Code := Code) (left := leftCode) index)

private def firstReplacement {Code : Type w} [Denotes.{w, v} Code] [HasCoproduct Code]
    {firstCode secondCode thirdCode : Code} (replacement :
      HasCoproduct.coproduct (Code := Code) firstCode
        (HasCoproduct.coproduct (Code := Code) secondCode thirdCode) →
        Expr Sig Name holeSort) : firstCode → Expr Sig Name holeSort :=
  leftReplacement replacement

private def secondReplacement {Code : Type w} [Denotes.{w, v} Code] [HasCoproduct Code]
    {firstCode secondCode thirdCode : Code} (replacement :
      HasCoproduct.coproduct (Code := Code) firstCode
        (HasCoproduct.coproduct (Code := Code) secondCode thirdCode) →
        Expr Sig Name holeSort) : secondCode → Expr Sig Name holeSort :=
  leftReplacement (rightReplacement replacement)

private def thirdReplacement {Code : Type w} [Denotes.{w, v} Code] [HasCoproduct Code]
    {firstCode secondCode thirdCode : Code} (replacement :
      HasCoproduct.coproduct (Code := Code) firstCode
        (HasCoproduct.coproduct (Code := Code) secondCode thirdCode) →
        Expr Sig Name holeSort) : thirdCode → Expr Sig Name holeSort :=
  rightReplacement (rightReplacement replacement)

/-- Fill every used hole label from one replacement family. -/
def fill {Code : Type w} [Denotes.{w, v} Code] [HasEmpty Code] [HasCoproduct Code] :
    {code : Code} → {resultSort : HolSort} →
      AffineHole Sig Name Code holeSort code resultSort →
      (code → Expr Sig Name holeSort) → Expr Sig Name resultSort
  | _, _, .hole index, replacement => replacement index
  | _, _, .boolTy, _ => .boolTy
  | _, _, .arr domain codomain, replacement =>
      .arr (domain.fill (leftReplacement replacement))
        (codomain.fill (rightReplacement replacement))
  | _, _, .tyApp function argument, replacement =>
      .tyApp (function.fill (leftReplacement replacement))
        (argument.fill (rightReplacement replacement))
  | _, _, .tyLam name body, replacement => .tyLam name (body.fill replacement)
  | _, _, .tyFv name kind, _ => .tyFv name kind
  | _, _, .sub carrier name predicate, replacement =>
      .sub (carrier.fill (leftReplacement replacement)) name
        (predicate.fill (rightReplacement replacement))
  | _, _, .tyExists name predicate, replacement =>
      .tyExists name (predicate.fill replacement)
  | _, _, .model name predicate, replacement => .model name (predicate.fill replacement)
  | _, _, .primFam symbol, _ => .primFam symbol
  | _, _, .primTm symbol, _ => .primTm symbol
  | _, _, .tmFv name type, replacement => .tmFv name (type.fill replacement)
  | _, _, .app function argument, replacement =>
      .app (function.fill (leftReplacement replacement))
        (argument.fill (rightReplacement replacement))
  | _, _, .lam name domain body, replacement =>
      .lam name (domain.fill (leftReplacement replacement))
        (body.fill (rightReplacement replacement))
  | _, _, .bool value, _ => .bool value
  | _, _, .eq type left right, replacement =>
      .eq (type.fill (firstReplacement replacement))
        (left.fill (secondReplacement replacement))
        (right.fill (thirdReplacement replacement))
  | _, _, .eps type predicate, replacement =>
      .eps (type.fill (leftReplacement replacement))
        (predicate.fill (rightReplacement replacement))
  | _, _, .abs carrier name predicate value, replacement =>
      .abs (carrier.fill (firstReplacement replacement)) name
        (predicate.fill (secondReplacement replacement))
        (value.fill (thirdReplacement replacement))
  | _, _, .rep carrier name predicate value, replacement =>
      .rep (carrier.fill (firstReplacement replacement)) name
        (predicate.fill (secondReplacement replacement))
        (value.fill (thirdReplacement replacement))

/-! The canonical finite-cardinality specialization. -/

/-- An affine expression with `n` ordered hole labels. -/
abbrev Finite (Sig : Signature) (Name : Type) (holeSort : HolSort)
    (n : Nat) (resultSort : HolSort) := AffineHole Sig Name Nat holeSort n resultSort

instance : Cslib.HasHContext (Expr Sig Name resultSort)
    (Fin n → Expr Sig Name holeSort) where
  Context := Finite Sig Name holeSort n resultSort
  fill := AffineHole.fill

/-- Embed an ordinary expression as a finite affine expression with no holes. -/
def ofExpr : Expr Sig Name resultSort → Finite Sig Name holeSort 0 resultSort
  | .boolTy => .boolTy
  | .arr domain codomain => .arr (ofExpr domain) (ofExpr codomain)
  | .tyApp function argument => .tyApp (ofExpr function) (ofExpr argument)
  | .tyLam name body => .tyLam name (ofExpr body)
  | .tyFv name kind => .tyFv name kind
  | .sub carrier name predicate => .sub (ofExpr carrier) name (ofExpr predicate)
  | .tyExists name predicate => .tyExists name (ofExpr predicate)
  | .model name predicate => .model name (ofExpr predicate)
  | .primFam symbol => .primFam symbol
  | .primTm symbol => .primTm symbol
  | .tmFv name type => .tmFv name (ofExpr type)
  | .app function argument => .app (ofExpr function) (ofExpr argument)
  | .lam name domain body => .lam name (ofExpr domain) (ofExpr body)
  | .bool value => .bool value
  | .eq type left right => .eq (ofExpr type) (ofExpr left) (ofExpr right)
  | .eps type predicate => .eps (ofExpr type) (ofExpr predicate)
  | .abs carrier name predicate value =>
      .abs (ofExpr carrier) name (ofExpr predicate) (ofExpr value)
  | .rep carrier name predicate value =>
      .rep (ofExpr carrier) name (ofExpr predicate) (ofExpr value)

/-- Filling an embedded hole-free expression is the identity. -/
@[simp] theorem fill_ofExpr (expression : Expr Sig Name resultSort)
    (replacement : Fin 0 → Expr Sig Name holeSort) :
    (ofExpr (holeSort := holeSort) expression).fill replacement = expression :=
  match expression with
  | .boolTy => rfl
  | .arr domain codomain => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr domain, fill_ofExpr codomain]
  | .tyApp function argument => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr function, fill_ofExpr argument]
  | .tyLam name body => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr body]
  | .tyFv _ _ => rfl
  | .sub carrier name predicate => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr carrier, fill_ofExpr predicate]
  | .tyExists name predicate => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr predicate]
  | .model name predicate => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr predicate]
  | .primFam _ => rfl
  | .primTm _ => rfl
  | .tmFv name type => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr type]
  | .app function argument => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr function, fill_ofExpr argument]
  | .lam name domain body => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr domain, fill_ofExpr body]
  | .bool _ => rfl
  | .eq type left right => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr type, fill_ofExpr left, fill_ofExpr right]
  | .eps type predicate => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr type, fill_ofExpr predicate]
  | .abs carrier name predicate value => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr carrier, fill_ofExpr predicate, fill_ofExpr value]
  | .rep carrier name predicate value => by
      simp only [ofExpr, fill]
      rw [fill_ofExpr carrier, fill_ofExpr predicate, fill_ofExpr value]

end AffineHole

end Nucleus.HolE.Named
