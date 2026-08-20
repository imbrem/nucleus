import Nucleus.HolE.Named.Hole
import Nucleus.HolE.Named.Typing

/-!
# Checked named expressions and single-hole contexts

`Checked` bundles a sorted named expression with its existing `Checks`
derivation.  `CheckedHole` similarly bundles a sorted one-hole context with
the fact that it maps one checked classification to another.  Because the
surface syntax is named, the hole itself needs no bound-variable index.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

/-- A named expression intrinsically bundled with its classification. -/
structure Checked {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {sort : HolSort}
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (context : Nucleus.HolE.BoundCtx Sig types (scopeDepth sort depth))
    (classification : Classification Sig sort) where
  expression : Expr Sig Nat sort
  checking : Checks typeScope termScope context expression classification

/-- A checked type family of the indicated kind. -/
abbrev CheckedFam {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types) (kind : Kind) :=
  Checked (Sig := Sig) typeScope (.nil : TmScope Sig 0)
    Nucleus.HolE.emptyBound (Classification.kind (kind := kind))

/-- A checked type. -/
abbrev CheckedTy {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types) := CheckedFam (Sig := Sig) typeScope .star

/-- A checked term of the indicated named type. -/
abbrev CheckedTm {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} (typeScope : TyScope types)
    (termScope : TmScope Sig depth) (context : Nucleus.HolE.BoundCtx Sig types depth)
    (type : Ty Sig) :=
  Checked (sort := .tm) typeScope termScope context (.tm type)

/-- A single-hole named context certified to preserve a classification.
The hole and result may live under different named scopes; binders in the
context account for that change through `preserves`. -/
structure CheckedHole {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {holeTypes resultTypes : List Kind} {holeDepth resultDepth : Nat}
    {holeSort resultSort : HolSort}
    (holeTypeScope : TyScope holeTypes) (holeTermScope : TmScope Sig holeDepth)
    (holeContext : Nucleus.HolE.BoundCtx Sig holeTypes (scopeDepth holeSort holeDepth))
    (holeClassification : Classification Sig holeSort)
    (resultTypeScope : TyScope resultTypes) (resultTermScope : TmScope Sig resultDepth)
    (resultContext : Nucleus.HolE.BoundCtx Sig resultTypes (scopeDepth resultSort resultDepth))
    (resultClassification : Classification Sig resultSort) where
  raw : OneHole Sig Nat holeSort resultSort
  preserves : ∀ {expression : Expr Sig Nat holeSort},
    Checks holeTypeScope holeTermScope holeContext expression holeClassification →
      Checks resultTypeScope resultTermScope resultContext
        (raw.fill expression) resultClassification

section CheckedContexts

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
variable {holeTypes resultTypes : List Kind} {holeDepth resultDepth : Nat}
variable {holeSort resultSort : HolSort}
variable {holeTypeScope : TyScope holeTypes} {holeTermScope : TmScope Sig holeDepth}
variable {holeContext : Nucleus.HolE.BoundCtx Sig holeTypes
  (scopeDepth holeSort holeDepth)}
variable {holeClassification : Classification Sig holeSort}
variable {resultTypeScope : TyScope resultTypes} {resultTermScope : TmScope Sig resultDepth}
variable {resultContext : Nucleus.HolE.BoundCtx Sig resultTypes
  (scopeDepth resultSort resultDepth)}
variable {resultClassification : Classification Sig resultSort}

namespace CheckedHole

/-- Fill a checked hole, retaining the result typing certificate. -/
def fill
    (context : CheckedHole holeTypeScope holeTermScope holeContext holeClassification
      resultTypeScope resultTermScope resultContext resultClassification)
    (expression : Checked holeTypeScope holeTermScope holeContext holeClassification) :
    Checked resultTypeScope resultTermScope resultContext resultClassification :=
  ⟨context.raw.fill expression.expression, context.preserves expression.checking⟩

end CheckedHole

instance : Cslib.HasHContext
    (Checked resultTypeScope resultTermScope resultContext resultClassification)
    (Checked holeTypeScope holeTermScope holeContext holeClassification) where
  Context := CheckedHole holeTypeScope holeTermScope holeContext holeClassification
    resultTypeScope resultTermScope resultContext resultClassification
  fill := CheckedHole.fill

end CheckedContexts

section CheckedAlpha

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
variable {types : List Kind} {depth : Nat} {sort : HolSort}
variable {typeScope : TyScope types} {termScope : TmScope Sig depth}
variable {boundContext : Nucleus.HolE.BoundCtx Sig types (scopeDepth sort depth)}
variable {classification : Classification Sig sort}

/-- Checked alpha equivalence forgets only the typing certificates. -/
def Checked.AlphaEquiv
    (left right : Checked typeScope termScope boundContext classification) : Prop :=
  Named.AlphaEquiv left.expression right.expression

instance : Cslib.HasAlphaEquiv
    (Checked typeScope termScope boundContext classification) where
  AlphaEquiv := Checked.AlphaEquiv

instance : Cslib.Congruence
    (Checked typeScope termScope boundContext classification) Checked.AlphaEquiv where
  refl := fun expression => AlphaEquiv.refl expression.expression
  symm := fun _ _ equivalent => AlphaEquiv.symm equivalent
  trans := fun _ _ _ leftMiddle middleRight => AlphaEquiv.trans leftMiddle middleRight
  elim context _ _ equivalent := AlphaEquiv.context context.raw equivalent

end CheckedAlpha

end Nucleus.HolE.Named
