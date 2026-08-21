import Nucleus.HolE.Named.Kernel
import Nucleus.HolE.Named.Unsorted.Typing

/-!
# Proof theory for unsorted named HolE

Equality and provability are exact pullbacks of the complete sorted named
kernel.  Thus every sorted kernel rule is available, while malformed syntax
cannot carry a proof certificate.
-/

namespace Nucleus.HolE.Named.Unsorted

set_option relaxedAutoImplicit true

def checkTerms (Sig : Signature) : List (Expr Sig) → Option (List (Named.Tm Sig))
  | [] => some []
  | term :: terms => return (← check .tm term) :: (← checkTerms Sig terms)

def eraseTerms (terms : List (Named.Tm Sig)) : List (Expr Sig) :=
  terms.map erase

@[simp] theorem checkTerms_eraseTerms (terms : List (Named.Tm Sig)) :
    checkTerms Sig (eraseTerms terms) = some terms := by
  induction terms <;> simp_all [checkTerms, eraseTerms]

/-- Unsorted named term equality backed by a sorted named derivation. -/
structure EqTm {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth)
    (left right type : Expr Sig) where
  sortedLeft : Named.Tm Sig
  sortedRight : Named.Tm Sig
  sortedType : Named.Ty Sig
  leftCheck : check .tm left = some sortedLeft
  rightCheck : check .tm right = some sortedRight
  typeCheck : check (.kind .star) type = some sortedType
  derivation : Named.EqTm typeScope termScope Γ sortedLeft sortedRight sortedType

/-- Unsorted named provability backed by a sorted named derivation. -/
structure Proves {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth)
    (hypotheses : List (Expr Sig)) (conclusion : Expr Sig) where
  sortedHypotheses : List (Named.Tm Sig)
  sortedConclusion : Named.Tm Sig
  hypothesesCheck : checkTerms Sig hypotheses = some sortedHypotheses
  conclusionCheck : check .tm conclusion = some sortedConclusion
  derivation : Named.Proves typeScope termScope Γ sortedHypotheses sortedConclusion

def EqTm.sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} {left right type : Expr Sig}
    (proof : EqTm typeScope termScope Γ left right type) :
    Named.EqTm typeScope termScope Γ proof.sortedLeft proof.sortedRight proof.sortedType :=
  proof.derivation

def EqTm.complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} {left right type : Expr Sig}
    {sortedLeft sortedRight : Named.Tm Sig} {sortedType : Named.Ty Sig}
    (leftCheck : check .tm left = some sortedLeft)
    (rightCheck : check .tm right = some sortedRight)
    (typeCheck : check (.kind .star) type = some sortedType)
    (derivation : Named.EqTm typeScope termScope Γ sortedLeft sortedRight sortedType) :
    EqTm typeScope termScope Γ left right type :=
  ⟨sortedLeft, sortedRight, sortedType, leftCheck, rightCheck, typeCheck, derivation⟩

def Proves.sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (Expr Sig)} {conclusion : Expr Sig}
    (proof : Proves typeScope termScope Γ hypotheses conclusion) :
    Named.Proves typeScope termScope Γ proof.sortedHypotheses proof.sortedConclusion :=
  proof.derivation

def Proves.complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (Expr Sig)} {conclusion : Expr Sig}
    {sortedHypotheses : List (Named.Tm Sig)} {sortedConclusion : Named.Tm Sig}
    (hypothesesCheck : checkTerms Sig hypotheses = some sortedHypotheses)
    (conclusionCheck : check .tm conclusion = some sortedConclusion)
    (derivation : Named.Proves typeScope termScope Γ sortedHypotheses sortedConclusion) :
    Proves typeScope termScope Γ hypotheses conclusion :=
  ⟨sortedHypotheses, sortedConclusion, hypothesesCheck, conclusionCheck, derivation⟩

/-- Every sorted named equality derivation has an unsorted preimage. -/
def EqTm.ofSorted {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {left right : Named.Tm Sig} {type : Named.Ty Sig}
    (derivation : Named.EqTm typeScope termScope Γ left right type) :
    EqTm typeScope termScope Γ (erase left) (erase right) (erase type) :=
  ⟨left, right, type, check_erase left, check_erase right, check_erase type, derivation⟩

/-- Every sorted named proof has an unsorted preimage. -/
def Proves.ofSorted {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (Named.Tm Sig)} {conclusion : Named.Tm Sig}
    (derivation : Named.Proves typeScope termScope Γ hypotheses conclusion) :
    Proves typeScope termScope Γ (eraseTerms hypotheses) (erase conclusion) :=
  ⟨hypotheses, conclusion, checkTerms_eraseTerms hypotheses, check_erase conclusion, derivation⟩

theorem not_proves_of_conclusion_check_eq_none
    {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (Expr Sig)} {conclusion : Expr Sig}
    (rejected : check .tm conclusion = none) :
    Proves typeScope termScope Γ hypotheses conclusion → False := by
  intro proof
  have checked := proof.conclusionCheck
  rw [rejected] at checked
  contradiction

end Nucleus.HolE.Named.Unsorted
