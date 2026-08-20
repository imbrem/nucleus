import Nucleus.Hol.Ethane.Semantics
import Nucleus.HolE.ClassicalConsistency

/-!
# Reference Ethane proof theory

This is the extensional reference judgment for the model-only fragment: a named
Ethane sequent holds exactly when its locally nameless HolE image has a kernel
certificate.  It immediately supplies soundness, completeness at every fixed
Ethane preimage, and consistency.

The eventual serialized Ethane kernel will use its own inductive certificate
type and lower each native rule into this reference relation.  Keeping the
reference relation separate prevents the inherited HolE certificate from being
mistaken for the final trusted representation.
-/

namespace Nucleus.Hol.Ethane.Reference

set_option relaxedAutoImplicit true

noncomputable def lowerTerms (typeScope : TyScope types)
    (termScope : TmScope Sig depth) :
    List (Tm Sig) → Option (List (Nucleus.HolE.Tm Sig types depth))
  | [] => some []
  | term :: terms =>
      return (← term.lowerTm typeScope termScope) ::
        (← lowerTerms typeScope termScope terms)

/-- Reference term conversion inherited from HolE. -/
structure EqTm {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : BoundCtx Sig types depth) (left right : Tm Sig) (type : Ty Sig) where
  loweredLeft : Nucleus.HolE.Tm Sig types depth
  loweredRight : Nucleus.HolE.Tm Sig types depth
  loweredType : Nucleus.HolE.Ty Sig types
  leftLowering : left.lowerTm typeScope termScope = some loweredLeft
  rightLowering : right.lowerTm typeScope termScope = some loweredRight
  typeLowering : type.lowerTy typeScope = some loweredType
  derivation : Nucleus.HolE.EqTm Γ loweredLeft loweredRight loweredType

/-- Reference provability inherited from HolE at a fixed Ethane preimage. -/
structure Proves {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : BoundCtx Sig types depth) (hypotheses : List (Tm Sig))
    (conclusion : Tm Sig) where
  loweredHypotheses : List (Nucleus.HolE.Tm Sig types depth)
  loweredConclusion : Nucleus.HolE.Tm Sig types depth
  hypothesesLowering :
    lowerTerms typeScope termScope hypotheses = some loweredHypotheses
  conclusionLowering :
    conclusion.lowerTm typeScope termScope = some loweredConclusion
  derivation : Nucleus.HolE.Proves Γ loweredHypotheses loweredConclusion

def EqTm.sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : BoundCtx Sig types depth}
    {left right : Tm Sig} {type : Ty Sig}
    (conversion : EqTm typeScope termScope Γ left right type) :
    Nucleus.HolE.EqTm Γ conversion.loweredLeft conversion.loweredRight
      conversion.loweredType :=
  conversion.derivation

def EqTm.complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : BoundCtx Sig types depth}
    {left right : Tm Sig} {type : Ty Sig}
    {loweredLeft loweredRight : Nucleus.HolE.Tm Sig types depth}
    {loweredType : Nucleus.HolE.Ty Sig types}
    (leftLowering : left.lowerTm typeScope termScope = some loweredLeft)
    (rightLowering : right.lowerTm typeScope termScope = some loweredRight)
    (typeLowering : type.lowerTy typeScope = some loweredType)
    (derivation : Nucleus.HolE.EqTm Γ loweredLeft loweredRight loweredType) :
    EqTm typeScope termScope Γ left right type :=
  ⟨loweredLeft, loweredRight, loweredType, leftLowering, rightLowering,
    typeLowering, derivation⟩

def Proves.sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : BoundCtx Sig types depth}
    {hypotheses : List (Tm Sig)} {conclusion : Tm Sig}
    (proof : Proves typeScope termScope Γ hypotheses conclusion) :
    Nucleus.HolE.Proves Γ proof.loweredHypotheses proof.loweredConclusion :=
  proof.derivation

def Proves.complete {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : BoundCtx Sig types depth}
    {hypotheses : List (Tm Sig)} {conclusion : Tm Sig}
    {loweredHypotheses : List (Nucleus.HolE.Tm Sig types depth)}
    {loweredConclusion : Nucleus.HolE.Tm Sig types depth}
    (hypothesesLowering :
      lowerTerms typeScope termScope hypotheses = some loweredHypotheses)
    (conclusionLowering :
      conclusion.lowerTm typeScope termScope = some loweredConclusion)
    (derivation : Nucleus.HolE.Proves Γ loweredHypotheses loweredConclusion) :
    Proves typeScope termScope Γ hypotheses conclusion :=
  ⟨loweredHypotheses, loweredConclusion, hypothesesLowering,
    conclusionLowering, derivation⟩

/-- The reference empty-signature Ethane theory cannot prove false. -/
theorem Proves.consistent
    (proof : Proves (.nil : TyScope []) (.nil : TmScope EmptySig 0)
      (Nucleus.HolE.emptyBound : BoundCtx EmptySig [] 0) [] (.bool false)) : False := by
  have hypotheses : proof.loweredHypotheses = [] := by
    simpa [lowerTerms] using proof.hypothesesLowering.symm
  have conclusion : proof.loweredConclusion = .bool false := by
    simpa [Expr.lowerTm, Expr.toHolE, Nucleus.HolE.Named.lowerTm]
      using proof.conclusionLowering.symm
  have derivation := proof.derivation
  rw [hypotheses, conclusion] at derivation
  exact Nucleus.HolE.classical_consistent derivation

end Nucleus.Hol.Ethane.Reference
