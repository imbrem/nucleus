import Nucleus.HolE.Kernel
import Nucleus.HolE.Named.Typing

/-!
# Named HolE proof certificates

Equality and provability are exact pullbacks of the locally nameless kernel.
Consequently this layer covers every kernel rule, including choice, beta/eta,
subtypes, type existence, and model specification, without duplicating the
trusted rule set.
-/

namespace Nucleus.HolE.Named

universe u
set_option relaxedAutoImplicit true

noncomputable def lowerTerms (typeScope : TyScope types) (termScope : TmScope Sig depth) :
    List (Tm Sig) → Option (List (Nucleus.HolE.Tm Sig types depth))
  | [] => some []
  | term :: terms => return (← lowerTm typeScope termScope term) ::
      (← lowerTerms typeScope termScope terms)

/-- Named term equality, carrying its locally nameless proof certificate. -/
structure EqTm {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth)
    (left right : Tm Sig) (A : Ty Sig) where
  loweredLeft : Nucleus.HolE.Tm Sig types depth
  loweredRight : Nucleus.HolE.Tm Sig types depth
  loweredType : Nucleus.HolE.Ty Sig types
  leftLowering : lowerTm typeScope termScope left = some loweredLeft
  rightLowering : lowerTm typeScope termScope right = some loweredRight
  typeLowering : lowerTy typeScope A = some loweredType
  derivation : Nucleus.HolE.EqTm Γ loweredLeft loweredRight loweredType

/-- Named provability, carrying a certificate for the lowered sequent. -/
structure Proves {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth)
    (hypotheses : List (Tm Sig)) (conclusion : Tm Sig) where
  loweredHypotheses : List (Nucleus.HolE.Tm Sig types depth)
  loweredConclusion : Nucleus.HolE.Tm Sig types depth
  hypothesesLowering :
    lowerTerms typeScope termScope hypotheses = some loweredHypotheses
  conclusionLowering :
    lowerTm typeScope termScope conclusion = some loweredConclusion
  derivation : Nucleus.HolE.Proves Γ loweredHypotheses loweredConclusion

/-- Soundness is projection of the locally nameless proof certificate. -/
def Proves.sound {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (Tm Sig)} {conclusion : Tm Sig}
    (proof : Proves typeScope termScope Γ hypotheses conclusion) :
    Nucleus.HolE.Proves Γ proof.loweredHypotheses proof.loweredConclusion :=
  proof.derivation

/-- Every locally nameless proof over fixed named preimages lifts back. -/
def Proves.complete
    {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (Tm Sig)} {conclusion : Tm Sig}
    {loweredHypotheses : List (Nucleus.HolE.Tm Sig types depth)}
    {loweredConclusion : Nucleus.HolE.Tm Sig types depth}
    (hypothesesLowering :
      lowerTerms typeScope termScope hypotheses = some loweredHypotheses)
    (conclusionLowering :
      lowerTm typeScope termScope conclusion = some loweredConclusion)
    (derivation : Nucleus.HolE.Proves Γ loweredHypotheses loweredConclusion) :
    Proves typeScope termScope Γ hypotheses conclusion :=
  ⟨loweredHypotheses, loweredConclusion, hypothesesLowering,
    conclusionLowering, derivation⟩

theorem Proves.alphaConclusion
    {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : TyScope types}
    {termScope : TmScope Sig depth} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {hypotheses : List (Tm Sig)} {left right : Tm Sig}
    (equivalent : Alpha typeScope termScope left right)
    (proof : Proves typeScope termScope Γ hypotheses left) :
    Nonempty (Proves typeScope termScope Γ hypotheses right) := by
  obtain ⟨lowered, leftLowering, rightLowering⟩ := equivalent
  have leftLowering' : lowerTm typeScope termScope left = some lowered := leftLowering
  have rightLowering' : lowerTm typeScope termScope right = some lowered := rightLowering
  rw [proof.conclusionLowering] at leftLowering'
  have same := Option.some.inj leftLowering'
  subst lowered
  exact ⟨⟨proof.loweredHypotheses, proof.loweredConclusion,
    proof.hypothesesLowering, rightLowering', proof.derivation⟩⟩

end Nucleus.HolE.Named
