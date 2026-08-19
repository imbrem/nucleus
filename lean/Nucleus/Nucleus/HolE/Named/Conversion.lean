import Nucleus.HolE.Named.Kernel

/-!
# Conversion for named HolE

These definitions are the small public interface to the conversion rules
already trusted by the locally nameless kernel.  They are exact pullbacks
along named lowering.  The proofs relating them to the kernel live in
`Named.ConversionLaws`.

Type-family eta is intentionally absent: `Nucleus.HolE.FamEq` does not contain
that rule.  Adding it here would strengthen the kernel rather than merely give
the existing rules a named presentation.
-/

namespace Nucleus.HolE.Named

universe u
set_option relaxedAutoImplicit true

/-- Named type-family conversion is a certificate for the two lowered
families.  This is the type-level analogue of `Named.EqTm`. -/
structure FamEq {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (left right : Fam Sig kind) where
  loweredLeft : Nucleus.HolE.Fam Sig types kind
  loweredRight : Nucleus.HolE.Fam Sig types kind
  leftLowering : lowerFam typeScope left = some loweredLeft
  rightLowering : lowerFam typeScope right = some loweredRight
  derivation : Nucleus.HolE.FamEq Sig loweredLeft loweredRight

/-- Propositional term conversion.  Proof-relevant certificates remain
available through `Named.EqTm`. -/
abbrev TmConv {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth)
    (left right : Tm Sig) (A : Ty Sig) : Prop :=
  Nonempty (EqTm typeScope termScope Γ left right A)

/-- Propositional type-family conversion. -/
abbrev FamConv {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (left right : Fam Sig kind) : Prop :=
  Nonempty (FamEq typeScope left right)

/-- Named typing modulo type-family conversion. -/
def HasTypeConv {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth) (term : Tm Sig) (A : Ty Sig) : Prop :=
  ∃ loweredTerm loweredType,
    lowerTm typeScope termScope term = some loweredTerm ∧
    lowerTy typeScope A = some loweredType ∧
    Nucleus.HolE.HasTypeDefEq Γ loweredTerm loweredType

/-- A named hypothesis list whose lowering is accepted by the kernel. -/
def TypedHyps {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth) (hypotheses : List (Tm Sig)) : Prop :=
  ∃ loweredHypotheses,
    lowerTerms typeScope termScope hypotheses = some loweredHypotheses ∧
    Nucleus.HolE.TypedHyps Γ loweredHypotheses

/-- One root type-family beta contraction, stated independently of typing. -/
structure FamBeta {Sig : Signature} (typeScope : TyScope types)
    (source target : Fam Sig codomain) where
  domain : Kind
  body : Nucleus.HolE.Fam Sig (domain :: types) codomain
  argument : Nucleus.HolE.Fam Sig types domain
  sourceLowering :
    lowerFam typeScope source = some (.tyApp (.tyLam body) argument)
  targetLowering :
    lowerFam typeScope target = some (Nucleus.HolE.openType body argument)

/-- One root term beta contraction, modulo alpha conversion of either named
endpoint. -/
structure TmBeta {Sig : Signature} (typeScope : TyScope types)
    (termScope : TmScope Sig depth) (source target : Tm Sig) where
  domain : Nucleus.HolE.Ty Sig types
  body : Nucleus.HolE.Tm Sig types (depth + 1)
  argument : Nucleus.HolE.Tm Sig types depth
  sourceLowering :
    lowerTm typeScope termScope source = some (.app (.lam domain body) argument)
  targetLowering :
    lowerTm typeScope termScope target =
      some (Nucleus.HolE.openBound body argument)

/-- One root term eta contraction.  The freshness witness is exactly the
side-condition consumed by the kernel eta rule. -/
structure TmEta {Sig : Signature} (typeScope : TyScope types)
    (termScope : TmScope Sig depth) (source target : Tm Sig) where
  domain : Nucleus.HolE.Ty Sig types
  function : Nucleus.HolE.Tm Sig types depth
  freshName : Nat
  fresh : Nucleus.HolE.Fresh freshName function
  sourceLowering : lowerTm typeScope termScope source = some
    (.lam domain (.app (Nucleus.HolE.weaken function) (.bv 0)))
  targetLowering : lowerTm typeScope termScope target = some function

end Nucleus.HolE.Named
