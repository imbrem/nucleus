import Nucleus.HolE.Kernel

/-!
# Cut admissibility for HolE proofs

The primitive kernel deliberately has no cut constructor.  This file derives
single-hypothesis elimination from Boolean case analysis, equality transport,
beta conversion, and false elimination, then iterates it over a hypothesis
list.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- The empty bound-variable context is well typed. -/
theorem typedCtx_emptyBound {Sig : Signature} [SigTyping Sig]
    {types : List Kind} :
    TypedCtx (emptyBound : BoundCtx Sig types 0) :=
  fun index => Fin.elim0 index

namespace Proves

private def boolIdentity {Sig : Signature} {types : List Kind} {depth : Nat} :
    Tm Sig types depth :=
  .lam .boolTy (.bv 0)

private theorem boolIdentity_type {Sig : Signature} [SigTyping Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth} :
    HasType Γ (boolIdentity (Sig := Sig)) (.arr .boolTy .boolTy) := by
  exact .lam _ .boolTy (.bv .boolTy rfl)

private theorem boolIdentity_app_type {Sig : Signature} [SigTyping Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {proposition : Tm Sig types depth}
    (typing : HasType Γ proposition .boolTy) :
    HasType Γ (.app boolIdentity proposition) .boolTy :=
  .app boolIdentity_type typing

private def boolIdentity_beta {Sig : Signature} [SigTyping Sig]
    [SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {proposition : Tm Sig types depth}
    (typedContext : TypedCtx Γ) (typing : HasType Γ proposition .boolTy) :
    EqTm Γ (.app boolIdentity proposition) proposition .boolTy := by
  have resultTyping :
      HasTypeDefEq Γ (openBound (.bv 0) proposition) .boolTy := by
    simpa [openBound] using (HasTypeDefEq.exact typing)
  simpa [boolIdentity, openBound] using
    (EqTm.beta (Γ := Γ) (.bv 0) proposition (.boolTy) typedContext
      (boolIdentity_app_type typing)
      (.exact (.bv (.boolTy : Kinded (.boolTy : Ty Sig types)) rfl))
      (.exact typing) resultTyping)

/-- Eliminate one raw-Boolean hypothesis.  `TypedCtx Γ` is required only for
the beta conversions used by the identity predicate in the false branch. -/
noncomputable def cutHead {Sig : Signature} [SigTyping Sig]
    [SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {hypotheses : List (Tm Sig types depth)} {proposition conclusion : Tm Sig types depth}
    (typedContext : TypedCtx Γ) (propositionTyping : HasType Γ proposition .boolTy)
    (premise : Proves Γ hypotheses proposition)
    (derivation : Proves Γ (proposition :: hypotheses) conclusion) :
    Proves Γ hypotheses conclusion := by
  let equation : Tm Sig types depth := .eq .boolTy proposition (.bool false)
  have equationTyping : HasType Γ equation .boolTy :=
    .eq .boolTy propositionTyping (.bool false)
  have extendedTyped : TypedHyps Γ (equation :: hypotheses) := by
    intro candidate membership
    rcases List.mem_cons.mp membership with rfl | membership
    · exact .exact equationTyping
    · exact premise.typedHypotheses candidate membership
  have right : Proves Γ (equation :: hypotheses) conclusion := by
    have equationProof : Proves Γ (equation :: hypotheses) equation :=
      .hyp extendedTyped (.exact equationTyping) (by simp [equation])
    have propositionProof : Proves Γ (equation :: hypotheses) proposition :=
      premise.mapHypotheses extendedTyped
        (fun candidate membership => List.mem_cons_of_mem _ membership)
    have applicationProof :
        Proves Γ (equation :: hypotheses) (.app boolIdentity proposition) :=
      .convert extendedTyped (.exact (boolIdentity_app_type propositionTyping))
        (EqTm.symm (boolIdentity_beta typedContext propositionTyping)) propositionProof
    have falseTyping : HasType Γ (.bool false) .boolTy := .bool false
    have falseApplicationProof :
        Proves Γ (equation :: hypotheses) (.app boolIdentity (.bool false)) :=
      .eqMp extendedTyped .boolTy
        (.exact (boolIdentity_app_type falseTyping))
        (.exact boolIdentity_type) (.exact propositionTyping) (.exact falseTyping)
        equationProof applicationProof
    have falseProof : Proves Γ (equation :: hypotheses) (.bool false) :=
      .convert extendedTyped (.exact falseTyping)
        (boolIdentity_beta typedContext falseTyping) falseApplicationProof
    exact .falseElim extendedTyped derivation.conclusionTyping
      derivation.conclusionTyping falseProof
  exact .boolCases premise.typedHypotheses (.exact propositionTyping)
    derivation.conclusionTyping derivation.typedHypotheses extendedTyped
    derivation right

/-- Replace every hypothesis used by a proof with a proof of that hypothesis
from a target context. -/
private noncomputable def cutList {Sig : Signature} [SigTyping Sig]
    [SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {source target : List (Tm Sig types depth)} {conclusion : Tm Sig types depth}
    (typedContext : TypedCtx Γ) (targetTyped : TypedHyps Γ target)
    (sourceTyped : ∀ proposition, proposition ∈ source →
      HasType Γ proposition .boolTy)
    (replacement : ∀ proposition, proposition ∈ source → Proves Γ target proposition)
    (derivation : Proves Γ (source ++ target) conclusion) :
    Proves Γ target conclusion := by
  match source with
  | [] => simpa using derivation
  | proposition :: rest =>
      have restTargetTyped : TypedHyps Γ (rest ++ target) := by
        intro candidate membership
        rcases List.mem_append.mp membership with membership | membership
        · exact .exact (sourceTyped candidate (by simp [membership]))
        · exact targetTyped candidate membership
      have propositionProof : Proves Γ (rest ++ target) proposition :=
        (replacement proposition (by simp)).mapHypotheses restTargetTyped
          (fun candidate membership => List.mem_append_right _ membership)
      have withoutHead : Proves Γ (rest ++ target) conclusion :=
        cutHead typedContext (sourceTyped proposition (by simp)) propositionProof
          (by simpa [List.cons_append] using derivation)
      exact cutList typedContext targetTyped
        (fun candidate membership =>
          sourceTyped candidate (List.mem_cons_of_mem _ membership))
        (fun candidate membership =>
          replacement candidate (List.mem_cons_of_mem _ membership))
        withoutHead
termination_by source.length

/-- Replace every hypothesis used by a proof with a proof of that hypothesis
from a target context.  Source hypotheses are required to have the raw Boolean
type because `boolCases` is syntax directed. -/
noncomputable def cut {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {Γ : BoundCtx Sig types depth}
    {source target : List (Tm Sig types depth)} {conclusion : Tm Sig types depth}
    (typedContext : TypedCtx Γ) (targetTyped : TypedHyps Γ target)
    (sourceTyped : ∀ proposition, proposition ∈ source →
      HasType Γ proposition .boolTy)
    (replacement : ∀ proposition, proposition ∈ source → Proves Γ target proposition)
    (derivation : Proves Γ source conclusion) : Proves Γ target conclusion := by
  have combinedTyped : TypedHyps Γ (source ++ target) := by
    intro proposition membership
    rcases List.mem_append.mp membership with membership | membership
    · exact .exact (sourceTyped proposition membership)
    · exact targetTyped proposition membership
  have combined : Proves Γ (source ++ target) conclusion :=
    derivation.mapHypotheses combinedTyped
      (fun proposition membership => List.mem_append_left _ membership)
  exact cutList typedContext targetTyped sourceTyped replacement combined

end Proves

end Nucleus.HolE
