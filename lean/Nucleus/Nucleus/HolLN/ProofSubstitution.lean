import Nucleus.HolLN.Kernel

/-!
# Type substitution for proof certificates

Admissible substitutions send atomic types to closed, well-kinded types.
Every equality and entailment certificate can then be transported to the
substituted signature.  In particular, this covers subtype predicates and the
natural-number rules that force the intended model to be infinite.
-/

namespace Nucleus.HolLN

universe u v

theorem TypedHyps.substTy {Base : Type u} {Target : Type v}
    {σ : TypeSub Base Target} (wellKinded : WellKindedTypeSub σ)
    {depth : Nat} {Γ : BoundCtx Base depth}
    {H : List (Tm Base depth)} (typed : TypedHyps Γ H) :
    TypedHyps (substBoundCtx σ Γ) (substHyps σ H) := by
  intro p member
  obtain ⟨q, original, equality⟩ := List.mem_map.mp member
  exact equality ▸ (typed q original).substTy wellKinded

def EqTm.substTy {Base : Type u} {Target : Type v} {σ : TypeSub Base Target}
    (admissible : AdmissibleTypeSub σ) :
    {depth : Nat} -> {Γ : BoundCtx Base depth} ->
    {t uterm : Tm Base depth} -> {A : Ty Base} -> EqTm Γ t uterm A ->
      EqTm (substBoundCtx σ Γ)
        (substTm σ t) (substTm σ uterm) (Nucleus.HolLN.substTy σ A)
  | _, _, _, _, _, .refl typing => .refl (typing.substTy admissible.wellKinded)
  | _, _, _, _, _, .symm equality => .symm (EqTm.substTy admissible equality)
  | _, _, _, _, _, .trans first second =>
      .trans (EqTm.substTy admissible first) (EqTm.substTy admissible second)
  | _, _, _, _, _, .app function argument =>
      .app (EqTm.substTy admissible function) (EqTm.substTy admissible argument)
  | _, _, _, _, _, .succ equality => .succ (EqTm.substTy admissible equality)
  | _, Γ, _, _, _, .lam hA equality => by
      apply EqTm.lam (hA.substTy admissible.wellKinded)
      simpa [substBoundCtx_extend] using EqTm.substTy admissible equality
  | _, Γ, _, _, _, .beta body x hA bodyTyping argumentTyping resultTyping => by
      have result := EqTm.beta (substTm σ body) (substTm σ x)
        (hA.substTy admissible.wellKinded)
        (by simpa [substBoundCtx_extend] using bodyTyping.substTy admissible.wellKinded)
        (argumentTyping.substTy admissible.wellKinded)
        (by simpa [substTm_openBound] using resultTyping.substTy admissible.wellKinded)
      simpa [substTm, Nucleus.HolLN.substTy, substHol, substTm_openBound] using result
  | _, _, _, _, _, .eta name fresh functionTyping etaTyping => by
      have result := EqTm.eta name
        (substHol_fresh σ name (fun kind base => admissible.closed kind base name) _ fresh)
        (functionTyping.substTy admissible.wellKinded)
        (by simpa [substTm, Nucleus.HolLN.substTy, substHol, substTm_weaken] using
          etaTyping.substTy admissible.wellKinded)
      simpa [substTm, Nucleus.HolLN.substTy, substHol, substTm_weaken] using result

def Proves.substTy {Base : Type u} {Target : Type v} {σ : TypeSub Base Target}
    (admissible : AdmissibleTypeSub σ) :
    {depth : Nat} -> {Γ : BoundCtx Base depth} ->
    {H : List (Tm Base depth)} -> {p : Tm Base depth} -> Proves Γ H p ->
      Proves (substBoundCtx σ Γ)
        (substHyps σ H) (substTm σ p)
  | _, _, _, _, .hyp typed member =>
      .hyp (typed.substTy admissible.wellKinded) (List.mem_map_of_mem member)
  | _, _, _, _, .truth typed => .truth (typed.substTy admissible.wellKinded)
  | _, _, _, _, .eqRefl typed hA hx =>
      .eqRefl (typed.substTy admissible.wellKinded)
        (hA.substTy admissible.wellKinded) (hx.substTy admissible.wellKinded)
  | _, _, _, _, .eqMp typed hA hp hx hy equality proof =>
      .eqMp (typed.substTy admissible.wellKinded)
        (hA.substTy admissible.wellKinded) (hp.substTy admissible.wellKinded)
        (hx.substTy admissible.wellKinded) (hy.substTy admissible.wellKinded)
        (Proves.substTy admissible equality) (Proves.substTy admissible proof)
  | _, _, _, _, .choice typed hA hp hx proof =>
      .choice (typed.substTy admissible.wellKinded)
        (hA.substTy admissible.wellKinded) (hp.substTy admissible.wellKinded)
        (hx.substTy admissible.wellKinded) (Proves.substTy admissible proof)
  | _, _, _, _, .convert typed equality proof =>
      .convert (typed.substTy admissible.wellKinded)
        (EqTm.substTy admissible equality) (Proves.substTy admissible proof)
  | _, _, _, _, .eqOfEqTm typed hA equality =>
      .eqOfEqTm (typed.substTy admissible.wellKinded)
        (hA.substTy admissible.wellKinded) (EqTm.substTy admissible equality)
  | _, _, _, _, .antisymm typed hp hq leftTyped rightTyped left right =>
      .antisymm (typed.substTy admissible.wellKinded)
        (hp.substTy admissible.wellKinded) (hq.substTy admissible.wellKinded)
        (leftTyped.substTy admissible.wellKinded)
        (rightTyped.substTy admissible.wellKinded)
        (Proves.substTy admissible left) (Proves.substTy admissible right)
  | _, _, _, _, .absRep typed hA hp hx => by
      apply Proves.absRep (typed.substTy admissible.wellKinded)
        (hA.substTy admissible.wellKinded)
      · simpa [Nucleus.HolLN.substTy, substTm, substHol, substBoundCtx_empty,
          substBoundCtx_extend] using
          hp.substTy admissible.wellKinded
      · exact hx.substTy admissible.wellKinded
  | _, _, _, _, .repAbs typed hA hp hx predicateTyping premise => by
      apply Proves.repAbs (typed.substTy admissible.wellKinded)
        (hA.substTy admissible.wellKinded)
      · simpa [Nucleus.HolLN.substTy, substTm, substHol, substBoundCtx_empty,
          substBoundCtx_extend] using
          hp.substTy admissible.wellKinded
      · exact hx.substTy admissible.wellKinded
      · simpa [Nucleus.HolLN.substTy, substTm, substHol, substTm_instantiateOne] using
          predicateTyping.substTy admissible.wellKinded
      · simpa [Nucleus.HolLN.substTy, substTm, substHol, substTm_instantiateOne] using
          Proves.substTy admissible premise
  | _, _, _, _, .succInjective typed hx hy premise =>
      .succInjective (typed.substTy admissible.wellKinded)
        (hx.substTy admissible.wellKinded) (hy.substTy admissible.wellKinded)
        (Proves.substTy admissible premise)
  | _, _, _, _, .zeroNotSucc typed hx =>
      .zeroNotSucc (typed.substTy admissible.wellKinded)
        (hx.substTy admissible.wellKinded)

end Nucleus.HolLN
