import Nucleus.HolOmega.Proof

/-! Typing regularity for raw HOL-omega proof certificates. -/

universe u

namespace Nucleus.HolOmega

variable {Base : Type u}

/-- Both endpoints of a raw equality certificate have its indexed type. -/
theorem EqTm.hasType (h : @EqTm Base Δ Γ t u A) :
    HasType Δ Γ t A ∧ HasType Δ Γ u A := by
  induction h with
  | refl ht => exact ⟨ht, ht⟩
  | symm _ ih => exact ⟨ih.2, ih.1⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | app _ _ ihf ihx => exact ⟨.tmApp ihf.1 ihx.1, .tmApp ihf.2 ihx.2⟩
  | lam hA _ ih => exact ⟨.tmLam hA ih.1, .tmLam hA ih.2⟩
  | tyApp hX _ ih => exact ⟨.tmTyApp ih.1 hX, .tmTyApp ih.2 hX⟩
  | tyLam _ ih => exact ⟨.tmTyLam ih.1, .tmTyLam ih.2⟩
  | beta hA hfun hx hinst => exact ⟨.tmApp (.tmLam hA hfun) hx, hinst⟩
  | eta hf heta => exact ⟨heta, hf⟩
  | tyBeta hbody hX hinst => exact ⟨.tmTyApp (.tmTyLam hbody) hX, hinst⟩
  | tyEta hf heta => exact ⟨heta, hf⟩
  | unpackPack hA hB hX ht hk hrhs =>
      exact ⟨.tmUnpack hA hB hk (.tmPack hA hX ht), hrhs⟩
  | packOnto hp heta => exact ⟨heta, hp⟩

theorem EqTm.leftType (h : @EqTm Base Δ Γ t u A) : HasType Δ Γ t A :=
  h.hasType.1

theorem EqTm.rightType (h : @EqTm Base Δ Γ t u A) : HasType Δ Γ u A :=
  h.hasType.2

/-- Membership in a typed hypothesis list supplies the Boolean typing proof. -/
theorem TypedHyps.lookup (hH : @TypedHyps Base Δ Γ H) (hp : p ∈ H) :
    HasType Δ Γ p .tyBool := hH p hp

/-- Every raw theorem certificate retains well-typed hypotheses and has a
Boolean conclusion. -/
theorem Proves.regular (h : @Proves Base Δ Γ H p) :
    TypedHyps Δ Γ H ∧ HasType Δ Γ p .tyBool := by
  induction h with
  | hyp hH hp => exact ⟨hH, hH.lookup hp⟩
  | truth hH => exact ⟨hH, .tmBool⟩
  | eqRefl hH hx hA => exact ⟨hH, .tmEq hA hx hx⟩
  | eqMp hH hp hx hy hA _ _ _ _ => exact ⟨hH, .tmApp hp hy⟩
  | choice hH hp hx hA _ _ => exact ⟨hH, .tmApp hp (.tmEps hA hp)⟩
  | convert hH heq _ _ => exact ⟨hH, heq.rightType⟩
  | eqOfEqTm hH hA heq => exact ⟨hH, .tmEq hA heq.leftType heq.rightType⟩
  | antisymm hH hp hq _ _ _ _ _ _ =>
      exact ⟨hH, .tmEq (Judgement.tyBool (r := 0)) hp hq⟩
  | absRep hH hA hp hx =>
      have hrep : HasType _ _ (.tmRep _ _ _) _ := .tmRep hA hp hx
      have habs : HasType _ _ (.tmAbs _ _ (.tmRep _ _ _)) _ := .tmAbs hA hp hrep
      exact ⟨hH, .tmEq (.tySub hA hp) habs hx⟩
  | repAbs hH hA hp hx hpx _ _ =>
      have habs : HasType _ _ (.tmAbs _ _ _) _ := .tmAbs hA hp hx
      have hrep : HasType _ _ (.tmRep _ _ (.tmAbs _ _ _)) _ := .tmRep hA hp habs
      exact ⟨hH, .tmEq hA hrep hx⟩

theorem Proves.typedHyps (h : @Proves Base Δ Γ H p) : TypedHyps Δ Γ H :=
  h.regular.1

theorem Proves.hasType (h : @Proves Base Δ Γ H p) : HasType Δ Γ p .tyBool :=
  h.regular.2

end Nucleus.HolOmega
