import Nucleus.HolE.ClassicalTransport
import Nucleus.HolE.ClassicalEquations

/-! # Semantic soundness of HolE type-family computation

This file isolates the transport facts for the deterministic classical model.
In particular, type-family beta is genuine semantic beta reduction rather
than an additional assumption made by the proof-system soundness theorem.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Heterogeneous-looking classifications have the same semantic result shape:
renaming changes the advertised syntax of a term's type, but not the evaluator
interface. -/
def CRenameEq {types target : List Kind} {sort : HolSort} {depth : Nat}
    (classification : Classification ClassicalSig types sort)
    (ρ : TyRen types target)
    (left : CResult (depth := depth) (classification.rename ρ))
    (right : CResult (depth := depth) classification) : Prop :=
  match classification with
  | .kind => left = right
  | .tm _ => left = right

private theorem cSem_rename_as
    {types target : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {expression : Expr ClassicalSig types sort depth}
    {classification : Classification ClassicalSig types sort}
    (checking : CChecks Γ expression classification)
    (ρ : TyRen types target) (env : CTypeEnv target)
    (renamed : CChecks (renameBoundCtx ρ Γ) (renameTypes ρ expression)
      (classification.rename ρ)) :
    cSem (checking.renameTypes ρ) env = cSem renamed env :=
  cSem_certificate_coherent _ _ env

private theorem cSem_kind_normalize
    {types target : List Kind} {kind : Kind}
    {family : Fam ClassicalSig types kind} (ρ : TyRen types target)
    (renamed : CChecks (renameBoundCtx ρ emptyBound) (renameTypes ρ family)
      (Classification.rename ρ .kind))
    (normalized : Fam ClassicalSig target kind)
    (syntaxEq : renameTypes ρ family = normalized)
    (clean : CKinded normalized) (env : CTypeEnv target) :
    cSem renamed env = cSem clean env := by
  subst normalized
  change CChecks (renameBoundCtx ρ emptyBound) (renameTypes ρ family) .kind at renamed
  have contextEq : renameBoundCtx ρ
      (emptyBound : BoundCtx ClassicalSig types 0) =
      (emptyBound : BoundCtx ClassicalSig target 0) := renameBoundCtx_empty ρ
  let Packed := Σ Γ : BoundCtx ClassicalSig target 0,
    CChecks Γ (renameTypes ρ family) .kind
  let left : Packed := ⟨renameBoundCtx ρ emptyBound, renamed⟩
  let right : Packed := ⟨emptyBound, clean⟩
  have packedEq : left = right := by
    apply Sigma.ext contextEq
    dsimp [left, right]
    let transported : CChecks (renameBoundCtx ρ emptyBound)
        (renameTypes ρ family) .kind := contextEq.symm ▸ clean
    have htransport : HEq transported clean := by
      dsimp only [transported]
      exact @eqRec_heq (BoundCtx ClassicalSig target 0)
        (fun Γ => CChecks Γ (renameTypes ρ family) .kind)
        emptyBound (renameBoundCtx ρ emptyBound) contextEq.symm clean
    exact (heq_of_eq (CChecks.unique renamed transported)).trans htransport
  exact congrArg (fun packed : Packed => cSem packed.2 env) packedEq

private theorem cSem_tm_normalize
    {types target : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {term : Tm ClassicalSig types depth} {A : Ty ClassicalSig types}
    (ρ : TyRen types target)
    (renamed : CChecks (renameBoundCtx ρ Γ) (renameTypes ρ term)
      (Classification.rename ρ (.tm A)))
    (targetΓ : BoundCtx ClassicalSig target depth)
    (contextEq : renameBoundCtx ρ Γ = targetΓ)
    (clean : CChecks targetΓ (renameTypes ρ term)
      (.tm (renameTypes ρ A))) (env : CTypeEnv target) :
    cSem renamed env = cSem clean env := by
  change CChecks (renameBoundCtx ρ Γ) (renameTypes ρ term)
    (.tm (renameTypes ρ A)) at renamed
  let Packed := Σ Δ : BoundCtx ClassicalSig target depth,
    CChecks Δ (renameTypes ρ term) (.tm (renameTypes ρ A))
  let left : Packed := ⟨renameBoundCtx ρ Γ, renamed⟩
  let right : Packed := ⟨targetΓ, clean⟩
  have packedEq : left = right := by
    apply Sigma.ext contextEq
    dsimp [left, right]
    let transported : CChecks (renameBoundCtx ρ Γ) (renameTypes ρ term)
        (.tm (renameTypes ρ A)) := contextEq.symm ▸ clean
    have htransport : HEq transported clean := by
      dsimp only [transported]
      exact @eqRec_heq (BoundCtx ClassicalSig target depth)
        (fun Δ => CChecks Δ (renameTypes ρ term) (.tm (renameTypes ρ A)))
        targetΓ (renameBoundCtx ρ Γ) contextEq.symm clean
    exact (heq_of_eq (CChecks.unique renamed transported)).trans htransport
  exact congrArg (fun packed : Packed => cSem packed.2 env) packedEq

/-- Renaming type variables only restricts the semantic environment. -/
theorem cSem_renameTypes {types target : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {expression : Expr ClassicalSig types sort depth}
    {classification : Classification ClassicalSig types sort}
    (checking : CChecks Γ expression classification)
    (ρ : TyRen types target) (env : CTypeEnv target) :
    CRenameEq classification ρ (cSem (checking.renameTypes ρ) env)
      (cSem checking (env.rename ρ)) := by
  induction checking generalizing target with
  | boolTy =>
      simp only [CRenameEq]
      rw [cSem_kind_normalize ρ (CChecks.boolTy.renameTypes ρ)
        .boolTy (by rfl) (CChecks.boolTy (types := target)) env]
      rfl
  | arr hA hB ihA ihB =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      have cB := hB.renameTypes ρ
      rw [renameBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      rw [cSem_kind_normalize ρ ((CChecks.arr hA hB).renameTypes ρ)
        (.arr (renameTypes ρ _) (renameTypes ρ _)) (by rfl)
        (CChecks.arr cA cB) env]
      simp only [cSem_arr_eq]
      have semA : cSem cA env = cSem hA (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hA.renameTypes ρ) _ rfl cA env]
        exact ihA ρ env
      have semB : cSem cB env = cSem hB (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hB.renameTypes ρ) _ rfl cB env]
        exact ihB ρ env
      rw [semA, semB]
  | tyApp hF hA ihF ihA =>
      simp only [CRenameEq]
      have cF := hF.renameTypes ρ
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cF cA
      change CKinded _ at cF cA
      rw [cSem_kind_normalize ρ ((CChecks.tyApp hF hA).renameTypes ρ)
        (.tyApp (renameTypes ρ _) (renameTypes ρ _)) (by rfl)
        (CChecks.tyApp cF cA) env]
      simp only [cSem_tyApp_eq]
      have semF : cSem cF env = cSem hF (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hF.renameTypes ρ) _ rfl cF env]
        exact ihF ρ env
      have semA : cSem cA env = cSem hA (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hA.renameTypes ρ) _ rfl cA env]
        exact ihA ρ env
      rw [semF, semA]
  | tyLam body ih =>
      simp only [CRenameEq]
      have cb := body.renameTypes (liftTyRen ρ)
      rw [renameBoundCtx_empty] at cb
      change CKinded _ at cb
      rw [cSem_kind_normalize ρ ((CChecks.tyLam body).renameTypes ρ)
        (.tyLam (renameTypes (liftTyRen ρ) _)) (by rfl)
        (CChecks.tyLam cb) env]
      funext argument
      change cSem cb (extendCTypeEnv argument env) =
        cSem body (extendCTypeEnv argument (env.rename ρ))
      have semBody : cSem cb (extendCTypeEnv argument env) =
          cSem body ((extendCTypeEnv argument env).rename (liftTyRen ρ)) := by
        rw [← cSem_kind_normalize (liftTyRen ρ) (body.renameTypes (liftTyRen ρ))
          _ rfl cb (extendCTypeEnv argument env)]
        exact ih (liftTyRen ρ) (extendCTypeEnv argument env)
      rw [semBody, CTypeEnv.rename_lift]
  | tyBv v =>
      simp only [CRenameEq]
      rw [cSem_kind_normalize ρ ((CChecks.tyBv v).renameTypes ρ)
        (.tyBv (ρ v)) (by rfl) (CChecks.tyBv (ρ v)) env]
      rfl
  | sub hA hp ihA ihp =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      have cp := hp.renameTypes ρ
      rw [renameBoundCtx_extend, renameBoundCtx_empty] at cp
      change CHasType (extendBound (renameTypes ρ _) emptyBound)
        (renameTypes ρ _) .boolTy at cp
      rw [cSem_kind_normalize ρ ((CChecks.sub hA hp).renameTypes ρ)
        (.sub (renameTypes ρ _) (renameTypes ρ _)) (by rfl)
        (CChecks.sub cA cp) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hA.renameTypes ρ) _ rfl cA env]
        exact ihA ρ env
      rw [semA]
      congr 1
      funext value
      have semP := cSem_tm_normalize ρ (hp.renameTypes ρ) _ (by
        rw [renameBoundCtx_extend, renameBoundCtx_empty]) cp env
      let bound := extendCBoundEnv (cSem hA (env.rename ρ)) value emptyCBoundEnv
      have cleanToRenamed := congrFun (congrFun semP.symm bound) cBool
      have renamedToOriginal := congrFun (congrFun (ihp ρ env) bound) cBool
      exact congrArg ULift.down (cleanToRenamed.trans renamedToOriginal)
  | model hp ih =>
      simp only [CRenameEq]
      have cp := hp.renameTypes (liftTyRen ρ)
      rw [renameBoundCtx_empty] at cp
      change CHasType emptyBound (renameTypes (liftTyRen ρ) _) .boolTy at cp
      rw [cSem_kind_normalize ρ ((CChecks.model hp).renameTypes ρ)
        (.model (renameTypes (liftTyRen ρ) _)) (by rfl)
        (CChecks.model cp) env]
      simp only [cSem]
      apply congrArg chooseCModel
      funext candidate
      have semP := cSem_tm_normalize (liftTyRen ρ)
        (hp.renameTypes (liftTyRen ρ)) _ (by rw [renameBoundCtx_empty]) cp
        (extendCTypeEnv (kind := .star) candidate env)
      have renamedEnv :
          (extendCTypeEnv (kind := .star) candidate env).rename (liftTyRen ρ) =
            extendCTypeEnv (kind := .star) candidate (env.rename ρ) :=
        CTypeEnv.rename_lift (kind := .star) ρ env candidate
      let extEnv := extendCTypeEnv (kind := .star) candidate env
      have cleanToRenamed := congrFun (congrFun semP.symm emptyCBoundEnv) cBool
      have renamedToOriginal := congrFun
        (congrFun (ih (liftTyRen ρ) extEnv) emptyCBoundEnv) cBool
      have evalEq := cleanToRenamed.trans renamedToOriginal
      rw [renamedEnv] at evalEq
      exact congrArg (fun result => result = ⟨true⟩) evalEq
  | primFam symbol => exact nomatch symbol
  | primTm rule => exact nomatch rule
  | bv hA lookup ihA =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [cSem_tm_normalize ρ ((CChecks.bv hA lookup).renameTypes ρ) _ rfl
        (CChecks.bv cA (congrArg (renameTypes ρ) lookup)) env]
      rfl
  | fv name hA ihA =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [cSem_tm_normalize ρ ((CChecks.fv name hA).renameTypes ρ) _ rfl
        (CChecks.fv name cA) env]
      rfl
  | app hA hB hf hx ihA ihB ihf ihx =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      have cB := hB.renameTypes ρ
      rw [renameBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      rw [cSem_tm_normalize ρ ((CChecks.app hA hB hf hx).renameTypes ρ) _ rfl
        (CChecks.app cA cB (hf.renameTypes ρ) (hx.renameTypes ρ)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hA.renameTypes ρ) _ rfl cA env]
        exact ihA ρ env
      have semB : cSem cB env = cSem hB (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hB.renameTypes ρ) _ rfl cB env]
        exact ihB ρ env
      rw [semA, semB]
      funext bound expected
      let domain := cSem hA (env.rename ρ)
      let codomain := cSem hB (env.rename ρ)
      let functionType : CPointed :=
        ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
      have fEq := congrFun (congrFun (ihf ρ env) bound) functionType
      have xEq := congrFun (congrFun (ihx ρ env) bound) domain
      dsimp [functionType, domain, codomain] at fEq xEq
      rw [fEq, xEq]
  | lam body hA hB hb ihA ihB ihb =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      have cB := hB.renameTypes ρ
      rw [renameBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      have cb := hb.renameTypes ρ
      rw [renameBoundCtx_extend] at cb
      change CHasType (extendBound (renameTypes ρ _) (renameBoundCtx ρ _))
        (renameTypes ρ _) (renameTypes ρ _) at cb
      rw [cSem_tm_normalize ρ ((CChecks.lam body hA hB hb).renameTypes ρ) _ rfl
        (CChecks.lam _ cA cB cb) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hA.renameTypes ρ) _ rfl cA env]
        exact ihA ρ env
      have semB : cSem cB env = cSem hB (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hB.renameTypes ρ) _ rfl cB env]
        exact ihB ρ env
      rw [semA, semB]
      funext bound expected
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      funext argument
      let carrier := cSem hA (env.rename ρ)
      let targetBound := extendCBoundEnv carrier argument bound
      have semBody := cSem_tm_normalize ρ (hb.renameTypes ρ) _ (by
        rw [renameBoundCtx_extend]) cb env
      have cleanToRenamed := congrFun (congrFun semBody.symm targetBound)
        (cSem hB (env.rename ρ))
      have renamedToOriginal := congrFun (congrFun (ihb ρ env) targetBound)
        (cSem hB (env.rename ρ))
      exact congrArg ULift.down (cleanToRenamed.trans renamedToOriginal)
  | bool value =>
      simp only [CRenameEq]
      rw [cSem_tm_normalize ρ ((CChecks.bool value).renameTypes ρ) _ rfl
        (CChecks.bool value) env]
      rfl
  | eq hA hx hy ihA ihx ihy =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [cSem_tm_normalize ρ ((CChecks.eq hA hx hy).renameTypes ρ) _ rfl
        (CChecks.eq cA (hx.renameTypes ρ) (hy.renameTypes ρ)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hA.renameTypes ρ) _ rfl cA env]
        exact ihA ρ env
      rw [semA]
      funext bound expected
      have xEq := congrFun (congrFun (ihx ρ env) bound)
        (cSem hA (env.rename ρ))
      have yEq := congrFun (congrFun (ihy ρ env) bound)
        (cSem hA (env.rename ρ))
      have xd := congrArg ULift.down xEq
      have yd := congrArg ULift.down yEq
      apply congrArg ULift.up
      apply congrArg (alignCValue cBool expected)
      apply decide_eq_decide.mpr
      constructor
      · intro equality
        exact xd.symm.trans (equality.trans yd)
      · intro equality
        exact xd.trans (equality.trans yd.symm)
  | eps hA hp ihA ihp =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [cSem_tm_normalize ρ ((CChecks.eps hA hp).renameTypes ρ) _ rfl
        (CChecks.eps cA (hp.renameTypes ρ)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hA.renameTypes ρ) _ rfl cA env]
        exact ihA ρ env
      rw [semA]
      funext bound expected
      let carrier := cSem hA (env.rename ρ)
      let functionType : CPointed := ⟨carrier.carrier → Bool, fun _ => false⟩
      have pEq := congrFun (congrFun (ihp ρ env) bound) functionType
      dsimp [functionType, carrier] at pEq
      rw [pEq]
  | abs hA hp hx ihA ihp ihx =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      have cp := hp.renameTypes ρ
      rw [renameBoundCtx_extend, renameBoundCtx_empty] at cp
      change CHasType (extendBound (renameTypes ρ _) emptyBound)
        (renameTypes ρ _) .boolTy at cp
      rw [cSem_tm_normalize ρ ((CChecks.abs hA hp hx).renameTypes ρ) _ rfl
        (CChecks.abs cA cp (hx.renameTypes ρ)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hA.renameTypes ρ) _ rfl cA env]
        exact ihA ρ env
      rw [semA]
      funext bound expected
      let carrier := cSem hA (env.rename ρ)
      have semP := cSem_tm_normalize ρ (hp.renameTypes ρ) _ (by
        rw [renameBoundCtx_extend, renameBoundCtx_empty]) cp env
      have predEq : (fun value =>
          (cSem cp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down) =
          (fun value => (cSem hp (env.rename ρ)
            (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down) := by
        funext value
        let predicateBound := extendCBoundEnv carrier value emptyCBoundEnv
        have cleanToRenamed := congrFun (congrFun semP.symm predicateBound) cBool
        have renamedToOriginal := congrFun (congrFun (ihp ρ env) predicateBound) cBool
        exact congrArg ULift.down (cleanToRenamed.trans renamedToOriginal)
      rw [predEq]
      have xEq := congrFun (congrFun (ihx ρ env) bound) carrier
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      exact congrArg (cGuardedAbs carrier _) (congrArg ULift.down xEq)
  | rep hA hp hx ihA ihp ihx =>
      simp only [CRenameEq]
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      have cp := hp.renameTypes ρ
      rw [renameBoundCtx_extend, renameBoundCtx_empty] at cp
      change CHasType (extendBound (renameTypes ρ _) emptyBound)
        (renameTypes ρ _) .boolTy at cp
      rw [cSem_tm_normalize ρ ((CChecks.rep hA hp hx).renameTypes ρ) _ rfl
        (CChecks.rep cA cp (hx.renameTypes ρ)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (env.rename ρ) := by
        rw [← cSem_kind_normalize ρ (hA.renameTypes ρ) _ rfl cA env]
        exact ihA ρ env
      rw [semA]
      funext bound expected
      let carrier := cSem hA (env.rename ρ)
      have semP := cSem_tm_normalize ρ (hp.renameTypes ρ) _ (by
        rw [renameBoundCtx_extend, renameBoundCtx_empty]) cp env
      have predEq : (fun value =>
          (cSem cp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down) =
          (fun value => (cSem hp (env.rename ρ)
            (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down) := by
        funext value
        let predicateBound := extendCBoundEnv carrier value emptyCBoundEnv
        have cleanToRenamed := congrFun (congrFun semP.symm predicateBound) cBool
        have renamedToOriginal := congrFun (congrFun (ihp ρ env) predicateBound) cBool
        exact congrArg ULift.down (cleanToRenamed.trans renamedToOriginal)
      rw [predEq]
      let subtype := cGuardedType carrier fun value =>
        (cSem hp (env.rename ρ)
          (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      have xEq := congrFun (congrFun (ihx ρ env) bound) subtype
      apply congrArg ULift.up
      apply congrArg (alignCValue carrier expected)
      exact congrArg (fun value => value.1) (congrArg ULift.down xEq)
  | tyExists hp ih =>
      simp only [CRenameEq]
      have cp := hp.renameTypes (liftTyRen ρ)
      rw [renameBoundCtx_empty] at cp
      change CHasType emptyBound (renameTypes (liftTyRen ρ) _) .boolTy at cp
      rw [cSem_tm_normalize ρ ((CChecks.tyExists hp).renameTypes ρ) _ rfl
        (CChecks.tyExists cp) env]
      simp only [cSem]
      funext bound expected
      apply congrArg ULift.up
      apply congrArg (alignCValue cBool expected)
      have propositions :
          (∃ candidate : CPointed,
            cSem cp (extendCTypeEnv (kind := .star) candidate env)
              emptyCBoundEnv cBool = ⟨true⟩) ↔
          (∃ candidate : CPointed,
            cSem hp (extendCTypeEnv (kind := .star) candidate (env.rename ρ))
              emptyCBoundEnv cBool = ⟨true⟩) := by
        constructor <;> rintro ⟨candidate, witness⟩ <;> refine ⟨candidate, ?_⟩
        · let extEnv := extendCTypeEnv (kind := .star) candidate env
          have semP := cSem_tm_normalize (liftTyRen ρ)
            (hp.renameTypes (liftTyRen ρ)) _ (by rw [renameBoundCtx_empty]) cp extEnv
          have cleanToRenamed := congrFun (congrFun semP.symm emptyCBoundEnv) cBool
          have renamedToOriginal := congrFun
            (congrFun (ih (liftTyRen ρ) extEnv) emptyCBoundEnv) cBool
          have evalEq := cleanToRenamed.trans renamedToOriginal
          rw [CTypeEnv.rename_lift (kind := .star) ρ env candidate] at evalEq
          exact evalEq.symm.trans witness
        · let extEnv := extendCTypeEnv (kind := .star) candidate env
          have semP := cSem_tm_normalize (liftTyRen ρ)
            (hp.renameTypes (liftTyRen ρ)) _ (by rw [renameBoundCtx_empty]) cp extEnv
          have cleanToRenamed := congrFun (congrFun semP.symm emptyCBoundEnv) cBool
          have renamedToOriginal := congrFun
            (congrFun (ih (liftTyRen ρ) extEnv) emptyCBoundEnv) cBool
          have evalEq := cleanToRenamed.trans renamedToOriginal
          rw [CTypeEnv.rename_lift (kind := .star) ρ env candidate] at evalEq
          exact evalEq.trans witness
      exact decide_eq_decide.mpr propositions

/-! ## Semantic type substitution -/

/-- A syntactic type substitution induces the semantic environment obtained
by denoting each of its (well-kinded) entries. -/
noncomputable def CTypeEnv.ofSub
    {source target : List Kind} (σ : TySub ClassicalSig source target)
    (wellFormed : WellFormedTySub σ) (env : CTypeEnv target) : CTypeEnv source :=
  fun _ v => cSem (wellFormed v).certificate env

private theorem cSem_instantiate_kind_normalize
    {source target : List Kind} {kind : Kind}
    {family : Fam ClassicalSig source kind}
    {σ : TySub ClassicalSig source target} (_wellFormed : WellFormedTySub σ)
    (instantiated : CChecks (instantiateBoundCtx σ emptyBound)
      (instantiateTypes σ family) (Classification.instantiate σ .kind))
    (normalized : Fam ClassicalSig target kind)
    (syntaxEq : instantiateTypes σ family = normalized)
    (clean : CKinded normalized) (env : CTypeEnv target) :
    cSem instantiated env = cSem clean env := by
  subst normalized
  change CChecks (instantiateBoundCtx σ emptyBound) (instantiateTypes σ family) .kind
    at instantiated
  have contextEq : instantiateBoundCtx σ
      (emptyBound : BoundCtx ClassicalSig source 0) =
      (emptyBound : BoundCtx ClassicalSig target 0) := instantiateBoundCtx_empty σ
  let Packed := Σ Γ : BoundCtx ClassicalSig target 0,
    CChecks Γ (instantiateTypes σ family) .kind
  let left : Packed := ⟨instantiateBoundCtx σ emptyBound, instantiated⟩
  let right : Packed := ⟨emptyBound, clean⟩
  have packedEq : left = right := by
    apply Sigma.ext contextEq
    dsimp [left, right]
    let transported : CChecks (instantiateBoundCtx σ emptyBound)
        (instantiateTypes σ family) .kind := contextEq.symm ▸ clean
    have htransport : HEq transported clean := by
      dsimp only [transported]
      exact @eqRec_heq (BoundCtx ClassicalSig target 0)
        (fun Γ => CChecks Γ (instantiateTypes σ family) .kind)
        emptyBound (instantiateBoundCtx σ emptyBound) contextEq.symm clean
    exact (heq_of_eq (CChecks.unique instantiated transported)).trans htransport
  exact congrArg (fun packed : Packed => cSem packed.2 env) packedEq

private theorem cSem_instantiate_tm_normalize
    {source target : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig source depth}
    {term : Tm ClassicalSig source depth} {A : Ty ClassicalSig source}
    {σ : TySub ClassicalSig source target} (_wellFormed : WellFormedTySub σ)
    (instantiated : CChecks (instantiateBoundCtx σ Γ) (instantiateTypes σ term)
      (Classification.instantiate σ (.tm A)))
    (targetΓ : BoundCtx ClassicalSig target depth)
    (contextEq : instantiateBoundCtx σ Γ = targetΓ)
    (clean : CChecks targetΓ (instantiateTypes σ term)
      (.tm (instantiateTypes σ A))) (env : CTypeEnv target) :
    cSem instantiated env = cSem clean env := by
  change CChecks (instantiateBoundCtx σ Γ) (instantiateTypes σ term)
    (.tm (instantiateTypes σ A)) at instantiated
  let Packed := Σ Δ : BoundCtx ClassicalSig target depth,
    CChecks Δ (instantiateTypes σ term) (.tm (instantiateTypes σ A))
  let left : Packed := ⟨instantiateBoundCtx σ Γ, instantiated⟩
  let right : Packed := ⟨targetΓ, clean⟩
  have packedEq : left = right := by
    apply Sigma.ext contextEq
    dsimp [left, right]
    let transported : CChecks (instantiateBoundCtx σ Γ) (instantiateTypes σ term)
        (.tm (instantiateTypes σ A)) := contextEq.symm ▸ clean
    have htransport : HEq transported clean := by
      dsimp only [transported]
      exact @eqRec_heq (BoundCtx ClassicalSig target depth)
        (fun Δ => CChecks Δ (instantiateTypes σ term) (.tm (instantiateTypes σ A)))
        targetΓ (instantiateBoundCtx σ Γ) contextEq.symm clean
    exact (heq_of_eq (CChecks.unique instantiated transported)).trans htransport
  exact congrArg (fun packed : Packed => cSem packed.2 env) packedEq

def CInstantiateEq {source target : List Kind} {sort : HolSort} {depth : Nat}
    (classification : Classification ClassicalSig source sort)
    (σ : TySub ClassicalSig source target)
    (left : CResult (depth := depth) (classification.instantiate σ))
    (right : CResult (depth := depth) classification) : Prop :=
  match classification with
  | .kind => left = right
  | .tm _ => left = right

theorem CTypeEnv.ofSub_lift
    {source target : List Kind} {domain : Kind}
    {σ : TySub ClassicalSig source target} (wellFormed : WellFormedTySub σ)
    (env : CTypeEnv target) (argument : CDenoteKind domain) :
    CTypeEnv.ofSub (liftTySub (kind := domain) σ) wellFormed.lift
        (extendCTypeEnv argument env) =
      extendCTypeEnv argument (CTypeEnv.ofSub σ wellFormed env) := by
  funext resultKind v
  cases v with
  | zero =>
      simp only [CTypeEnv.ofSub, extendCTypeEnv]
      rw [show (wellFormed.lift (.zero)).certificate =
          (CChecks.tyBv (.zero : TyVar (domain :: target) domain)) by
        apply CChecks.unique]
      rfl
  | succ v =>
      simp only [CTypeEnv.ofSub, extendCTypeEnv]
      let rhoWeak : TyRen target (domain :: target) := fun v => .succ v
      have renamed := (wellFormed v).certificate.renameTypes rhoWeak
      have clean : CKinded (weakenTypes (kind := domain) (σ v)) := by
        rw [show weakenTypes (kind := domain) (σ v) =
          renameTypes rhoWeak (σ v) by rfl]
        rw [renameBoundCtx_empty] at renamed
        change CKinded _ at renamed
        exact renamed
      rw [cSem_certificate_coherent (wellFormed.lift (.succ v)).certificate clean]
      change cSem clean (extendCTypeEnv argument env) = cSem (wellFormed v).certificate env
      have semanticRename := cSem_renameTypes (wellFormed v).certificate rhoWeak
        (extendCTypeEnv argument env)
      change cSem ((wellFormed v).certificate.renameTypes rhoWeak)
          (extendCTypeEnv argument env) = _ at semanticRename
      rw [cSem_kind_normalize rhoWeak
        ((wellFormed v).certificate.renameTypes rhoWeak)
        (weakenTypes (kind := domain) (σ v)) rfl clean
        (extendCTypeEnv argument env)] at semanticRename
      change cSem clean (extendCTypeEnv argument env) =
        cSem (wellFormed v).certificate
          ((extendCTypeEnv argument env).rename rhoWeak) at semanticRename
      have envEq : (extendCTypeEnv argument env).rename rhoWeak = env := by
        funext resultKind w
        rfl
      rw [envEq] at semanticRename
      exact semanticRename

/-- Type substitution is interpreted by composition with the semantic
environment induced by the substitution. -/
theorem cSem_instantiateTypes
    {source target : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx ClassicalSig source depth}
    {expression : Expr ClassicalSig source sort depth}
    {classification : Classification ClassicalSig source sort}
    (checking : CChecks Γ expression classification)
    {σ : TySub ClassicalSig source target} (wellFormed : WellFormedTySub σ)
    (env : CTypeEnv target) :
    CInstantiateEq classification σ (cSem (checking.instantiateTypes wellFormed) env)
      (cSem checking (CTypeEnv.ofSub σ wellFormed env)) := by
  induction checking generalizing target with
  | boolTy =>
      simp only [CInstantiateEq]
      rw [cSem_instantiate_kind_normalize wellFormed
        (CChecks.boolTy.instantiateTypes wellFormed) .boolTy rfl
        (CChecks.boolTy (types := target)) env]
      rfl
  | arr hA hB ihA ihB =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      have cB := hB.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      rw [cSem_instantiate_kind_normalize wellFormed
        ((CChecks.arr hA hB).instantiateTypes wellFormed)
        (.arr (instantiateTypes σ _) (instantiateTypes σ _)) rfl
        (CChecks.arr cA cB) env]
      simp only [cSem_arr_eq]
      have semA : cSem cA env = cSem hA (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hA.instantiateTypes wellFormed) _ rfl cA env]
        exact ihA wellFormed env
      have semB : cSem cB env = cSem hB (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hB.instantiateTypes wellFormed) _ rfl cB env]
        exact ihB wellFormed env
      rw [semA, semB]
  | tyApp hF hA ihF ihA =>
      simp only [CInstantiateEq]
      have cF := hF.instantiateTypes wellFormed
      have cA := hA.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cF cA
      change CKinded _ at cF cA
      rw [cSem_instantiate_kind_normalize wellFormed
        ((CChecks.tyApp hF hA).instantiateTypes wellFormed)
        (.tyApp (instantiateTypes σ _) (instantiateTypes σ _)) rfl
        (CChecks.tyApp cF cA) env]
      simp only [cSem_tyApp_eq]
      have semF : cSem cF env = cSem hF (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hF.instantiateTypes wellFormed) _ rfl cF env]
        exact ihF wellFormed env
      have semA : cSem cA env = cSem hA (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hA.instantiateTypes wellFormed) _ rfl cA env]
        exact ihA wellFormed env
      rw [semF, semA]
  | tyLam body ih =>
      simp only [CInstantiateEq]
      have cb := body.instantiateTypes wellFormed.lift
      rw [instantiateBoundCtx_empty] at cb
      change CKinded _ at cb
      rw [cSem_instantiate_kind_normalize wellFormed
        ((CChecks.tyLam body).instantiateTypes wellFormed)
        (.tyLam (instantiateTypes (liftTySub σ) _)) rfl
        (CChecks.tyLam cb) env]
      funext argument
      change cSem cb (extendCTypeEnv argument env) =
        cSem body (extendCTypeEnv argument (CTypeEnv.ofSub σ wellFormed env))
      have semBody : cSem cb (extendCTypeEnv argument env) =
          cSem body (CTypeEnv.ofSub (liftTySub σ) wellFormed.lift
            (extendCTypeEnv argument env)) := by
        rw [← cSem_instantiate_kind_normalize wellFormed.lift
          (body.instantiateTypes wellFormed.lift) _ rfl cb
          (extendCTypeEnv argument env)]
        exact ih wellFormed.lift (extendCTypeEnv argument env)
      rw [semBody, CTypeEnv.ofSub_lift]
  | tyBv v =>
      simp only [CInstantiateEq]
      let clean := (wellFormed v).certificate
      rw [cSem_instantiate_kind_normalize wellFormed
        ((CChecks.tyBv v).instantiateTypes wellFormed) (σ v) rfl clean env]
      change cSem clean env = cSem (wellFormed v).certificate env
      rw [cSem_certificate_coherent clean (wellFormed v).certificate]
  | sub hA hp ihA ihp =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA
      change CKinded _ at cA
      have cp := hp.instantiateTypes wellFormed
      rw [instantiateBoundCtx_extend, instantiateBoundCtx_empty] at cp
      change CHasType (extendBound (instantiateTypes σ _) emptyBound)
        (instantiateTypes σ _) .boolTy at cp
      rw [cSem_instantiate_kind_normalize wellFormed
        ((CChecks.sub hA hp).instantiateTypes wellFormed)
        (.sub (instantiateTypes σ _) (instantiateTypes σ _)) rfl
        (CChecks.sub cA cp) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hA.instantiateTypes wellFormed) _ rfl cA env]
        exact ihA wellFormed env
      rw [semA]
      congr 1
      funext value
      have semP := cSem_instantiate_tm_normalize wellFormed
        (hp.instantiateTypes wellFormed) _ (by
          rw [instantiateBoundCtx_extend, instantiateBoundCtx_empty]) cp env
      let bound := extendCBoundEnv (cSem hA (CTypeEnv.ofSub σ wellFormed env))
        value emptyCBoundEnv
      have cleanToInstantiated := congrFun (congrFun semP.symm bound) cBool
      have instantiatedToOriginal := congrFun
        (congrFun (ihp wellFormed env) bound) cBool
      exact congrArg ULift.down (cleanToInstantiated.trans instantiatedToOriginal)
  | model hp ih =>
      simp only [CInstantiateEq]
      have cp := hp.instantiateTypes wellFormed.lift
      rw [instantiateBoundCtx_empty] at cp
      change CHasType emptyBound (instantiateTypes (liftTySub σ) _) .boolTy at cp
      rw [cSem_instantiate_kind_normalize wellFormed
        ((CChecks.model hp).instantiateTypes wellFormed)
        (.model (instantiateTypes (liftTySub σ) _)) rfl (CChecks.model cp) env]
      simp only [cSem]
      apply congrArg chooseCModel
      funext candidate
      let extEnv := extendCTypeEnv (kind := .star) candidate env
      have semP := cSem_instantiate_tm_normalize wellFormed.lift
        (hp.instantiateTypes wellFormed.lift) _ (by rw [instantiateBoundCtx_empty]) cp extEnv
      have cleanToInstantiated := congrFun (congrFun semP.symm emptyCBoundEnv) cBool
      have instantiatedToOriginal := congrFun
        (congrFun (ih wellFormed.lift extEnv) emptyCBoundEnv) cBool
      have evalEq := cleanToInstantiated.trans instantiatedToOriginal
      rw [CTypeEnv.ofSub_lift (domain := .star) wellFormed env candidate] at evalEq
      exact congrArg (fun result => result = ⟨true⟩) evalEq
  | primFam symbol => exact nomatch symbol
  | primTm rule => exact nomatch rule
  | bv hA lookup ihA =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.bv hA lookup).instantiateTypes wellFormed) _ rfl
        (CChecks.bv cA (congrArg (instantiateTypes σ) lookup)) env]
      rfl
  | fv name hA ihA =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.fv name hA).instantiateTypes wellFormed) _ rfl
        (CChecks.fv name cA) env]
      rfl
  | app hA hB hf hx ihA ihB ihf ihx =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      have cB := hB.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.app hA hB hf hx).instantiateTypes wellFormed) _ rfl
        (CChecks.app cA cB (hf.instantiateTypes wellFormed)
          (hx.instantiateTypes wellFormed)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hA.instantiateTypes wellFormed) _ rfl cA env]
        exact ihA wellFormed env
      have semB : cSem cB env = cSem hB (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hB.instantiateTypes wellFormed) _ rfl cB env]
        exact ihB wellFormed env
      rw [semA, semB]
      funext bound expected
      let domain := cSem hA (CTypeEnv.ofSub σ wellFormed env)
      let codomain := cSem hB (CTypeEnv.ofSub σ wellFormed env)
      let functionType : CPointed :=
        ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
      have fEq := congrFun (congrFun (ihf wellFormed env) bound) functionType
      have xEq := congrFun (congrFun (ihx wellFormed env) bound) domain
      dsimp [functionType, domain, codomain] at fEq xEq
      rw [fEq, xEq]
  | lam body hA hB hb ihA ihB ihb =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      have cB := hB.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      have cb := hb.instantiateTypes wellFormed
      rw [instantiateBoundCtx_extend] at cb
      change CHasType (extendBound (instantiateTypes σ _)
        (instantiateBoundCtx σ _)) (instantiateTypes σ _)
        (instantiateTypes σ _) at cb
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.lam body hA hB hb).instantiateTypes wellFormed) _ rfl
        (CChecks.lam _ cA cB cb) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hA.instantiateTypes wellFormed) _ rfl cA env]
        exact ihA wellFormed env
      have semB : cSem cB env = cSem hB (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hB.instantiateTypes wellFormed) _ rfl cB env]
        exact ihB wellFormed env
      rw [semA, semB]
      funext bound expected
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      funext argument
      let carrier := cSem hA (CTypeEnv.ofSub σ wellFormed env)
      let targetBound := extendCBoundEnv carrier argument bound
      have semBody := cSem_instantiate_tm_normalize wellFormed
        (hb.instantiateTypes wellFormed) _ (by rw [instantiateBoundCtx_extend]) cb env
      have cleanToInstantiated := congrFun (congrFun semBody.symm targetBound)
        (cSem hB (CTypeEnv.ofSub σ wellFormed env))
      have instantiatedToOriginal := congrFun
        (congrFun (ihb wellFormed env) targetBound)
        (cSem hB (CTypeEnv.ofSub σ wellFormed env))
      exact congrArg ULift.down (cleanToInstantiated.trans instantiatedToOriginal)
  | bool value =>
      simp only [CInstantiateEq]
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.bool value).instantiateTypes wellFormed) _ rfl
        (CChecks.bool value) env]
      rfl
  | eq hA hx hy ihA ihx ihy =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.eq hA hx hy).instantiateTypes wellFormed) _ rfl
        (CChecks.eq cA (hx.instantiateTypes wellFormed)
          (hy.instantiateTypes wellFormed)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hA.instantiateTypes wellFormed) _ rfl cA env]
        exact ihA wellFormed env
      rw [semA]
      funext bound expected
      have xEq := congrFun (congrFun (ihx wellFormed env) bound)
        (cSem hA (CTypeEnv.ofSub σ wellFormed env))
      have yEq := congrFun (congrFun (ihy wellFormed env) bound)
        (cSem hA (CTypeEnv.ofSub σ wellFormed env))
      have xd := congrArg ULift.down xEq
      have yd := congrArg ULift.down yEq
      apply congrArg ULift.up
      apply congrArg (alignCValue cBool expected)
      apply decide_eq_decide.mpr
      constructor
      · intro equality
        exact xd.symm.trans (equality.trans yd)
      · intro equality
        exact xd.trans (equality.trans yd.symm)
  | eps hA hp ihA ihp =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.eps hA hp).instantiateTypes wellFormed) _ rfl
        (CChecks.eps cA (hp.instantiateTypes wellFormed)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hA.instantiateTypes wellFormed) _ rfl cA env]
        exact ihA wellFormed env
      rw [semA]
      funext bound expected
      let carrier := cSem hA (CTypeEnv.ofSub σ wellFormed env)
      let functionType : CPointed := ⟨carrier.carrier → Bool, fun _ => false⟩
      have pEq := congrFun (congrFun (ihp wellFormed env) bound) functionType
      dsimp [functionType, carrier] at pEq
      rw [pEq]
  | abs hA hp hx ihA ihp ihx =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA
      change CKinded _ at cA
      have cp := hp.instantiateTypes wellFormed
      rw [instantiateBoundCtx_extend, instantiateBoundCtx_empty] at cp
      change CHasType (extendBound (instantiateTypes σ _) emptyBound)
        (instantiateTypes σ _) .boolTy at cp
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.abs hA hp hx).instantiateTypes wellFormed) _ rfl
        (CChecks.abs cA cp (hx.instantiateTypes wellFormed)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hA.instantiateTypes wellFormed) _ rfl cA env]
        exact ihA wellFormed env
      rw [semA]
      funext bound expected
      let carrier := cSem hA (CTypeEnv.ofSub σ wellFormed env)
      have semP := cSem_instantiate_tm_normalize wellFormed
        (hp.instantiateTypes wellFormed) _ (by
          rw [instantiateBoundCtx_extend, instantiateBoundCtx_empty]) cp env
      have predEq : (fun value =>
          (cSem cp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down) =
          (fun value => (cSem hp (CTypeEnv.ofSub σ wellFormed env)
            (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down) := by
        funext value
        let predicateBound := extendCBoundEnv carrier value emptyCBoundEnv
        have cleanToInstantiated := congrFun (congrFun semP.symm predicateBound) cBool
        have instantiatedToOriginal := congrFun
          (congrFun (ihp wellFormed env) predicateBound) cBool
        exact congrArg ULift.down (cleanToInstantiated.trans instantiatedToOriginal)
      rw [predEq]
      have xEq := congrFun (congrFun (ihx wellFormed env) bound) carrier
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      exact congrArg (cGuardedAbs carrier _) (congrArg ULift.down xEq)
  | rep hA hp hx ihA ihp ihx =>
      simp only [CInstantiateEq]
      have cA := hA.instantiateTypes wellFormed
      rw [instantiateBoundCtx_empty] at cA
      change CKinded _ at cA
      have cp := hp.instantiateTypes wellFormed
      rw [instantiateBoundCtx_extend, instantiateBoundCtx_empty] at cp
      change CHasType (extendBound (instantiateTypes σ _) emptyBound)
        (instantiateTypes σ _) .boolTy at cp
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.rep hA hp hx).instantiateTypes wellFormed) _ rfl
        (CChecks.rep cA cp (hx.instantiateTypes wellFormed)) env]
      simp only [cSem]
      have semA : cSem cA env = cSem hA (CTypeEnv.ofSub σ wellFormed env) := by
        rw [← cSem_instantiate_kind_normalize wellFormed
          (hA.instantiateTypes wellFormed) _ rfl cA env]
        exact ihA wellFormed env
      rw [semA]
      funext bound expected
      let carrier := cSem hA (CTypeEnv.ofSub σ wellFormed env)
      have semP := cSem_instantiate_tm_normalize wellFormed
        (hp.instantiateTypes wellFormed) _ (by
          rw [instantiateBoundCtx_extend, instantiateBoundCtx_empty]) cp env
      have predEq : (fun value =>
          (cSem cp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down) =
          (fun value => (cSem hp (CTypeEnv.ofSub σ wellFormed env)
            (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down) := by
        funext value
        let predicateBound := extendCBoundEnv carrier value emptyCBoundEnv
        have cleanToInstantiated := congrFun (congrFun semP.symm predicateBound) cBool
        have instantiatedToOriginal := congrFun
          (congrFun (ihp wellFormed env) predicateBound) cBool
        exact congrArg ULift.down (cleanToInstantiated.trans instantiatedToOriginal)
      rw [predEq]
      let subtype := cGuardedType carrier fun value =>
        (cSem hp (CTypeEnv.ofSub σ wellFormed env)
          (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      have xEq := congrFun (congrFun (ihx wellFormed env) bound) subtype
      apply congrArg ULift.up
      apply congrArg (alignCValue carrier expected)
      exact congrArg (fun value => value.1) (congrArg ULift.down xEq)
  | tyExists hp ih =>
      simp only [CInstantiateEq]
      have cp := hp.instantiateTypes wellFormed.lift
      rw [instantiateBoundCtx_empty] at cp
      change CHasType emptyBound (instantiateTypes (liftTySub σ) _) .boolTy at cp
      rw [cSem_instantiate_tm_normalize wellFormed
        ((CChecks.tyExists hp).instantiateTypes wellFormed) _ rfl
        (CChecks.tyExists cp) env]
      simp only [cSem]
      funext bound expected
      apply congrArg ULift.up
      apply congrArg (alignCValue cBool expected)
      apply decide_eq_decide.mpr
      constructor <;> rintro ⟨candidate, witness⟩ <;> refine ⟨candidate, ?_⟩
      · let extEnv := extendCTypeEnv (kind := .star) candidate env
        have semP := cSem_instantiate_tm_normalize wellFormed.lift
          (hp.instantiateTypes wellFormed.lift) _ (by rw [instantiateBoundCtx_empty]) cp extEnv
        have cleanToInstantiated := congrFun (congrFun semP.symm emptyCBoundEnv) cBool
        have instantiatedToOriginal := congrFun
          (congrFun (ih wellFormed.lift extEnv) emptyCBoundEnv) cBool
        have evalEq := cleanToInstantiated.trans instantiatedToOriginal
        rw [CTypeEnv.ofSub_lift (domain := .star) wellFormed env candidate] at evalEq
        exact evalEq.symm.trans witness
      · let extEnv := extendCTypeEnv (kind := .star) candidate env
        have semP := cSem_instantiate_tm_normalize wellFormed.lift
          (hp.instantiateTypes wellFormed.lift) _ (by rw [instantiateBoundCtx_empty]) cp extEnv
        have cleanToInstantiated := congrFun (congrFun semP.symm emptyCBoundEnv) cBool
        have instantiatedToOriginal := congrFun
          (congrFun (ih wellFormed.lift extEnv) emptyCBoundEnv) cBool
        have evalEq := cleanToInstantiated.trans instantiatedToOriginal
        rw [CTypeEnv.ofSub_lift (domain := .star) wellFormed env candidate] at evalEq
        exact evalEq.trans witness

/-- Opening substitution is well formed whenever its replacement is. -/
theorem wellFormed_headTySub {types : List Kind} {kind : Kind}
    {argument : Fam ClassicalSig types kind} (hargument : Kinded argument) :
    WellFormedTySub (headTySub argument) := by
  intro resultKind v
  cases v with
  | zero => exact hargument
  | succ v => exact .tyBv v

/-- The semantic environment induced by opening is exactly environment
extension by the denotation of the replacement. -/
theorem CTypeEnv.ofSub_head
    {types : List Kind} {kind : Kind}
    {argument : Fam ClassicalSig types kind} (hargument : Kinded argument)
    (env : CTypeEnv types) :
    CTypeEnv.ofSub (headTySub argument) (wellFormed_headTySub hargument) env =
      extendCTypeEnv (denoteChecked hargument env) env := by
  funext resultKind v
  cases v with
  | zero =>
      simp only [CTypeEnv.ofSub, headTySub, extendCTypeEnv, denoteChecked]
  | succ v =>
      simp only [CTypeEnv.ofSub, headTySub, extendCTypeEnv]
      have semantic := cSem_instantiateTypes
        (CChecks.tyBv (.succ v)) (wellFormed_headTySub hargument) env
      change cSem ((CChecks.tyBv (.succ v)).instantiateTypes
          (wellFormed_headTySub hargument)) env =
        cSem (CChecks.tyBv (.succ v))
          (CTypeEnv.ofSub (headTySub argument) (wellFormed_headTySub hargument) env)
        at semantic
      rw [cSem_instantiate_kind_normalize (wellFormed_headTySub hargument)
        ((CChecks.tyBv (.succ v)).instantiateTypes (wellFormed_headTySub hargument))
        (.tyBv v) rfl (CChecks.tyBv v) env] at semantic
      exact semantic.symm

/-! ## Soundness of family definitional equality -/

theorem FamEq.sound {types : List Kind} {kind : Kind}
    {A B : Fam ClassicalSig types kind} (equality : FamEq ClassicalSig A B)
    (hA : Kinded A) (hB : Kinded B) (env : CTypeEnv types) :
    denoteChecked hA env = denoteChecked hB env := by
  induction equality with
  | refl =>
      congr 1
  | symm equality ih =>
      exact (ih hB hA env).symm
  | trans left hMiddle right ihLeft ihRight =>
      exact (ihLeft hA hMiddle env).trans (ihRight hMiddle hB env)
  | arr left right ihLeft ihRight =>
      let wholeA := hA.certificate
      let wholeB := hB.certificate
      cases hA with
      | arr hA₁ hA₂ =>
        cases hB with
        | arr hB₁ hB₂ =>
          unfold denoteChecked
          rw [cSem_certificate_coherent wholeA
            (CChecks.arr hA₁.certificate hA₂.certificate)]
          rw [cSem_certificate_coherent wholeB
            (CChecks.arr hB₁.certificate hB₂.certificate)]
          simp only [cSem_arr_eq]
          have leftSem := ihLeft hA₁ hB₁ env
          have rightSem := ihRight hA₂ hB₂ env
          unfold denoteChecked at leftSem rightSem
          rw [leftSem, rightSem]
  | app left right ihLeft ihRight =>
      let wholeA := hA.certificate
      let wholeB := hB.certificate
      cases hA with
      | tyApp hF hArg =>
        cases hB with
        | tyApp hF' hArg' =>
          unfold denoteChecked
          rw [cSem_certificate_coherent wholeA
            (CChecks.tyApp hF.certificate hArg.certificate)]
          rw [cSem_certificate_coherent wholeB
            (CChecks.tyApp hF'.certificate hArg'.certificate)]
          simp only [cSem_tyApp_eq]
          have functionSem := ihLeft hF hF' env
          have argumentSem := ihRight hArg hArg' env
          unfold denoteChecked at functionSem argumentSem
          rw [functionSem, argumentSem]
  | lam equality ih =>
      let wholeA := hA.certificate
      let wholeB := hB.certificate
      cases hA with
      | tyLam hbody =>
        cases hB with
        | tyLam hbody' =>
          unfold denoteChecked
          rw [cSem_certificate_coherent wholeA
            (CChecks.tyLam hbody.certificate)]
          rw [cSem_certificate_coherent wholeB
            (CChecks.tyLam hbody'.certificate)]
          funext argument
          exact ih hbody hbody' (extendCTypeEnv argument env)
  | sub carrierEq predicateEq =>
      subst carrierEq
      subst predicateEq
      unfold denoteChecked
      exact cSem_certificate_coherent hA.certificate hB.certificate env
  | model predicateEq =>
      subst predicateEq
      unfold denoteChecked
      exact cSem_certificate_coherent hA.certificate hB.certificate env
  | beta body argument hbody hargument =>
      let bodyCheck := hbody.certificate
      let argumentCheck := hargument.certificate
      let wellFormed : WellFormedTySub (headTySub argument) :=
        wellFormed_headTySub hargument
      have openedKinded : Kinded (openType body argument) := by
        change Kinded (HolE.instantiateTypes (headTySub argument) body)
        simpa only [instantiateBoundCtx_empty, Classification.instantiate] using
          hbody.instantiateTypes wellFormed
      unfold denoteChecked
      rw [cSem_certificate_coherent hA.certificate
        (CChecks.tyApp (CChecks.tyLam bodyCheck) argumentCheck)]
      rw [cSem_certificate_coherent hB.certificate openedKinded.certificate]
      change cSem bodyCheck (extendCTypeEnv (cSem argumentCheck env) env) =
        cSem openedKinded.certificate env
      have openedSem := cSem_instantiateTypes bodyCheck wellFormed env
      change cSem (bodyCheck.instantiateTypes wellFormed) env =
        cSem bodyCheck (CTypeEnv.ofSub (headTySub argument) wellFormed env) at openedSem
      rw [CTypeEnv.ofSub_head hargument env] at openedSem
      have normalizeOpened := cSem_instantiate_kind_normalize wellFormed
        (bodyCheck.instantiateTypes wellFormed) (openType body argument) rfl
        openedKinded.certificate env
      rw [normalizeOpened] at openedSem
      rw [cSem_certificate_coherent argumentCheck hargument.certificate]
      exact openedSem.symm
  | rename equality originalA originalB rho ih =>
      unfold denoteChecked
      have semA := cSem_renameTypes originalA.certificate rho env
      have semB := cSem_renameTypes originalB.certificate rho env
      change cSem (originalA.certificate.renameTypes rho) env =
        cSem originalA.certificate (env.rename rho) at semA
      change cSem (originalB.certificate.renameTypes rho) env =
        cSem originalB.certificate (env.rename rho) at semB
      rw [cSem_kind_normalize rho (originalA.certificate.renameTypes rho)
        (HolE.renameTypes rho _) rfl hA.certificate env] at semA
      rw [cSem_kind_normalize rho (originalB.certificate.renameTypes rho)
        (HolE.renameTypes rho _) rfl hB.certificate env] at semB
      exact semA.trans ((ih originalA originalB (env.rename rho)).trans semB.symm)
  | instantiate equality originalA originalB sigma wellFormed ih =>
      unfold denoteChecked
      have semA := cSem_instantiateTypes originalA.certificate wellFormed env
      have semB := cSem_instantiateTypes originalB.certificate wellFormed env
      change cSem (originalA.certificate.instantiateTypes wellFormed) env =
        cSem originalA.certificate (CTypeEnv.ofSub sigma wellFormed env) at semA
      change cSem (originalB.certificate.instantiateTypes wellFormed) env =
        cSem originalB.certificate (CTypeEnv.ofSub sigma wellFormed env) at semB
      rw [cSem_instantiate_kind_normalize wellFormed
        (originalA.certificate.instantiateTypes wellFormed)
        (HolE.instantiateTypes sigma _) rfl hA.certificate env] at semA
      rw [cSem_instantiate_kind_normalize wellFormed
        (originalB.certificate.instantiateTypes wellFormed)
        (HolE.instantiateTypes sigma _) rfl hB.certificate env] at semB
      exact semA.trans
        ((ih originalA originalB (CTypeEnv.ofSub sigma wellFormed env)).trans semB.symm)
  | signature certificate => exact nomatch certificate

end Nucleus.HolE
