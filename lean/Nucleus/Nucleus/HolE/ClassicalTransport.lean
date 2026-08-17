import Nucleus.HolE.ClassicalSemantics

/-! # Type-variable transport for the classical HolE semantics -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Restrict a semantic type environment along a syntactic renaming. -/
def CTypeEnv.rename (ρ : TyRen source target) (env : CTypeEnv target) :
    CTypeEnv source := fun _ v => env _ (ρ v)

@[simp] theorem CTypeEnv.rename_apply (ρ : TyRen source target)
    (env : CTypeEnv target) (v : TyVar source kind) :
    env.rename ρ kind v = env kind (ρ v) := rfl

@[simp] theorem CTypeEnv.rename_lift (ρ : TyRen source target)
    (env : CTypeEnv target) (value : CDenoteKind kind) :
    (extendCTypeEnv value env).rename (liftTyRen ρ) =
      extendCTypeEnv value (env.rename ρ) := by
  funext resultKind v
  cases v <;> rfl

/-- The proof-relevant checking mirror is stable under type renaming. -/
noncomputable def CChecks.renameTypes {Γ : BoundCtx ClassicalSig source depth}
    {expression : Expr ClassicalSig source sort depth}
    {classification : Classification ClassicalSig source sort}
    (checking : CChecks Γ expression classification) (ρ : TyRen source target) :
    CChecks (renameBoundCtx ρ Γ) (HolE.renameTypes ρ expression)
      (classification.rename ρ) := by
  induction checking generalizing target with
  | boolTy => simpa using (CChecks.boolTy (types := target))
  | arr _ _ ihA ihB =>
      have cA := ihA ρ
      have cB := ihB ρ
      rw [renameBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.arr cA cB
  | tyApp _ _ ihF ihA =>
      have cF := ihF ρ
      have cA := ihA ρ
      rw [renameBoundCtx_empty] at cF cA
      change CKinded _ at cF cA
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.tyApp cF cA
  | tyLam _ ih =>
      have cb := ih (liftTyRen ρ)
      rw [renameBoundCtx_empty] at cb
      change CKinded _ at cb
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.tyLam cb
  | tyBv v => simpa using CChecks.tyBv (ρ v)
  | sub _ _ ihA ihp =>
      have cA := ihA ρ
      have cp := ihp ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [renameBoundCtx_extend, renameBoundCtx_empty] at cp
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.sub cA cp
  | model _ ihp =>
      have cp := ihp (liftTyRen ρ)
      rw [renameBoundCtx_empty] at cp
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.model cp
  | primFam symbol => exact nomatch symbol
  | primTm rule => exact nomatch rule
  | bv hA lookup ihA =>
      have cA := ihA ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      exact .bv cA (congrArg (HolE.renameTypes ρ) lookup)
  | fv name hA ihA =>
      have cA := ihA ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      exact .fv name cA
  | app hA hB hf hx ihA ihB ihf ihx =>
      have cA := ihA ρ
      have cB := ihB ρ
      rw [renameBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      exact .app cA cB (ihf ρ) (ihx ρ)
  | lam body hA hB hb ihA ihB ihb =>
      have cA := ihA ρ
      have cB := ihB ρ
      rw [renameBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      have cb := ihb ρ
      rw [renameBoundCtx_extend] at cb
      simpa [renameBoundCtx_extend, Classification.rename, HolE.renameTypes] using
        CChecks.lam _ cA cB cb
  | bool value => exact .bool value
  | eq hA hx hy ihA ihx ihy =>
      have cA := ihA ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      exact .eq cA (ihx ρ) (ihy ρ)
  | eps hA hp ihA ihp =>
      have cA := ihA ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      exact .eps cA (ihp ρ)
  | abs hA hp hx ihA ihp ihx =>
      have cA := ihA ρ
      have cp := ihp ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [renameBoundCtx_extend, renameBoundCtx_empty] at cp
      exact .abs cA cp (ihx ρ)
  | rep hA hp hx ihA ihp ihx =>
      have cA := ihA ρ
      have cp := ihp ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [renameBoundCtx_extend, renameBoundCtx_empty] at cp
      exact .rep cA cp (ihx ρ)
  | tyExists hp ihp =>
      have cp := ihp (liftTyRen ρ)
      rw [renameBoundCtx_empty] at cp
      exact .tyExists cp

@[simp] theorem cSem_boolTy (env : CTypeEnv types) :
    cSem (CChecks.boolTy (types := types)) env = cBool := rfl

@[simp] theorem cSem_tyBv (v : TyVar types kind) (env : CTypeEnv types) :
    cSem (@CChecks.tyBv types kind v) env = env kind v := rfl

end Nucleus.HolE
