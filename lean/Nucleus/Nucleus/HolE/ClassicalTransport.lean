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
  exact match checking with
  | .boolTy => by simpa using (CChecks.boolTy (types := target))
  | .arr hA hB => by
      have cA := hA.renameTypes ρ
      have cB := hB.renameTypes ρ
      rw [renameBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.arr cA cB
  | .tyApp hF hA => by
      have cF := hF.renameTypes ρ
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cF cA
      change CKinded _ at cF cA
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.tyApp cF cA
  | .tyLam body => by
      have cb := body.renameTypes (liftTyRen ρ)
      rw [renameBoundCtx_empty] at cb
      change CKinded _ at cb
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.tyLam cb
  | .tyBv v => by simpa using CChecks.tyBv (ρ v)
  | .sub hA hp => by
      have cA := hA.renameTypes ρ
      have cp := hp.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [renameBoundCtx_extend, renameBoundCtx_empty] at cp
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.sub cA cp
  | .model hp => by
      have cp := hp.renameTypes (liftTyRen ρ)
      rw [renameBoundCtx_empty] at cp
      simpa [renameBoundCtx, Classification.rename, HolE.renameTypes] using
        CChecks.model cp
  | .primFam symbol => nomatch symbol
  | .primTm rule => nomatch rule
  | .bv hA lookup => by
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      exact .bv cA (congrArg (HolE.renameTypes ρ) lookup)
  | .fv name hA => by
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      exact .fv name cA
  | .app hA hB hf hx => by
      have cA := hA.renameTypes ρ
      have cB := hB.renameTypes ρ
      rw [renameBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      exact .app cA cB (hf.renameTypes ρ) (hx.renameTypes ρ)
  | .lam body hA hB hb => by
      have cA := hA.renameTypes ρ
      have cB := hB.renameTypes ρ
      rw [renameBoundCtx_empty] at cA cB
      change CKinded _ at cA cB
      have cb := hb.renameTypes ρ
      rw [renameBoundCtx_extend] at cb
      simpa [renameBoundCtx_extend, Classification.rename, HolE.renameTypes] using
        CChecks.lam _ cA cB cb
  | .bool value => .bool value
  | .eq hA hx hy => by
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      exact .eq cA (hx.renameTypes ρ) (hy.renameTypes ρ)
  | .eps hA hp => by
      have cA := hA.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      exact .eps cA (hp.renameTypes ρ)
  | .abs hA hp hx => by
      have cA := hA.renameTypes ρ
      have cp := hp.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [renameBoundCtx_extend, renameBoundCtx_empty] at cp
      exact .abs cA cp (hx.renameTypes ρ)
  | .rep hA hp hx => by
      have cA := hA.renameTypes ρ
      have cp := hp.renameTypes ρ
      rw [renameBoundCtx_empty] at cA
      change CKinded _ at cA
      rw [renameBoundCtx_extend, renameBoundCtx_empty] at cp
      exact .rep cA cp (hx.renameTypes ρ)
  | .tyExists hp => by
      have cp := hp.renameTypes (liftTyRen ρ)
      rw [renameBoundCtx_empty] at cp
      exact .tyExists cp

@[simp] theorem cSem_boolTy (env : CTypeEnv types) :
    cSem (CChecks.boolTy (types := types)) env = cBool := rfl

@[simp] theorem cSem_tyBv (v : TyVar types kind) (env : CTypeEnv types) :
    cSem (@CChecks.tyBv types kind v) env = env kind v := rfl

end Nucleus.HolE
