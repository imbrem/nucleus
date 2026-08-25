import Nucleus.HolE.ClassicalKernelSoundness
import Nucleus.HolE.ClassicalTermTransport

/-! # Bound-environment transport equations

These cast-free equations are the environment half of semantic weakening and
opening.  Certificate transport is kept downstream of typing-coherence: a
dependent cast introduced while renaming a proof-relevant `CChecks`
certificate must first be erased by that coherence theorem.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

private theorem CChecks.eraseForBound : CChecks Γ expression classification →
    Checks Γ expression classification
  | .boolTy => .boolTy
  | .arr hA hB => .arr hA.eraseForBound hB.eraseForBound
  | .tyApp hF hA => .tyApp hF.eraseForBound hA.eraseForBound
  | .tyLam body => .tyLam body.eraseForBound
  | .tyBv v => .tyBv v
  | .sub hA hp => .sub hA.eraseForBound hp.eraseForBound
  | .model hp => .model hp.eraseForBound
  | .primFam symbol => nomatch symbol
  | .primTm rule => nomatch rule
  | .bv hA lookup => .bv hA.eraseForBound lookup
  | .fv name hA => .fv name hA.eraseForBound
  | .app _ _ hf hx => .app hf.eraseForBound hx.eraseForBound
  | .lam body hA _ hb => .lam body hA.eraseForBound hb.eraseForBound
  | .bool literal => .bool literal
  | .eq hA hx hy => .eq hA.eraseForBound hx.eraseForBound hy.eraseForBound
  | .eps hA hp => .eps hA.eraseForBound hp.eraseForBound
  | .abs hA hp hx => .abs hA.eraseForBound hp.eraseForBound hx.eraseForBound
  | .rep hA hp hx => .rep hA.eraseForBound hp.eraseForBound hx.eraseForBound
  | .tyExists hp => .tyExists hp.eraseForBound

  | .tyForall hp => .tyForall hp.eraseForBound

theorem cSem_term_normalize
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types}
    (checking : CChecks Γ term (.tm A)) (normalized : Tm ClassicalSig types depth)
    (syntaxEq : term = normalized) (clean : CChecks Γ normalized (.tm A))
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed) :
    cSem checking env bound expected = cSem clean env bound expected := by
  subst normalized
  rw [checking.unique clean]

/-- Pulling an extended environment back along successor forgets its head. -/
@[simp] theorem CBoundEnv.rename_succ_extend (semantic : CPointed)
    (value : semantic.carrier) (bound : CBoundEnv depth) :
    (extendCBoundEnv semantic value bound).rename Fin.succ = bound := by
  funext i expected
  exact extendCBoundEnv_succ semantic value bound i expected

/-- Weakening below a binder commutes with extending the semantic environment. -/
@[simp] theorem CBoundEnv.rename_lift_extend (rho : Fin m → Fin n)
    (semantic : CPointed) (value : semantic.carrier) (bound : CBoundEnv n) :
    (extendCBoundEnv semantic value bound).rename (liftRen rho) =
      extendCBoundEnv semantic value (bound.rename rho) :=
  CBoundEnv.rename_lift rho bound semantic value

/-- Two successive weakenings forget two successive semantic binders. -/
@[simp] theorem CBoundEnv.rename_succ_succ_extend_extend
    (outer inner : CPointed) (outerValue : outer.carrier)
    (innerValue : inner.carrier) (bound : CBoundEnv depth) :
    (extendCBoundEnv inner innerValue
      (extendCBoundEnv outer outerValue bound)).rename
        (fun i => Fin.succ (Fin.succ i)) = bound := by
  rw [← CBoundEnv.rename_comp]
  simp

private def CChecks.renameForBound
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {term : Tm ClassicalSig types m} {A : Ty ClassicalSig types}
    (source : CChecks Γ term (.tm A)) (rho : Fin m → Fin n)
    (contexts : ∀ i, Δ (rho i) = Γ i) :
    CChecks Δ (rename rho term) (.tm A) :=
  match source with
  | .primTm rule => nomatch rule
  | .bv hA lookup => by
      simpa [rename] using CChecks.bv hA ((contexts _).trans lookup)
  | .fv name hA => by simpa [rename] using CChecks.fv (Γ := Δ) name hA
  | .app hA hB hf hx => by simpa [rename] using (CChecks.app hA hB
      (hf.renameForBound rho contexts) (hx.renameForBound rho contexts))
  | .lam body hA hB hb => by simpa [rename] using (CChecks.lam _ hA hB
      (hb.renameForBound (liftRen rho) fun i => Fin.cases rfl (fun j => contexts j) i))
  | .bool literal => by simpa [rename] using CChecks.bool (Γ := Δ) literal
  | .eq hA hx hy => by simpa [rename] using (CChecks.eq hA
      (hx.renameForBound rho contexts) (hy.renameForBound rho contexts))
  | .eps hA hp => by simpa [rename] using (CChecks.eps hA (hp.renameForBound rho contexts))
  | .abs hA hp hx => by simpa [rename] using (CChecks.abs hA hp (hx.renameForBound rho contexts))
  | .rep hA hp hx => by simpa [rename] using (CChecks.rep hA hp (hx.renameForBound rho contexts))
  -- The predicate lives in the same bound context, weakened by one type
  -- variable, so the renaming recurses into it unchanged.
  | .tyExists hp => by simpa [rename] using (CChecks.tyExists (Γ := Δ)
      (hp.renameForBound (Δ := weakenBoundCtx Δ) rho
        (fun i => congrArg weakenTypes (contexts i))))
  | .tyForall hp => by simpa [rename] using (CChecks.tyForall (Γ := Δ)
      (hp.renameForBound (Δ := weakenBoundCtx Δ) rho
        (fun i => congrArg weakenTypes (contexts i))))
termination_by sizeOf source

private theorem CChecks.cSem_renameForBound
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {term : Tm ClassicalSig types m} {A : Ty ClassicalSig types}
    (source : CChecks Γ term (.tm A)) (rho : Fin m → Fin n)
    (contexts : ∀ i, Δ (rho i) = Γ i)
    (env : CTypeEnv types) (bound : CBoundEnv n) (expected : CPointed) :
    cSem (source.renameForBound rho contexts) env bound expected =
      cSem source env (bound.rename rho) expected :=
  match source with
  | .primTm rule => nomatch rule
  | .bv hA lookup => by
      rw [cSem_term_normalize ((CChecks.bv hA lookup).renameForBound rho contexts) (.bv (rho _)) (by simp)
        (.bv hA ((contexts _).trans lookup))]
      rfl
  | .fv name hA => by
      rw [cSem_term_normalize ((CChecks.fv name hA).renameForBound rho contexts) (.fv name _) (by simp [rename]) (.fv name hA)]
      rfl
  | .bool literal => by
      rw [cSem_term_normalize ((CChecks.bool literal).renameForBound rho contexts) (.bool literal) (by simp [rename]) (.bool literal)]
      rfl
  -- A type binder does not touch the bound environment: `CBoundEnv` is indexed
  -- only by term depth.  So the renaming commutes with the quantifier by
  -- pointwise appeal to the induction hypothesis under every candidate type.
  | .tyExists hp => by
      rw [cSem_term_normalize ((CChecks.tyExists hp).renameForBound rho contexts)
        (.tyExists (rename rho _)) (by simp [rename])
        (.tyExists (hp.renameForBound (Δ := weakenBoundCtx Δ) rho
          (fun i => congrArg weakenTypes (contexts i))))]
      simp only [cSem]
      have bodies := fun candidate : CPointed =>
        hp.cSem_renameForBound (Δ := weakenBoundCtx Δ) rho
          (fun i => congrArg weakenTypes (contexts i))
          (extendCTypeEnv candidate env) bound cBool
      exact congrArg ULift.up (congrArg (alignCValue cBool expected)
        (decide_eq_decide.mpr (exists_congr (fun candidate => by rw [bodies candidate]))))
  | .tyForall hp => by
      rw [cSem_term_normalize ((CChecks.tyForall hp).renameForBound rho contexts)
        (.tyForall (rename rho _)) (by simp [rename])
        (.tyForall (hp.renameForBound (Δ := weakenBoundCtx Δ) rho
          (fun i => congrArg weakenTypes (contexts i))))]
      simp only [cSem]
      have bodies := fun candidate : CPointed =>
        hp.cSem_renameForBound (Δ := weakenBoundCtx Δ) rho
          (fun i => congrArg weakenTypes (contexts i))
          (extendCTypeEnv candidate env) bound cBool
      exact congrArg ULift.up (congrArg (alignCValue cBool expected)
        (decide_eq_decide.mpr (forall_congr' (fun candidate => by rw [bodies candidate]))))
  | .app hA hB hf hx => by
      rw [cSem_term_normalize ((CChecks.app hA hB hf hx).renameForBound rho contexts)
        (.app (rename rho _) (rename rho _)) (by simp [rename])
        (.app hA hB (hf.renameForBound rho contexts) (hx.renameForBound rho contexts))]
      simp only [cSem]
      rw [hf.cSem_renameForBound rho contexts env bound
            ⟨(cSem hA env).carrier → (cSem hB env).carrier,
              fun _ => (cSem hB env).point⟩,
          hx.cSem_renameForBound rho contexts env bound (cSem hA env)]
  | .lam body hA hB hb => by
      rw [cSem_term_normalize ((CChecks.lam body hA hB hb).renameForBound rho contexts)
        (.lam _ (rename (liftRen rho) body)) (by simp [rename])
        (.lam _ hA hB (hb.renameForBound (liftRen rho)
          (fun i => Fin.cases rfl (fun j => contexts j) i)))]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      funext value
      have semantic := hb.cSem_renameForBound (Δ := extendBound _ Δ) (liftRen rho) (by
          intro i
          exact Fin.cases rfl (fun j => contexts j) i) env
        (extendCBoundEnv (cSem hA env) value bound) (cSem hB env)
      have envEq := CBoundEnv.rename_lift rho bound (cSem hA env) value
      rw [envEq] at semantic
      exact congrArg ULift.down semantic
  | .eq hA hx hy => by
      rw [cSem_term_normalize ((CChecks.eq hA hx hy).renameForBound rho contexts)
        (.eq _ (rename rho _) (rename rho _)) (by simp [rename])
        (.eq hA (hx.renameForBound rho contexts) (hy.renameForBound rho contexts))]
      simp only [cSem]
      rw [hx.cSem_renameForBound rho contexts env bound (cSem hA env),
        hy.cSem_renameForBound rho contexts env bound (cSem hA env)]
  | .eps hA hp => by
      rw [cSem_term_normalize ((CChecks.eps hA hp).renameForBound rho contexts)
        (.eps _ (rename rho _)) (by simp [rename])
        (.eps hA (hp.renameForBound rho contexts))]
      simp only [cSem]
      rw [hp.cSem_renameForBound rho contexts env bound
        ⟨(cSem hA env).carrier → Bool, fun _ => false⟩]
  | .abs hA hp hx => by
      rw [cSem_term_normalize ((CChecks.abs hA hp hx).renameForBound rho contexts)
        (.abs _ _ (rename rho _)) (by simp [rename])
        (.abs hA hp (hx.renameForBound rho contexts))]
      simp only [cSem]
      rw [hx.cSem_renameForBound rho contexts env bound (cSem hA env)]
  | .rep hA hp hx => by
      rw [cSem_term_normalize ((CChecks.rep hA hp hx).renameForBound rho contexts)
        (.rep _ _ (rename rho _)) (by simp [rename])
        (.rep hA hp (hx.renameForBound rho contexts))]
      simp only [cSem]
      rw [hx.cSem_renameForBound rho contexts env bound
        (cGuardedType (cSem hA env) (fun value =>
          (cSem hp env (extendCBoundEnv (cSem hA env) value emptyCBoundEnv) cBool).down))]
termination_by sizeOf source

theorem cSem_rename_raw
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {term : Tm ClassicalSig types m} {A : Ty ClassicalSig types}
    (source : CChecks Γ term (.tm A)) (rho : Fin m → Fin n)
    (contexts : ∀ i, Δ (rho i) = Γ i)
    (target : CChecks Δ (rename rho term) (.tm A))
    (env : CTypeEnv types) (bound : CBoundEnv n) (expected : CPointed) :
    cSem target env bound expected = cSem source env (bound.rename rho) expected := by
  rw [target.unique (source.renameForBound rho contexts)]
  exact source.cSem_renameForBound rho contexts env bound expected

/-- Definitional typing certificates evaluate compatibly with weakening. -/
theorem cDefSem_weaken
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A B : Ty ClassicalSig types}
    (source : CDefChecks Γ term A)
    (target : CDefChecks (extendBound B Γ) (weaken term) A)
    (env : CTypeEnv types) (bound : CBoundEnv (depth + 1)) (expected : CPointed) :
    cDefSem target env bound expected =
      cDefSem source env (bound.rename Fin.succ) expected := by
  rw [source.rawView_semantics, target.rawView_semantics]
  cases hs : source.rawView with
  | mk sourceType sourceRaw =>
    cases ht : target.rawView with
    | mk targetType targetRaw =>
      simp only [CDefRawView.sem]
      let renamed : CChecks (extendBound B Γ) (weaken term) (.tm sourceType) :=
        ((sourceRaw.toChecks.renameTm Fin.succ (fun _ => rfl)).certificate)
      have typeEq : targetType = sourceType := targetRaw.type_unique renamed
      cases typeEq
      exact cSem_rename_raw sourceRaw Fin.succ (fun _ => rfl) targetRaw
        env bound expected

theorem CRealizes.weaken
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A B : Ty ClassicalSig types} {env : CTypeEnv types}
    {bound : CBoundEnv depth} {expected : CPointed} {value : expected.carrier}
    (semantic : CPointed) (head : semantic.carrier)
    (typing : HasTypeDefEq Γ term A)
    (realizes : CRealizes (Γ := Γ) env bound term A expected value) :
    CRealizes (Γ := extendBound B Γ) env
      (extendCBoundEnv semantic head bound)
      (weaken term) A expected value := by
  obtain ⟨source, sourceValue⟩ := realizes
  let target := typing.weaken (B := B) |>.certificate
  refine ⟨target, ?_⟩
  rw [cDefSem_weaken source target]
  simpa using sourceValue

theorem CRealizes.of_weaken
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A B : Ty ClassicalSig types} {env : CTypeEnv types}
    {bound : CBoundEnv depth} {expected : CPointed} {value : expected.carrier}
    (semantic : CPointed) (head : semantic.carrier)
    (typing : HasTypeDefEq Γ term A)
    (realizes : CRealizes (Γ := extendBound B Γ) env
      (extendCBoundEnv semantic head bound) (HolE.weaken term) A expected value) :
    CRealizes (Γ := Γ) env bound term A expected value := by
  obtain ⟨target, targetValue⟩ := realizes
  let source := typing.certificate
  refine ⟨source, ?_⟩
  have transported := cDefSem_weaken source target env
    (extendCBoundEnv semantic head bound) expected
  rw [CBoundEnv.rename_succ_extend] at transported
  exact transported.symm.trans targetValue

theorem CRealizes.of_weakenAt
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A B : Ty ClassicalSig types} {env : CTypeEnv types}
    {bound : CBoundEnv (depth + 1)} {expected : CPointed}
    {value : expected.carrier}
    (typing : HasTypeDefEq Γ term A)
    (realizes : CRealizes (Γ := extendBound B Γ) env bound
      (HolE.weaken term) A expected value) :
    CRealizes (Γ := Γ) env (bound.rename Fin.succ) term A expected value := by
  obtain ⟨target, targetValue⟩ := realizes
  let source := typing.certificate
  exact ⟨source, (cDefSem_weaken source target env bound expected).symm.trans targetValue⟩

end Nucleus.HolE
