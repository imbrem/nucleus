import Nucleus.HolE.ClassicalSubtypeKernelLaws
import Nucleus.HolE.ClassicalBoundTransport

/-! # Semantic opening for a single bound variable -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Proof-relevant, syntax-directed typing of every member of a term
substitution. -/
abbrev CWellTypedSub {types : List Kind} {m n : Nat}
    (Γ : BoundCtx ClassicalSig types m) (Δ : BoundCtx ClassicalSig types n)
    (σ : Fin m → Tm ClassicalSig types n) : Type 1 :=
  ∀ i, CChecks Δ (σ i) (.tm (Γ i))

/-- The semantic bound environment induced by a checked substitution. -/
noncomputable def CWellTypedSub.bound {types : List Kind} {m n : Nat}
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {σ : Fin m → Tm ClassicalSig types n} (checked : CWellTypedSub Γ Δ σ)
    (env : CTypeEnv types) (bound : CBoundEnv n) : CBoundEnv m :=
  fun i expected => (cSem (checked i) env bound expected).down

/-- Construct the syntax-directed certificate for term substitution. -/
noncomputable def CChecks.instantiateTmC {types : List Kind} {m n : Nat}
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {term : Tm ClassicalSig types m} {A : Ty ClassicalSig types}
    (typing : CChecks Γ term (.tm A)) (σ : Fin m → Tm ClassicalSig types n)
    (checked : CWellTypedSub Γ Δ σ) :
    CChecks Δ (instantiate σ term) (.tm A) :=
  match typing with
  | .primTm rule => nomatch rule
  | .bv (index := index) hA lookup => by
      have result := checked index
      rw [lookup] at result
      simpa [instantiate] using result
  | .fv name hA => by simpa [instantiate] using (.fv (Γ := Δ) name hA)
  | .app hA hB hf hx => by simpa [instantiate] using (.app hA hB
      (CChecks.instantiateTmC hf σ checked)
      (CChecks.instantiateTmC hx σ checked))
  | .lam body hA hB hb => by simpa [instantiate] using (.lam _ hA hB
      (CChecks.instantiateTmC hb (liftSub σ) fun i =>
        Fin.cases (.bv hA rfl) (fun j =>
          ((checked j).toChecks.renameTm Fin.succ (fun _ => rfl)).certificate) i))
  | .bool literal => by simpa [instantiate] using (.bool (Γ := Δ) literal)
  | .tyExists hp => by simpa [instantiate] using (.tyExists (Γ := Δ) hp)
  | .eq hA hx hy => by simpa [instantiate] using (.eq hA
      (CChecks.instantiateTmC hx σ checked)
      (CChecks.instantiateTmC hy σ checked))
  | .eps hA hp => by simpa [instantiate] using
      (.eps hA (CChecks.instantiateTmC hp σ checked))
  | .abs hA hp hx => by simpa [instantiate] using
      (.abs hA hp (CChecks.instantiateTmC hx σ checked))
  | .rep hA hp hx => by simpa [instantiate] using
      (.rep hA hp (CChecks.instantiateTmC hx σ checked))
termination_by sizeOf typing

private noncomputable def CWellTypedSub.lift
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {σ : Fin m → Tm ClassicalSig types n} {A : Ty ClassicalSig types}
    (hA : CKinded A) (checked : CWellTypedSub Γ Δ σ) :
    CWellTypedSub (extendBound A Γ) (extendBound A Δ) (liftSub σ) :=
  fun i => Fin.cases (.bv hA rfl) (fun j =>
    ((checked j).toChecks.renameTm Fin.succ (fun _ => rfl)).certificate) i

theorem CWellTypedSub.bound_lift
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {σ : Fin m → Tm ClassicalSig types n} {A : Ty ClassicalSig types}
    (hA : CKinded A) (checked : CWellTypedSub Γ Δ σ)
    (env : CTypeEnv types) (bound : CBoundEnv n)
    (value : (cSem hA env).carrier) :
    (CWellTypedSub.lift hA checked).bound env
        (extendCBoundEnv (cSem hA env) value bound) =
      extendCBoundEnv (cSem hA env) value (checked.bound env bound) := by
  funext i expected
  refine Fin.cases ?_ (fun j => ?_) i
  · unfold CWellTypedSub.bound
    rw [cSem_term_normalize
      ((CWellTypedSub.lift hA checked) 0) (.bv 0) rfl (.bv hA rfl)]
    simp only [cSem]
    exact (extendCBoundEnv_zero (cSem hA env) value bound expected).trans
      (extendCBoundEnv_zero (cSem hA env) value
        (fun i expected => (cSem (checked i) env bound expected).down) expected).symm
  · let weakened : CChecks (extendBound A Δ) (weaken (σ j)) (.tm (Γ j)) :=
      ((checked j).toChecks.renameTm Fin.succ (fun _ => rfl)).certificate
    change (cSem weakened env
      (extendCBoundEnv (cSem hA env) value bound) expected).down =
      (cSem (checked j) env bound expected).down
    have semantic := cSem_rename_raw (checked j) Fin.succ (fun _ => rfl)
      weakened env (extendCBoundEnv (cSem hA env) value bound) expected
    rw [CBoundEnv.rename_succ_extend (cSem hA env) value bound] at semantic
    have semantic' : cSem weakened env
        (extendCBoundEnv (cSem hA env) value bound) expected =
        cSem (checked j) env bound expected := semantic
    exact congrArg ULift.down semantic'

/-- Evaluation of a checked simultaneous substitution is evaluation in the
semantic environment induced by its replacement terms. -/
theorem CChecks.cSem_instantiateTmC
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {term : Tm ClassicalSig types m} {A : Ty ClassicalSig types}
    (source : CChecks Γ term (.tm A)) (σ : Fin m → Tm ClassicalSig types n)
    (checked : CWellTypedSub Γ Δ σ)
    (env : CTypeEnv types) (bound : CBoundEnv n) (expected : CPointed) :
    cSem (source.instantiateTmC σ checked) env bound expected =
      cSem source env (checked.bound env bound) expected :=
  match source with
  | .primTm rule => nomatch rule
  | .bv (index := index) hA lookup => by
      cases lookup
      let replacement := checked index
      rw [cSem_term_normalize ((CChecks.bv hA rfl).instantiateTmC σ checked)
        (σ index) (by simp) replacement]
      unfold CWellTypedSub.bound
      rfl
  | .fv name hA => by
      rw [cSem_term_normalize ((CChecks.fv name hA).instantiateTmC σ checked)
        (.fv name _) (by simp [instantiate]) (.fv name hA)]
      rfl
  | .bool literal => by
      rw [cSem_term_normalize ((CChecks.bool literal).instantiateTmC σ checked)
        (.bool literal) (by simp [instantiate]) (.bool literal)]
      rfl
  | .tyExists hp => by
      rw [cSem_term_normalize ((CChecks.tyExists hp).instantiateTmC σ checked)
        (.tyExists _) (by simp [instantiate]) (.tyExists hp)]
      rfl
  | .app hA hB hf hx => by
      let cf := CChecks.instantiateTmC hf σ checked
      let cx := CChecks.instantiateTmC hx σ checked
      rw [cSem_term_normalize ((CChecks.app hA hB hf hx).instantiateTmC σ checked)
        (.app (instantiate σ _) (instantiate σ _))
        (by simp [instantiate]) (.app hA hB cf cx)]
      simp only [cSem]
      dsimp [cf, cx]
      rw [hf.cSem_instantiateTmC σ checked env bound
          ⟨(cSem hA env).carrier → (cSem hB env).carrier,
            fun _ => (cSem hB env).point⟩,
        hx.cSem_instantiateTmC σ checked env bound (cSem hA env)]
  | .lam body hA hB hb => by
      let lifted := CWellTypedSub.lift hA checked
      let cb := CChecks.instantiateTmC hb (liftSub σ) lifted
      rw [cSem_term_normalize ((CChecks.lam body hA hB hb).instantiateTmC σ checked)
        (.lam _ (instantiate (liftSub σ) body))
        (by simp [instantiate]) (.lam _ hA hB cb)]
      simp only [cSem]
      apply congrArg ULift.up
      apply congrArg (alignCValue _ expected)
      funext value
      have bodySem := hb.cSem_instantiateTmC (liftSub σ) lifted env
        (extendCBoundEnv (cSem hA env) value bound) (cSem hB env)
      rw [CWellTypedSub.bound_lift] at bodySem
      exact congrArg ULift.down bodySem
  | .eq hA hx hy => by
      let cx := CChecks.instantiateTmC hx σ checked
      let cy := CChecks.instantiateTmC hy σ checked
      rw [cSem_term_normalize ((CChecks.eq hA hx hy).instantiateTmC σ checked)
        (.eq _ (instantiate σ _) (instantiate σ _))
        (by simp [instantiate]) (.eq hA cx cy)]
      simp only [cSem]
      dsimp [cx, cy]
      rw [hx.cSem_instantiateTmC σ checked env bound (cSem hA env),
        hy.cSem_instantiateTmC σ checked env bound (cSem hA env)]
  | .eps hA hp => by
      let cp := CChecks.instantiateTmC hp σ checked
      rw [cSem_term_normalize ((CChecks.eps hA hp).instantiateTmC σ checked)
        (.eps _ (instantiate σ _))
        (by simp [instantiate]) (.eps hA cp)]
      simp only [cSem]
      dsimp [cp]
      rw [hp.cSem_instantiateTmC σ checked env bound
        ⟨(cSem hA env).carrier → Bool, fun _ => false⟩]
  | .abs hA hp hx => by
      let cx := CChecks.instantiateTmC hx σ checked
      rw [cSem_term_normalize ((CChecks.abs hA hp hx).instantiateTmC σ checked)
        (.abs _ _ (instantiate σ _))
        (by simp [instantiate]) (.abs hA hp cx)]
      simp only [cSem]
      dsimp [cx]
      rw [hx.cSem_instantiateTmC σ checked env bound (cSem hA env)]
  | .rep hA hp hx => by
      let cx := CChecks.instantiateTmC hx σ checked
      rw [cSem_term_normalize ((CChecks.rep hA hp hx).instantiateTmC σ checked)
        (.rep _ _ (instantiate σ _))
        (by simp [instantiate]) (.rep hA hp cx)]
      simp only [cSem]
      dsimp [cx]
      rw [hx.cSem_instantiateTmC σ checked env bound
        (cGuardedType (cSem hA env) (fun value =>
          (cSem hp env (extendCBoundEnv (cSem hA env) value emptyCBoundEnv)
            cBool).down))]
termination_by sizeOf source

theorem cSem_instantiate_raw
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {term : Tm ClassicalSig types m} {A : Ty ClassicalSig types}
    (source : CChecks Γ term (.tm A)) (σ : Fin m → Tm ClassicalSig types n)
    (checked : CWellTypedSub Γ Δ σ)
    (target : CChecks Δ (instantiate σ term) (.tm A))
    (env : CTypeEnv types) (bound : CBoundEnv n) (expected : CPointed) :
    cSem target env bound expected =
      cSem source env (checked.bound env bound) expected := by
  rw [target.unique (source.instantiateTmC σ checked)]
  exact source.cSem_instantiateTmC σ checked env bound expected

/-- Erasure of a proof-relevant definitional typing certificate. -/
theorem CDefChecks.toHasTypeDefEq : CDefChecks Γ term A → HasTypeDefEq Γ term A
  | .exact raw => .exact raw.toChecks
  | .app raw f x => .app raw.toChecks f.toHasTypeDefEq x.toHasTypeDefEq
  | .lam body raw hA bodyTyping =>
      .lam body raw.toChecks hA.toChecks bodyTyping.toHasTypeDefEq
  | .eq raw hA x y =>
      .eq raw.toChecks hA.toChecks x.toHasTypeDefEq y.toHasTypeDefEq
  | .eps raw hA p => .eps raw.toChecks hA.toChecks p.toHasTypeDefEq
  | .abs raw hA hp x =>
      .abs raw.toChecks hA.toChecks hp.toChecks x.toHasTypeDefEq
  | .rep raw hA hp x =>
      .rep raw.toChecks hA.toChecks hp.toChecks x.toHasTypeDefEq
  | .tyExists raw p => .tyExists raw.toChecks p.toHasTypeDefEq
  | .conv source hB equality =>
      .conv source.toHasTypeDefEq hB.toChecks equality

/-- The raw root type of a definitional certificate is definitionally equal
to its advertised type. -/
noncomputable def CDefChecks.rawTypeEq (checking : CDefChecks Γ term A) :
    FamEq ClassicalSig checking.rawView.type A :=
  match checking with
  | .exact _ | .app .. | .lam .. | .eq .. | .eps .. | .abs .. | .rep .. |
      .tyExists .. => .refl
  | .conv source _ equality =>
      .trans source.rawTypeEq source.typeKinded.toChecks equality

/-- Any two definitional typings of one term have definitionally equal result
types.  This is uniqueness of raw typing, closed under explicit conversion. -/
noncomputable def CDefChecks.typeEq (left : CDefChecks Γ term A)
    (right : CDefChecks Γ term B) : FamEq ClassicalSig A B := by
  have rawEqual := left.rawView.raw.type_unique right.rawView.raw
  have rightEq : FamEq ClassicalSig left.rawView.type B := by
    simpa only [rawEqual] using right.rawTypeEq
  exact .trans (.symm left.rawTypeEq) left.rawView.raw.typeKinded.toChecks
    rightEq

abbrev CDefWellTypedSub {types : List Kind} {m n : Nat}
    (Γ : BoundCtx ClassicalSig types m) (Δ : BoundCtx ClassicalSig types n)
    (σ : Fin m → Tm ClassicalSig types n) : Type 1 :=
  ∀ i, CDefChecks Δ (σ i) (Γ i)

noncomputable def CDefWellTypedSub.bound
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {σ : Fin m → Tm ClassicalSig types n} (checked : CDefWellTypedSub Γ Δ σ)
    (env : CTypeEnv types) (bound : CBoundEnv n) : CBoundEnv m :=
  fun i expected => (cDefSem (checked i) env bound expected).down

private noncomputable def CDefWellTypedSub.lift
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {σ : Fin m → Tm ClassicalSig types n} {A : Ty ClassicalSig types}
    (hA : CKinded A) (checked : CDefWellTypedSub Γ Δ σ) :
    CDefWellTypedSub (extendBound A Γ) (extendBound A Δ) (liftSub σ) :=
  fun i => Fin.cases (.exact (.bv hA rfl)) (fun j =>
    ((checked j).toHasTypeDefEq.weaken (B := A)).certificate) i

theorem CDefWellTypedSub.bound_lift
    {Γ : BoundCtx ClassicalSig types m} {Δ : BoundCtx ClassicalSig types n}
    {σ : Fin m → Tm ClassicalSig types n} {A : Ty ClassicalSig types}
    (hA : CKinded A) (checked : CDefWellTypedSub Γ Δ σ)
    (env : CTypeEnv types) (bound : CBoundEnv n)
    (value : (cSem hA env).carrier) :
    (CDefWellTypedSub.lift hA checked).bound env
        (extendCBoundEnv (cSem hA env) value bound) =
      extendCBoundEnv (cSem hA env) value (checked.bound env bound) := by
  funext i expected
  refine Fin.cases ?_ (fun j => ?_) i
  · unfold CDefWellTypedSub.bound
    rw [CDefChecks.coherent ((CDefWellTypedSub.lift hA checked) 0)
      (.exact (.bv hA rfl))]
    simp only [cDefSem, cSem]
    exact (extendCBoundEnv_zero (cSem hA env) value bound expected).trans
      (extendCBoundEnv_zero (cSem hA env) value
        (fun i expected => (cDefSem (checked i) env bound expected).down)
        expected).symm
  · unfold CDefWellTypedSub.bound
    let weakened := ((checked j).toHasTypeDefEq.weaken (B := A)).certificate
    rw [CDefChecks.coherent ((CDefWellTypedSub.lift hA checked) j.succ) weakened]
    have semantic := cDefSem_weaken (checked j) weakened env
      (extendCBoundEnv (cSem hA env) value bound) expected
    rw [CBoundEnv.rename_succ_extend (cSem hA env) value bound] at semantic
    exact congrArg ULift.down semantic

end Nucleus.HolE
