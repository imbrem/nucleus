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

end Nucleus.HolE
