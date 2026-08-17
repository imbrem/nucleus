import Nucleus.HolE.ClassicalTermTransport

/-! # Bound-environment transport equations

These cast-free equations are the environment half of semantic weakening and
opening.  Certificate transport is kept downstream of typing-coherence: a
dependent cast introduced while renaming a proof-relevant `CChecks`
certificate must first be erased by that coherence theorem.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

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

end Nucleus.HolE
