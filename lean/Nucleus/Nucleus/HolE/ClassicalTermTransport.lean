import Nucleus.HolE.ClassicalEquations
import Nucleus.HolE.Substitution

/-! # Bound-variable transport for deterministic HolE semantics -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Pull a polymorphic bound environment back along a renaming. -/
def CBoundEnv.rename (rho : Fin m -> Fin n) (bound : CBoundEnv n) : CBoundEnv m :=
  fun i semantic => bound (rho i) semantic

@[simp] theorem CBoundEnv.rename_apply (rho : Fin m -> Fin n)
    (bound : CBoundEnv n) (i : Fin m) (semantic : CPointed) :
    bound.rename rho i semantic = bound (rho i) semantic := rfl

@[simp] theorem CBoundEnv.rename_lift (rho : Fin m -> Fin n)
    (bound : CBoundEnv n) (semantic : CPointed) (value : semantic.carrier) :
    (extendCBoundEnv semantic value bound).rename (liftRen rho) =
      extendCBoundEnv semantic value (bound.rename rho) := by
  funext i target
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

@[simp] theorem CBoundEnv.rename_id (bound : CBoundEnv n) :
    bound.rename id = bound := by
  funext i semantic
  rfl

@[simp] theorem CBoundEnv.rename_comp (rho : Fin m -> Fin n)
    (tau : Fin n -> Fin k) (bound : CBoundEnv k) :
    (bound.rename tau).rename rho = bound.rename (fun i => tau (rho i)) := by
  funext i semantic
  rfl

@[simp] theorem extendCBoundEnv_zero (semantic : CPointed)
    (value : semantic.carrier) (bound : CBoundEnv depth) (target : CPointed) :
  extendCBoundEnv semantic value bound 0 target =
      alignCValue semantic target value := by
  classical
  by_cases equal : target = semantic
  · subst target
    simp [extendCBoundEnv, alignCValue]
  · have reverse : semantic ≠ target := fun h => equal h.symm
    simp [extendCBoundEnv, alignCValue, equal, reverse]

@[simp] theorem extendCBoundEnv_succ (semantic : CPointed)
    (value : semantic.carrier) (bound : CBoundEnv depth)
    (i : Fin depth) (target : CPointed) :
    extendCBoundEnv semantic value bound i.succ target = bound i target := by
  classical
  simp [extendCBoundEnv]

end Nucleus.HolE
