import Nucleus.HolE.ClassicalSemantics

/-! # Reduction equations for the deterministic HolE semantics -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

@[simp] theorem cEval_bool (literal : Bool) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (expected : CPointed) :
    (cEval env bound (CChecks.bool (Γ := Γ) literal) expected).down =
      alignCValue cBool expected literal := rfl

@[simp] theorem alignCValue_bool (literal : Bool) :
    alignCValue cBool cBool literal = literal := by
  simpa only [cBool] using
    (alignCValue_self (⟨Bool, false⟩ : CPointed) literal)

@[simp] theorem cEval_bool_at_bool (literal : Bool) (env : CTypeEnv types)
    (bound : CBoundEnv depth) :
    (cEval env bound (CChecks.bool (Γ := Γ) literal) cBool).down = literal := by
  rw [cEval_bool, alignCValue_bool]

end Nucleus.HolE
