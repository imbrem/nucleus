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

@[simp] theorem cSem_arr_eq {types : List Kind}
    {A B : Ty ClassicalSig types} (hA : CKinded A) (hB : CKinded B)
    (env : CTypeEnv types) :
    cSem (CChecks.arr hA hB) env =
      let domain := cSem hA env
      let codomain := cSem hB env
      (⟨domain.carrier → codomain.carrier,
        fun _ => codomain.point⟩ : CPointed) := rfl

@[simp] theorem cSem_tyApp_eq {types : List Kind} {domain codomain : Kind}
    {F : Fam ClassicalSig types (.arr domain codomain)}
    {A : Fam ClassicalSig types domain} (hF : CKinded F) (hA : CKinded A)
    (env : CTypeEnv types) :
    cSem (CChecks.tyApp hF hA) env = cSem hF env (cSem hA env) := rfl

@[simp] theorem cSem_tyLam_eq {types : List Kind} {domain codomain : Kind}
    {body : Fam ClassicalSig (domain :: types) codomain} (hbody : CKinded body)
    (env : CTypeEnv types) (argument : CDenoteKind domain) :
    cSem (CChecks.tyLam hbody) env argument =
      cSem hbody (extendCTypeEnv argument env) := rfl

@[simp] theorem cEval_eq_eq {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    {left right : Tm ClassicalSig types depth}
    (hA : CKinded A) (hx : CHasType Γ left A) (hy : CHasType Γ right A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed) :
    (cEval env bound (CChecks.eq hA hx hy) expected).down =
      let carrier := cSem hA env
      alignCValue cBool expected
        (@decide ((cSem hx env bound carrier).down =
          (cSem hy env bound carrier).down) (Classical.propDecidable _)) := by
  classical
  rfl

end Nucleus.HolE
