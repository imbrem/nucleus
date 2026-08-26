import Nucleus.HolE.ClassicalKernelSoundness
import Nucleus.HolE.ClassicalFamilySoundness

/-! # Classical semantic law for premise-free type universals -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- A proposition proved with one free type parameter and no hypotheses is
uniform in that parameter, hence proves its type-universal closure. -/
theorem tyForallIntro_sound
    {types : List Kind} {predicate : Tm ClassicalSig (.star :: types) 0}
    (conclusionTyping : HasTypeDefEq
      (emptyBound : BoundCtx ClassicalSig types 0) (.tyForall predicate) .boolTy)
    (_predicateTyping : HasTypeDefEq
      (emptyBound : BoundCtx ClassicalSig (.star :: types) 0) predicate .boolTy)
    (premise : CEntails
      (Γ := (emptyBound : BoundCtx ClassicalSig (.star :: types) 0)) [] predicate) :
    CEntails (Γ := (emptyBound : BoundCtx ClassicalSig types 0)) []
      (.tyForall predicate) := by
  classical
  intro env bound typed valid truths
  have boundEq : bound = emptyCBoundEnv := by
    funext i
    exact Fin.elim0 i
  subst bound
  let conclusionCheck := conclusionTyping.certificate
  refine ⟨conclusionCheck, ?_⟩
  rw [conclusionCheck.rawView_semantics]
  cases hv : conclusionCheck.rawView with
  | mk result raw =>
    cases raw with
    | tyForall hp =>
      simp only [CDefRawView.sem, cSem]
      apply congrArg ULift.up
      rw [alignCValue_bool]
      apply decide_eq_true
      intro candidate
      obtain ⟨predicateCheck, predicateTrue⟩ := premise
        (extendCTypeEnv candidate env) emptyCBoundEnv
        (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
        (by simp [CHypsTrue])
      let closed : CChecks
          (emptyBound : BoundCtx ClassicalSig (.star :: types) 0)
          predicate (.tm .boolTy) := weakenBoundCtx_empty ▸ hp
      have closedTrue :
          cSem closed (extendCTypeEnv candidate env) emptyCBoundEnv cBool = ⟨true⟩ :=
        (predicateCheck.coherent (.exact closed)
          (extendCTypeEnv candidate env) emptyCBoundEnv cBool).symm.trans predicateTrue
      have transported :
          cSem closed (extendCTypeEnv candidate env) emptyCBoundEnv cBool =
            cSem hp (extendCTypeEnv candidate env) emptyCBoundEnv cBool :=
        congrFun (congrFun (cSem_transport_ctx weakenBoundCtx_empty hp)
          (extendCTypeEnv candidate env)) emptyCBoundEnv ▸ rfl
      exact transported.symm.trans closedTrue

end Nucleus.HolE
