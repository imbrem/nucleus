import Nucleus.HolOmega.LogicalSoundness
import Nucleus.HolOmega.Model

namespace Nucleus.HolOmega

noncomputable def emptyBaseSemantics : BaseSemantics Empty Beth.model where
  code := fun x => nomatch x
  rank_code := fun x => nomatch x

abbrev falseEquality : Tm Empty :=
  .tmEq .tyBool (.tmBool true) (.tmBool false)

/-- The raw, content-addressable HOL-omega proof calculus cannot prove that
the two Boolean values are equal. -/
theorem raw_consistent : ¬Proves ([] : KindCtx) ([] : TmCtx Empty) [] falseEquality := by
  intro d
  have hs := d.sound emptyBaseSemantics PUnit.unit PUnit.unit (by trivial)
    (by simp) 
  have hden : TmDenotes emptyBaseSemantics PUnit.unit PUnit.unit falseEquality .tyBool
      (Omega.equal (Omega.bool Beth.model true) (Omega.bool Beth.model false) rfl rfl) :=
    .tmEq (.tyBool) (.tmBool) (.tmBool) rfl rfl
  have h := hs _ hden
  simp [Omega.equal, Omega.bool, Omega.cast] at h

/-- Model-independent raw consistency: the empty raw calculus does not prove
Boolean false.  The theorem mentions no model; `Beth.model` is its witness. -/
theorem raw_not_proves_false :
    ¬Proves ([] : KindCtx) ([] : TmCtx Empty) [] (.tmBool false) := by
  intro d
  have hs := d.sound emptyBaseSemantics PUnit.unit PUnit.unit (by trivial) (by simp)
  have hden : TmDenotes emptyBaseSemantics PUnit.unit PUnit.unit (.tmBool false)
      .tyBool (Omega.bool Beth.model false) := .tmBool
  have h := hs _ hden
  simpa [Omega.bool] using congrArg (fun z => Beth.model.boolEquiv z.2) h

end Nucleus.HolOmega
