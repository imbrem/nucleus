import Nucleus.Hol.Universe
import Nucleus.Hol.Kernel
import Nucleus.HolOmega.Kernel
import Nucleus.HolOmega.Model

/-! The forgetful map exhibiting ordinary HOL as the universe fragment of HOL-omega. -/

universe u

namespace Nucleus.Hol

set_option warn.classDefReducibility false

/-- Forget ranks and closure under ranked products/sums.  Thus every HOL-omega
universe is, definitionally, a model of the ordinary HOL universe interface. -/
def Universe.ofOmega (U : HolOmega.Kernel.Universe) : Hol.Universe where
  Code := U.Code
  El := U.El
  inhabited := U.inhabited
  boolCode := U.boolCode
  boolEquiv := U.boolEquiv
  arr := U.arr
  arrEquiv := U.arrEquiv
  subCode := U.subCode
  subEquiv := U.subEquiv

/-- Concrete consistency of the ordinary HOL kernel in the beth-tower model. -/
theorem beth_consistent :
    ¬ Kernel.Derives (Universe.ofOmega HolOmega.Beth.model)
      ([] : List (Kernel.Tm (Universe.ofOmega HolOmega.Beth.model) []
        (Kernel.Ty.bool (Universe.ofOmega HolOmega.Beth.model))))
      (Kernel.Tm.bool (Universe.ofOmega HolOmega.Beth.model) false) := by
  intro h
  have hs := Kernel.Derives.sound (U := Universe.ofOmega HolOmega.Beth.model) h
  have bad := hs PUnit.unit (by simp)
  simp [Kernel.Tm.bool] at bad

end Nucleus.Hol
