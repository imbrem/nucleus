import Nucleus.Hol.Universe
import Nucleus.HolOmega.Kernel

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

end Nucleus.Hol
