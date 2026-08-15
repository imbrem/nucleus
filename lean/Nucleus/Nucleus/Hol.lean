import Nucleus.Hol.Traits
import Nucleus.Hol.Tag
import Nucleus.Hol.Nat
import Nucleus.Hol.Soundness
import Nucleus.Hol.Intrinsic
import Nucleus.Hol.FamilySub
import Nucleus.Hol.FamilySub.Substitution
import Nucleus.Hol.FamilySub.Kernel
import Nucleus.Hol.FamilySub.Intrinsic
import Nucleus.Hol.FamilySub.BoolLogic
import Nucleus.Hol.FamilySub.Product
import Nucleus.Hol.FamilySub.ProductLaws
import Nucleus.Hol.FamilySub.Coproduct
import Nucleus.Hol.FamilySub.CoproductLaws
import Nucleus.Hol.FamilySub.Algebraic
import Nucleus.Hol.FamilySub.Basic
import Nucleus.Hol.FamilySub.Finite
import Nucleus.Hol.FamilySub.Quantifiers
import Nucleus.Hol.FamilySub.Infinity
import Nucleus.Hol.FamilySub.Natural
import Nucleus.Hol.FamilySub.Recursion
import Nucleus.Hol.FamilySub.Peano
import Nucleus.Hol.FamilySub.Json
import Nucleus.Hol.GuardedSubtype

/-!
# Signature-parametric HOL

The empty signature is `Hol.Finite`; `Hol.NatSig` adds the natural-number
extension.  `Hol.Traits` exposes their common syntax, typing, intrinsic, and
proof-system interfaces.
-/
