import Nucleus.Hol.Ethane.Arena.OneBased
import Nucleus.Hol.Ethane.Standard

/-!
# Standard one-based arena interface

These are the stable row references exported by Rust's ordinary Ethane
initialization arena. The named definitions they designate live in
`Nucleus.Hol.Ethane.Standard`; this file fixes the shared numeric interface.
-/

namespace Nucleus.Hol.Ethane.OneBased.Standard

private def reference (value : UInt64) (nonzero : value ≠ 0 := by decide) : Ref :=
  ⟨value, nonzero⟩

/-- Stable public roots of the ordinary initialization arena. -/
structure Roots where
  star : Ref
  boolTy : Ref
  truth : Ref
  falsehood : Ref
  not : Ref
  and : Ref
  or : Ref
  imp : Ref
  infinity : Ref
  natExists : Ref
  nat : Ref
  zero : Ref
  succ : Ref
  deriving DecidableEq, Repr

def rowCount : Nat := 296

def roots : Roots where
  star := reference 1
  boolTy := reference 2
  truth := reference 4
  falsehood := reference 3
  not := reference 8
  and := reference 27
  or := reference 38
  imp := reference 48
  infinity := reference 89
  natExists := reference 161
  nat := reference 162
  zero := reference 296
  succ := reference 232

/-- Every exported root is a local row of the standard arena. -/
theorem roots_within_bounds :
    roots.star.value.toNat ≤ rowCount ∧
    roots.boolTy.value.toNat ≤ rowCount ∧
    roots.truth.value.toNat ≤ rowCount ∧
    roots.falsehood.value.toNat ≤ rowCount ∧
    roots.not.value.toNat ≤ rowCount ∧
    roots.and.value.toNat ≤ rowCount ∧
    roots.or.value.toNat ≤ rowCount ∧
    roots.imp.value.toNat ≤ rowCount ∧
    roots.infinity.value.toNat ≤ rowCount ∧
    roots.natExists.value.toNat ≤ rowCount ∧
    roots.nat.value.toNat ≤ rowCount ∧
    roots.zero.value.toNat ≤ rowCount ∧
    roots.succ.value.toNat ≤ rowCount := by
  decide

/-- Distinct exported names never alias the same standard row. -/
theorem roots_nodup :
    [roots.star, roots.boolTy, roots.truth, roots.falsehood, roots.not,
      roots.and, roots.or, roots.imp, roots.infinity, roots.natExists,
      roots.nat, roots.zero, roots.succ].Nodup := by
  decide

end Nucleus.Hol.Ethane.OneBased.Standard
