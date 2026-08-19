import Nucleus.Finset.Nat
import Mathlib.Data.Fintype.EquivFin

/-!
# Fresh names

`FreshName` isolates the single operation needed by named syntax: choosing an
element outside a finite support.  The fallback instance is noncomputable and
works for every infinite type.
-/

namespace Nucleus

class FreshName (Name : Type) [DecidableEq Name] where
  fresh : Finset Name → Name
  fresh_not_mem (support : Finset Name) : fresh support ∉ support

namespace FreshName

variable {Name : Type}

def next [DecidableEq Name] [FreshName Name] (support : Finset Name) : Name :=
  FreshName.fresh support

@[simp] theorem next_not_mem [DecidableEq Name] [FreshName Name]
    (support : Finset Name) : next support ∉ support :=
  FreshName.fresh_not_mem support

instance : FreshName Nat where
  fresh := Finset.freshNat
  fresh_not_mem := Finset.freshNat_not_mem

noncomputable instance (priority := low) [DecidableEq Name] [Infinite Name] :
    FreshName Name where
  fresh support := Classical.choose (Infinite.exists_notMem_finset support)
  fresh_not_mem support := Classical.choose_spec (Infinite.exists_notMem_finset support)

end FreshName

end Nucleus
