import Nucleus.HolE.Named.Dense.Representation
import Mathlib.Logic.Equiv.Defs

/-! # Postorder encodings modulo decoding -/

namespace Nucleus.HolE.Named.Unsorted.Dense.Encoder

universe u
set_option relaxedAutoImplicit true

theorem postorderQuotient_bijective :
    Function.Bijective (@postorderQuotient Sig Name) := by
  constructor
  · intro left right equality
    have equivalent := Quotient.exact equality
    change ValidRootEncoding.Equivalent (postorderValid left) (postorderValid right)
      at equivalent
    change unpostorder (postorder left) = unpostorder (postorder right) at equivalent
    simpa using equivalent
  · intro quotient
    refine Quotient.inductionOn quotient ?_
    intro encoding
    obtain ⟨tree, equivalent⟩ := postorder_surjective_upToEquivalent encoding
    exact ⟨tree, Quotient.sound equivalent⟩

/-- Named HolE trees are canonically equivalent to valid finite postorder
root encodings modulo decoding equivalence. -/
noncomputable def postorderEquivQuotient :
    HolE Sig Name ≃ PostorderQuotient Sig Name :=
  Equiv.ofBijective postorderQuotient postorderQuotient_bijective

end Nucleus.HolE.Named.Unsorted.Dense.Encoder
