import Nucleus.HolE.Named.Dense.Representation
import Mathlib.Logic.Equiv.Defs

/-! # Postorder as a canonical representative of finite rooted DAGs -/

namespace Nucleus.HolE.Named.Unsorted.Dense.Encoder

universe u
set_option relaxedAutoImplicit true

theorem postorderQuotient_bijective :
    Function.Bijective (@postorderQuotient Sig Name) := by
  constructor
  · intro left right equality
    have equivalent := Quotient.exact equality
    change DAGRootEncoding.Equivalent (postorderDAG left) (postorderDAG right)
      at equivalent
    change (postorder left).decodeTree = (postorder right).decodeTree at equivalent
    simpa using equivalent
  · intro quotient
    refine Quotient.inductionOn quotient ?_
    intro encoding
    obtain ⟨tree, equivalent⟩ := postorder_surjective_upToEquivalent encoding
    exact ⟨tree, Quotient.sound equivalent⟩

/-- Named HolE trees are canonically equivalent to finite-depth rooted dense
DAGs modulo decoding equivalence.  Postorder merely chooses a canonical
representative of each equivalence class. -/
noncomputable def postorderEquivDAGQuotient :
    HolE Sig Name ≃ DAGQuotient Sig Name :=
  Equiv.ofBijective postorderQuotient postorderQuotient_bijective

end Nucleus.HolE.Named.Unsorted.Dense.Encoder
