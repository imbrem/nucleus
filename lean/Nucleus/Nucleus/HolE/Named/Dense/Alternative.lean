import Nucleus.HolE.Named.Dense.Postorder

/-!
# Noncanonical dense encodings

Postorder fixes the relative order of rows, but absolute numbering is still a
choice.  Starting at a nonzero offset gives a concrete encoding distinct from
the zero-based canonical representative while preserving its decoded tree.
This is a small witness that dense encodings are not canonical before taking
the decoding quotient.
-/

namespace Nucleus.HolE.Named.Unsorted.Dense.Encoder

universe u
set_option relaxedAutoImplicit true

/-- Postorder encoding with a caller-selected absolute starting index. -/
def offsetPostorder (offset : Nat) (tree : HolE Sig Name) : RootEncoding Sig Name :=
  run tree offset

@[simp] theorem offsetPostorder_offset (offset : Nat) (tree : HolE Sig Name) :
    (offsetPostorder offset tree).offset = offset := rfl

@[simp] theorem decodeTree_offsetPostorder (offset : Nat) (tree : HolE Sig Name) :
    (offsetPostorder offset tree).decodeTree = some tree :=
  decodeSyntax_run tree offset

/-- Package an offset encoding as a valid finite-depth dense DAG. -/
def offsetPostorderDAG (offset : Nat) (tree : HolE Sig Name) :
    DAGRootEncoding Sig Name :=
  ⟨offsetPostorder offset tree, tree, decodeTree_offsetPostorder offset tree⟩

/-- Every offset choice is decoding-equivalent to canonical zero-based
postorder. -/
theorem offsetPostorderDAG_equivalent (offset : Nat) (tree : HolE Sig Name) :
    DAGRootEncoding.Equivalent (offsetPostorderDAG offset tree) (postorderDAG tree) := by
  simp [DAGRootEncoding.Equivalent, offsetPostorderDAG, postorderDAG]

/-- The quotient class selected by an offset postorder encoding. -/
def offsetPostorderQuotient (offset : Nat) (tree : HolE Sig Name) :
    DAGQuotient Sig Name :=
  Quotient.mk _ (offsetPostorderDAG offset tree)

@[simp] theorem offsetPostorderQuotient_eq_postorder
    (offset : Nat) (tree : HolE Sig Name) :
    offsetPostorderQuotient offset tree = postorderQuotient tree :=
  Quotient.sound (offsetPostorderDAG_equivalent offset tree)

/-- A nonzero offset makes the concrete encoding provably different from the
canonical encoding, even though the preceding theorem identifies them in the
quotient. -/
theorem offsetPostorder_ne_postorder (tree : HolE Sig Name)
    {offset : Nat} (nonzero : offset ≠ 0) :
    offsetPostorder offset tree ≠ postorder tree := by
  intro equality
  have offsets := congrArg EncodingResult.offset equality
  exact nonzero offsets

example (tree : HolE Sig Name) :
    offsetPostorder 1 tree ≠ postorder tree ∧
      offsetPostorderQuotient 1 tree = postorderQuotient tree :=
  ⟨offsetPostorder_ne_postorder tree Nat.one_ne_zero,
    offsetPostorderQuotient_eq_postorder 1 tree⟩

end Nucleus.HolE.Named.Unsorted.Dense.Encoder
