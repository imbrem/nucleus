import Nucleus.SExpr.Cell
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List

/-!
# Pointer representations of binary S-expressions

The primary format is a one-indexed node table. Pointer zero is `nil`; every
positive pointer addresses an atom or cons cell. Fuel bounds unfolding even
for cyclic or dangling tables. A backward table is the useful acyclic normal
form: each cons cell only references earlier entries.
-/

namespace Nucleus

universe u

namespace SExpr2

/-- One entry in a one-indexed S-expression heap. -/
inductive HeapNode (Atom : Type u) where
  | atom (value : Atom)
  | cons (car cdr : Nat)
  deriving DecidableEq, Repr

/-- A finite one-indexed heap and a pointer to its root. Pointer zero is nil. -/
structure Heap (Atom : Type u) where
  nodes : List (HeapNode Atom)
  root : Nat
  deriving DecidableEq, Repr

private def HeapNode.countableCode : HeapNode α → α ⊕ Nat × Nat
  | .atom value => .inl value
  | .cons car cdr => .inr (car, cdr)

private theorem HeapNode.countableCode_injective :
    Function.Injective (@HeapNode.countableCode α) := by
  intro left right h
  cases left <;> cases right <;> simp_all [HeapNode.countableCode]

instance [Countable α] : Countable (HeapNode α) :=
  HeapNode.countableCode_injective.countable

private def Heap.countableCode (heap : Heap α) : List (HeapNode α) × Nat :=
  (heap.nodes, heap.root)

private theorem Heap.countableCode_injective :
    Function.Injective (@Heap.countableCode α) := by
  intro left right h
  cases left
  cases right
  simp_all [Heap.countableCode]

instance [Countable α] : Countable (Heap α) :=
  Heap.countableCode_injective.countable

namespace Heap

variable {Atom : Type u}

/-- Dereference a positive one-indexed pointer. -/
def get? (heap : Heap Atom) (pointer : Nat) : Option (HeapNode Atom) :=
  if pointer = 0 then none else heap.nodes[pointer - 1]?

/-- Unfold at most `gas` addressed nodes. Zero itself needs no gas. -/
def deref (heap : Heap Atom) : Nat → Nat → Option (SExpr2 Atom)
  | _, 0 => some .nil
  | 0, _ + 1 => none
  | gas + 1, pointer =>
      match heap.get? pointer with
      | some (.atom value) => some (.atom value)
      | some (.cons car cdr) => .cons <$> heap.deref gas car <*> heap.deref gas cdr
      | none => none

/-- Decode the selected root with a caller-supplied depth bound. -/
def decode (heap : Heap Atom) (gas : Nat) : Option (SExpr2 Atom) :=
  heap.deref gas heap.root

@[simp] theorem deref_nil (heap : Heap Atom) (gas : Nat) :
    heap.deref gas 0 = some .nil := by cases gas <;> rfl

/-- Every pointer appearing in a node at index `i` is strictly earlier than
`i`. This syntactic invariant implies both validity and acyclicity. -/
def Backward (heap : Heap Atom) : Prop :=
  heap.root ≤ heap.nodes.length ∧
    ∀ (i : Nat) (node : HeapNode Atom), heap.nodes[i]? = some node →
      match node with
      | .atom _ => True
      | .cons car cdr => car ≤ i ∧ cdr ≤ i

noncomputable instance (heap : Heap Atom) : Decidable heap.Backward :=
  Classical.propDecidable _

private theorem deref_backward (heap : Heap Atom) (h : heap.Backward) :
    ∀ gas pointer, gas ≤ heap.nodes.length → pointer ≤ gas →
      ∃ value, heap.deref gas pointer = some value := by
  intro gas
  induction gas with
  | zero =>
      intro pointer _ hp
      have : pointer = 0 := by omega
      subst pointer
      exact ⟨.nil, rfl⟩
  | succ gas ih =>
      intro pointer hgas hp
      cases pointer with
      | zero => exact ⟨.nil, rfl⟩
      | succ i =>
          have hi : i < heap.nodes.length := by omega
          let node := heap.nodes[i]
          have hnode : heap.nodes[i]? = some node := by simp [node, hi]
          have hget : heap.get? (i + 1) = some node := by simp [get?, hnode]
          cases hn : node with
          | atom value =>
              exact ⟨.atom value, by simp [deref, hget, hn]⟩
          | cons car cdr =>
              have hc := h.2 i (.cons car cdr) (by simpa [hn] using hnode)
              obtain ⟨carValue, hcar⟩ := ih car (by omega) (by omega)
              obtain ⟨cdrValue, hcdr⟩ := ih cdr (by omega) (by omega)
              exact ⟨.cons carValue cdrValue, by
                simp [deref, hget, hn, hcar, hcdr]⟩

/-- Gas equal to table length always suffices for a backward (hence acyclic)
heap. -/
theorem decode_length_isSome (heap : Heap Atom) (h : heap.Backward) :
    (heap.decode heap.nodes.length).isSome := by
  obtain ⟨value, hv⟩ := deref_backward heap h heap.nodes.length heap.root
    (by rfl) h.1
  simp [decode, hv]

/-- Postorder serialization of a finite S-expression. The returned pointer is
zero for nil and otherwise points at the newly appended final node. -/
def appendSExpr : List (HeapNode Atom) → SExpr2 Atom → List (HeapNode Atom) × Nat
  | nodes, .nil => (nodes, 0)
  | nodes, .atom value => (nodes ++ [.atom value], nodes.length + 1)
  | nodes, .cons car cdr =>
      let (nodes, carPointer) := appendSExpr nodes car
      let (nodes, cdrPointer) := appendSExpr nodes cdr
      (nodes ++ [.cons carPointer cdrPointer], nodes.length + 1)

/-- Every finite `SExpr2` has a backward one-indexed heap representation. -/
def ofSExpr2 (value : SExpr2 Atom) : Heap Atom :=
  let (nodes, root) := appendSExpr [] value
  ⟨nodes, root⟩

private theorem appendSExpr_length (nodes : List (HeapNode Atom)) (value : SExpr2 Atom) :
    nodes.length ≤ (appendSExpr nodes value).1.length := by
  induction value generalizing nodes with
  | nil => rfl
  | atom => simp [appendSExpr]
  | cons car cdr ihCar ihCdr =>
      have h₁ := ihCar nodes
      have h₂ := ihCdr (appendSExpr nodes car).1
      simp only [appendSExpr, List.length_append, List.length_singleton]
      omega

private theorem appendSExpr_root (nodes : List (HeapNode Atom)) (value : SExpr2 Atom) :
    (appendSExpr nodes value).2 ≤ (appendSExpr nodes value).1.length := by
  cases value <;> simp [appendSExpr]

theorem ofSExpr2_root_valid (value : SExpr2 Atom) :
    (ofSExpr2 value).root ≤ (ofSExpr2 value).nodes.length := by
  exact appendSExpr_root [] value

end Heap
end SExpr2
end Nucleus
