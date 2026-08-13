import Nucleus.SExpr.Coinductive

/-!
# Alternative pointer-table conventions

`Tree2.Table` is zero-indexed because binary trees have no nil pointer.
`SExpr2.SplitHeap` reserves zero for nil, negative indices for atoms, and
positive indices for cons cells. Both translate to the unified one-indexed
heap representation.
-/

namespace Nucleus

universe u

namespace Tree2

/-- A zero-indexed node table for binary trees. -/
abbrev TableNode := SExpr2.HeapNode

structure Table (Atom : Type u) where
  nodes : List (TableNode Atom)
  root : Nat
  deriving DecidableEq, Repr

namespace Table

variable {Atom : Type u}

def deref (table : Table Atom) : Nat → Nat → Option (Tree2 Atom)
  | 0, _ => none
  | gas + 1, pointer =>
      match table.nodes[pointer]? with
      | some (.atom value) => some (.atom value)
      | some (.cons left right) =>
          .cons <$> table.deref gas left <*> table.deref gas right
      | none => none

def decode (table : Table Atom) (gas : Nat) : Option (Tree2 Atom) :=
  table.deref gas table.root

private def shiftNode : TableNode Atom → SExpr2.HeapNode Atom
  | .atom value => .atom value
  | .cons left right => .cons (left + 1) (right + 1)

/-- Change zero-indexed tree pointers into one-indexed non-nil pointers. -/
def toHeap (table : Table Atom) : SExpr2.Heap Atom :=
  ⟨table.nodes.map shiftNode, table.root + 1⟩

private theorem get?_shiftNode (table : Table Atom) (pointer : Nat) :
    (table.toHeap.get? (pointer + 1)) = table.nodes[pointer]?.map shiftNode := by
  simp [toHeap, SExpr2.Heap.get?, List.getElem?_map]

/-- Zero-indexed decoding agrees with one-indexed heap decoding after mapping
away the impossible nil case. -/
theorem deref_toHeap (table : Table Atom) : ∀ gas pointer,
    table.toHeap.deref gas (pointer + 1) =
      (table.deref gas pointer).map SExpr2.ofTree := by
  intro gas
  induction gas with
  | zero => intro pointer; rfl
  | succ gas ih =>
      intro pointer
      change table.toHeap.deref (gas + 1) (Nat.succ pointer) = _
      simp only [SExpr2.Heap.deref]
      rw [get?_shiftNode]
      cases hnode : table.nodes[pointer]? with
      | none => simp [deref, hnode]
      | some node =>
          cases node with
          | atom value => simp [deref, hnode, shiftNode, SExpr2.ofTree]
          | cons left right =>
              change Option.map SExpr2.cons
                (table.toHeap.deref gas (left + 1))
                <*> table.toHeap.deref gas (right + 1) = _
              rw [ih left, ih right]
              cases hl : table.deref gas left <;>
                cases hr : table.deref gas right <;>
                simp [deref, hnode, hl, hr, SExpr2.ofTree] <;> rfl

end Table
end Tree2

namespace SExpr2

/-- Typed view of the signed split-heap convention. -/
inductive SignedIndex where
  | nil
  | atom (index : Nat)
  | cons (index : Nat)
  deriving DecidableEq, Repr

namespace SignedIndex

/-- `atom i` is `-(i+1)`, `cons i` is `i+1`, and nil is zero. -/
def toInt : SignedIndex → Int
  | .nil => 0
  | .atom index => .negSucc index
  | .cons index => .ofNat (index + 1)

def ofInt : Int → SignedIndex
  | .ofNat 0 => .nil
  | .ofNat (index + 1) => .cons index
  | .negSucc index => .atom index

@[simp] theorem ofInt_toInt (index : SignedIndex) : ofInt index.toInt = index := by
  cases index <;> rfl

@[simp] theorem toInt_ofInt (index : Int) : (ofInt index).toInt = index := by
  cases index with
  | ofNat index => cases index <;> rfl
  | negSucc => rfl

/-- The signed convention has no redundancy. -/
def equivInt : SignedIndex ≃ Int where
  toFun := toInt
  invFun := ofInt
  left_inv := ofInt_toInt
  right_inv := toInt_ofInt

end SignedIndex

/-- Split storage: negative pointers address atoms, positive pointers address
cons cells, and zero denotes nil. Pointer `-(i+1)` addresses atom `i`; pointer
`i+1` addresses cell `i`. -/
structure SplitHeap (Atom : Type u) where
  atoms : List Atom
  cells : List (ConsCell Int)
  root : Int
  deriving DecidableEq, Repr

namespace SplitHeap

variable {Atom : Type u}

def ValidIndex (heap : SplitHeap Atom) : SignedIndex → Prop
  | .nil => True
  | .atom index => index < heap.atoms.length
  | .cons index => index < heap.cells.length

def Closed (heap : SplitHeap Atom) : Prop :=
  heap.ValidIndex (SignedIndex.ofInt heap.root) ∧
    ∀ (index : Nat) (cell : ConsCell Int), heap.cells[index]? = some cell →
      heap.ValidIndex (SignedIndex.ofInt cell.car) ∧
      heap.ValidIndex (SignedIndex.ofInt cell.cdr)

noncomputable instance (heap : SplitHeap Atom) : Decidable heap.Closed :=
  Classical.propDecidable _

def deref (heap : SplitHeap Atom) : Nat → Int → Option (SExpr2 Atom)
  | gas, pointer => match SignedIndex.ofInt pointer with
    | .nil => some .nil
    | .atom index => match gas with
      | 0 => none
      | _ + 1 => .atom <$> heap.atoms[index]?
    | .cons index => match gas with
      | 0 => none
      | gas + 1 =>
        match heap.cells[index]? with
        | some cell => .cons <$> heap.deref gas cell.car <*> heap.deref gas cell.cdr
        | none => none

def decode (heap : SplitHeap Atom) (gas : Nat) : Option (SExpr2 Atom) :=
  heap.deref gas heap.root

/-- Translate a signed pointer to the unified table formed by atoms followed
by cons cells. -/
def pointerToHeap (heap : SplitHeap Atom) (pointer : Int) : Nat :=
  match SignedIndex.ofInt pointer with
  | .nil => 0
  | .atom index => index + 1
  | .cons index => heap.atoms.length + index + 1

def indexToHeap (heap : SplitHeap Atom) : SignedIndex → Nat
  | .nil => 0
  | .atom index => index + 1
  | .cons index => heap.atoms.length + index + 1

@[simp] theorem pointerToHeap_toInt (heap : SplitHeap Atom) (index : SignedIndex) :
    heap.pointerToHeap index.toInt = heap.indexToHeap index := by
  cases index <;> rfl

private def cellToNode (heap : SplitHeap Atom) (cell : ConsCell Int) : HeapNode Atom :=
  .cons (heap.pointerToHeap cell.car) (heap.pointerToHeap cell.cdr)

/-- Forget split storage by concatenating atom nodes and translated cons cells. -/
def toHeap (heap : SplitHeap Atom) : Heap Atom :=
  ⟨heap.atoms.map .atom ++ heap.cells.map (cellToNode heap),
    heap.pointerToHeap heap.root⟩

@[simp] theorem pointerToHeap_zero (heap : SplitHeap Atom) :
    heap.pointerToHeap 0 = 0 := rfl

private theorem get?_atom (heap : SplitHeap Atom) (index : Nat)
    (valid : index < heap.atoms.length) :
    heap.toHeap.get? (index + 1) = some (.atom heap.atoms[index]) := by
  unfold toHeap Heap.get?
  simp only [Nat.add_sub_cancel]
  rw [List.getElem?_append_left (by simp [valid])]
  simp [valid]

private theorem get?_cons (heap : SplitHeap Atom) (index : Nat)
    (valid : index < heap.cells.length) :
    heap.toHeap.get? (heap.atoms.length + index + 1) =
      some (cellToNode heap heap.cells[index]) := by
  unfold toHeap Heap.get?
  rw [show heap.atoms.length + index + 1 - 1 = heap.atoms.length + index by omega]
  rw [List.getElem?_append_right (by simp)]
  simp [valid]

/-- On closed split heaps, direct signed decoding agrees with translation to
the unified one-indexed heap at every gas level. -/
theorem deref_toHeap (heap : SplitHeap Atom) (closed : heap.Closed) :
    ∀ gas index, heap.ValidIndex index →
      heap.toHeap.deref gas (heap.indexToHeap index) = heap.deref gas index.toInt := by
  intro gas
  induction gas with
  | zero =>
      intro index valid
      cases index <;> rfl
  | succ gas ih =>
      intro index valid
      cases index with
      | nil => rfl
      | atom index =>
          have hv : index < heap.atoms.length := valid
          have hget := get?_atom heap index hv
          change heap.toHeap.deref (gas + 1) (Nat.succ index) = _
          simp only [Heap.deref]
          simp only [hget]
          change some (SExpr2.atom heap.atoms[index]) =
            SExpr2.atom <$> heap.atoms[index]?
          rw [List.getElem?_eq_getElem hv]
          rfl
      | cons index =>
          have hv : index < heap.cells.length := valid
          have hcell : heap.cells[index]? = some heap.cells[index] :=
            List.getElem?_eq_getElem hv
          have children := closed.2 index heap.cells[index] hcell
          have hget := get?_cons heap index hv
          change heap.toHeap.deref (gas + 1) (Nat.succ (heap.atoms.length + index)) = _
          simp only [Heap.deref]
          simp only [hget, cellToNode]
          change (Option.map SExpr2.cons
              (heap.toHeap.deref gas (heap.pointerToHeap heap.cells[index].car))
              <*> heap.toHeap.deref gas (heap.pointerToHeap heap.cells[index].cdr)) = _
          rw [show heap.pointerToHeap heap.cells[index].car =
            heap.indexToHeap (SignedIndex.ofInt heap.cells[index].car) by
              simpa using heap.pointerToHeap_toInt
                (SignedIndex.ofInt heap.cells[index].car)]
          rw [show heap.pointerToHeap heap.cells[index].cdr =
            heap.indexToHeap (SignedIndex.ofInt heap.cells[index].cdr) by
              simpa using heap.pointerToHeap_toInt
                (SignedIndex.ofInt heap.cells[index].cdr)]
          rw [ih _ children.1, ih _ children.2]
          change _ = (match heap.cells[index]? with
            | some cell => SExpr2.cons <$> heap.deref gas cell.car <*> heap.deref gas cell.cdr
            | none => none)
          rw [hcell]
          simp only [SignedIndex.toInt_ofInt]
          rfl

theorem decode_toHeap (heap : SplitHeap Atom) (closed : heap.Closed) (gas : Nat) :
    heap.toHeap.decode gas = heap.decode gas := by
  have hp : heap.pointerToHeap heap.root =
      heap.indexToHeap (SignedIndex.ofInt heap.root) := by
    simpa using heap.pointerToHeap_toInt (SignedIndex.ofInt heap.root)
  change heap.toHeap.deref gas (heap.pointerToHeap heap.root) = heap.deref gas heap.root
  rw [hp]
  simpa only [SignedIndex.toInt_ofInt] using
    heap.deref_toHeap closed gas (SignedIndex.ofInt heap.root) closed.1

end SplitHeap
end SExpr2
end Nucleus
