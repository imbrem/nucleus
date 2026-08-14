import Nucleus.SExpr.Indexed
import Mathlib.Data.Finset.Basic

/-!
# Partial S-expression memories and allocation

A partial memory maps addresses to optional atom/cons cells. Missing addresses
are genuinely free, rather than another spelling of nil. Rooted denotation is
coinductive and treats an accidental missing dereference as nil, while the
separate `RootsAllocated` predicate prevents free roots from being exposed.
-/

namespace Nucleus.SExpr2

universe u v

/-- A heap with an arbitrary address type and explicit free addresses. -/
structure PartialMemory (ι : Type u) (α : Type v) where
  cells : ι → Option (Cell ι α)

namespace PartialMemory

variable {ι : Type u} {κ : Type*} {α : Type v}

def Free (memory : PartialMemory ι α) (address : ι) : Prop :=
  memory.cells address = none

def Allocated (memory : PartialMemory ι α) (address : ι) : Prop :=
  (memory.cells address).isSome

/-- Allocate at a known-free address. -/
def allocate [DecidableEq ι] (memory : PartialMemory ι α) (address : ι)
    (cell : Cell ι α) (_free : memory.Free address) : PartialMemory ι α :=
  ⟨Function.update memory.cells address (some cell)⟩

@[simp] theorem allocate_eq [DecidableEq ι] (memory : PartialMemory ι α)
    (address : ι) (cell : Cell ι α) (free : memory.Free address) :
    (memory.allocate address cell free).cells address = some cell := by
  simp [allocate]

theorem allocate_ne [DecidableEq ι] (memory : PartialMemory ι α)
    (address other : ι) (cell : Cell ι α) (free : memory.Free address)
    (hne : other ≠ address) :
    (memory.allocate address cell free).cells other = memory.cells other := by
  simp [allocate, hne]

/-- Fuelled least-fixpoint interpretation. -/
def deref (memory : PartialMemory ι α) : Nat → ι → Option (Tree2 α)
  | 0, _ => none
  | gas + 1, address => match memory.cells address with
    | some .nil => none
    | some (.atom value) => some (.atom value)
    | some (.cons cell) =>
        .cons <$> memory.deref gas cell.car <*> memory.deref gas cell.cdr
    | none => none

/-- Greatest-fixpoint observations. Missing addresses canonically observe nil. -/
def observe (memory : PartialMemory ι α) : ι → List Bool → Shape α
  | address, [] => match memory.cells address with
    | some .nil => .nil
    | some (.atom value) => .atom value
    | some (.cons _) => .cons
    | none => .nil
  | address, direction :: path => match memory.cells address with
    | some (.cons cell) => memory.observe (if direction then cell.cdr else cell.car) path
    | _ => .nil

private theorem observe_below (memory : PartialMemory ι α) :
    ∀ address path direction, memory.observe address path ≠ .cons →
      memory.observe address (path ++ [direction]) = .nil := by
  intro address path
  induction path generalizing address with
  | nil =>
      intro direction h
      cases hc : memory.cells address with
      | none => simp [observe, hc]
      | some cell => cases cell <;> simp_all [observe]
  | cons side path ih =>
      intro direction h
      cases hc : memory.cells address with
      | none => simp [observe, hc]
      | some cell =>
          cases cell with
          | nil => simp [observe, hc]
          | atom => simp [observe, hc]
          | cons cell =>
              simp only [List.cons_append, observe, hc] at h ⊢
              exact ih _ direction h

def denote (memory : PartialMemory ι α) (root : ι) : Coinductive α where
  observe := memory.observe root
  below_noncons := memory.observe_below root

/-- Reindex a memory along an address equivalence. -/
def reindex (equiv : ι ≃ κ) (memory : PartialMemory ι α) : PartialMemory κ α :=
  ⟨fun address => (memory.cells (equiv.symm address)).map (.mapIndex equiv)⟩

private theorem observe_reindex (equiv : ι ≃ κ) (memory : PartialMemory ι α) :
    ∀ address path,
      (memory.reindex equiv).observe (equiv address) path = memory.observe address path := by
  intro address path
  induction path generalizing address with
  | nil =>
      cases hc : memory.cells address with
      | none => simp [reindex, observe, hc]
      | some cell => cases cell <;> simp [reindex, observe, hc, Cell.mapIndex]
  | cons side path ih =>
      simp only [observe, reindex, Equiv.symm_apply_apply]
      cases hc : memory.cells address with
      | none => rfl
      | some cell =>
          cases cell with
          | nil => rfl
          | atom => rfl
          | cons cell =>
              cases side
              · change (memory.reindex equiv).observe (equiv cell.car) path = _
                exact ih cell.car
              · change (memory.reindex equiv).observe (equiv cell.cdr) path = _
                exact ih cell.cdr

theorem denote_reindex (equiv : ι ≃ κ) (memory : PartialMemory ι α)
    (root : ι) :
    (memory.reindex equiv).denote (equiv root) = memory.denote root := by
  apply Coinductive.ext
  exact memory.observe_reindex equiv root

end PartialMemory

/-- List-backed zero-indexed partial memory. Appending is allocation. -/
structure ListMemory (α : Type v) where
  cells : List (Cell Nat α)
  deriving DecidableEq, Repr

namespace ListMemory

variable {α : Type v}

def toPartial (memory : ListMemory α) : PartialMemory Nat α :=
  ⟨fun address => memory.cells[address]?⟩

def allocate (memory : ListMemory α) (cell : Cell Nat α) :
    ListMemory α × Nat :=
  (⟨memory.cells ++ [cell]⟩, memory.cells.length)

@[simp] theorem allocate_lookup (memory : ListMemory α) (cell : Cell Nat α) :
    (memory.allocate cell).1.toPartial.cells (memory.allocate cell).2 = some cell := by
  simp [allocate, toPartial]

theorem allocate_preserves (memory : ListMemory α) (cell : Cell Nat α)
    (address : Nat) (h : address < memory.cells.length) :
    (memory.allocate cell).1.toPartial.cells address = memory.toPartial.cells address := by
  simp [allocate, toPartial, List.getElem?_append_left h]

end ListMemory

end Nucleus.SExpr2
