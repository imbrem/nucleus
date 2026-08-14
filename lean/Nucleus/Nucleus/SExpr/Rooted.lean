import Nucleus.SExpr.Allocator

/-!
# Rooted memories, pointer equality, and garbage collection

Path equivalence compares the trees observed at finitely many named roots and
therefore forgets sharing.  `PointerEquivalent` is intentionally stronger: it
is an isomorphism only of the reachable address subtypes.  It preserves
pointer equality but assumes no order on addresses, and ignores both the
contents and even the cardinality of unreachable storage.
-/

namespace Nucleus.SExpr2

universe u v w

structure RootedMemory (ι : Type u) (α : Type v) (n : Nat) where
  memory : PartialMemory ι α
  roots : Fin n → ι

namespace RootedMemory

variable {ι : Type u} {κ : Type w} {α : Type v} {n : Nat}

/-- Addresses reached by following zero or more car/cdr pointers from a root. -/
inductive Reachable (rooted : RootedMemory ι α n) : ι → Prop where
  | root (i : Fin n) : Reachable rooted (rooted.roots i)
  | car {address : ι} (h : Reachable rooted address) {cell : ConsCell ι}
      (hc : rooted.memory.cells address = some (.cons cell)) :
      Reachable rooted cell.car
  | cdr {address : ι} (h : Reachable rooted address) {cell : ConsCell ι}
      (hc : rooted.memory.cells address = some (.cons cell)) :
      Reachable rooted cell.cdr

/-- No exposed or transitively reachable pointer is free. -/
def Closed (rooted : RootedMemory ι α n) : Prop :=
  ∀ address, rooted.Reachable address → rooted.memory.Allocated address

/-- Equality of all path observations. This deliberately forgets sharing. -/
def PathEquivalent (left : RootedMemory ι α n) (right : RootedMemory κ α n) : Prop :=
  ∀ i, left.memory.denote (left.roots i) = right.memory.denote (right.roots i)

@[refl] theorem pathEquivalent_refl (rooted : RootedMemory ι α n) :
    rooted.PathEquivalent rooted := fun _ => rfl

@[symm] theorem PathEquivalent.symm {left : RootedMemory ι α n}
    {right : RootedMemory κ α n} (h : left.PathEquivalent right) :
    right.PathEquivalent left := fun i => (h i).symm

theorem PathEquivalent.trans {left : RootedMemory ι α n}
    {middle : RootedMemory κ α n} {right : RootedMemory γ α n}
    (hlm : left.PathEquivalent middle) (hmr : middle.PathEquivalent right) :
    left.PathEquivalent right := fun i => (hlm i).trans (hmr i)

/-- Isomorphism of reachable graphs. This preserves pointer equality and cell
labels, but provides no pointer ordering and places no constraint on garbage. -/
structure PointerEquivalent (left : RootedMemory ι α n)
    (right : RootedMemory κ α n) where
  equiv : {a // left.Reachable a} ≃ {a // right.Reachable a}
  roots : ∀ i, equiv ⟨left.roots i, .root i⟩ = ⟨right.roots i, .root i⟩
  nil_cell : ∀ address h, left.memory.cells address = some .nil →
    right.memory.cells (equiv ⟨address, h⟩).1 = some .nil
  atom_cell : ∀ address h value, left.memory.cells address = some (.atom value) →
    right.memory.cells (equiv ⟨address, h⟩).1 = some (.atom value)
  cons_cell : ∀ address h cell (hc : left.memory.cells address = some (.cons cell)),
    right.memory.cells (equiv ⟨address, h⟩).1 = some (.cons {
      car := (equiv ⟨cell.car, .car h hc⟩).1
      cdr := (equiv ⟨cell.cdr, .cdr h hc⟩).1 })
  free_cell : ∀ address h, left.memory.cells address = none →
    right.memory.cells (equiv ⟨address, h⟩).1 = none

namespace PointerEquivalent

private theorem observe_eq {left : RootedMemory ι α n}
    {right : RootedMemory κ α n} (h : left.PointerEquivalent right) :
    ∀ (address : ι) (ha : left.Reachable address) path,
      right.memory.observe (h.equiv ⟨address, ha⟩).1 path =
        left.memory.observe address path := by
  intro address ha path
  induction path generalizing address with
  | nil =>
      cases hx : left.memory.cells address with
      | none => simp [PartialMemory.observe, hx, h.free_cell address ha hx]
      | some cell =>
          cases cell with
          | nil => simp [PartialMemory.observe, hx, h.nil_cell address ha hx]
          | atom value => simp [PartialMemory.observe, hx, h.atom_cell address ha value hx]
          | cons cell => simp [PartialMemory.observe, hx, h.cons_cell address ha cell hx]
  | cons side path ih =>
      cases hx : left.memory.cells address with
      | none => simp [PartialMemory.observe, hx, h.free_cell address ha hx]
      | some cell =>
          cases cell with
          | nil => simp [PartialMemory.observe, hx, h.nil_cell address ha hx]
          | atom value => simp [PartialMemory.observe, hx, h.atom_cell address ha value hx]
          | cons cell =>
              cases side
              · simpa [PartialMemory.observe, hx, h.cons_cell address ha cell hx] using
                  ih cell.car (.car ha hx)
              · simpa [PartialMemory.observe, hx, h.cons_cell address ha cell hx] using
                  ih cell.cdr (.cdr ha hx)

/-- Preserving pointer equality implies path equivalence; the converse need
not hold, since two equal subtrees may be shared in one memory and copied in
the other. -/
theorem pathEquivalent {left : RootedMemory ι α n}
    {right : RootedMemory κ α n} (h : left.PointerEquivalent right) :
    left.PathEquivalent right := by
  intro i
  apply Coinductive.ext
  intro path
  change left.memory.observe (left.roots i) path = right.memory.observe (right.roots i) path
  have ho := h.observe_eq (left.roots i) (.root i) path
  rw [h.roots i] at ho
  exact ho.symm

end PointerEquivalent

/-- Garbage collection frees exactly the unreachable addresses. -/
noncomputable def collect (rooted : RootedMemory ι α n) : RootedMemory ι α n := by
  classical
  exact {
    memory.cells := fun address =>
      if h : rooted.Reachable address then rooted.memory.cells address else none
    roots := rooted.roots }

@[simp] theorem collect_cells_of_reachable (rooted : RootedMemory ι α n)
    {address : ι} (h : rooted.Reachable address) :
    rooted.collect.memory.cells address = rooted.memory.cells address := by
  simp [collect, h]

theorem reachable_collect_iff (rooted : RootedMemory ι α n) (address : ι) :
    rooted.collect.Reachable address ↔ rooted.Reachable address := by
  constructor
  · intro h
    induction h with
    | root i => exact .root i
    | car hr hc ih =>
        rw [collect_cells_of_reachable rooted ih] at hc
        exact .car ih hc
    | cdr hr hc ih =>
        rw [collect_cells_of_reachable rooted ih] at hc
        exact .cdr ih hc
  · intro h
    induction h with
    | root i => exact .root i
    | car hr hc ih => exact .car ih (by simpa [collect, hr] using hc)
    | cdr hr hc ih => exact .cdr ih (by simpa [collect, hr] using hc)

/-- Collection preserves the reachable graph, hence pointer equality as well
as every path observation. -/
noncomputable def pointerEquivalentCollect (rooted : RootedMemory ι α n) :
    rooted.PointerEquivalent rooted.collect where
  equiv := Equiv.subtypeEquiv (Equiv.refl ι) (by simp [reachable_collect_iff])
  roots i := rfl
  nil_cell address h hc := by
    change rooted.collect.memory.cells address = _
    rw [collect_cells_of_reachable rooted h]
    exact hc
  atom_cell address h value hc := by
    change rooted.collect.memory.cells address = _
    rw [collect_cells_of_reachable rooted h]
    exact hc
  cons_cell address h cell hc := by
    change rooted.collect.memory.cells address = _
    rw [collect_cells_of_reachable rooted h]
    simpa using hc
  free_cell address h hc := by
    change rooted.collect.memory.cells address = _
    rw [collect_cells_of_reachable rooted h]
    exact hc

theorem pathEquivalent_collect (rooted : RootedMemory ι α n) :
    rooted.PathEquivalent rooted.collect :=
  rooted.pointerEquivalentCollect.pathEquivalent

theorem collect_frees_unreachable (rooted : RootedMemory ι α n)
    {address : ι} (h : ¬ rooted.Reachable address) :
    rooted.collect.memory.Free address := by simp [collect, PartialMemory.Free, h]

/-- Rooted memories quotiented by path observations. -/
def pathSetoid (ι : Type u) (α : Type v) (n : Nat) :
    Setoid (RootedMemory ι α n) where
  r := PathEquivalent
  iseqv := ⟨pathEquivalent_refl, PathEquivalent.symm, PathEquivalent.trans⟩

def PathQuotient (ι : Type u) (α : Type v) (n : Nat) :=
  Quotient (pathSetoid ι α n)

namespace PathQuotient

def denote : PathQuotient ι α n → Fin n → Coinductive α :=
  Quotient.lift (fun rooted i => rooted.memory.denote (rooted.roots i))
    (fun _ _ h => funext h)

/-- The path quotient has no equality beyond observable denotation. -/
theorem denote_injective :
    Function.Injective (denote : PathQuotient ι α n → Fin n → Coinductive α) := by
  intro left right h
  induction left using Quotient.inductionOn with
  | _ left =>
      induction right using Quotient.inductionOn with
      | _ right => exact Quotient.sound (congrFun h)

end PathQuotient

private noncomputable def cellOfShape (path : List Bool) (shape : Shape α) : Cell (List Bool) α :=
  Shape.rec (motive := fun _ => Cell (List Bool) α)
    .nil (fun atom => .atom atom)
    (.cons ⟨path ++ [false], path ++ [true]⟩) shape

private theorem observe_below_path (value : Coinductive α) (address : List Bool)
    (h : value.observe address ≠ .cons) : ∀ side path,
    value.observe (address ++ side :: path) = .nil := by
  intro side path
  induction path generalizing address side with
  | nil => simpa using value.below_noncons address side h
  | cons next path ih =>
      have first : value.observe (address ++ [side]) = .nil :=
        value.below_noncons address side h
      simpa [List.append_assoc] using
        ih (address ++ [side]) (by simp [first]) next

/-- The canonical unrestricted presentation uses finite Boolean paths as
addresses. It allocates every address, including explicit nil leaves. -/
noncomputable def ofCoinductive (value : Coinductive α) : RootedMemory (List Bool) α 1 where
  memory.cells path := some (cellOfShape path (value.observe path))
  roots _ := []

private theorem observe_ofCoinductive (value : Coinductive α) :
    ∀ address path, (ofCoinductive value).memory.observe address path =
      value.observe (address ++ path) := by
  intro address path
  induction path generalizing address with
  | nil =>
      cases h : value.observe address <;>
        simp [ofCoinductive, PartialMemory.observe, cellOfShape, h]
  | cons side path ih =>
      cases h : value.observe address with
      | cons =>
          cases side
          · simpa [ofCoinductive, PartialMemory.observe, cellOfShape, h,
              List.append_assoc] using ih (address ++ [false])
          · simpa [ofCoinductive, PartialMemory.observe, cellOfShape, h,
              List.append_assoc] using ih (address ++ [true])
      | nil =>
          have hb := observe_below_path value address (by simp [h]) side path
          simpa [ofCoinductive, PartialMemory.observe, cellOfShape, h,
            List.append_assoc] using hb.symm
      | atom atom =>
          have hb := observe_below_path value address (by simp [h]) side path
          simpa [ofCoinductive, PartialMemory.observe, cellOfShape, h,
            List.append_assoc] using hb.symm

theorem denote_ofCoinductive (value : Coinductive α) :
    (ofCoinductive value).memory.denote [] = value := by
  apply Coinductive.ext
  intro path
  exact observe_ofCoinductive value [] path

/-- With unrestricted path addresses, quotienting a single exposed root by
path equivalence gives the whole greatest fixpoint (surjectivity direction). -/
theorem pathQuotient_surjective : Function.Surjective
    (PathQuotient.denote : PathQuotient (List Bool) α 1 → Fin 1 → Coinductive α) := by
  intro values
  let rooted := ofCoinductive (values 0)
  refine ⟨Quotient.mk _ rooted, ?_⟩
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact denote_ofCoinductive (values 0)

end RootedMemory
end Nucleus.SExpr2
