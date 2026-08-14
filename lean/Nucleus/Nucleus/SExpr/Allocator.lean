import Nucleus.SExpr.Memory
import Mathlib.Data.Finset.Powerset

/-!
# Persistent allocators and finite allocation

An allocator is a concrete injective stream of addresses, all currently free.
Allocation consumes its head and shifts the stream, so another allocation is
always available. Finite allocation is represented by an exact finite support;
enumerating that support relates it to list storage without assuming addresses
are an initial segment of naturals.
-/

namespace Nucleus.SExpr2

universe u v

structure AllocatorMemory (ι : Type u) (α : Type v) where
  memory : PartialMemory ι α
  free : Nat → ι
  free_injective : Function.Injective free
  free_mem : ∀ n, memory.Free (free n)

namespace AllocatorMemory

variable {ι : Type u} {α : Type v}

def allocate [DecidableEq ι] (state : AllocatorMemory ι α)
    (cell : Cell ι α) : AllocatorMemory ι α × ι :=
  let address := state.free 0
  let memory := state.memory.allocate address cell (state.free_mem 0)
  let nextFree := fun n => state.free (n + 1)
  (⟨memory, nextFree,
    fun n m h => by
      have := state.free_injective h
      omega,
    fun n => by
      unfold PartialMemory.Free
      rw [state.memory.allocate_ne address (nextFree n) cell (state.free_mem 0) (by
        intro h
        have := state.free_injective h
        omega)]
      exact state.free_mem (n + 1)⟩,
   address)

@[simp] theorem allocate_lookup [DecidableEq ι] (state : AllocatorMemory ι α)
    (cell : Cell ι α) :
    (state.allocate cell).1.memory.cells (state.allocate cell).2 = some cell := by
  simp [allocate, PartialMemory.allocate]

theorem allocate_fresh [DecidableEq ι] (state : AllocatorMemory ι α)
    (cell : Cell ι α) : state.memory.Free (state.allocate cell).2 := by
  exact state.free_mem 0

end AllocatorMemory

/-- A partial memory with exactly a finite set of allocated addresses. -/
structure FiniteMemory (ι : Type u) (α : Type v) [DecidableEq ι] where
  memory : PartialMemory ι α
  support : Finset ι
  allocated_iff : ∀ address, memory.Allocated address ↔ address ∈ support

namespace FiniteMemory

variable {ι : Type u} {α : Type v} [DecidableEq ι]

/-- The list of cells obtained after choosing an enumeration of the finite
support. Pointers remain in the original address type. -/
noncomputable def cells (memory : FiniteMemory ι α) : List (Cell ι α) :=
  memory.support.attach.toList.map fun address =>
    (memory.memory.cells address.1).get (by
      exact (memory.allocated_iff address.1).mpr address.2)

@[simp] theorem cells_length (memory : FiniteMemory ι α) :
    memory.cells.length = memory.support.card := by
  simp [cells]

/-- List memory is the special finite-allocation natural memory whose support
is the initial segment `[0, length)`. -/
def ofListMemory (memory : ListMemory α) : FiniteMemory Nat α where
  memory := memory.toPartial
  support := Finset.range memory.cells.length
  allocated_iff address := by
    simp [PartialMemory.Allocated, ListMemory.toPartial, Option.isSome_iff_ne_none]

end FiniteMemory
end Nucleus.SExpr2
