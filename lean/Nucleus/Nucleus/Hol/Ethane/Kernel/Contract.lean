import Nucleus.Hol.Ethane.Amber.Arena.Dense
import Nucleus.O256

/-!
# Ethane kernel contract

This file fixes the smallest implementation/formalization boundary for the
Ethane MVP.  A runtime kernel owns an arena; logically it is an arena together
with a proof of soundness relative to one shared, implicit CAS.  The CAS is a
ghost parameter of the Lean model and need not be stored by the Rust kernel.

Kernel identity is deliberately absent. Facts are checked `sort` and `eq`
data carried by arena rows, not standalone values. Kernel operations are pure
arena-to-arena functions; an in-place implementation is an optimization.

Cryptographic bounds are outside this contract.  Their connection to a real
BLAKE3 implementation is explicitly deferred beyond the deterministic MVP;
`CAS.Coherent` is only an assumption on the shared implicit CAS here.
-/

namespace Nucleus.Hol.Ethane.Kernel

open Nucleus.Hol.Ethane
open Nucleus.Hol.Ethane.Amber

universe u v
set_option relaxedAutoImplicit true

/-- An ideal, partial BLAKE3-shaped content-addressed store.  Its 256-bit keys
are the BLAKE3 output shape; no collision-resistance theorem is assumed here. -/
structure CAS (Object : Type u) where
  lookup : O256 → Option Object

namespace CAS

/-- Every object observed at an address has that address according to the
chosen content-addressing function.  This is deterministic coherence, not a
claim about the probability of BLAKE3 collisions. -/
def Coherent (address : Object → O256) (cas : CAS Object) : Prop :=
  ∀ key object, cas.lookup key = some object → address object = key

/-- A finite/runtime view agrees with a shared implicit CAS on every object it
has observed.  Different trusted views can therefore be composed by proving
agreement with the same `cas`. -/
def ViewAgrees (view cas : CAS Object) : Prop :=
  ∀ key object, view.lookup key = some object → cas.lookup key = some object

end CAS

/-- The implementation-facing arena state.  Syntax uses absolute signed
indices and an optional O256 parent. Fact classifications live on rows. -/
structure Arena (Sig : Signature.{u}) (Name : Type) where
  dense : Amber.Arena.Dense.Syntax O256 Sig Name Int

namespace Arena

/-- Structural and logical soundness relative to one shared ghost CAS. -/
def Sound (_Meaning : CAS Object → Statement → Prop)
    (_cas : CAS Object) (arena : Arena Sig Name) : Prop :=
  arena.dense.Valid

/-- The empty persistent arena. -/
def empty : Arena Sig Name where
  dense := ⟨none, 0, #[]⟩

@[simp] theorem empty_sound (Meaning : CAS Object → Statement → Prop)
    (cas : CAS Object) : (empty : Arena Sig Name).Sound Meaning cas := by
  simp [empty, Sound, Amber.Arena.Dense.Valid, Amber.Arena.Dense.RowsValid]

/-- Result of appending the nullary Boolean type constructor. -/
structure BoolTyResult (Sig : Signature.{u}) (Name : Type) where
  arena : Arena Sig Name
  reference : Int

/-- Pure model of the Boolean-type kernel constructor.  A Rust `&mut` method
implements this transition when it replaces its receiver with `result.arena`.
The returned reference is the old first-unallocated index. -/
def boolTy (arena : Arena Sig Name) : BoolTyResult Sig Name :=
  ⟨⟨arena.dense.push .boolTy⟩, arena.dense.next⟩

/-- Appending Boolean type preserves soundness for every shared CAS and every
logical interpretation. -/
theorem boolTy_sound
    (oldSound : Sound Meaning cas arena) :
    Sound Meaning cas (boolTy arena).arena := by
  refine oldSound.push ?_
  intro child childMem
  simp [Arena.Row.children] at childMem

/-- Pure model of either nullary Boolean term constructor. -/
def bool (arena : Arena Sig Name) (value : Bool) :
    BoolTyResult Sig Name :=
  ⟨⟨arena.dense.push (.bool value)⟩, arena.dense.next⟩

/-- Appending a Boolean term preserves soundness. -/
theorem bool_sound
    (oldSound : Sound Meaning cas arena) :
    Sound Meaning cas (bool arena value).arena := by
  refine oldSound.push ?_
  intro child childMem
  simp [Arena.Row.children] at childMem

@[simp] theorem boolTy_reference :
    (boolTy arena : BoolTyResult Sig Name).reference = arena.dense.next :=
  rfl

end Arena

/-! Stable correspondence names used by the Rust/Lean operation registry. -/

/-- Stable kernel constructor name; see `Arena.empty`. -/
def empty : Arena Sig Name := Arena.empty

/-- Stable preservation name for `empty`. -/
theorem empty_sound (Meaning : CAS Object → Statement → Prop)
    (cas : CAS Object) : Arena.Sound Meaning cas (empty : Arena Sig Name) :=
  Arena.empty_sound Meaning cas

/-- Stable persistent Boolean-type operation name. -/
def boolTy (arena : Arena Sig Name) : Arena.BoolTyResult Sig Name :=
  Arena.boolTy arena

/-- Stable preservation name for `boolTy`. -/
theorem boolTy_sound (oldSound : Arena.Sound Meaning cas arena) :
    Arena.Sound Meaning cas (boolTy arena).arena :=
  Arena.boolTy_sound oldSound

/-- Stable persistent Boolean-term operation name. -/
def bool (arena : Arena Sig Name) (value : Bool) :
    Arena.BoolTyResult Sig Name :=
  Arena.bool arena value

/-- Stable preservation name for `bool`. -/
theorem bool_sound (oldSound : Arena.Sound Meaning cas arena) :
    Arena.Sound Meaning cas (bool arena value).arena :=
  Arena.bool_sound oldSound

/-- The logical form of an owning kernel wrapper.  `cas` and `Meaning` are
ghost parameters: Rust stores only `arena`. -/
structure CheckedArena (Meaning : CAS Object → Statement → Prop)
    (cas : CAS Object) (Sig : Signature.{u}) (Name : Type)
    (Statement : Type v) where
  arena : Arena Sig Name
  sound : Arena.Sound Meaning cas arena

namespace CheckedArena

/-- Sound constructor for an empty kernel arena. -/
def empty : CheckedArena Meaning cas Sig Name Statement :=
  ⟨Arena.empty, Arena.empty_sound Meaning cas⟩

/-- Persistent Boolean-type operation on a checked arena. -/
def boolTy (kernel : CheckedArena Meaning cas Sig Name Statement) :
    CheckedArena Meaning cas Sig Name Statement × Int :=
  let result := Arena.boolTy kernel.arena
  (⟨result.arena, Arena.boolTy_sound kernel.sound⟩, result.reference)

end CheckedArena

end Nucleus.Hol.Ethane.Kernel
