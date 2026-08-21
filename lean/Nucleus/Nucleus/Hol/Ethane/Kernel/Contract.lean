import Nucleus.Hol.Ethane.Amber.Arena.Dense
import Nucleus.O256

/-!
# Ethane kernel contract

This file fixes the smallest implementation/formalization boundary for the
Ethane MVP.  A runtime kernel owns an arena; logically it is an arena together
with a proof of soundness relative to one shared, implicit CAS.  The CAS is a
ghost parameter of the Lean model and need not be stored by the Rust kernel.

Kernel identity is deliberately absent.  Facts carry their assumptions, so a
fact can be copied between arenas interpreted against the same CAS.  Kernel
operations are pure arena-to-arena functions; an in-place implementation is an
optimization of these functions rather than an additional logical rule.

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

/-- A theorem stored in an arena.  Assumptions are part of the fact itself and
are retained when the fact crosses arena boundaries. -/
structure Fact (Statement : Type v) where
  assumptions : List Statement
  conclusion : Statement

namespace Fact

/-- Semantic validity of an assumption-carrying fact relative to a CAS.
`Meaning` is intentionally supplied by the logical layer rather than by the
wire representation. -/
def ValidUnder (Meaning : CAS Object → Statement → Prop)
    (cas : CAS Object) (fact : Fact Statement) : Prop :=
  (∀ assumption ∈ fact.assumptions, Meaning cas assumption) →
    Meaning cas fact.conclusion

end Fact

/-- The implementation-facing arena state.  Syntax uses absolute signed
indices and an optional O256 parent; facts explicitly retain assumptions. -/
structure Arena (Sig : Signature.{u}) (Name : Type v) (Statement : Type v) where
  syntax : Amber.Arena.Dense.Syntax O256 Sig Name Int
  facts : Array (Fact Statement)

namespace Arena

/-- Structural and logical soundness relative to one shared ghost CAS. -/
def Sound (Meaning : CAS Object → Statement → Prop)
    (cas : CAS Object) (arena : Arena Sig Name Statement) : Prop :=
  arena.syntax.Valid ∧
    ∀ fact ∈ arena.facts, fact.ValidUnder Meaning cas

theorem Sound.fact_valid (sound : arena.Sound Meaning cas)
    (member : fact ∈ arena.facts) : fact.ValidUnder Meaning cas :=
  sound.2 fact member

/-- The empty persistent arena. -/
def empty : Arena Sig Name Statement where
  syntax := ⟨none, 0, #[]⟩
  facts := #[]

@[simp] theorem empty_sound (Meaning : CAS Object → Statement → Prop)
    (cas : CAS Object) : (empty : Arena Sig Name Statement).Sound Meaning cas := by
  constructor <;> simp [empty, Sound, Amber.Arena.Dense.Valid,
    Amber.Arena.Dense.RowsValid]

/-- Result of appending the nullary Boolean type constructor. -/
structure BoolTyResult (Sig : Signature.{u}) (Name : Type v)
    (Statement : Type v) where
  arena : Arena Sig Name Statement
  reference : Int

/-- Pure model of the Boolean-type kernel constructor.  A Rust `&mut` method
implements this transition when it replaces its receiver with `result.arena`.
The returned reference is the old first-unallocated index. -/
def boolTy (arena : Arena Sig Name Statement) : BoolTyResult Sig Name Statement :=
  ⟨⟨arena.syntax.push .boolTy, arena.facts⟩, arena.syntax.next⟩

/-- Appending Boolean type preserves soundness for every shared CAS and every
logical interpretation.  It adds syntax only and cannot alter stored facts or
their assumptions. -/
theorem boolTy_sound
    (oldSound : arena.Sound Meaning cas) :
    (arena.boolTy.arena).Sound Meaning cas := by
  rcases oldSound with ⟨syntaxSound, factsSound⟩
  refine ⟨syntaxSound.push ?_, factsSound⟩
  intro child childMem
  simp [Arena.Row.children] at childMem

/-- Pure model of either nullary Boolean term constructor. -/
def bool (arena : Arena Sig Name Statement) (value : Bool) :
    BoolTyResult Sig Name Statement :=
  ⟨⟨arena.syntax.push (.bool value), arena.facts⟩, arena.syntax.next⟩

/-- Appending a Boolean term preserves soundness. -/
theorem bool_sound
    (oldSound : arena.Sound Meaning cas) :
    (arena.bool value).arena.Sound Meaning cas := by
  rcases oldSound with ⟨syntaxSound, factsSound⟩
  refine ⟨syntaxSound.push ?_, factsSound⟩
  intro child childMem
  simp [Arena.Row.children] at childMem

@[simp] theorem boolTy_reference :
    (arena.boolTy : BoolTyResult Sig Name Statement).reference = arena.syntax.next :=
  rfl

@[simp] theorem boolTy_facts :
    (arena.boolTy : BoolTyResult Sig Name Statement).arena.facts = arena.facts :=
  rfl

/-- Pure destination-side operation used when a fact is moved between
arenas.  The complete assumption list moves with the fact. -/
def copyFact (destination : Arena Sig Name Statement) (fact : Fact Statement) :
    Arena Sig Name Statement :=
  ⟨destination.syntax, destination.facts.push fact⟩

/-- Copying a fact valid under the shared CAS preserves destination soundness. -/
theorem copyFact_sound (destinationSound : destination.Sound Meaning cas)
    (factSound : fact.ValidUnder Meaning cas) :
    (destination.copyFact fact).Sound Meaning cas := by
  refine ⟨destinationSound.1, ?_⟩
  intro candidate member
  simp only [copyFact, Array.mem_push] at member
  rcases member with member | rfl
  · exact destinationSound.2 candidate member
  · exact factSound

/-- A fact selected from one sound arena can be copied to another sound arena
without a kernel-identity check.  Both soundness hypotheses mention the same
ghost CAS, and the fact's assumptions are unchanged. -/
theorem copyFact_from_sound
    (sourceSound : source.Sound Meaning cas)
    (destinationSound : destination.Sound Meaning cas)
    (member : fact ∈ source.facts) :
    (destination.copyFact fact).Sound Meaning cas :=
  copyFact_sound destinationSound (sourceSound.fact_valid member)

end Arena

/-! Stable correspondence names used by the Rust/Lean operation registry. -/

/-- Stable kernel constructor name; see `Arena.empty`. -/
def empty : Arena Sig Name Statement := Arena.empty

/-- Stable preservation name for `empty`. -/
theorem empty_sound (Meaning : CAS Object → Statement → Prop)
    (cas : CAS Object) : (empty : Arena Sig Name Statement).Sound Meaning cas :=
  Arena.empty_sound Meaning cas

/-- Stable persistent Boolean-type operation name. -/
def boolTy (arena : Arena Sig Name Statement) : Arena.BoolTyResult Sig Name Statement :=
  arena.boolTy

/-- Stable preservation name for `boolTy`. -/
theorem boolTy_sound (oldSound : arena.Sound Meaning cas) :
    (boolTy arena).arena.Sound Meaning cas :=
  Arena.boolTy_sound oldSound

/-- Stable persistent Boolean-term operation name. -/
def bool (arena : Arena Sig Name Statement) (value : Bool) :
    Arena.BoolTyResult Sig Name Statement :=
  arena.bool value

/-- Stable preservation name for `bool`. -/
theorem bool_sound (oldSound : arena.Sound Meaning cas) :
    (bool arena value).arena.Sound Meaning cas :=
  Arena.bool_sound oldSound

/-- The logical form of an owning kernel wrapper.  `cas` and `Meaning` are
ghost parameters: Rust stores only `arena`. -/
structure CheckedArena (Meaning : CAS Object → Statement → Prop)
    (cas : CAS Object) (Sig : Signature.{u}) (Name : Type v)
    (Statement : Type v) where
  arena : Arena Sig Name Statement
  sound : arena.Sound Meaning cas

namespace CheckedArena

/-- Sound constructor for an empty kernel arena. -/
def empty : CheckedArena Meaning cas Sig Name Statement :=
  ⟨Arena.empty, Arena.empty_sound Meaning cas⟩

/-- Persistent Boolean-type operation on a checked arena. -/
def boolTy (kernel : CheckedArena Meaning cas Sig Name Statement) :
    CheckedArena Meaning cas Sig Name Statement × Int :=
  let result := kernel.arena.boolTy
  (⟨result.arena, Arena.boolTy_sound kernel.sound⟩, result.reference)

end CheckedArena

end Nucleus.Hol.Ethane.Kernel
