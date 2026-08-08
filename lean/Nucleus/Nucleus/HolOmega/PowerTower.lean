import Mathlib.Data.Set.Image
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Set

/-!
# Levels and towers

Everything here is an explicit injection. No cardinal arithmetic: a level is a
type, and "small enough" means "embeds into a level".

One recursion does all the work:

* `Level Lift Base n` is `Base` under `n` applications of `Lift`.
* `Tower Lift Base` is all of those at once, so it absorbs any *fixed* number
  of further applications.

`Raise Lift` says `Lift` is a step *up*: there is a way in, and it carries
embeddings. That is all `raise` and `mapBase` need.

Two instantiations, at different scales:

* `PowerLevel`/`PowerTower` take `Lift := Set`, giving `ℶ_n` and `ℶ_ω`. These
  follow the reference development's names.
* `Beth.Block` (in `Beth.lean`) takes `Lift := PowerTower`, giving
  `ℶ_(ω * n)`.

The file closes with the two embeddings the reference does not have: a function
is its graph, a graph is a set of pairs, and a pair costs three levels — so a
function space costs four. `rangeEquiv` is what turns a type into a code.
-/

universe u v w

namespace Nucleus.HolOmega

/-- `Base` under `n` applications of `Lift`. -/
def Level (Lift : Type u → Type u) (Base : Type u) : Nat → Type u
  | 0 => Base
  | n + 1 => Lift (Level Lift Base n)

/-- Every level below `ω`, in one type. -/
abbrev Tower (Lift : Type u → Type u) (Base : Type u) := Σ n, Level Lift Base n

/-- `Lift` is a step *up*: there is a way in, and it carries embeddings. -/
class Raise (Lift : Type u → Type u) where
  ix : {X : Type u} → X ↪ Lift X
  map : {X Y : Type u} → (X ↪ Y) → (Lift X ↪ Lift Y)

namespace Level

variable {Lift : Type u → Type u} [Raise Lift] {Base Base' : Type u}

/-- Levels are cumulative. -/
def raise : {m n : Nat} → m ≤ n → Level Lift Base m ↪ Level Lift Base n
  | 0, 0, _ => Function.Embedding.refl _
  | 0, _m + 1, _ => (raise (Nat.zero_le _)).trans Raise.ix
  | _n + 1, 0, h => nomatch h
  | _n + 1, _m + 1, h => Raise.map (raise (Nat.succ_le_succ_iff.mp h))

/-- Transport a level along a map of bases. -/
def mapBase (f : Base ↪ Base') :
    (n : Nat) → Level Lift Base n ↪ Level Lift Base' n
  | 0 => f
  | n + 1 => Raise.map (mapBase f n)

end Level

namespace Tower

variable {Lift : Type u → Type u} {Base Base' : Type u}

def ofLevel (n : Nat) : Level Lift Base n ↪ Tower Lift Base where
  toFun x := ⟨n, x⟩
  inj' _ _ h := by injection h

/-- The tower contains its own base. -/
def base : Base ↪ Tower Lift Base := ofLevel 0

def mapBase [Raise Lift] (f : Base ↪ Base') :
    Tower Lift Base ↪ Tower Lift Base' where
  toFun x := ⟨x.1, Level.mapBase f x.1 x.2⟩
  inj' x y h := by
    obtain ⟨n, a⟩ := x
    obtain ⟨m, b⟩ := y
    injection h with hn h
    cases hn
    exact congrArg _ ((Level.mapBase f n).injective (eq_of_heq h))

end Tower

/-! ## Powersets, and towers of powersets -/

/-- Images along an embedding are injective on sets. -/
def imageEmb {α β : Type u} (e : α ↪ β) : Set α ↪ Set β where
  toFun := Set.image e
  inj' := Set.image_injective.mpr e.injective

/-- Taking powersets is a step up: singletons go in, and images carry
embeddings. -/
instance : Raise Set.{u} where
  ix := ⟨fun x => {x}, fun _ _ h => Set.singleton_injective h⟩
  map := imageEmb

/-- `Base` under `n` iterated powersets, of size `ℶ_n`. -/
abbrev PowerLevel (Base : Type u) := Level Set Base

/-- Everything below `ω` powersets over `Base`, of size `ℶ_ω`. -/
abbrev PowerTower (Base : Type u) := Tower Set Base

/-- Taking a whole power tower is a step up too. This is the step the beth
levels are built from. -/
instance : Raise PowerTower.{u} where
  ix := Tower.base
  map := Tower.mapBase

/-! ## Pairs and functions

An unordered encoding of ordered pairs, tagging the two components so they can
be told apart: the left tag has no empty member, the right tag does. -/

namespace Pairing

variable {X : Type u}

private def leftCode (x : X) : Set (Set X) := {{x}}
private def rightCode (x : X) : Set (Set X) := {∅, {x}}

private theorem leftCode_injective : Function.Injective (@leftCode X) := by
  intro x y h
  simpa [leftCode] using h

private theorem rightCode_injective : Function.Injective (@rightCode X) := by
  intro x y h
  have h' : ({x} : Set X) ∈ rightCode x := by simp [rightCode]
  rw [h] at h'
  simpa [rightCode] using h'

private theorem left_ne_right (x y : X) : leftCode x ≠ rightCode y := by
  intro h
  have h' : (∅ : Set X) ∈ leftCode x := by simp [h, rightCode]
  simp [leftCode] at h'

/-- An ordered pair costs three powerset levels. -/
def pairEmb : X × X ↪ PowerLevel X 3 where
  toFun p := ({leftCode p.1, rightCode p.2} : Set (Set (Set X)))
  inj' a b h := by
    change ({leftCode a.1, rightCode a.2} : Set (Set (Set X))) =
      {leftCode b.1, rightCode b.2} at h
    have ha : leftCode a.1 ∈ ({leftCode b.1, rightCode b.2} : Set (Set (Set X))) := by
      rw [← h]; simp
    have hb : rightCode a.2 ∈ ({leftCode b.1, rightCode b.2} : Set (Set (Set X))) := by
      rw [← h]; simp
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · exact absurd hb.symm (left_ne_right b.1 a.2)
      · exact Prod.ext (leftCode_injective ha) (rightCode_injective hb)
    · exact absurd ha (left_ne_right a.1 b.2)

end Pairing

/-- A function is determined by its graph. -/
def graphSet {α β : Type u} : (α → β) ↪ Set (α × β) where
  toFun f := {p | p.2 = f p.1}
  inj' f g h := by
    funext a
    have hmem : (a, f a) ∈ {p : α × β | p.2 = f p.1} := rfl
    rw [show {p : α × β | p.2 = f p.1} = {p | p.2 = g p.1} from h] at hmem
    exact hmem

/-- A function space between two types at a level costs four more levels: one
for the graph, three for the pairs it is made of. -/
def graphEmb {α β X : Type u} (ea : α ↪ X) (eb : β ↪ X) :
    (α → β) ↪ PowerLevel X 4 :=
  graphSet.trans (imageEmb ((ea.prodMap eb).trans Pairing.pairEmb))

/-- An embedding is an equivalence onto its range. This is what turns a type
into a code: pick a level it embeds into, and take the image. -/
noncomputable def rangeEquiv {α β : Type u} (e : α ↪ β) : α ≃ Set.range e :=
  Equiv.ofInjective e e.injective

end Nucleus.HolOmega
