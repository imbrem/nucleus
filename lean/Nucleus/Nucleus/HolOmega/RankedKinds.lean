import Mathlib
import Nucleus.HolOmega.Model

/-!
# Whole higher-kind values and rank slices

An isolated prototype for ranking *all* kinds.  It does not change the current
kernel.  `WholeVal` gives the unrestricted simple-kind hierarchy; `AtRank`
states preservation of a rank slice.  `Slice` is the executable presentation
used by the current kernel, with variance-correct restriction and extension.
-/

universe u

namespace Nucleus.HolOmega.RankedKinds

open Kernel

def WholeVal (U : Universe.{u}) : Kind → Type u
  | .star => U.Code
  | .arr K L => WholeVal U K → WholeVal U L

def PreservesSlice (U : Universe.{u}) (r : Nat) : (K : Kind) → WholeVal U K → Prop
  | .star, c => U.rank c ≤ r
  | .arr K L, f => ∀ x, PreservesSlice U r K x → PreservesSlice U r L (f x)

theorem PreservesSlice.star_mono (hrs : r ≤ s) {c : WholeVal U .star}
    (hc : PreservesSlice U r .star c) : PreservesSlice U s .star c := hc.trans hrs

variable (U : Universe.{u})

/-- Rank slices are exactly the current kernel's `KindVal`. -/
abbrev Slice (r : Nat) (K : Kind) : Type u := KindVal U.rank r K

theorem slice_eq_kernel : Slice U r K = KindVal U.rank r K := rfl

def defaultSlice (U : Universe.{u}) : (r : Nat) → (K : Kind) → Slice U r K
  | r, .star => ⟨U.boolCode, by simp [U.rank_boolCode]⟩
  | r, .arr K L => fun _ => defaultSlice U r L

mutual
  noncomputable def extend (hrs : r ≤ s) : (K : Kind) → Slice U r K → Slice U s K
    | .star, c => ⟨c.val, c.property.trans hrs⟩
    | .arr K L, f => fun x => extend hrs L (f (restrict hrs K x))

  noncomputable def restrict (hrs : r ≤ s) : (K : Kind) → Slice U s K → Slice U r K
    | .star, c => by
        classical
        exact if h : U.rank c.val ≤ r then ⟨c.val, h⟩ else defaultSlice U r .star
    | .arr K L, f => fun x => restrict hrs L (f (extend hrs K x))
end

@[simp] theorem restrict_extend (hrs : r ≤ s) :
    ∀ (K : Kind) (x : Slice U r K), restrict U hrs K (extend U hrs K x) = x := by
  intro K
  induction K with
  | star =>
    intro x
    apply Subtype.ext
    simp [extend, restrict, x.property]
  | arr K L ihK ihL =>
    intro f
    funext x
    simp only [extend, restrict]
    rw [ihK, ihL]

/-- Application after aligning both ranks at their maximum. -/
noncomputable def appMax (F : Slice U r₁ (.arr K L)) (X : Slice U r₂ K) :
    Slice U (max r₁ r₂) L :=
  extend U (Nat.le_max_left _ _) (.arr K L) F
    (extend U (Nat.le_max_right _ _) K X)

/-- Base slices embed in whole values and satisfy `AtRank`. -/
def Slice.toWholeStar (x : Slice U r .star) : WholeVal U .star := x.val

theorem Slice.toWholeStar_atRank (x : Slice U r .star) :
    PreservesSlice U r .star (Slice.toWholeStar U x) := x.property

/-- At base kind, the whole-value predicate and the existing kernel slice are
literally the same subtype data. -/
def wholeStarEquiv : {c : WholeVal U .star // PreservesSlice U r .star c} ≃ Slice U r .star :=
  Equiv.refl _

/-!
`PreservesSlice` alone is intentionally not called `AtRank`: at arrow kinds it
is not monotone, since a larger rank admits new inputs.  The corrected whole
domain is a coherent family of slices with both restriction and canonical
extension laws. -/

structure CoherentVal (K : Kind) where
  slice : ∀ r, Slice U r K
  restrict_natural : ∀ {r s} (hrs : r ≤ s),
    restrict U hrs K (slice s) = slice r
  extend_natural : ∀ {r s} (hrs : r ≤ s),
    extend U hrs K (slice r) = slice s

/-- A rank view retains the coherent whole value; only its observation level
changes.  This is the restricted-graph presentation needed for higher-kind
subsumption. -/
structure AtRank (r : Nat) (K : Kind) where
  whole : CoherentVal U K

def AtRank.observe (x : AtRank U r K) : Slice U r K := x.whole.slice r

def down (r : Nat) (x : CoherentVal U K) : AtRank U r K := ⟨x⟩
def up (x : AtRank U r K) : CoherentVal U K := x.whole

@[simp] theorem up_down (r : Nat) (x : CoherentVal U K) : up U (down U r x) = x := rfl
@[simp] theorem down_up (x : AtRank U r K) : down U r (up U x) = x := by cases x; rfl

/-- All-kind rank subsumption is monotone because both views share the same
coherent whole value. -/
def subsume (hrs : r ≤ s) (x : AtRank U r K) : AtRank U s K := ⟨x.whole⟩

@[simp] theorem subsume_observe (hrs : r ≤ s) (x : AtRank U r K) :
    (subsume U hrs x).observe = extend U hrs K x.observe := by
  exact (x.whole.extend_natural hrs).symm

/-- Coherent application is pointwise on every slice. -/
noncomputable def coherentApp (F : CoherentVal U (.arr K L))
    (X : CoherentVal U K) : CoherentVal U L where
  slice r := F.slice r (X.slice r)
  restrict_natural := by
    intro r s hrs
    have hF := F.restrict_natural hrs
    have hX := X.extend_natural hrs
    change restrict U hrs L (F.slice s (X.slice s)) = F.slice r (X.slice r)
    rw [← hX]
    have happ := congrFun hF (X.slice r)
    simpa [restrict, restrict_extend] using happ
  extend_natural := by
    intro r s hrs
    have hF := F.extend_natural hrs
    have hX := X.restrict_natural hrs
    change extend U hrs L (F.slice r (X.slice r)) = F.slice s (X.slice s)
    rw [← hX]
    have happ := congrFun hF (X.slice s)
    simpa [extend, restrict_extend] using happ

def coherentAppAt (F : AtRank U r₁ (.arr K L)) (X : AtRank U r₂ K) :
    AtRank U (max r₁ r₂) L := down U _ (coherentApp U F.whole X.whole)

/-- Beth's existing model supplies the prototype maps directly. -/
example : Slice Beth.model r K = KindVal Beth.model.rank r K := rfl

/-!
## Exact `+1` quantifier ranks

The slice redesign itself does not prove an exact `max r s + 1` bound.
`Beth.piCode`/`sigmaCode` place their carrier in block `max r s + 1`, while a
`Code`'s rank is the successor of its block, yielding the existing `+2`.
Closing the gap requires a new cardinal-closure theorem constructing the
dependent product/sum in a block at most `max r s`, or a changed code/rank
convention.  Restriction/extension laws cannot alter that cardinal fact.
-/

end Nucleus.HolOmega.RankedKinds
