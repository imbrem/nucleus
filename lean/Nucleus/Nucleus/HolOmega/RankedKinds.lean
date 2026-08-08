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

def AtRank (U : Universe.{u}) (r : Nat) : (K : Kind) → WholeVal U K → Prop
  | .star, c => U.rank c ≤ r
  | .arr K L, f => ∀ x, AtRank U r K x → AtRank U r L (f x)

theorem AtRank.star_mono (hrs : r ≤ s) {c : WholeVal U .star}
    (hc : AtRank U r .star c) : AtRank U s .star c := hc.trans hrs

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
    AtRank U r .star (Slice.toWholeStar U x) := x.property

/-- At base kind, the whole-value predicate and the existing kernel slice are
literally the same subtype data. -/
def wholeStarEquiv : {c : WholeVal U .star // AtRank U r .star c} ≃ Slice U r .star :=
  Equiv.refl _

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
