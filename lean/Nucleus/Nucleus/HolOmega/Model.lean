import Mathlib.Data.Nat.Find
import Nucleus.HolOmega.Beth
import Nucleus.HolOmega.Kernel

/-!
# A model of the kernel universe

The beth tower gives `Kernel.Universe` an instance, so `EqTm.sound` and
`Derives.sound` stop being statements about nothing.

The only thing to check is that `∀` lands somewhere. Kind values at rank `r`
are built from the codes of rank at most `r`, and those are bounded: they are
the bounded subsets of block `r`, so they all fit in block `r + 1`. A product
over them with fibres of rank at most `s` is therefore a code again, at rank
`max r s + 2`. Nothing else moves: `→` and `Sub` leave rank alone.

`consistent` is the point of the exercise — `false` is not derivable, and with
a model in hand that is a statement about something.
-/

namespace Nucleus.HolOmega.Beth

open Nucleus.HolOmega.Kernel

-- `model` is applied explicitly rather than found by instance search, so the
-- semireducible projection this warns about is what we want.
set_option warn.classDefReducibility false

/-- Kind values at rank `r` are bounded, by induction on the kind: the base
case is the codes below `r`, and every arrow is a function space, which a block
absorbs. -/
def kindValFits (r : Nat) :
    (K : HolOmega.Kind) → Fits (r + 1) (KindVal Code.rank r K)
  | .star => CodeLE.fits r
  | .arr K L => (kindValFits r K).arrow (kindValFits r L)

/-- Kind values are never empty: `boolCode` has rank `0` so it inhabits every
`CodeLE`, and function kinds inherit. A dependent sum needs this, since every
code must be inhabited. -/
theorem kindValNonempty (r : Nat) :
    ∀ K : HolOmega.Kind, Nonempty (KindVal Code.rank r K)
  | .star => ⟨⟨boolCode, Nat.zero_le r⟩⟩
  | .arr _ L => (kindValNonempty r L).elim fun y => ⟨fun _ => y⟩

/-- The least uniform rank bound for a family of codes.  Choosing it inside
the model makes the resulting product and sum codes independent of which
bound a formation derivation happened to exhibit. -/
noncomputable def leastBound {I : Type} (F : I → Code)
    (h : ∃ s, ∀ X, (F X).rank ≤ s) : Nat := by
  classical
  exact Nat.find h

theorem rank_le_leastBound {I : Type} (F : I → Code)
    (h : ∃ s, ∀ X, (F X).rank ≤ s) (X : I) :
    (F X).rank ≤ leastBound F h := by
  classical
  exact Nat.find_spec h X

theorem leastBound_le {I : Type} (F : I → Code)
    (h : ∃ s, ∀ X, (F X).rank ≤ s) {s : Nat}
    (hs : ∀ X, (F X).rank ≤ s) : leastBound F h ≤ s := by
  classical
  exact Nat.find_min' h hs

/-- The beth tower as a HOLω universe. -/
noncomputable def model : Universe.{0} where
  Code := Code
  El := El
  inhabited _ := inferInstance
  rank := Code.rank
  boolCode := boolCode
  boolEquiv := boolEquiv
  rank_boolCode := rfl
  arr := arr
  arrEquiv := arrEquiv
  rank_arr A B := le_of_eq (rank_arr A B)
  subCode := subCode
  subEquiv := subEquiv
  rank_subCode A P := le_of_eq (rank_subCode A P)
  allCode K r F h := piCode (kindValFits r K) F (rank_le_leastBound F h)
  allEquiv K r F h := piEquiv (kindValFits r K) F (rank_le_leastBound F h)
  rank_allCode _K r F h s hs := by
    rw [rank_piCode]
    have := leastBound_le F h hs
    omega
  exCode K r F h := sigmaCode (kindValFits r K) (kindValNonempty r K) F
    (rank_le_leastBound F h)
  exEquiv K r F h := sigmaEquiv (kindValFits r K) (kindValNonempty r K) F
    (rank_le_leastBound F h)
  rank_exCode _K r F h s hs := by
    rw [rank_sigmaCode]
    have := leastBound_le F h hs
    omega

/-- The bottom Beth block contains the ordinary natural numbers. -/
def natFits : Fits 0 Nat := ⟨0, Block.ofNat 0⟩

/-- Rank-zero standard individuals for the Beth model. -/
noncomputable def natCode : Code := Code.of natFits inferInstance

noncomputable def natEquiv : El natCode ≃ Nat :=
  Code.ofEquiv natFits inferInstance

noncomputable instance modelUniverseWithNat : UniverseWithNat model where
  indCode := natCode
  indEquiv := natEquiv
  rank_indCode := Code.rank_of _ _

/-- Nothing derives `false`. Vacuous for an arbitrary universe; `consistent`
discharges it against the tower. -/
theorem not_derives_false (U : Universe) :
    ¬ Derives U (Δ := []) (Γ := []) [] (Tm.boolCode U false) := by
  intro h
  have hfalse := h.sound U PUnit.unit PUnit.unit (by simp)
  simp [Tm.boolCode] at hfalse

/-- The proof calculus is consistent. -/
theorem consistent :
    ¬ Derives model (Δ := []) (Γ := []) [] (Tm.boolCode model false) :=
  not_derives_false model

end Nucleus.HolOmega.Beth
