import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-!
# Immutable roots and checked equality transport

Syntactic/conversion unions select the signed minimum. Semantic unions prefer
a resident literal among positive roots, then the signed minimum. A negative
root is immutable, so two distinct negative roots cannot be merged. That
operational rejection is not a proof
of semantic inequality. A successful union transports an equality already
established by the kernel; it does not manufacture the equality premise.

This models the root-redirect authority boundary. Rust's traversal and path
compression are not identified with this executable recursive lookup.
-/

namespace Nucleus.Hol.Ethane.LiteralRoots

abbrev Parents := Int → Int

def Valid (reference : Int) : Prop :=
  reference ≠ 0 ∧ -(2 ^ 31 - 1) < reference ∧ reference < 2 ^ 31 - 1

instance (reference : Int) : Decidable (Valid reference) := inferInstanceAs
  (Decidable (reference ≠ 0 ∧ -(2 ^ 31 - 1) < reference ∧ reference < 2 ^ 31 - 1))

def Immutable (parents : Parents) : Prop :=
  ∀ reference, reference < 0 → parents reference = reference

def Sound {α : Type} (meaning : Int → α) (parents : Parents) : Prop :=
  ∀ reference, meaning (parents reference) = meaning reference

def root (parents : Parents) : Nat → Int → Option Int
  | 0, _ => none
  | fuel + 1, reference =>
      if reference < 0 ∨ parents reference = reference then some reference
      else root parents fuel (parents reference)

theorem root_negative (parents : Parents) (fuel : Nat) (reference : Int)
    (negative : reference < 0) : root parents (fuel + 1) reference = some reference := by
  simp [root, negative]

theorem root_sound {α : Type} {meaning : Int → α} {parents : Parents}
    (sound : Sound meaning parents) {fuel : Nat} {reference result : Int}
    (found : root parents fuel reference = some result) : meaning result = meaning reference := by
  induction fuel generalizing reference with
  | zero => simp [root] at found
  | succ fuel ih =>
      unfold root at found
      split at found
      · cases found
        rfl
      · exact (ih found).trans (sound reference)

def redirect (parents : Parents) (source target : Int) : Parents :=
  fun reference => if reference = source then target else parents reference

private theorem redirect_sound {α : Type} {meaning : Int → α} {parents : Parents}
    {source target : Int} (sound : Sound meaning parents)
    (equal : meaning target = meaning source) :
    Sound meaning (redirect parents source target) := by
  intro reference
  unfold redirect
  split
  · rename_i same
    subst reference
    exact equal
  · exact sound reference

def unionRoots (parents : Parents) (left right : Int) : Option Parents :=
  if ¬Valid left ∨ ¬Valid right ∨ parents left ≠ left ∨ parents right ≠ right then none
  else if left = right then some parents
  else if left < 0 ∧ right < 0 then none
  else some (redirect parents (max left right) (min left right))

theorem union_negative_conflict (parents : Parents) (left right : Int)
    (leftNegative : left < 0) (rightNegative : right < 0) (different : left ≠ right) :
    unionRoots parents left right = none := by
  simp [unionRoots, different, leftNegative, rightNegative]

theorem union_preserves_immutable {parents after : Parents} {left right : Int}
    (immutable : Immutable parents) (merged : unionRoots parents left right = some after) :
    Immutable after := by
  unfold unionRoots at merged
  split at merged
  · contradiction
  · rename_i accepted
    split at merged
    · cases merged
      exact immutable
    · split at merged
      · contradiction
      · rename_i compatible
        cases merged
        intro reference negative
        have different : reference ≠ max left right := by
          simp only [not_or, not_not] at accepted
          rcases accepted with ⟨leftValid, rightValid, _⟩
          have leftNonzero := leftValid.1
          have rightNonzero := rightValid.1
          omega
        simp [redirect, different, immutable reference negative]

/-- The required equality is checked evidence, not inferred from reference IDs. -/
theorem union_preserves_sound {α : Type} {meaning : Int → α} {parents after : Parents}
    {left right : Int} (sound : Sound meaning parents) (equal : meaning left = meaning right)
    (merged : unionRoots parents left right = some after) : Sound meaning after := by
  unfold unionRoots at merged
  split at merged
  · contradiction
  · split at merged
    · cases merged
      exact sound
    · split at merged
      · contradiction
      · cases merged
        intro reference
        unfold redirect
        split
        · rename_i same
          subst reference
          by_cases order : left ≤ right
          · simpa only [Int.min_eq_left order, Int.max_eq_right order] using equal
          · have order : right ≤ left := by omega
            simpa only [Int.min_eq_right order, Int.max_eq_left order] using equal.symm
        · exact sound reference

/-- Rust's semantic cache priority: global, then resident literal, then signed ID. -/
def semanticWinner (literal : Int → Bool) (left right : Int) : Int :=
  if left < 0 ∨ right < 0 then min left right
  else if literal left && !literal right then left
  else if literal right && !literal left then right
  else min left right

theorem semanticWinner_member (literal : Int → Bool) (left right : Int) :
    semanticWinner literal left right = left ∨ semanticWinner literal left right = right := by
  unfold semanticWinner
  repeat' split
  all_goals first | exact Or.inl rfl | exact Or.inr rfl |
    { by_cases order : left ≤ right
      · exact Or.inl (Int.min_eq_left order)
      · exact Or.inr (Int.min_eq_right (by omega)) }

def unionSemanticRoots (literal : Int → Bool) (parents : Parents) (left right : Int) :
    Option Parents :=
  if ¬Valid left ∨ ¬Valid right ∨ parents left ≠ left ∨ parents right ≠ right then none
  else if left = right then some parents
  else if left < 0 ∧ right < 0 then none
  else
    let winner := semanticWinner literal left right
    some (redirect parents (if winner = left then right else left) winner)

theorem semantic_union_preserves_sound {α : Type} {meaning : Int → α}
    {parents after : Parents} {left right : Int} (literal : Int → Bool)
    (sound : Sound meaning parents) (equal : meaning left = meaning right)
    (merged : unionSemanticRoots literal parents left right = some after) :
    Sound meaning after := by
  unfold unionSemanticRoots at merged
  split at merged
  · cases merged
  · split at merged
    · cases merged
      exact sound
    · split at merged
      · cases merged
      · cases merged
        apply redirect_sound sound
        rcases semanticWinner_member literal left right with winner | winner
        · simp only [winner, ↓reduceIte]
          exact equal
        · by_cases same : right = left
          · subst right
            simp only [winner, ↓reduceIte]
          · simp only [winner, same, ↓reduceIte]
            exact equal.symm

theorem semantic_union_preserves_immutable {parents after : Parents} {left right : Int}
    (literal : Int → Bool) (immutable : Immutable parents)
    (merged : unionSemanticRoots literal parents left right = some after) : Immutable after := by
  unfold unionSemanticRoots at merged
  split at merged
  · cases merged
  · rename_i accepted
    split at merged
    · cases merged
      exact immutable
    · split at merged
      · cases merged
      · rename_i compatible
        cases merged
        intro reference negative
        have different : reference ≠
            (if semanticWinner literal left right = left then right else left) := by
          simp only [not_or, not_not] at accepted
          rcases accepted with ⟨leftValid, rightValid, _⟩
          have leftNonzero := leftValid.1
          have rightNonzero := rightValid.1
          by_cases global : left < 0 ∨ right < 0
          · simp only [semanticWinner, global, ↓reduceIte]
            split <;> omega
          · have leftPositive : 0 < left := by omega
            have rightPositive : 0 < right := by omega
            split <;> omega
        simp only [redirect, different, ↓reduceIte]
        exact immutable reference negative

/-- A cache conflict gives no logical disequality: even a constant meaning is compatible. -/
example : unionRoots (fun reference => reference) (-2) (-3) = none ∧
    (fun _ : Int => True) (-2) = (fun _ : Int => True) (-3) := by decide

end Nucleus.Hol.Ethane.LiteralRoots
