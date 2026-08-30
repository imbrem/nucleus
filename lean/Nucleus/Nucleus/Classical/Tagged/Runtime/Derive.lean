import Nucleus.Classical.Tagged.Equality
import Nucleus.Classical.Tagged.Rules

/-!
# Canonical binary derivations for the tagged runtime

These executable rules operate only on decoded tagged syntax.  The LCF kernel
re-encodes their result with the canonical packer; no packed pointer or subtree
is borrowed across theorem arenas.
-/

namespace Nucleus.Classical.Tagged.Runtime.Derive

open Nucleus.Classical
open Nucleus.Classical.Tagged

/-- Remove the first structural occurrence of `target`. -/
def eraseFirst? [DecidableEq α] (target : α) : List α → Option (List α)
  | [] => none
  | value :: values =>
      if value = target then some values
      else
        match eraseFirst? target values with
        | none => none
        | some result => some (value :: result)

/-- Successful removal differs only by moving the removed occurrence to the
end. -/
theorem eraseFirst?_perm_last [DecidableEq α] {target : α}
    {before after : List α} (erased : eraseFirst? target before = some after) :
    before.Perm (after ++ [target]) := by
  induction before generalizing after with
  | nil => simp [eraseFirst?] at erased
  | cons value values ih =>
      by_cases equal : value = target
      · subst value
        rw [eraseFirst?, if_pos rfl] at erased
        have afterEqual : values = after := Option.some.inj erased
        subst after
        simpa using
          (List.perm_append_comm : ([target] ++ values).Perm (values ++ [target]))
      · cases recursive : eraseFirst? target values with
        | none => simp [eraseFirst?, equal, recursive] at erased
        | some result =>
            rw [eraseFirst?, if_neg equal, recursive] at erased
            have afterEqual : value :: result = after := Option.some.inj erased
            subst after
            exact (ih recursive).cons value

/-- Successful removal differs only by moving the removed occurrence to the
front. -/
theorem eraseFirst?_perm_front [DecidableEq α] {target : α}
    {before after : List α} (erased : eraseFirst? target before = some after) :
    before.Perm (target :: after) := by
  induction before generalizing after with
  | nil => simp [eraseFirst?] at erased
  | cons value values ih =>
      by_cases equal : value = target
      · subst value
        rw [eraseFirst?, if_pos rfl] at erased
        have afterEqual : values = after := Option.some.inj erased
        subst after
        exact List.Perm.refl _
      · cases recursive : eraseFirst? target values with
        | none => simp [eraseFirst?, equal, recursive] at erased
        | some result =>
            rw [eraseFirst?, if_neg equal, recursive] at erased
            have afterEqual : value :: result = after := Option.some.inj erased
            subst after
            exact ((ih recursive).cons value).trans
              (List.Perm.swap value target result).symm

/-- Decode a positive conjunction root. -/
def positiveAnd? : Formula Nat → Option (List (Formula Nat))
  | .and false children => some children
  | _ => none

/-- Decode a positive disjunction root. -/
def positiveOr? : Formula Nat → Option (List (Formula Nat))
  | .or false children => some children
  | _ => none

theorem positiveAnd?_result {formula : Formula Nat} {children : List (Formula Nat)}
    (decoded : positiveAnd? formula = some children) :
    formula = .and false children := by
  cases formula with
  | literal _ | or _ _ | sat _ _ => simp [positiveAnd?] at decoded
  | and negative values =>
      cases negative with
      | true => simp [positiveAnd?] at decoded
      | false =>
          have equal : values = children := by simpa [positiveAnd?] using Option.some.inj decoded
          subst children
          rfl

theorem positiveOr?_result {formula : Formula Nat} {children : List (Formula Nat)}
    (decoded : positiveOr? formula = some children) :
    formula = .or false children := by
  cases formula with
  | literal _ | and _ _ | sat _ _ => simp [positiveOr?] at decoded
  | or negative values =>
      cases negative with
      | true => simp [positiveOr?] at decoded
      | false =>
          have equal : values = children := by simpa [positiveOr?] using Option.some.inj decoded
          subst children
          rfl

private theorem sequent_eq {left right : Sequent Nat}
    (premise : left.premise = right.premise)
    (conclusion : left.conclusion = right.conclusion) : left = right := by
  cases left
  cases right
  simp_all

/-- Cut the first matching pivot from the left conclusion and right premise.
Both sequents must use positive root conjunction/disjunction nodes. -/
def cutTarget? (pivot : Formula Nat) (left right : Sequent Nat) :
    Option (Sequent Nat) := do
  let leftPrem ← positiveAnd? left.premise
  let leftConc ← positiveOr? left.conclusion
  let rightPrem ← positiveAnd? right.premise
  let rightConc ← positiveOr? right.conclusion
  let leftConc ← eraseFirst? pivot leftConc
  let rightPrem ← eraseFirst? pivot rightPrem
  some ⟨.and false (leftPrem ++ rightPrem), .or false (leftConc ++ rightConc)⟩

/-- Resolve the first matching pivot and complement from two conclusions.
Both sequents must use positive root conjunction/disjunction nodes. -/
def resolveTarget? (pivot : Formula Nat) (left right : Sequent Nat) :
    Option (Sequent Nat) := do
  let leftPrem ← positiveAnd? left.premise
  let leftConc ← positiveOr? left.conclusion
  let rightPrem ← positiveAnd? right.premise
  let rightConc ← positiveOr? right.conclusion
  let leftConc ← eraseFirst? pivot leftConc
  let rightConc ← eraseFirst? pivot.neg rightConc
  some ⟨.and false (leftPrem ++ rightPrem), .or false (leftConc ++ rightConc)⟩

theorem cutTarget?_result {pivot : Formula Nat} {left right result : Sequent Nat}
    (derived : cutTarget? pivot left right = some result) :
    ∃ leftPrem leftConc rightPrem rightConc leftRest rightRest,
      left = ⟨.and false leftPrem, .or false leftConc⟩ ∧
      right = ⟨.and false rightPrem, .or false rightConc⟩ ∧
      eraseFirst? pivot leftConc = some leftRest ∧
      eraseFirst? pivot rightPrem = some rightRest ∧
      result = ⟨.and false (leftPrem ++ rightRest),
        .or false (leftRest ++ rightConc)⟩ := by
  unfold cutTarget? at derived
  cases leftPremDecoded : positiveAnd? left.premise with
  | none => simp [leftPremDecoded] at derived
  | some leftPrem =>
    rw [leftPremDecoded] at derived
    cases leftConcDecoded : positiveOr? left.conclusion with
    | none => simp [leftConcDecoded] at derived
    | some leftConc =>
      rw [leftConcDecoded] at derived
      cases rightPremDecoded : positiveAnd? right.premise with
      | none => simp [rightPremDecoded] at derived
      | some rightPrem =>
        rw [rightPremDecoded] at derived
        cases rightConcDecoded : positiveOr? right.conclusion with
        | none => simp [rightConcDecoded] at derived
        | some rightConc =>
          rw [rightConcDecoded] at derived
          change (do
            let leftRest ← eraseFirst? pivot leftConc
            let rightRest ← eraseFirst? pivot rightPrem
            some (⟨.and false (leftPrem ++ rightRest),
              .or false (leftRest ++ rightConc)⟩ : Sequent Nat)) =
                some result at derived
          cases leftErased : eraseFirst? pivot leftConc with
          | none => simp [leftErased] at derived
          | some leftRest =>
            rw [leftErased] at derived
            cases rightErased : eraseFirst? pivot rightPrem with
            | none => simp [rightErased] at derived
            | some rightRest =>
              rw [rightErased] at derived
              have resultEqual : result =
                  ⟨.and false (leftPrem ++ rightRest),
                    .or false (leftRest ++ rightConc)⟩ :=
                (Option.some.inj derived).symm
              exact ⟨leftPrem, leftConc, rightPrem, rightConc, leftRest,
                rightRest,
                sequent_eq (positiveAnd?_result leftPremDecoded)
                  (positiveOr?_result leftConcDecoded),
                sequent_eq (positiveAnd?_result rightPremDecoded)
                  (positiveOr?_result rightConcDecoded),
                leftErased, rightErased, resultEqual⟩

theorem resolveTarget?_result {pivot : Formula Nat}
    {left right result : Sequent Nat}
    (derived : resolveTarget? pivot left right = some result) :
    ∃ leftPrem leftConc rightPrem rightConc leftRest rightRest,
      left = ⟨.and false leftPrem, .or false leftConc⟩ ∧
      right = ⟨.and false rightPrem, .or false rightConc⟩ ∧
      eraseFirst? pivot leftConc = some leftRest ∧
      eraseFirst? pivot.neg rightConc = some rightRest ∧
      result = ⟨.and false (leftPrem ++ rightPrem),
        .or false (leftRest ++ rightRest)⟩ := by
  unfold resolveTarget? at derived
  cases leftPremDecoded : positiveAnd? left.premise with
  | none => simp [leftPremDecoded] at derived
  | some leftPrem =>
    rw [leftPremDecoded] at derived
    cases leftConcDecoded : positiveOr? left.conclusion with
    | none => simp [leftConcDecoded] at derived
    | some leftConc =>
      rw [leftConcDecoded] at derived
      cases rightPremDecoded : positiveAnd? right.premise with
      | none => simp [rightPremDecoded] at derived
      | some rightPrem =>
        rw [rightPremDecoded] at derived
        cases rightConcDecoded : positiveOr? right.conclusion with
        | none => simp [rightConcDecoded] at derived
        | some rightConc =>
          rw [rightConcDecoded] at derived
          change (do
            let leftRest ← eraseFirst? pivot leftConc
            let rightRest ← eraseFirst? pivot.neg rightConc
            some (⟨.and false (leftPrem ++ rightPrem),
              .or false (leftRest ++ rightRest)⟩ : Sequent Nat)) =
                some result at derived
          cases leftErased : eraseFirst? pivot leftConc with
          | none => simp [leftErased] at derived
          | some leftRest =>
            rw [leftErased] at derived
            cases rightErased : eraseFirst? pivot.neg rightConc with
            | none => simp [rightErased] at derived
            | some rightRest =>
              rw [rightErased] at derived
              have resultEqual : result =
                  ⟨.and false (leftPrem ++ rightPrem),
                    .or false (leftRest ++ rightRest)⟩ :=
                (Option.some.inj derived).symm
              exact ⟨leftPrem, leftConc, rightPrem, rightConc, leftRest,
                rightRest,
                sequent_eq (positiveAnd?_result leftPremDecoded)
                  (positiveOr?_result leftConcDecoded),
                sequent_eq (positiveAnd?_result rightPremDecoded)
                  (positiveOr?_result rightConcDecoded),
                leftErased, rightErased, resultEqual⟩

theorem cutTarget?_entailsAt {pivot : Formula Nat} {left right result : Sequent Nat}
    (derived : cutTarget? pivot left right = some result)
    (known : PartialAssignment Nat) (leftHolds : left.EntailsAt known)
    (rightHolds : right.EntailsAt known) : result.EntailsAt known := by
  obtain ⟨leftPrem, leftConc, rightPrem, rightConc, leftRest, rightRest,
    rfl, rfl, leftErased, rightErased, rfl⟩ := cutTarget?_result derived
  have leftReordered := Sequent.EntailsAt.rhsOrPermute known
    (eraseFirst?_perm_last leftErased) leftHolds
  have rightReordered := Sequent.EntailsAt.lhsAndPermute known
    (eraseFirst?_perm_front rightErased) rightHolds
  exact Sequent.EntailsAt.cut known leftPrem rightRest leftRest
    rightConc pivot leftReordered rightReordered

theorem resolveTarget?_entailsAt {pivot : Formula Nat}
    {left right result : Sequent Nat}
    (derived : resolveTarget? pivot left right = some result)
    (known : PartialAssignment Nat) (leftHolds : left.EntailsAt known)
    (rightHolds : right.EntailsAt known) : result.EntailsAt known := by
  obtain ⟨leftPrem, leftConc, rightPrem, rightConc, leftRest, rightRest,
    rfl, rfl, leftErased, rightErased, rfl⟩ := resolveTarget?_result derived
  have leftReordered := Sequent.EntailsAt.rhsOrPermute known
    (eraseFirst?_perm_last leftErased) leftHolds
  have rightReordered := Sequent.EntailsAt.rhsOrPermute known
    (eraseFirst?_perm_last rightErased) rightHolds
  exact Sequent.EntailsAt.resolve known leftPrem rightPrem
    leftRest rightRest pivot leftReordered rightReordered

/-! Small executable examples pin first-occurrence removal and the exact
decoded syntax produced by the binary rules. -/

private def p : Formula Nat := .atom 1
private def q : Formula Nat := .atom 2
private def r : Formula Nat := .atom 3
private theorem q_ne_p : q ≠ p := by simp [q, p, Formula.atom]

example : eraseFirst? p [q, p, p] = some [q, p] := by
  simp [eraseFirst?, q_ne_p]

example : cutTarget? p
    ⟨.and false [], .or false [q, p]⟩
  ⟨.and false [p, r], .or false [q]⟩ =
    some ⟨.and false [r], .or false [q, q]⟩ := by
  simp [cutTarget?, positiveAnd?, positiveOr?, eraseFirst?, q_ne_p]

example : resolveTarget? p
    ⟨.and false [q], .or false [p, r]⟩
    ⟨.and false [r], .or false [p.neg, q]⟩ =
    some ⟨.and false [q, r], .or false [r, q]⟩ := by
  simp [resolveTarget?, positiveAnd?, positiveOr?, eraseFirst?]

end Nucleus.Classical.Tagged.Runtime.Derive
