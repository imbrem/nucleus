import Nucleus.Hol.Ethane.LogicalOpcode

/-!
# Canonical signed classical sequents

This file specifies the semantic contract for the compact theorem table.  A
`PropId` is a nonzero signed integer.  Deliberately following the kernel wire
contract, a negative integer denotes the positive proposition and a positive
integer denotes its negation.  `PropSet` is a finite set, so normalization is
intrinsically sorted and duplicate-free when serialized with `toList`.
-/

namespace Nucleus.Hol.Ethane.ClassicalSequent

open Nucleus.Hol.Ethane

/-- A signed reference to a Boolean term.  Negative is positive polarity. -/
abbrev PropId := { value : Int // value ≠ 0 }

/-- The referenced one-based term index, with polarity erased. -/
def PropId.ref (id : PropId) : Nat := id.val.natAbs

/-- Flip polarity without changing the referenced term. -/
def PropId.neg (id : PropId) : PropId :=
  ⟨-id.val, neg_ne_zero.mpr id.property⟩

@[simp] theorem PropId.neg_val (id : PropId) : id.neg.val = -id.val := rfl

@[simp] theorem PropId.neg_neg (id : PropId) : id.neg.neg = id := by
  apply Subtype.ext
  simp [PropId.neg]

/-- Canonical proposition sets. `Finset.sort` supplies their unique wire list. -/
abbrev PropSet := Finset PropId

/-- The unique sorted, duplicate-free list representation of a proposition set. -/
def PropSet.toList (set : PropSet) : List PropId := set.sort (· ≤ ·)

theorem PropSet.toList_sorted (set : PropSet) : set.toList.SortedLT :=
  Finset.sortedLT_sort set

theorem PropSet.toList_nodup (set : PropSet) : set.toList.Nodup :=
  Finset.sort_nodup set (· ≤ ·)

@[simp] theorem PropSet.mem_toList (id : PropId) (set : PropSet) :
    id ∈ set.toList ↔ id ∈ set := Finset.mem_sort _

theorem PropSet.toList_injective : Function.Injective PropSet.toList := by
  intro left right equal
  ext id
  have membership : id ∈ left.toList ↔ id ∈ right.toList := by rw [equal]
  simpa only [PropSet.mem_toList] using membership

/-- A compact theorem row: `prem |- conc`. -/
structure Sequent where
  prem : PropSet
  conc : PropSet
  deriving DecidableEq

/-- A valuation assigns truth to the underlying (unsigned) Boolean term refs. -/
abbrev Valuation := Nat → Prop

/-- Interpret the intentionally inverted signed representation. -/
def PropId.eval (valuation : Valuation) (id : PropId) : Prop :=
  if id.val < 0 then valuation id.ref else ¬valuation id.ref

@[simp] theorem PropId.eval_neg (valuation : Valuation) (id : PropId) :
    id.neg.eval valuation ↔ ¬id.eval valuation := by
  by_cases negative : id.val < 0
  · have notNegative : ¬ id.neg.val < 0 := by simp [PropId.neg]; omega
    simp only [PropId.eval]
    have sameRef : id.neg.ref = id.ref := by simp [PropId.ref, PropId.neg]
    rw [if_neg notNegative, if_pos negative, sameRef]
  · have idPositive : 0 < id.val := by
      exact lt_of_le_of_ne (Int.le_of_not_gt negative) (Ne.symm id.property)
    have negNegative : id.neg.val < 0 := by simp [PropId.neg]; omega
    simp only [PropId.eval]
    have sameRef : id.neg.ref = id.ref := by simp [PropId.ref, PropId.neg]
    rw [if_pos negNegative, if_neg negative, sameRef]
    exact Classical.not_not.symm

/-- Classical validity of the compact sequent. -/
def Holds (valuation : Valuation) (sequent : Sequent) : Prop :=
  (∀ id ∈ sequent.prem, id.eval valuation) → ∃ id ∈ sequent.conc, id.eval valuation

/-- Kernel-table soundness means every live theorem row is classically valid. -/
def Sound (sequent : Sequent) : Prop := ∀ valuation, Holds valuation sequent

theorem identity (id : PropId) : Sound ⟨{id}, {id}⟩ := by
  intro valuation premises
  exact ⟨id, by simp, premises id (by simp)⟩

theorem weaken {source target : Sequent} (sound : Sound source)
    (prem : source.prem ⊆ target.prem) (conc : source.conc ⊆ target.conc) : Sound target := by
  intro valuation targetPremises
  obtain ⟨id, member, truth⟩ := sound valuation fun id member => targetPremises id (prem member)
  exact ⟨id, conc member, truth⟩

/-- Cut/resolution on complementary signed references. -/
theorem resolution (pivot : PropId) {left right : Sequent}
    (leftSound : Sound left) (rightSound : Sound right)
    (_leftPivot : pivot ∈ left.conc) (_rightPivot : pivot.neg ∈ right.conc) :
    Sound ⟨left.prem ∪ right.prem,
      left.conc.erase pivot ∪ right.conc.erase pivot.neg⟩ := by
  intro valuation premises
  by_cases pivotTrue : pivot.eval valuation
  · obtain ⟨id, member, truth⟩ := rightSound valuation (by
      intro id member
      exact premises id (by simp [member]))
    by_cases same : id = pivot.neg
    · subst id
      exact ((PropId.eval_neg valuation pivot).mp truth pivotTrue).elim
    · exact ⟨id, by simp [member, same], truth⟩
  · obtain ⟨id, member, truth⟩ := leftSound valuation (by
      intro id member
      exact premises id (by simp [member]))
    by_cases same : id = pivot
    · subst id
      exact (pivotTrue truth).elim
    · exact ⟨id, by simp [member, same], truth⟩

/-! The following equations are precisely what opcode lowering must establish
for a parent row and its operand rows.  They mention the registry's actual
`Op1` and `Op2` types rather than duplicating an opcode vocabulary. -/

def Op1Equation (valuation : Valuation) (parent : PropId)
    (op : Builtin.Op1) (operand : PropId) : Prop :=
  parent.eval valuation ↔ match op with | .not => ¬operand.eval valuation

def Op2Equation (valuation : Valuation) (parent : PropId)
    (op : Builtin.Op2) (left right : PropId) : Prop :=
  parent.eval valuation ↔ match op with
    | .and => left.eval valuation ∧ right.eval valuation
    | .or => left.eval valuation ∨ right.eval valuation
    | .imp => left.eval valuation → right.eval valuation

/-- Expand conjunction in the premise. -/
theorem andPrem {parent left right : PropId} {rest conc : PropSet}
    (source : Sound ⟨insert parent rest, conc⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .and left right) :
    Sound ⟨insert left (insert right rest), conc⟩ := by
  intro valuation premises
  apply source valuation
  intro id member
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact (equation valuation).mpr ⟨premises left (by simp), premises right (by simp)⟩
  · exact premises id (by simp [member])

/-- Expand disjunction in the conclusion. -/
theorem orConc {parent left right : PropId} {prem rest : PropSet}
    (source : Sound ⟨prem, insert parent rest⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .or left right) :
    Sound ⟨prem, insert left (insert right rest)⟩ := by
  intro valuation premises
  obtain ⟨id, member, truth⟩ := source valuation premises
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · rcases (equation valuation).mp truth with leftTruth | rightTruth
    · exact ⟨left, by simp, leftTruth⟩
    · exact ⟨right, by simp, rightTruth⟩
  · exact ⟨id, by simp [member], truth⟩

/-- Expand conjunction in the conclusion.  Both branches are required. -/
theorem andConc {parent left right : PropId} {prem rest : PropSet}
    (leftSource : Sound ⟨prem, insert left rest⟩)
    (rightSource : Sound ⟨prem, insert right rest⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .and left right) :
    Sound ⟨prem, insert parent rest⟩ := by
  intro valuation premises
  obtain ⟨leftId, leftMember, leftTruth⟩ := leftSource valuation premises
  obtain ⟨rightId, rightMember, rightTruth⟩ := rightSource valuation premises
  simp only [Finset.mem_insert] at leftMember rightMember
  rcases leftMember with rfl | leftMember
  · rcases rightMember with rfl | rightMember
    · exact ⟨parent, by simp, (equation valuation).mpr ⟨leftTruth, rightTruth⟩⟩
    · exact ⟨rightId, by simp [rightMember], rightTruth⟩
  · exact ⟨leftId, by simp [leftMember], leftTruth⟩

/-- Expand disjunction in a premise.  Both branches are required. -/
theorem orPrem {parent left right : PropId} {rest conc : PropSet}
    (leftSource : Sound ⟨insert left rest, conc⟩)
    (rightSource : Sound ⟨insert right rest, conc⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .or left right) :
    Sound ⟨insert parent rest, conc⟩ := by
  intro valuation premises
  have parentTruth := premises parent (by simp)
  rcases (equation valuation).mp parentTruth with leftTruth | rightTruth
  · exact leftSource valuation (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact leftTruth
      · exact premises id (by simp [member]))
  · exact rightSource valuation (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact rightTruth
      · exact premises id (by simp [member]))

/-- Expand implication in the conclusion (`p -> q` becomes `p |- q`). -/
theorem impConc {parent left right : PropId} {prem rest : PropSet}
    (source : Sound ⟨prem, insert parent rest⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .imp left right) :
    Sound ⟨insert left prem, insert right rest⟩ := by
  intro valuation premises
  obtain ⟨id, member, truth⟩ := source valuation fun id member => premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact ⟨right, by simp, (equation valuation).mp truth (premises left (by simp))⟩
  · exact ⟨id, by simp [member], truth⟩

/-- Expand implication in a premise.  This is the classical two-branch rule. -/
theorem impPrem {parent left right : PropId} {rest conc : PropSet}
    (antecedent : Sound ⟨rest, insert left conc⟩)
    (consequent : Sound ⟨insert right rest, conc⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .imp left right) :
    Sound ⟨insert parent rest, conc⟩ := by
  intro valuation premises
  obtain ⟨id, member, truth⟩ := antecedent valuation fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · have rightTruth := (equation valuation).mp (premises parent (by simp)) truth
    exact consequent valuation (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact rightTruth
      · exact premises id (by simp [member]))
  · exact ⟨id, member, truth⟩

/-- Expand negation in a premise by moving its operand to the conclusion. -/
theorem notPrem {parent operand : PropId} {rest conc : PropSet}
    (source : Sound ⟨insert parent rest, conc⟩)
    (equation : ∀ valuation, Op1Equation valuation parent .not operand) :
    Sound ⟨rest, insert operand conc⟩ := by
  intro valuation premises
  by_cases truth : operand.eval valuation
  · exact ⟨operand, by simp, truth⟩
  · obtain ⟨id, member, valid⟩ := source valuation (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact (equation valuation).mpr truth
      · exact premises id member)
    exact ⟨id, by simp [member], valid⟩

/-- Expand negation in a conclusion by moving its operand to the premise. -/
theorem notConc {parent operand : PropId} {prem rest : PropSet}
    (source : Sound ⟨prem, insert parent rest⟩)
    (equation : ∀ valuation, Op1Equation valuation parent .not operand) :
    Sound ⟨insert operand prem, rest⟩ := by
  intro valuation premises
  obtain ⟨id, member, truth⟩ := source valuation fun id member => premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact ((equation valuation).mp truth (premises operand (by simp))).elim
  · exact ⟨id, member, truth⟩

/-- A recursively expanded proposition set, characterized semantically. -/
structure Flattening (valuation : Valuation) (source flat : PropSet) where
  all_iff : (∀ id ∈ source, id.eval valuation) ↔ ∀ id ∈ flat, id.eval valuation
  any_iff : (∃ id ∈ source, id.eval valuation) ↔ ∃ id ∈ flat, id.eval valuation

/-- Recursive AND/OR flattening preserves a theorem row.  The executable
walker need only establish the two local `Flattening` invariants. -/
theorem flatten {source : Sequent} {prem conc : PropSet} (sound : Sound source)
    (premises : ∀ valuation, Flattening valuation source.prem prem)
    (conclusions : ∀ valuation, Flattening valuation source.conc conc) :
    Sound ⟨prem, conc⟩ := by
  intro valuation flatPremises
  have sourcePremises := (premises valuation).all_iff.mpr flatPremises
  exact (conclusions valuation).any_iff.mp (sound valuation sourcePremises)

/-- An empty conclusion is exactly a refutation of the premise conjunction. -/
theorem emptyConclusion_iff (prem : PropSet) :
    Sound ⟨prem, ∅⟩ ↔ ∀ valuation, ¬∀ id ∈ prem, id.eval valuation := by
  simp [Sound, Holds]

theorem contradiction (id : PropId) : Sound ⟨{id, id.neg}, ∅⟩ := by
  intro valuation premises
  have positive := premises id (by simp)
  have negative := premises id.neg (by simp)
  exact ((PropId.eval_neg valuation id).mp negative positive).elim

/-! Focused executable examples pin the inverted sign and canonical set wire
shape. -/

private def testId : PropId := ⟨-1, by decide⟩

example : testId.ref = 1 := rfl
example : testId.neg.val = 1 := rfl
example : ({testId, testId, testId.neg} : PropSet).toList = [testId, testId.neg] := by
  native_decide

example : Sound ⟨{testId, testId.neg}, ∅⟩ := contradiction testId

end Nucleus.Hol.Ethane.ClassicalSequent
