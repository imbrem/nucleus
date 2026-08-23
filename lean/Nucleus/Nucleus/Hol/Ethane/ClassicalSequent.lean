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

/-- A signed reference to a Boolean term.  Negative is positive polarity.  Its
magnitude is globally bounded by the same strict limit as `OneBased.Ref`. -/
abbrev PropId := { value : Int //
  value ≠ 0 ∧ value.natAbs < OneBased.Ref.maxExclusive }

/-- The referenced one-based term index, with polarity erased. -/
def PropId.ref (id : PropId) : Nat := id.val.natAbs

/-- Flip polarity without changing the referenced term. -/
def PropId.neg (id : PropId) : PropId :=
  ⟨-id.val, by omega, by simpa using id.property.2⟩

/-- Total positive-polarity conversion from the globally bounded local ref. -/
def PropId.positive (reference : OneBased.Ref) : PropId :=
  ⟨-Int.ofNat reference.val.toNat, by
    constructor
    · have natNonzero : reference.val.toNat ≠ 0 := by
        intro zero
        apply reference.property.1
        exact UInt64.toNat_inj.mp (by simpa using zero)
      simpa using natNonzero
    · simpa using reference.property.2⟩

@[simp] theorem PropId.positive_val (reference : OneBased.Ref) :
    (PropId.positive reference).val = -Int.ofNat reference.val.toNat := rfl

@[simp] theorem PropId.positive_ref (reference : OneBased.Ref) :
    (PropId.positive reference).ref = reference.val.toNat := by
  simp [PropId.positive, PropId.ref]

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

/-- Canonical merge used by every binary theorem rule. -/
def PropSet.merge (left right : PropSet) : PropSet := left ∪ right

@[simp] theorem PropSet.mem_merge (id : PropId) (left right : PropSet) :
    id ∈ left.merge right ↔ id ∈ left ∨ id ∈ right := by simp [PropSet.merge]

theorem PropSet.merge_comm (left right : PropSet) : left.merge right = right.merge left := by
  simp [PropSet.merge, Finset.union_comm]

theorem PropSet.merge_assoc (first second third : PropSet) :
    (first.merge second).merge third = first.merge (second.merge third) := by
  simp [PropSet.merge, Finset.union_assoc]

@[simp] theorem PropSet.merge_self (set : PropSet) : set.merge set = set := by
  simp [PropSet.merge]

theorem PropSet.merge_wire_unique {left right merged : PropSet}
    (equal : merged = left.merge right) :
    merged.toList = (left.merge right).toList := congrArg PropSet.toList equal

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
      exact lt_of_le_of_ne (Int.le_of_not_gt negative) (Ne.symm id.property.1)
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

/-- Gentzen cut: remove the same signed proposition from the left conclusion
and the right premise. -/
theorem cut (pivot : PropId) {left right : Sequent}
    (leftSound : Sound left) (rightSound : Sound right)
    (_leftPivot : pivot ∈ left.conc) (_rightPivot : pivot ∈ right.prem) :
    Sound ⟨left.prem ∪ right.prem.erase pivot,
      left.conc.erase pivot ∪ right.conc⟩ := by
  intro valuation premises
  obtain ⟨id, member, truth⟩ := leftSound valuation fun id member =>
    premises id (by simp [member])
  by_cases same : id = pivot
  · subst id
    obtain ⟨rightId, rightMember, rightTruth⟩ := rightSound valuation (by
      intro id member
      by_cases pivotMember : id = pivot
      · subst id
        exact truth
      · exact premises id (by simp [member, pivotMember]))
    exact ⟨rightId, by simp [rightMember], rightTruth⟩
  · exact ⟨id, by simp [member, same], truth⟩

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

/-- Semantic bridge for a checked `tm.bool false` row. -/
def FalseEquation (valuation : Valuation) (falsehood : PropId) : Prop :=
  ¬falsehood.eval valuation

/-- Semantic bridge for a checked `tm.bool true` row. -/
def TrueEquation (valuation : Valuation) (truth : PropId) : Prop :=
  truth.eval valuation

theorem falseLeft (falsehood : PropId)
    (equation : ∀ valuation, FalseEquation valuation falsehood) :
    Sound ⟨{falsehood}, ∅⟩ := by
  intro valuation premises
  exact (equation valuation (premises falsehood (by simp))).elim

theorem trueRight (truth : PropId)
    (equation : ∀ valuation, TrueEquation valuation truth) :
    Sound ⟨∅, {truth}⟩ := by
  intro valuation _
  exact ⟨truth, by simp, equation valuation⟩

/-! ## Exact checked Gentzen rule correspondence

| Rust kernel method | Lean soundness theorem |
| --- | --- |
| `assume` | `identity` |
| `weaken` | `weaken` |
| `cut` | `cut` |
| `resolve` | `resolution` |
| `false_left` / `true_right` | `falseLeft` / `trueRight` |
| `not_left` / `not_right` | `notLeft` / `notRight` |
| `and_left` / `and_right` | `andLeft` / `andRight` |
| `or_left` / `or_right` | `orLeft` / `orRight` |
| `imp_left` / `imp_right` | `impLeft` / `impRight` |
| `expand_conclusion` | `andConcBranch`, `orConc`, `impConc`, `notConc` |
| `flatten_conclusion` / `fold_conclusion` | `flattenConclusion` / `foldConclusion` |
| `flatten_premise` / `fold_premise` | `flattenPremise` / `foldPremise` |

The opcode equations below are discharged by checking the exact OneBased row
and its children.  Binary rules deliberately allow different contexts and
merge them by canonical set union, matching the Rust API.
-/

theorem notLeft {parent operand : PropId} {prem conc : PropSet}
    (source : Sound ⟨prem, insert operand conc⟩)
    (equation : ∀ valuation, Op1Equation valuation parent .not operand) :
    Sound ⟨insert parent prem, conc⟩ := by
  intro valuation premises
  obtain ⟨id, member, truth⟩ := source valuation fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact ((equation valuation).mp (premises parent (by simp)) truth).elim
  · exact ⟨id, member, truth⟩

theorem notRight {parent operand : PropId} {prem conc : PropSet}
    (source : Sound ⟨insert operand prem, conc⟩)
    (equation : ∀ valuation, Op1Equation valuation parent .not operand) :
    Sound ⟨prem, insert parent conc⟩ := by
  intro valuation premises
  by_cases operandTruth : operand.eval valuation
  · obtain ⟨id, member, truth⟩ := source valuation (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact operandTruth
      · exact premises id member)
    exact ⟨id, by simp [member], truth⟩
  · exact ⟨parent, by simp, (equation valuation).mpr operandTruth⟩

theorem andLeft {parent left right : PropId} {prem conc : PropSet}
    (source : Sound ⟨insert left (insert right prem), conc⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .and left right) :
    Sound ⟨insert parent prem, conc⟩ := by
  intro valuation premises
  apply source valuation
  intro id member
  simp only [Finset.mem_insert] at member
  rcases member with rfl | rfl | member
  · exact ((equation valuation).mp (premises parent (by simp))).1
  · exact ((equation valuation).mp (premises parent (by simp))).2
  · exact premises id (by simp [member])

theorem andRight {parent left right : PropId} {leftPrem leftConc rightPrem rightConc : PropSet}
    (leftSource : Sound ⟨leftPrem, insert left leftConc⟩)
    (rightSource : Sound ⟨rightPrem, insert right rightConc⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .and left right) :
    Sound ⟨leftPrem ∪ rightPrem, insert parent (leftConc ∪ rightConc)⟩ := by
  intro valuation premises
  obtain ⟨leftId, leftMember, leftTruth⟩ := leftSource valuation fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at leftMember
  rcases leftMember with rfl | leftMember
  · obtain ⟨rightId, rightMember, rightTruth⟩ := rightSource valuation fun id member =>
      premises id (by simp [member])
    simp only [Finset.mem_insert] at rightMember
    rcases rightMember with rfl | rightMember
    · exact ⟨parent, by simp, (equation valuation).mpr ⟨leftTruth, rightTruth⟩⟩
    · exact ⟨rightId, by simp [rightMember], rightTruth⟩
  · exact ⟨leftId, by simp [leftMember], leftTruth⟩

theorem orLeft {parent left right : PropId} {leftPrem leftConc rightPrem rightConc : PropSet}
    (leftSource : Sound ⟨insert left leftPrem, leftConc⟩)
    (rightSource : Sound ⟨insert right rightPrem, rightConc⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .or left right) :
    Sound ⟨insert parent (leftPrem ∪ rightPrem), leftConc ∪ rightConc⟩ := by
  intro valuation premises
  rcases (equation valuation).mp (premises parent (by simp)) with leftTruth | rightTruth
  · obtain ⟨id, member, truth⟩ := leftSource valuation (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact leftTruth
      · exact premises id (by simp [member]))
    exact ⟨id, by simp [member], truth⟩
  · obtain ⟨id, member, truth⟩ := rightSource valuation (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact rightTruth
      · exact premises id (by simp [member]))
    exact ⟨id, by simp [member], truth⟩

theorem orRight {parent left right : PropId} {prem conc : PropSet}
    (source : Sound ⟨prem, insert left (insert right conc)⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .or left right) :
    Sound ⟨prem, insert parent conc⟩ := by
  intro valuation premises
  obtain ⟨id, member, truth⟩ := source valuation premises
  simp only [Finset.mem_insert] at member
  rcases member with rfl | rfl | member
  · exact ⟨parent, by simp, (equation valuation).mpr (Or.inl truth)⟩
  · exact ⟨parent, by simp, (equation valuation).mpr (Or.inr truth)⟩
  · exact ⟨id, by simp [member], truth⟩

theorem impLeft {parent left right : PropId} {leftPrem leftConc rightPrem rightConc : PropSet}
    (leftSource : Sound ⟨leftPrem, insert left leftConc⟩)
    (rightSource : Sound ⟨insert right rightPrem, rightConc⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .imp left right) :
    Sound ⟨insert parent (leftPrem ∪ rightPrem), leftConc ∪ rightConc⟩ := by
  intro valuation premises
  obtain ⟨id, member, truth⟩ := leftSource valuation fun id member =>
    premises id (by simp [member])
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · have rightTruth := (equation valuation).mp (premises parent (by simp)) truth
    obtain ⟨id, member, valid⟩ := rightSource valuation (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact rightTruth
      · exact premises id (by simp [member]))
    exact ⟨id, by simp [member], valid⟩
  · exact ⟨id, by simp [member], truth⟩

theorem impRight {parent left right : PropId} {prem conc : PropSet}
    (source : Sound ⟨insert left prem, insert right conc⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .imp left right) :
    Sound ⟨prem, insert parent conc⟩ := by
  intro valuation premises
  by_cases leftTruth : left.eval valuation
  · obtain ⟨id, member, truth⟩ := source valuation (by
      intro id member
      simp only [Finset.mem_insert] at member
      rcases member with rfl | member
      · exact leftTruth
      · exact premises id member)
    simp only [Finset.mem_insert] at member
    rcases member with rfl | member
    · exact ⟨parent, by simp, (equation valuation).mpr fun _ => truth⟩
    · exact ⟨id, by simp [member], truth⟩
  · exact ⟨parent, by simp, (equation valuation).mpr fun truth => (leftTruth truth).elim⟩

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

/-- The branch-selecting one-step RHS projection used by
`Kernel::expand_conclusion` for conjunction. -/
theorem andConcBranch {parent selected other : PropId} {prem rest : PropSet}
    (source : Sound ⟨prem, insert parent rest⟩)
    (equation : ∀ valuation, Op2Equation valuation parent .and selected other) :
    Sound ⟨prem, insert selected rest⟩ := by
  intro valuation premises
  obtain ⟨id, member, truth⟩ := source valuation premises
  simp only [Finset.mem_insert] at member
  rcases member with rfl | member
  · exact ⟨selected, by simp, ((equation valuation).mp truth).1⟩
  · exact ⟨id, by simp [member], truth⟩

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

/-- Recursive folding is the inverse semantic direction of `flatten`.  An
executable opcode walker may fold any tree for which it returns these local
all/any invariants. -/
theorem fold {source : Sequent} {prem conc : PropSet} (sound : Sound ⟨prem, conc⟩)
    (premises : ∀ valuation, Flattening valuation source.prem prem)
    (conclusions : ∀ valuation, Flattening valuation source.conc conc) :
    Sound source := by
  intro valuation sourcePremises
  have flatPremises := (premises valuation).all_iff.mp sourcePremises
  exact (conclusions valuation).any_iff.mpr (sound valuation flatPremises)

/-- Exact semantic contract of `Kernel::flatten_conclusion`. -/
theorem flattenConclusion {prem source flat : PropSet} (sound : Sound ⟨prem, source⟩)
    (expansion : ∀ valuation, Flattening valuation source flat) :
    Sound ⟨prem, flat⟩ :=
  flatten sound (fun _valuation => ⟨Iff.rfl, Iff.rfl⟩) expansion

/-- Exact semantic contract of `Kernel::fold_conclusion`. -/
theorem foldConclusion {prem source flat : PropSet} (sound : Sound ⟨prem, flat⟩)
    (expansion : ∀ valuation, Flattening valuation source flat) :
    Sound ⟨prem, source⟩ :=
  fold sound (fun _valuation => ⟨Iff.rfl, Iff.rfl⟩) expansion

/-- Exact semantic contract of `Kernel::flatten_premise`. -/
theorem flattenPremise {source flat conc : PropSet} (sound : Sound ⟨source, conc⟩)
    (expansion : ∀ valuation, Flattening valuation source flat) :
    Sound ⟨flat, conc⟩ :=
  flatten sound expansion (fun _valuation => ⟨Iff.rfl, Iff.rfl⟩)

/-- Exact semantic contract of `Kernel::fold_premise`. -/
theorem foldPremise {source flat conc : PropSet} (sound : Sound ⟨flat, conc⟩)
    (expansion : ∀ valuation, Flattening valuation source flat) :
    Sound ⟨source, conc⟩ :=
  fold sound expansion (fun _valuation => ⟨Iff.rfl, Iff.rfl⟩)

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

private def testId : PropId := ⟨-1, by decide, by decide⟩

example : testId.ref = 1 := rfl
example : testId.neg.val = 1 := rfl
example : PropId.positive LogicalOpcode.Raw.one = testId := by decide
example : testId ∈ ({testId, testId, testId.neg} : PropSet).toList := by simp
example : ({testId, testId, testId.neg} : PropSet).toList.Nodup :=
  PropSet.toList_nodup _

example : Sound ⟨{testId, testId.neg}, ∅⟩ := contradiction testId

end Nucleus.Hol.Ethane.ClassicalSequent
