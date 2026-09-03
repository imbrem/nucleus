import Nucleus.Classical.Refutation
import Nucleus.Classical.Tagged.Runtime.EncodeCorrect
import Nucleus.Classical.Tagged.Runtime.Mutate

/-!
# Refutation contracts for the checked tagged runtime

SAT nodes always quantify over fresh uninterpreted Boolean variables.  These
theorems connect that abstract meaning to a validated runtime arena and to the
existing RUP/RAT development. Certificate parsing remains outside this
checked layer; the state machine performs stable clause-ID lookup itself.
-/

namespace Nucleus.Classical.Tagged.Runtime.Refutation

open Nucleus.Classical
open Nucleus.Hol.Ethane.ClassicalMatrix
open Nucleus.Classical.Tagged.Runtime

namespace Abstract
export Nucleus.Classical.Refutation.Tagged
  (sequent satSequent closedRefutation sequent_syllogism_iff
    satSequent_entailsAt_iff closedRefutation_entailsAt_iff)
end Abstract

namespace Matrix
export Nucleus.Classical.Refutation.Matrix
  (BooleanUnsat booleanUnsat_iff_legacy)
end Matrix

namespace Certificate
export Nucleus.Classical.Refutation.Certificate
  (learned rat_unsat_iff rup_unsat_iff)
end Certificate

variable {payloadWidth : Nat}

/-- One decoded sequent occurs in a checked runtime arena. -/
def Contains (checked : Checked payloadWidth)
    (sequent : Tagged.Sequent Nat) : Prop :=
  sequent ∈ checked.decoded.sequents

/-- Runtime theoremhood specializes to every decoded member. -/
theorem entailsAt_member {known : PartialAssignment Nat}
    {checked : Checked payloadWidth} {sequent : Tagged.Sequent Nat}
    (holds : Mutate.EntailsAt known checked)
    (member : Contains checked sequent) : sequent.EntailsAt known := by
  intro assignment completes
  exact holds assignment completes sequent member

/-- A checked universal `CNF ⊢ false` member is exactly a Boolean
refutation of that CNF. -/
theorem unsat_of_sequent {checked : Checked payloadWidth} {value : Cnf Nat}
    (holds : Mutate.Syllogism checked)
    (member : Contains checked (Abstract.sequent value)) :
    Matrix.BooleanUnsat value := by
  exact (Abstract.sequent_syllogism_iff value).mp
    (entailsAt_member holds member)

/-- A checked closed `sat(CNF) ⊢ false` member has the same refutation
meaning under any ambient partial assignment. -/
theorem unsat_of_satSequent {known : PartialAssignment Nat}
    {checked : Checked payloadWidth} {value : Cnf Nat}
    (holds : Mutate.EntailsAt known checked)
    (member : Contains checked (Abstract.satSequent value)) :
    Matrix.BooleanUnsat value := by
  exact (Abstract.satSequent_entailsAt_iff known value).mp
    (entailsAt_member holds member)

theorem unsat_of_closedRefutation {known : PartialAssignment Nat}
    {checked : Checked payloadWidth} {value : Cnf Nat}
    (holds : Mutate.EntailsAt known checked)
    (member : Contains checked (Abstract.closedRefutation value)) :
    Matrix.BooleanUnsat value := by
  exact (Abstract.closedRefutation_entailsAt_iff known value).mp
    (entailsAt_member holds member)

/-- The canonical runtime can represent a refutation goal whenever its public
resource bound holds. -/
theorem packSequent_complete {value : Cnf Nat}
    (fits : Encode.Fits payloadWidth [Abstract.sequent value]) :
    ∃ checked,
      Encode.pack? payloadWidth [Abstract.sequent value] = some checked ∧
      checked.decoded.sequents = [Abstract.sequent value] := by
  obtain ⟨checked, packed⟩ := Encode.pack?_complete fits
  exact ⟨checked, packed, (Encode.pack?_result packed).2.1⟩

/-- General RAT preserves the runtime refutation goal in both directions. -/
theorem rat_preserves_unsat {formula : Cnf Nat} {clause : Clause Nat}
    (rat : Nucleus.Hol.Ethane.ClassicalRefutation.Rat formula clause) :
    Matrix.BooleanUnsat (Certificate.learned formula clause) ↔
      Matrix.BooleanUnsat formula := by
  rw [Matrix.booleanUnsat_iff_legacy, Matrix.booleanUnsat_iff_legacy]
  exact Certificate.rat_unsat_iff rat

/-- RUP is the consequence-producing special case and likewise preserves the
runtime refutation goal. -/
theorem rup_preserves_unsat {formula : Cnf Nat} {clause : Clause Nat}
    (rup : Nucleus.Hol.Ethane.ClassicalRefutation.Rup formula clause) :
    Matrix.BooleanUnsat (Certificate.learned formula clause) ↔
      Matrix.BooleanUnsat formula := by
  rw [Matrix.booleanUnsat_iff_legacy, Matrix.booleanUnsat_iff_legacy]
  exact Certificate.rup_unsat_iff rup

/-! ## Executable certificate checking

The types below model the parser-independent part of the Rust refuter.  Clause
identifiers are explicit and stable across deletion.  Proof fields are erased
by code generation: callers supply only clauses, identifiers, and ordered
hints.
-/

namespace Checker

open Nucleus.Hol.Ethane.ClassicalRefutation

/-- A one-based LRAT clause identifier.  `position = 0` corresponds to the
wire identifier `1`; the representation makes identifier zero uninhabited. -/
structure ClauseId where
  position : Nat
  deriving DecidableEq, Repr

namespace ClauseId

def wire (id : ClauseId) : Nat := id.position + 1

end ClauseId

structure Entry where
  id : ClauseId
  clause : Clause Nat
  deriving DecidableEq

abbrev Database := List Entry

namespace Database

def cnf (database : Database) : Cnf Nat :=
  ⟨database.map Entry.clause⟩

/-- Lookup retains erased evidence that the returned clause is live. -/
def lookup? : (database : Database) → (id : ClauseId) →
    Option { clause : Clause Nat //
      ∃ entry ∈ database, entry.id = id ∧ entry.clause = clause }
  | [], _ => none
  | entry :: rest, id =>
      if equal : entry.id = id then
        some ⟨entry.clause, entry, by simp, equal, rfl⟩
      else
        match lookup? rest id with
        | none => none
        | some found => some ⟨found.1, by
            obtain ⟨source, member, sourceId, sourceClause⟩ := found.2
            exact ⟨source, by simp [member], sourceId, sourceClause⟩⟩

theorem Lookup.clause_mem {database : Database} {id : ClauseId}
    {found : { clause : Clause Nat //
      ∃ entry ∈ database, entry.id = id ∧ entry.clause = clause }} :
    found.1 ∈ database.cnf.clauses := by
  obtain ⟨entry, member, _, equal⟩ := found.2
  rw [← equal]
  exact List.mem_map.mpr ⟨entry, member, rfl⟩

end Database

structure TrailConflict (trail : List (Lit Nat)) where
  literal : Lit Nat
  positive : literal ∈ trail
  negative : literal.neg ∈ trail

private def conflictIn? (trail : List (Lit Nat)) :
    (candidates : List (Lit Nat)) → Option (TrailConflict trail)
  | [] => none
  | literal :: rest =>
      if negative : literal.neg ∈ trail then
        if positive : literal ∈ trail then
          some ⟨literal, positive, negative⟩
        else
          conflictIn? trail rest
      else
        conflictIn? trail rest

def conflict? (trail : List (Lit Nat)) : Option (TrailConflict trail) :=
  conflictIn? trail trail

structure UnitAdvance (trail : List (Lit Nat)) (clause : Clause Nat) where
  literal : Lit Nat
  member : literal ∈ clause.literals
  closed : ∀ other ∈ clause.literals, other ≠ literal → other.neg ∈ trail

inductive Advance (trail : List (Lit Nat)) (clause : Clause Nat) where
  | conflict (closed : ∀ literal ∈ clause.literals, literal.neg ∈ trail)
  | unit (step : UnitAdvance trail clause)

/-- Exact ordered-propagation classification used by Rust.  A hint already
satisfied by the trail is rejected; otherwise it must be conflicting or unit. -/
def advance? (trail : List (Lit Nat)) (clause : Clause Nat) :
    Option (Advance trail clause) :=
  if clause.literals.any (fun literal => decide (literal ∈ trail)) then
    none
  else
    let openLiterals := clause.literals.filter
      (fun literal => decide (literal.neg ∉ trail))
    match equal : openLiterals with
    | [] => some (.conflict (by
        intro literal member
        by_contra absent
        have present : literal ∈ openLiterals := by
          simp [openLiterals, member, absent]
        simp [equal] at present))
    | [literal] => some (.unit ⟨literal, by
          have present : literal ∈ openLiterals := by simp [equal]
          exact (List.mem_filter.mp present).1, by
          intro other member different
          by_contra absent
          have present : other ∈ openLiterals := by
            simp [openLiterals, member, absent]
          have same : other = literal := by simpa [equal] using present
          exact different same⟩)
    | _ => none

theorem UnitAdvance.holds {trail : List (Lit Nat)} {clause : Clause Nat}
    (step : UnitAdvance trail clause) (valuation : Valuation Nat)
    (clauseTruth : clause.Holds valuation)
    (trailTruth : Trail.Holds valuation trail) :
    step.literal.Holds valuation := by
  obtain ⟨witness, member, truth⟩ := clauseTruth
  by_cases equal : witness = step.literal
  · simpa [equal] using truth
  · exact (((Lit.holds_neg valuation witness).mp
      (trailTruth witness.neg (step.closed witness member equal))) truth).elim

/-- The result of replaying a valid hint prefix.  The open case carries only
the semantic fact needed to reuse the prefix for RAT groups. -/
inductive PropagationResult (formula : Cnf Nat) (start : List (Lit Nat)) where
  | conflict (derivation : RupTrail formula start)
  | open (trail : List (Lit Nat))
      (follows : ∀ valuation, formula.Holds valuation →
        Trail.Holds valuation start → Trail.Holds valuation trail)

def propagate? (database : Database) :
    (trail : List (Lit Nat)) → List ClauseId →
      Option (PropagationResult database.cnf trail)
  | trail, [] => some (.open trail (fun _ _ truth => truth))
  | trail, id :: hints => do
      let found ← database.lookup? id
      let step ← advance? trail found.1
      match step with
      | .conflict closed =>
          some (.conflict (.clauseConflict trail found.1
            Database.Lookup.clause_mem closed))
      | .unit unit =>
          let next ← propagate? database (unit.literal :: trail) hints
          match next with
          | .conflict derivation =>
              some (.conflict (.unit trail found.1 unit.literal
                Database.Lookup.clause_mem unit.member unit.closed derivation))
          | .open final follows =>
              some (.open final (by
                intro valuation formulaTruth trailTruth
                apply follows valuation formulaTruth
                intro literal member
                rcases List.mem_cons.mp member with rfl | member
                · exact unit.holds valuation
                    (formulaTruth found.1 Database.Lookup.clause_mem) trailTruth
                · exact trailTruth literal member))

structure RupCheck (database : Database) (clause : Clause Nat) : Type where
  sound : Rup database.cnf clause

/-- Validate a complete ordered RUP check.  A contradictory initial trail
accepts a tautological clause without consulting hints. -/
def checkRup? (database : Database) (clause : Clause Nat)
    (hints : List ClauseId) : Option (RupCheck database clause) :=
  let trail := falsifyingTrail clause
  match conflict? trail with
  | some conflict => some ⟨.trailConflict trail conflict.literal
      conflict.positive conflict.negative⟩
  | none =>
      match propagate? database trail hints with
      | some (.conflict derivation) => some ⟨derivation⟩
      | _ => none

structure RatGroup where
  opposing : ClauseId
  hints : List ClauseId
  deriving DecidableEq, Repr

def opposingIds (database : Database) (pivot : Lit Nat) : List ClauseId :=
  (database.filter fun entry => decide (pivot.neg ∈ entry.clause.literals)).map Entry.id

/-- RAT groups form an exact set: no duplicate group identifiers, no missing
opposing live row, and no group for a non-opposing row. -/
def exactCoverage (database : Database) (pivot : Lit Nat)
    (groups : List RatGroup) : Bool :=
  let supplied := groups.map RatGroup.opposing
  supplied.Nodup &&
    (opposingIds database pivot).all supplied.contains &&
    supplied.all (opposingIds database pivot).contains

private def prefixWitnessIn? (trailPrefix : List (Lit Nat))
    (excluded : Lit Nat) (clause : Clause Nat) :
    (candidates : List (Lit Nat)) → Option { literal : Lit Nat //
      literal ∈ clause.literals ∧ literal ≠ excluded ∧ literal ∈ trailPrefix }
  | [] => none
  | literal :: rest =>
      if member : literal ∈ clause.literals then
        if different : literal ≠ excluded then
          if present : literal ∈ trailPrefix then
            some ⟨literal, member, different, present⟩
          else
            prefixWitnessIn? trailPrefix excluded clause rest
        else
          prefixWitnessIn? trailPrefix excluded clause rest
      else
        prefixWitnessIn? trailPrefix excluded clause rest

def prefixWitness? (trailPrefix : List (Lit Nat)) (excluded : Lit Nat)
    (clause : Clause Nat) : Option { literal : Lit Nat //
      literal ∈ clause.literals ∧ literal ≠ excluded ∧ literal ∈ trailPrefix } :=
  prefixWitnessIn? trailPrefix excluded clause clause.literals

def groupTrail (trailPrefix : List (Lit Nat)) (opposing : Clause Nat)
    (excluded : Lit Nat) : List (Lit Nat) :=
  (opposing.literals.filter (· ≠ excluded)).map Lit.neg ++ trailPrefix

def FalsifiesExcept (valuation : Valuation Nat) (clause : Clause Nat)
    (excluded : Lit Nat) : Prop :=
  ∀ literal ∈ clause.literals, literal ≠ excluded → ¬literal.Holds valuation

structure GroupCheck (database : Database) (trailPrefix : List (Lit Nat))
    (opposing : Clause Nat) (excluded : Lit Nat) : Type where
  refutes : ∀ valuation, database.cnf.Holds valuation →
    Trail.Holds valuation trailPrefix → FalsifiesExcept valuation opposing excluded → False

private theorem groupTrail_holds {trailPrefix : List (Lit Nat)}
    {opposing : Clause Nat} {excluded : Lit Nat} {valuation : Valuation Nat}
    (prefixTruth : Trail.Holds valuation trailPrefix)
    (falseOthers : FalsifiesExcept valuation opposing excluded) :
    Trail.Holds valuation (groupTrail trailPrefix opposing excluded) := by
  intro literal member
  rcases List.mem_append.mp member with added | old
  · obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp added
    obtain ⟨opposingMember, different⟩ := List.mem_filter.mp sourceMember
    exact (Lit.holds_neg valuation source).mpr
      (falseOthers source opposingMember (of_decide_eq_true different))
  · exact prefixTruth literal old

/-- Validate one RAT group.  The early case is the asymmetric-tautology
shortcut used by Rust; otherwise the ordered hints must conflict. -/
def checkGroup? (database : Database) (trailPrefix : List (Lit Nat))
    (opposing : Clause Nat) (excluded : Lit Nat) (hints : List ClauseId) :
    Option (GroupCheck database trailPrefix opposing excluded) :=
  match prefixWitness? trailPrefix excluded opposing with
  | some witness => some ⟨by
      intro valuation _ prefixTruth falseOthers
      exact falseOthers witness.1 witness.2.1 witness.2.2.1
        (prefixTruth witness.1 witness.2.2.2)⟩
  | none =>
      let trail := groupTrail trailPrefix opposing excluded
      match conflict? trail with
      | some conflict => some ⟨by
          intro valuation formulaTruth prefixTruth falseOthers
          exact (RupTrail.trailConflict trail conflict.literal
            conflict.positive conflict.negative).contradiction valuation formulaTruth
            (groupTrail_holds prefixTruth falseOthers)⟩
      | none =>
          match propagate? database trail hints with
          | some (.conflict derivation) => some ⟨by
              intro valuation formulaTruth prefixTruth falseOthers
              exact derivation.contradiction valuation formulaTruth
                (groupTrail_holds prefixTruth falseOthers)⟩
          | _ => none

private def findGroup? (id : ClauseId) : List RatGroup → Option RatGroup
  | [] => none
  | group :: groups =>
      if group.opposing = id then some group else findGroup? id groups

structure GroupsCheck (database entries : Database)
    (trailPrefix : List (Lit Nat)) (pivot : Lit Nat) : Type where
  checked : ∀ entry ∈ entries, pivot.neg ∈ entry.clause.literals →
    ∀ valuation, database.cnf.Holds valuation → Trail.Holds valuation trailPrefix →
      FalsifiesExcept valuation entry.clause pivot.neg → False

private def checkGroupsIn? (database : Database) (trailPrefix : List (Lit Nat))
    (pivot : Lit Nat) (groups : List RatGroup) :
    (remaining : Database) → Option (GroupsCheck database remaining trailPrefix pivot)
  | [] => some ⟨by
      intro _ member
      simp at member⟩
  | entry :: rest =>
      if opposing : pivot.neg ∈ entry.clause.literals then do
        let group ← findGroup? entry.id groups
        let head ← checkGroup? database trailPrefix entry.clause pivot.neg group.hints
        let tail ← checkGroupsIn? database trailPrefix pivot groups rest
        some ⟨by
          intro candidate member complement
          rcases List.mem_cons.mp member with rfl | member
          · exact head.refutes
          · exact tail.checked candidate member complement⟩
      else do
        let tail ← checkGroupsIn? database trailPrefix pivot groups rest
        some ⟨by
          intro candidate member complement
          rcases List.mem_cons.mp member with rfl | member
          · exact (opposing complement).elim
          · exact tail.checked candidate member complement⟩

def checkGroups? (database : Database) (trailPrefix : List (Lit Nat))
    (pivot : Lit Nat) (groups : List RatGroup) :
    Option (GroupsCheck database database trailPrefix pivot) := do
  if exactCoverage database pivot groups then pure () else none
  checkGroupsIn? database trailPrefix pivot groups database

private theorem true_before_false_after_flip (valuation : Valuation Nat)
    (pivot literal : Lit Nat) (pivotFalse : ¬pivot.Holds valuation)
    (before : literal.Holds valuation)
    (after : ¬literal.Holds (flipValuation valuation pivot.1)) :
    literal = pivot.neg := by
  by_cases different : literal.1 ≠ pivot.1
  · exact (after ((Lit.holds_flip_other valuation literal different).mpr before)).elim
  · rcases Lit.eq_or_eq_neg_of_same_atom literal pivot (not_ne_iff.mp different) with
      equal | equal
    · subst literal
      exact (pivotFalse before).elim
    · exact equal

private theorem true_before_true_after_flip_unless_complement
    (valuation : Valuation Nat) (pivot literal : Lit Nat)
    (pivotFalse : ¬pivot.Holds valuation) (before : literal.Holds valuation)
    (notComplement : literal ≠ pivot.neg) :
    literal.Holds (flipValuation valuation pivot.1) := by
  by_cases different : literal.1 ≠ pivot.1
  · exact (Lit.holds_flip_other valuation literal different).mpr before
  · rcases Lit.eq_or_eq_neg_of_same_atom literal pivot (not_ne_iff.mp different) with
      equal | equal
    · subst literal
      exact (pivotFalse before).elim
    · exact (notComplement equal).elim

private theorem rat_of_groups {database : Database} {learned : Clause Nat}
    {pivot : Lit Nat} {trailPrefix : List (Lit Nat)}
    (pivotMember : pivot ∈ learned.literals)
    (prefixFollows : ∀ valuation, database.cnf.Holds valuation →
      Trail.Holds valuation (falsifyingTrail learned) →
      Trail.Holds valuation trailPrefix)
    (groups : GroupsCheck database database trailPrefix pivot) :
    Rat database.cnf learned := by
  rintro ⟨valuation, formulaTruth⟩
  by_cases learnedTruth : learned.Holds valuation
  · refine ⟨valuation, ?_⟩
    intro clause member
    rcases List.mem_append.mp member with member | member
    · exact formulaTruth clause member
    · have equal : clause = learned := by simpa using member
      simpa [equal] using learnedTruth
  · let flipped := flipValuation valuation pivot.1
    have pivotFalse : ¬pivot.Holds valuation := by
      intro truth
      exact learnedTruth ⟨pivot, pivotMember, truth⟩
    have learnedFlipped : learned.Holds flipped :=
      ⟨pivot, pivotMember, (Lit.holds_flip_self valuation pivot).mpr pivotFalse⟩
    have prefixTruth : Trail.Holds valuation trailPrefix :=
      prefixFollows valuation formulaTruth
        ((falsifyingTrail_holds valuation learned).mpr learnedTruth)
    refine ⟨flipped, ?_⟩
    intro clause member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
      by_contra clauseFalse
      obtain ⟨literal, literalMember, literalTruth⟩ :=
        formulaTruth entry.clause (List.mem_map.mpr ⟨entry, entryMember, rfl⟩)
      have complementEqual := true_before_false_after_flip valuation pivot literal
        pivotFalse literalTruth (fun truth =>
          clauseFalse ⟨literal, literalMember, truth⟩)
      have complementMember : pivot.neg ∈ entry.clause.literals := by
        rw [← complementEqual]
        exact literalMember
      exact groups.checked entry entryMember complementMember valuation
        formulaTruth prefixTruth (by
          intro other otherMember notComplement otherTruth
          exact clauseFalse ⟨other, otherMember,
            true_before_true_after_flip_unless_complement valuation pivot other
              pivotFalse otherTruth notComplement⟩)
    · have equal : clause = learned := by simpa using member
      simpa [equal] using learnedFlipped

structure RatCheck (database : Database) (clause : Clause Nat) : Type where
  sound : Rat database.cnf clause

private theorem member_of_head?_eq_some {values : List α} {value : α}
    (head : values.head? = some value) : value ∈ values := by
  cases values with
  | nil => simp at head
  | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst first
      simp

/-- Validate a RUP-or-RAT learning step.  SAT here and in the sealed result is
always over fresh, uninterpreted propositional variables. -/
def checkRat? (database : Database) (learned : Clause Nat) (pivot : Lit Nat)
    (prefixHints : List ClauseId) (groups : List RatGroup) :
    Option (RatCheck database learned) :=
  if first : learned.literals.head? = some pivot then
    let trail := falsifyingTrail learned
    match conflict? trail with
    | some conflict =>
        some ⟨rat_of_rup (.trailConflict trail conflict.literal
          conflict.positive conflict.negative)⟩
    | none =>
        match propagate? database trail prefixHints with
        | none => none
        | some (.conflict derivation) => some ⟨rat_of_rup derivation⟩
        | some (.open trailPrefix follows) => do
            let checked ← checkGroups? database trailPrefix pivot groups
            some ⟨rat_of_groups (member_of_head?_eq_some first) follows checked⟩
  else
    none

/-! ### Stateful proof replay -/

structure State where
  initial : Cnf Nat
  live : Database
  highWater : Nat
  refuted : Bool

def numberClauses : List (Clause Nat) → Nat → Database
  | [], _ => []
  | clause :: clauses, position =>
      ⟨⟨position⟩, clause⟩ :: numberClauses clauses (position + 1)

@[simp] theorem numberClauses_clauses (clauses : List (Clause Nat)) (position : Nat) :
    (numberClauses clauses position).map Entry.clause = clauses := by
  induction clauses generalizing position with
  | nil => rfl
  | cons clause clauses ih => simp [numberClauses, ih]

def openState (initial : Cnf Nat) : State :=
  { initial
    live := numberClauses initial.clauses 0
    highWater := initial.clauses.length
    refuted := initial.clauses.any fun clause => clause.literals.isEmpty }

def State.Valid (state : State) : Prop :=
  PreservesSatisfiability state.initial state.live.cnf ∧
    (state.refuted = true → Unsat state.initial)

structure CheckedState : Type where
  state : State
  valid : state.Valid

private theorem open_refuted_sound {initial : Cnf Nat}
    (refuted : (openState initial).refuted = true) : Unsat initial := by
  simp only [openState] at refuted
  rw [List.any_eq_true] at refuted
  obtain ⟨clause, member, empty⟩ := refuted
  have literals : clause.literals = [] := List.isEmpty_iff.mp empty
  have equal : clause = Clause.mk [] := by cases clause; simp_all
  exact contains_empty_clause_unsat (equal ▸ member)

def start (initial : Cnf Nat) : CheckedState :=
  ⟨openState initial, by
    constructor
    · have same : (openState initial).live.cnf = initial := by
        cases initial
        simp [openState, Database.cnf]
      rw [same]
      exact PreservesSatisfiability.refl initial
    · exact open_refuted_sound⟩

def addLearned (state : State) (id : ClauseId) (clause : Clause Nat) : State :=
  { state with
    live := state.live ++ [⟨id, clause⟩]
    highWater := id.wire
    refuted := state.refuted || clause.literals.isEmpty }

private theorem addLearned_cnf (state : State) (id : ClauseId)
    (clause : Clause Nat) :
    (addLearned state id clause).live.cnf =
      Cnf.mk (state.live.cnf.clauses ++ [clause]) := by
  apply congrArg Cnf.mk
  simp [addLearned, Database.cnf]

private theorem addLearned_valid {before : State} (valid : before.Valid)
    (id : ClauseId) (clause : Clause Nat) (rat : Rat before.live.cnf clause) :
    (addLearned before id clause).Valid := by
  have preservesLearned := valid.1.trans rat
  constructor
  · change PreservesSatisfiability before.initial (addLearned before id clause).live.cnf
    rw [addLearned_cnf]
    exact preservesLearned
  · intro refuted
    by_cases already : before.refuted = true
    · exact valid.2 already
    · have empty : clause.literals = [] := by
        have notAlready : before.refuted = false := Bool.eq_false_of_not_eq_true already
        have isEmpty : clause.literals.isEmpty = true := by
          simpa only [addLearned, notAlready, Bool.false_or] using refuted
        exact List.isEmpty_iff.mp isEmpty
      apply preservesLearned.unsat
      apply contains_empty_clause_unsat
      have clauseEmpty : clause = Clause.mk [] := by cases clause; simp_all
      simp [clauseEmpty]

def learnRup? (before : CheckedState) (id : ClauseId) (clause : Clause Nat)
    (hints : List ClauseId) : Option CheckedState :=
  if before.state.highWater < id.wire then
    match checkRup? before.state.live clause hints with
    | none => none
    | some checked =>
        some ⟨addLearned before.state id clause,
          addLearned_valid before.valid id clause (rat_of_rup checked.sound)⟩
  else
    none

def learnRat? (before : CheckedState) (id : ClauseId) (clause : Clause Nat)
    (pivot : Lit Nat) (prefixHints : List ClauseId) (groups : List RatGroup) :
    Option CheckedState :=
  if before.state.highWater < id.wire then
    match checkRat? before.state.live clause pivot prefixHints groups with
    | none => none
    | some checked =>
        some ⟨addLearned before.state id clause,
          addLearned_valid before.valid id clause checked.sound⟩
  else
    none

def forgetLive (database : Database) (ids : List ClauseId) : Database :=
  database.filter fun entry => decide (entry.id ∉ ids)

def forgetState (state : State) (ids : List ClauseId) : State :=
  { state with live := forgetLive state.live ids }

private theorem forget_valid {before : State} (valid : before.Valid)
    (ids : List ClauseId) : (forgetState before ids).Valid := by
  constructor
  · apply Nucleus.Hol.Ethane.ClassicalRefutation.delete before.initial
      before.live.cnf (forgetState before ids).live.cnf valid.1
    intro valuation truth clause member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
    have oldMember : entry ∈ before.live := (List.mem_filter.mp entryMember).1
    exact truth entry.clause (List.mem_map.mpr ⟨entry, oldMember, rfl⟩)
  · exact valid.2

def forget? (before : CheckedState) (ids : List ClauseId) : Option CheckedState :=
  if ids.Nodup && ids.all (fun id => (before.state.live.lookup? id).isSome) then
    some ⟨forgetState before.state ids, forget_valid before.valid ids⟩
  else
    none

inductive Step where
  | rup (id : ClauseId) (clause : Clause Nat) (hints : List ClauseId)
  | rat (id : ClauseId) (clause : Clause Nat) (pivot : Lit Nat)
      (prefixHints : List ClauseId) (groups : List RatGroup)
  | forget (ids : List ClauseId)
  deriving DecidableEq

def apply? (before : CheckedState) : Step → Option CheckedState
  | .rup id clause hints => learnRup? before id clause hints
  | .rat id clause pivot prefixHints groups =>
      learnRat? before id clause pivot prefixHints groups
  | .forget ids => forget? before ids

def replay? (initial : Cnf Nat) (steps : List Step) : Option CheckedState :=
  List.foldlM apply? (start initial) steps

structure Result (initial : Cnf Nat) : Type where
  private mk ::
  unsat : Unsat initial

def finish? (checked : CheckedState) : Option (Result checked.state.initial) :=
  if refuted : checked.state.refuted = true then
    some ⟨checked.valid.2 refuted⟩
  else
    none

/-- Replay a complete parser-independent proof and expose only its universal
unsatisfiability conclusion. -/
def refute? (initial : Cnf Nat) (steps : List Step) : Option (Result initial) := do
  let checked ← replay? initial steps
  if same : checked.state.initial = initial then
    let result ← finish? checked
    some ⟨same ▸ result.unsat⟩
  else
    none

private def testPositive : Clause Nat := ⟨[(0, false)]⟩
private def testNegative : Clause Nat := ⟨[(0, true)]⟩
private def testEmpty : Clause Nat := ⟨[]⟩
private def testTautologicalOpposing : Clause Nat :=
  ⟨[(0, true), (1, false), (1, true)]⟩

/-- Ordered RUP closes the canonical contradictory pair of unit clauses. -/
example : (refute? ⟨[testPositive, testNegative]⟩
    [.rup ⟨2⟩ testEmpty [⟨0⟩, ⟨1⟩]]).isSome = true := by
  rfl

/-- Exhausting the same proof without a conflict is rejected. -/
example : (refute? ⟨[testPositive]⟩
    [.rup ⟨1⟩ testEmpty [⟨0⟩]]).isSome = false := by
  rfl

/-- A blocked-pivot RAT step has no opposing groups. -/
example : (learnRat? (start ⟨[]⟩) ⟨0⟩ testPositive (0, false) [] []).isSome = true := by
  rfl

/-- A tautological opposing remainder closes a RAT group before hints run. -/
example : (checkGroup? [] [] testTautologicalOpposing (0, true) []).isSome = true := by
  rfl

end Checker

end Nucleus.Classical.Tagged.Runtime.Refutation
