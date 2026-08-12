import Mathlib.Data.List.Defs

/-! # Parser-independent LRAT clause kernel -/

namespace Nucleus.Lrat

inductive Literal where
  | positive : Nat → Literal
  | negative : Nat → Literal
  deriving DecidableEq, Repr

namespace Literal

def negate : Literal → Literal
  | positive index => negative index
  | negative index => positive index

@[simp] theorem negate_negate (literal : Literal) : literal.negate.negate = literal := by
  cases literal <;> rfl

def eval (assignment : Nat → Bool) : Literal → Bool
  | positive index => assignment index
  | negative index => !(assignment index)

@[simp] theorem eval_negate (assignment : Nat → Bool) (literal : Literal) :
    literal.negate.eval assignment = !(literal.eval assignment) := by
  cases literal <;> simp [eval, negate]

end Literal

abbrev Clause := List Literal
abbrev ClauseId := Nat
abbrev Assignment := Nat → Bool
abbrev Database := List (ClauseId × Clause)

def SatisfiesClause (assignment : Assignment) (clause : Clause) : Prop :=
  ∃ literal ∈ clause, literal.eval assignment = true

def SatisfiesDatabase (assignment : Assignment) (database : Database) : Prop :=
  ∀ entry ∈ database, SatisfiesClause assignment entry.2

def Unsatisfiable (database : Database) : Prop :=
  ¬∃ assignment, SatisfiesDatabase assignment database

def lookup (database : Database) (id : ClauseId) : Option Clause :=
  (database.find? fun entry => entry.1 = id).map Prod.snd

abbrev Trail := List Literal

inductive PropagationError where
  | unknownClause (id : ClauseId)
  | uselessHint (id : ClauseId)
  | noConflict
  deriving DecidableEq, Repr

inductive PropagationResult where
  | unit (trail : Trail)
  | conflict
  deriving DecidableEq, Repr

private def advance (trail : Trail) (clause : Clause) : Option PropagationResult :=
  if clause.any (trail.contains ·) then none
  else
    match clause.filter fun literal => !(trail.contains literal.negate) with
    | [] => some .conflict
    | [literal] => some (.unit (literal :: trail))
    | _ => none

/-- Executable ordered unit propagation; `true` means conflict. -/
def propagate (database : Database) (initialTrail : Trail) (hints : List ClauseId) :
    Except PropagationError Bool := do
  let mut trail := initialTrail
  for id in hints do
    let clause ← match lookup database id with
      | some clause => pure clause
      | none => throw (.unknownClause id)
    match advance trail clause with
    | none => throw (.uselessHint id)
    | some .conflict => return true
    | some (.unit next) => trail := next
  throw .noConflict

structure RatGroup where
  opposingClauseId : ClauseId
  resolventRupHints : List ClauseId
  deriving DecidableEq, Repr

def resolvent (clause opposing : Clause) (pivot : Literal) : Clause :=
  (clause.filter (· != pivot)) ++ (opposing.filter (· != pivot.negate))

def Tautological (clause : Clause) : Prop :=
  ∃ literal ∈ clause, literal.negate ∈ clause

def tautological (clause : Clause) : Bool :=
  clause.any fun literal => clause.contains literal.negate

theorem tautological_iff (clause : Clause) :
    tautological clause = true ↔ Tautological clause := by
  simp [tautological, Tautological]

def opposingClauseIds (database : Database) (pivot : Literal) : List ClauseId :=
  (database.filter fun entry => entry.2.contains pivot.negate).map Prod.fst

/-- Every opposing live clause occurs in exactly one explicit RAT group. -/
def exactRatCoverage (database : Database) (pivot : Literal) (groups : List RatGroup) : Bool :=
  let supplied := groups.map RatGroup.opposingClauseId
  supplied.Nodup &&
    (opposingClauseIds database pivot).all supplied.contains &&
    supplied.all (opposingClauseIds database pivot).contains

/-- The versioned parser-independent vocabulary shared with Rust. -/
inductive ValidatorCall where
  | learnRup (id : ClauseId) (clause : Clause) (orderedHints : List ClauseId)
  | learnRat (id : ClauseId) (clause : Clause) (pivot : Literal)
      (prefixRupHints : List ClauseId) (groups : List RatGroup)
  | forget (ids : List ClauseId)
  deriving DecidableEq, Repr

structure State where
  initial : Database
  live : Database
  highWater : ClauseId
  refuted : Bool
  deriving DecidableEq, Repr

def numberClauses : List Clause → Nat → Database
  | [], _ => []
  | clause :: clauses, next => (next, clause) :: numberClauses clauses (next + 1)

def openState (clauses : List Clause) : State :=
  let numbered := numberClauses clauses 1
  { initial := numbered, live := numbered, highWater := clauses.length, refuted := false }

def forget (state : State) (ids : List ClauseId) : State :=
  { state with live := state.live.filter (fun entry => !(ids.contains entry.1)) }

/-- Freshness remains monotone across deletion. -/
@[simp] theorem forget_highWater (state : State) (ids : List ClauseId) :
    (forget state ids).highWater = state.highWater := rfl

def ModelsInitialImplyLive (state : State) : Prop :=
  ∀ assignment, SatisfiesDatabase assignment state.initial →
    SatisfiesDatabase assignment state.live

def Entails (database : Database) (clause : Clause) : Prop :=
  ∀ assignment, SatisfiesDatabase assignment database → SatisfiesClause assignment clause

def addLearned (state : State) (id : ClauseId) (clause : Clause) : State :=
  { state with
    live := (id, clause) :: state.live
    highWater := id
    refuted := state.refuted || clause.isEmpty }

theorem learned_consequence_invariant (state : State) (id : ClauseId) (clause : Clause)
    (invariant : ModelsInitialImplyLive state) (consequence : Entails state.initial clause) :
    ModelsInitialImplyLive (addLearned state id clause) := by
  intro assignment models entry member
  simp only [addLearned, List.mem_cons] at member
  rcases member with rfl | old
  · exact consequence assignment models
  · exact invariant assignment models entry old

theorem open_invariant (clauses : List Clause) : ModelsInitialImplyLive (openState clauses) := by
  intro assignment models
  exact models

/-- Deletion preserves the live-clause soundness invariant. -/
theorem forget_invariant (state : State) (ids : List ClauseId)
    (invariant : ModelsInitialImplyLive state) :
    ModelsInitialImplyLive (forget state ids) := by
  intro assignment models entry member
  apply invariant assignment models entry
  exact (List.mem_filter.mp member).1

theorem empty_clause_unsatisfied (assignment : Assignment) :
    ¬SatisfiesClause assignment [] := by
  simp [SatisfiesClause]

/-- Successful validation ending in an empty live clause proves initial-CNF UNSAT. -/
theorem validator_success_ending_empty_implies_initial_unsat
    (state : State) (invariant : ModelsInitialImplyLive state)
    (emptyLive : ∃ id, (id, []) ∈ state.live) : Unsatisfiable state.initial := by
  rintro ⟨assignment, models⟩
  obtain ⟨id, emptyMember⟩ := emptyLive
  have emptySatisfied := invariant assignment models (id, []) emptyMember
  exact empty_clause_unsatisfied assignment emptySatisfied

def acceptedTrace : List ValidatorCall := [.learnRup 3 [] [1, 2]]
def rejectedTrace : List ValidatorCall := [.learnRup 2 [] [1, 99]]

example : propagate [(1, [.positive 0]), (2, [.negative 0])] [] [1, 2] = .ok true := by
  rfl

example : propagate [(1, [.positive 0])] [] [99] = .error (.unknownClause 99) := by
  rfl

end Nucleus.Lrat
