import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Lex

/-!
# Classical CNF-to-DNF matrix sequents

This module is the representation-independent specification of the reusable
classical theorem arena.  The left side is a conjunction of disjunctive
clauses (CNF), while the right side is a disjunction of conjunctive cubes
(DNF).  In particular, the two physically identical list-of-lists have
different polarity-aware types and meanings.

Empty rows and matrices have their standard meanings: an empty clause is
false, an empty CNF is true, an empty cube is true, and an empty DNF is false.
Normalization only sorts and removes duplicates; it performs no semantic
simplification.
-/

namespace Nucleus.Hol.Ethane.ClassicalMatrix

variable {Atom : Type}

/-- A literal carries an atom and a polarity bit. `false` is positive. -/
abbrev Lit (Atom : Type) := Atom × Bool

/-- Rust's compact literal representation: nonzero signed `i32`, excluding
both extrema used by fallible integer negation.  The semantic development uses
`Lit Atom`; this structure formalizes the representation invariant separately. -/
structure LitCode where
  value : Int
  nonzero : value ≠ 0
  lower : -2_147_483_647 < value
  upper : value < 2_147_483_647
  deriving DecidableEq

/-- Negation of a valid literal code is total and remains valid. -/
def LitCode.neg (literal : LitCode) : LitCode :=
  ⟨-literal.value, by
    intro equal
    exact literal.nonzero (Int.neg_eq_zero.mp equal), by
      have := literal.upper
      omega, by
      have := literal.lower
      omega⟩

theorem LitCode.ext (left right : LitCode) (equal : left.value = right.value) : left = right := by
  cases left
  cases right
  simp_all

@[simp] theorem LitCode.neg_neg (literal : LitCode) : literal.neg.neg = literal := by
  apply LitCode.ext
  simp [LitCode.neg]

/-- Complement a literal without inspecting its atom. -/
def Lit.neg {Atom : Type} (literal : Lit Atom) : Lit Atom :=
  (literal.1, !literal.2)

@[simp] theorem Lit.neg_neg {Atom : Type} (literal : Lit Atom) :
    literal.neg.neg = literal := by
  simp [Lit.neg]

structure Clause (Atom : Type) where
  literals : List (Lit Atom)
  deriving DecidableEq

structure Cnf (Atom : Type) where
  clauses : List (Clause Atom)
  deriving DecidableEq

structure Cube (Atom : Type) where
  literals : List (Lit Atom)
  deriving DecidableEq

structure Dnf (Atom : Type) where
  cubes : List (Cube Atom)
  deriving DecidableEq

structure Sequent (Atom : Type) where
  left : Cnf Atom
  right : Dnf Atom
  deriving DecidableEq

/-- A valuation is deliberately over unsigned atoms. -/
abbrev Valuation (Atom : Type) := Atom → Prop

def Lit.Holds {Atom : Type} (valuation : Valuation Atom) (literal : Lit Atom) : Prop :=
  if literal.2 then ¬valuation literal.1 else valuation literal.1

@[simp] theorem Lit.holds_neg {Atom : Type} (valuation : Valuation Atom)
    (literal : Lit Atom) : literal.neg.Holds valuation ↔ ¬literal.Holds valuation := by
  cases literal with
  | mk atom polarity =>
      cases polarity <;> simp [Lit.neg, Lit.Holds]

def Clause.Holds {Atom : Type} (valuation : Valuation Atom) (clause : Clause Atom) : Prop :=
  ∃ literal ∈ clause.literals, literal.Holds valuation

def Cnf.Holds {Atom : Type} (valuation : Valuation Atom) (cnf : Cnf Atom) : Prop :=
  ∀ clause ∈ cnf.clauses, clause.Holds valuation

def Cube.Holds {Atom : Type} (valuation : Valuation Atom) (cube : Cube Atom) : Prop :=
  ∀ literal ∈ cube.literals, literal.Holds valuation

def Dnf.Holds {Atom : Type} (valuation : Valuation Atom) (dnf : Dnf Atom) : Prop :=
  ∃ cube ∈ dnf.cubes, cube.Holds valuation

def Sequent.Holds {Atom : Type} (valuation : Valuation Atom) (sequent : Sequent Atom) : Prop :=
  sequent.left.Holds valuation → sequent.right.Holds valuation

def Sequent.Sound {Atom : Type} (sequent : Sequent Atom) : Prop :=
  ∀ valuation, sequent.Holds valuation

/-! ## Untyped atoms and partial HOL interpretations

The classical arena deliberately does not know which atoms name well-typed HOL
propositions.  Its soundness quantifies over every total Boolean valuation of
the atom type.  A HOL arena may therefore interpret the atoms it recognizes
and leave every other atom indeterminate: any assignment to the unknown atoms
is a completion, and a universally sound syllogism holds for every such
completion.
-/

/-- A consumer such as HOL may know the meaning of only some classical atoms. -/
abbrev PartialValuation (Atom : Type) := Atom → Option Prop

/-- A total Boolean valuation agrees with every atom whose meaning is known. -/
def Valuation.Completes {Atom : Type} (valuation : Valuation Atom)
    (interpretation : PartialValuation Atom) : Prop :=
  ∀ atom proposition, interpretation atom = some proposition →
    (valuation atom ↔ proposition)

/-- Universally sound syllogisms remain valid under every completion of a
partial HOL interpretation.  No typing premise is needed for unknown atoms. -/
theorem Sequent.Sound.holds_of_completion {Atom : Type} {sequent : Sequent Atom}
    (sound : sequent.Sound) (interpretation : PartialValuation Atom)
    (valuation : Valuation Atom) (_completion : valuation.Completes interpretation) :
    sequent.Holds valuation :=
  sound valuation

/-- Complete known atoms with an entirely caller-chosen valuation for unknown
atoms.  The fallback is semantically relevant only where the interpretation
returns `none`. -/
def PartialValuation.complete {Atom : Type} (interpretation : PartialValuation Atom)
    (fallback : Valuation Atom) : Valuation Atom := fun atom =>
  match interpretation atom with
  | some proposition => proposition
  | none => fallback atom

theorem PartialValuation.complete_completes {Atom : Type}
    (interpretation : PartialValuation Atom) (fallback : Valuation Atom) :
    (interpretation.complete fallback).Completes interpretation := by
  intro atom proposition known
  simp [PartialValuation.complete, known]

@[simp] theorem PartialValuation.complete_unknown {Atom : Type}
    (interpretation : PartialValuation Atom) (fallback : Valuation Atom) (atom : Atom)
    (unknown : interpretation atom = none) :
    interpretation.complete fallback atom = fallback atom := by
  simp [PartialValuation.complete, unknown]

/-- There is always a completion: unknown atoms may receive an arbitrary
Boolean value.  This witnesses the intended indeterminate semantics. -/
theorem PartialValuation.exists_completion {Atom : Type}
    (interpretation : PartialValuation Atom) :
    ∃ valuation : Valuation Atom, valuation.Completes interpretation := by
  exact ⟨interpretation.complete fun _ => False,
    interpretation.complete_completes fun _ => False⟩

@[simp] theorem empty_clause_false {Atom : Type} (valuation : Valuation Atom) :
    ¬(Clause.mk []).Holds valuation := by
  simp [Clause.Holds]

@[simp] theorem empty_cnf_true {Atom : Type} (valuation : Valuation Atom) :
    (Cnf.mk []).Holds valuation := by
  simp [Cnf.Holds]

@[simp] theorem empty_cube_true {Atom : Type} (valuation : Valuation Atom) :
    (Cube.mk []).Holds valuation := by
  simp [Cube.Holds]

@[simp] theorem empty_dnf_false {Atom : Type} (valuation : Valuation Atom) :
    ¬(Dnf.mk []).Holds valuation := by
  simp [Dnf.Holds]

/-- Pointwise complement turns a disjunctive clause into a conjunctive cube. -/
def Clause.neg {Atom : Type} (clause : Clause Atom) : Cube Atom :=
  ⟨clause.literals.map Lit.neg⟩

/-- Pointwise complement turns a conjunctive cube into a disjunctive clause. -/
def Cube.neg {Atom : Type} (cube : Cube Atom) : Clause Atom :=
  ⟨cube.literals.map Lit.neg⟩

@[simp] theorem Clause.neg_neg {Atom : Type} (clause : Clause Atom) :
    clause.neg.neg = clause := by
  cases clause
  simp [Clause.neg, Cube.neg, List.map_map, Function.comp_def]

@[simp] theorem Cube.neg_neg {Atom : Type} (cube : Cube Atom) :
    cube.neg.neg = cube := by
  cases cube
  simp [Clause.neg, Cube.neg, List.map_map, Function.comp_def]

theorem Clause.neg_holds {Atom : Type} (valuation : Valuation Atom) (clause : Clause Atom) :
    clause.neg.Holds valuation ↔ ¬clause.Holds valuation := by
  simp only [Clause.neg, Cube.Holds, Clause.Holds, List.mem_map]
  constructor
  · intro all ⟨literal, member, truth⟩
    exact (Lit.holds_neg valuation literal).mp (all literal.neg ⟨literal, member, rfl⟩) truth
  · intro notClause literal member
    obtain ⟨source, sourceMember, rfl⟩ := member
    rw [Lit.holds_neg]
    intro truth
    exact notClause ⟨source, sourceMember, truth⟩

theorem Cube.neg_holds {Atom : Type} (valuation : Valuation Atom) (cube : Cube Atom) :
    cube.neg.Holds valuation ↔ ¬cube.Holds valuation := by
  simp only [Cube.neg, Clause.Holds, Cube.Holds, List.mem_map]
  constructor
  · rintro ⟨literal, ⟨source, sourceMember, equal⟩, truth⟩ all
    subst literal
    exact ((Lit.holds_neg valuation source).mp truth) (all source sourceMember)
  · intro notCube
    by_contra noComplement
    push Not at noComplement
    apply notCube
    intro literal member
    by_contra false
    exact noComplement literal.neg ⟨literal, member, rfl⟩
      ((Lit.holds_neg valuation literal).mpr false)

/-! ## Backward-compatible singleton embedding -/

def embedLeft {Atom : Type} (premises : List (Lit Atom)) : Cnf Atom :=
  ⟨premises.map fun literal => Clause.mk [literal]⟩

def embedRight {Atom : Type} (conclusions : List (Lit Atom)) : Dnf Atom :=
  ⟨conclusions.map fun literal => Cube.mk [literal]⟩

@[simp] theorem embedLeft_holds {Atom : Type} (valuation : Valuation Atom)
    (premises : List (Lit Atom)) :
    (embedLeft premises).Holds valuation ↔
      ∀ literal ∈ premises, literal.Holds valuation := by
  constructor
  · intro all literal member
    have singleton := all (Clause.mk [literal]) (by simp [embedLeft, member])
    simpa [Clause.Holds] using singleton
  · intro all clause member
    obtain ⟨literal, literalMember, rfl⟩ := (List.mem_map.mp member)
    simpa [Clause.Holds] using all literal literalMember

@[simp] theorem embedRight_holds {Atom : Type} (valuation : Valuation Atom)
    (conclusions : List (Lit Atom)) :
    (embedRight conclusions).Holds valuation ↔
      ∃ literal ∈ conclusions, literal.Holds valuation := by
  constructor
  · rintro ⟨cube, member, truth⟩
    obtain ⟨literal, literalMember, rfl⟩ := List.mem_map.mp member
    exact ⟨literal, literalMember, by simpa [Cube.Holds] using truth⟩
  · rintro ⟨literal, member, truth⟩
    exact ⟨Cube.mk [literal], by simp [embedRight, member], by simpa [Cube.Holds]⟩

/-! ## Sort-and-deduplicate normalization -/

def canonical [LinearOrder α] (values : List α) : List α :=
  values.toFinset.sort (· ≤ ·)

@[simp] theorem mem_canonical [LinearOrder α] (value : α) (values : List α) :
    value ∈ canonical values ↔ value ∈ values := by
  simp [canonical]

def Clause.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (clause : Clause Atom) : Clause Atom :=
  ⟨canonical clause.literals⟩

def Cube.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)] (cube : Cube Atom) : Cube Atom :=
  ⟨canonical cube.literals⟩

def Cnf.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)] (cnf : Cnf Atom) : Cnf Atom :=
  ⟨(canonical (cnf.clauses.map fun (clause : Clause Atom) => canonical clause.literals)).map
    Clause.mk⟩

def Dnf.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)] (dnf : Dnf Atom) : Dnf Atom :=
  ⟨(canonical (dnf.cubes.map fun (cube : Cube Atom) => canonical cube.literals)).map Cube.mk⟩

def Sequent.normalize [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (sequent : Sequent Atom) : Sequent Atom :=
  ⟨sequent.left.normalize, sequent.right.normalize⟩

@[simp] theorem Clause.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (clause : Clause Atom) : clause.normalize.Holds valuation ↔ clause.Holds valuation := by
  simp [Clause.normalize, Clause.Holds]

@[simp] theorem Cube.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (cube : Cube Atom) : cube.normalize.Holds valuation ↔ cube.Holds valuation := by
  simp [Cube.normalize, Cube.Holds]

@[simp] theorem Cnf.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (cnf : Cnf Atom) : cnf.normalize.Holds valuation ↔ cnf.Holds valuation := by
  constructor
  · intro normalized clause member
    have rowMember : canonical clause.literals ∈
        canonical (cnf.clauses.map fun (source : Clause Atom) => canonical source.literals) := by
      rw [mem_canonical]
      exact List.mem_map.mpr ⟨clause, member, rfl⟩
    have rowTruth := normalized (Clause.mk (canonical clause.literals)) (by
      simp only [Cnf.normalize, List.mem_map]
      exact ⟨canonical clause.literals, rowMember, rfl⟩)
    exact (Clause.normalize_holds valuation clause).mp rowTruth
  · intro source normalizedClause normalizedMember
    simp only [Cnf.normalize, List.mem_map] at normalizedMember
    obtain ⟨row, rowMember, rfl⟩ := normalizedMember
    rw [mem_canonical] at rowMember
    obtain ⟨clause, clauseMember, rfl⟩ := List.mem_map.mp rowMember
    exact (Clause.normalize_holds valuation clause).mpr (source clause clauseMember)

@[simp] theorem Dnf.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (dnf : Dnf Atom) : dnf.normalize.Holds valuation ↔ dnf.Holds valuation := by
  constructor
  · rintro ⟨normalizedCube, normalizedMember, normalizedTruth⟩
    simp only [Dnf.normalize, List.mem_map] at normalizedMember
    obtain ⟨row, rowMember, rfl⟩ := normalizedMember
    rw [mem_canonical] at rowMember
    obtain ⟨cube, cubeMember, rfl⟩ := List.mem_map.mp rowMember
    exact ⟨cube, cubeMember, (Cube.normalize_holds valuation cube).mp normalizedTruth⟩
  · rintro ⟨cube, cubeMember, cubeTruth⟩
    refine ⟨Cube.mk (canonical cube.literals), ?_,
      (Cube.normalize_holds valuation cube).mpr cubeTruth⟩
    simp only [Dnf.normalize, List.mem_map]
    refine ⟨canonical cube.literals, ?_, rfl⟩
    rw [mem_canonical]
    exact List.mem_map.mpr ⟨cube, cubeMember, rfl⟩

@[simp] theorem Sequent.normalize_holds [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (valuation : Valuation Atom)
    (sequent : Sequent Atom) : sequent.normalize.Holds valuation ↔ sequent.Holds valuation := by
  simp [Sequent.normalize, Sequent.Holds]

theorem normalize_sound_iff [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (sequent : Sequent Atom) :
    sequent.normalize.Sound ↔ sequent.Sound := by
  simp [Sequent.Sound]

/-! ## Primitive matrix rules -/

theorem identity (literal : Lit Atom) :
    (Sequent.mk (Cnf.mk [Clause.mk [literal]]) (Dnf.mk [Cube.mk [literal]])).Sound := by
  intro valuation premise
  have clauseTruth := premise (Clause.mk [literal]) (by simp)
  obtain ⟨found, member, truth⟩ := clauseTruth
  have equal : found = literal := by simpa using member
  subst found
  exact ⟨Cube.mk [literal], by simp, by simpa [Cube.Holds]⟩

/-- Adding left clauses strengthens an antecedent; adding right cubes weakens
the consequent. -/
theorem weaken {sourceLeft extraLeft : List (Clause Atom)}
    {sourceRight extraRight : List (Cube Atom)}
    (sound : (Sequent.mk (Cnf.mk sourceLeft) (Dnf.mk sourceRight)).Sound) :
    (Sequent.mk (Cnf.mk (sourceLeft ++ extraLeft))
      (Dnf.mk (sourceRight ++ extraRight))).Sound := by
  intro valuation targetLeft
  obtain ⟨cube, member, truth⟩ := sound valuation (by
    intro clause member
    exact targetLeft clause (List.mem_append_left _ member))
  exact ⟨cube, List.mem_append_left _ member, truth⟩

/-- Indexed transfer: remove one left clause and insert its complemented cube
on the right. The list decomposition is the proof-level form of a checked row
index. -/
theorem transferClauseRight {before after : List (Clause Atom)} {right : List (Cube Atom)}
    (clause : Clause Atom)
    (sound : (Sequent.mk (Cnf.mk (before ++ clause :: after)) (Dnf.mk right)).Sound) :
    (Sequent.mk (Cnf.mk (before ++ after)) (Dnf.mk (clause.neg :: right))).Sound := by
  intro valuation left
  by_cases clauseTruth : clause.Holds valuation
  · obtain ⟨cube, member, truth⟩ := sound valuation (by
      intro candidate member
      rcases List.mem_append.mp member with member | member
      · exact left candidate (List.mem_append_left _ member)
      · simp only [List.mem_cons] at member
        rcases member with equal | member
        · simpa [equal] using clauseTruth
        · exact left candidate (List.mem_append_right _ member))
    exact ⟨cube, by simp [member], truth⟩
  · exact ⟨clause.neg, by simp, (Clause.neg_holds valuation clause).mpr clauseTruth⟩

/-- Indexed transfer: remove one right cube and insert its complemented clause
on the left. -/
theorem transferCubeLeft {left : List (Clause Atom)} {before after : List (Cube Atom)}
    (cube : Cube Atom)
    (sound : (Sequent.mk (Cnf.mk left) (Dnf.mk (before ++ cube :: after))).Sound) :
    (Sequent.mk (Cnf.mk (cube.neg :: left)) (Dnf.mk (before ++ after))).Sound := by
  intro valuation premises
  obtain ⟨candidate, member, truth⟩ := sound valuation (by
    intro clause member
    exact premises clause (by simp [member]))
  rcases List.mem_append.mp member with member | member
  · exact ⟨candidate, List.mem_append_left _ member, truth⟩
  · simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst candidate
      have notCube : ¬cube.Holds valuation := (Cube.neg_holds valuation cube).mp
        (premises cube.neg (by simp))
      exact (notCube truth).elim
    · exact ⟨candidate, List.mem_append_right _ member, truth⟩

/-- Singleton cut between a right cube and a left clause. -/
theorem cut (pivot : Lit Atom) {leftPrem rightPrem : List (Clause Atom)}
    {leftConc rightConc : List (Cube Atom)}
    (leftSound : (Sequent.mk (Cnf.mk leftPrem)
      (Dnf.mk (Cube.mk [pivot] :: leftConc))).Sound)
    (rightSound : (Sequent.mk (Cnf.mk (Clause.mk [pivot] :: rightPrem))
      (Dnf.mk rightConc)).Sound) :
    (Sequent.mk (Cnf.mk (leftPrem ++ rightPrem))
      (Dnf.mk (leftConc ++ rightConc))).Sound := by
  intro valuation premises
  obtain ⟨cube, member, truth⟩ := leftSound valuation (by
    intro clause member
    exact premises clause (List.mem_append_left _ member))
  simp only [List.mem_cons] at member
  rcases member with equal | member
  · subst cube
    have pivotTruth : pivot.Holds valuation := by
      simpa [Cube.Holds] using truth
    obtain ⟨cube, member, truth⟩ := rightSound valuation (by
      intro clause member
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · subst clause
        simpa [Clause.Holds] using pivotTruth
      · exact premises clause (List.mem_append_right _ member))
    exact ⟨cube, List.mem_append_right _ member, truth⟩
  · exact ⟨cube, List.mem_append_left _ member, truth⟩

/-- Resolution between complementary singleton cubes. -/
theorem resolution (pivot : Lit Atom) {leftPrem rightPrem : List (Clause Atom)}
    {leftConc rightConc : List (Cube Atom)}
    (leftSound : (Sequent.mk (Cnf.mk leftPrem)
      (Dnf.mk (Cube.mk [pivot] :: leftConc))).Sound)
    (rightSound : (Sequent.mk (Cnf.mk rightPrem)
      (Dnf.mk (Cube.mk [pivot.neg] :: rightConc))).Sound) :
    (Sequent.mk (Cnf.mk (leftPrem ++ rightPrem))
      (Dnf.mk (leftConc ++ rightConc))).Sound := by
  intro valuation premises
  by_cases truth : pivot.Holds valuation
  · obtain ⟨cube, member, cubeTruth⟩ := rightSound valuation (by
      intro clause member
      exact premises clause (List.mem_append_right _ member))
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst cube
      have complement : pivot.neg.Holds valuation := by simpa [Cube.Holds] using cubeTruth
      exact ((Lit.holds_neg valuation pivot).mp complement truth).elim
    · exact ⟨cube, List.mem_append_right _ member, cubeTruth⟩
  · obtain ⟨cube, member, cubeTruth⟩ := leftSound valuation (by
      intro clause member
      exact premises clause (List.mem_append_left _ member))
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst cube
      have pivotTruth : pivot.Holds valuation := by simpa [Cube.Holds] using cubeTruth
      exact (truth pivotTruth).elim
    · exact ⟨cube, List.mem_append_left _ member, cubeTruth⟩

/-! ## HOL connective schemas

The classical arena treats literals as opaque.  The HOL kernel discharges the
displayed semantic equation after checking the corresponding opcode.  These
theorems therefore isolate the complete propositional obligation of each HOL
rule, with arbitrary matrix contexts on both sides. -/

@[simp] theorem singleton_clause_holds (valuation : Valuation Atom) (literal : Lit Atom) :
    (Clause.mk [literal]).Holds valuation ↔ literal.Holds valuation := by
  simp [Clause.Holds]

@[simp] theorem singleton_cube_holds (valuation : Valuation Atom) (literal : Lit Atom) :
    (Cube.mk [literal]).Holds valuation ↔ literal.Holds valuation := by
  simp [Cube.Holds]

theorem notLeft {left : List (Clause Atom)} {right : List (Cube Atom)} (p : Lit Atom)
    (sound : (Sequent.mk (Cnf.mk left) (Dnf.mk (Cube.mk [p] :: right))).Sound) :
    (Sequent.mk (Cnf.mk (Clause.mk [p.neg] :: left)) (Dnf.mk right)).Sound := by
  simpa [Cube.neg] using transferCubeLeft (before := []) (after := right) (Cube.mk [p]) sound

theorem notRight {left : List (Clause Atom)} {right : List (Cube Atom)} (p : Lit Atom)
    (sound : (Sequent.mk (Cnf.mk (Clause.mk [p] :: left)) (Dnf.mk right)).Sound) :
    (Sequent.mk (Cnf.mk left) (Dnf.mk (Cube.mk [p.neg] :: right))).Sound := by
  simpa [Clause.neg] using transferClauseRight (before := []) (after := left)
    (right := right) (Clause.mk [p]) sound

theorem falseLeft (falsehood : Lit Atom)
    (meaning : ∀ valuation, ¬falsehood.Holds valuation) :
    (Sequent.mk (Cnf.mk [Clause.mk [falsehood]]) (Dnf.mk [])).Sound := by
  intro valuation premises
  exact (meaning valuation ((singleton_clause_holds valuation falsehood).mp
    (premises (Clause.mk [falsehood]) (by simp)))).elim

theorem trueRight (truth : Lit Atom)
    (meaning : ∀ valuation, truth.Holds valuation) :
    (Sequent.mk (Cnf.mk []) (Dnf.mk [Cube.mk [truth]])).Sound := by
  intro valuation _
  exact ⟨Cube.mk [truth], by simp, (singleton_cube_holds valuation truth).mpr (meaning valuation)⟩

theorem andLeft {left : List (Clause Atom)} {right : List (Cube Atom)}
    (p q conjunction : Lit Atom)
    (meaning : ∀ valuation, conjunction.Holds valuation ↔
      p.Holds valuation ∧ q.Holds valuation)
    (sound : (Sequent.mk (Cnf.mk (Clause.mk [p] :: Clause.mk [q] :: left))
      (Dnf.mk right)).Sound) :
    (Sequent.mk (Cnf.mk (Clause.mk [conjunction] :: left)) (Dnf.mk right)).Sound := by
  intro valuation premises
  apply sound valuation
  intro clause member
  simp only [List.mem_cons] at member
  rcases member with rfl | rfl | member
  · have conjunctionTruth := (singleton_clause_holds valuation conjunction).mp
      (premises (Clause.mk [conjunction]) (by simp))
    exact (singleton_clause_holds valuation p).mpr ((meaning valuation).mp conjunctionTruth).1
  · have conjunctionTruth := (singleton_clause_holds valuation conjunction).mp
      (premises (Clause.mk [conjunction]) (by simp))
    exact (singleton_clause_holds valuation q).mpr ((meaning valuation).mp conjunctionTruth).2
  · exact premises clause (by simp [member])

theorem andRight {leftPrem rightPrem : List (Clause Atom)}
    {leftConc rightConc : List (Cube Atom)} (p q conjunction : Lit Atom)
    (meaning : ∀ valuation, conjunction.Holds valuation ↔
      p.Holds valuation ∧ q.Holds valuation)
    (leftSound : (Sequent.mk (Cnf.mk leftPrem)
      (Dnf.mk (Cube.mk [p] :: leftConc))).Sound)
    (rightSound : (Sequent.mk (Cnf.mk rightPrem)
      (Dnf.mk (Cube.mk [q] :: rightConc))).Sound) :
    (Sequent.mk (Cnf.mk (leftPrem ++ rightPrem))
      (Dnf.mk (leftConc ++ rightConc ++ [Cube.mk [conjunction]]))).Sound := by
  intro valuation premises
  have leftResult := leftSound valuation (by
    intro clause member
    exact premises clause (List.mem_append_left _ member))
  have rightResult := rightSound valuation (by
    intro clause member
    exact premises clause (List.mem_append_right _ member))
  rcases leftResult with ⟨leftCube, leftMember, leftTruth⟩
  rcases rightResult with ⟨rightCube, rightMember, rightTruth⟩
  simp only [List.mem_cons] at leftMember rightMember
  rcases leftMember with rfl | leftMember
  · rcases rightMember with rfl | rightMember
    · refine ⟨Cube.mk [conjunction], by simp, ?_⟩
      apply (singleton_cube_holds valuation conjunction).mpr
      exact (meaning valuation).mpr
        ⟨(singleton_cube_holds valuation p).mp leftTruth,
          (singleton_cube_holds valuation q).mp rightTruth⟩
    · exact ⟨rightCube, by simp [rightMember], rightTruth⟩
  · exact ⟨leftCube, by simp [leftMember], leftTruth⟩

theorem orLeft {leftPrem rightPrem : List (Clause Atom)}
    {leftConc rightConc : List (Cube Atom)} (p q disjunction : Lit Atom)
    (meaning : ∀ valuation, disjunction.Holds valuation ↔
      p.Holds valuation ∨ q.Holds valuation)
    (leftSound : (Sequent.mk (Cnf.mk (Clause.mk [p] :: leftPrem))
      (Dnf.mk leftConc)).Sound)
    (rightSound : (Sequent.mk (Cnf.mk (Clause.mk [q] :: rightPrem))
      (Dnf.mk rightConc)).Sound) :
    (Sequent.mk (Cnf.mk (Clause.mk [disjunction] :: leftPrem ++ rightPrem))
      (Dnf.mk (leftConc ++ rightConc))).Sound := by
  intro valuation premises
  have disjunctionTruth := (singleton_clause_holds valuation disjunction).mp
    (premises (Clause.mk [disjunction]) (by simp))
  rcases (meaning valuation).mp disjunctionTruth with pTruth | qTruth
  · obtain ⟨cube, member, truth⟩ := leftSound valuation (by
      intro clause member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact (singleton_clause_holds valuation p).mpr pTruth
      · exact premises clause (by simp [member]))
    exact ⟨cube, List.mem_append_left _ member, truth⟩
  · obtain ⟨cube, member, truth⟩ := rightSound valuation (by
      intro clause member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact (singleton_clause_holds valuation q).mpr qTruth
      · exact premises clause (by simp [member]))
    exact ⟨cube, List.mem_append_right _ member, truth⟩

theorem orRight {left : List (Clause Atom)} {right : List (Cube Atom)}
    (p q disjunction : Lit Atom)
    (meaning : ∀ valuation, disjunction.Holds valuation ↔
      p.Holds valuation ∨ q.Holds valuation)
    (sound : (Sequent.mk (Cnf.mk left)
      (Dnf.mk (Cube.mk [p] :: Cube.mk [q] :: right))).Sound) :
    (Sequent.mk (Cnf.mk left) (Dnf.mk (Cube.mk [disjunction] :: right))).Sound := by
  intro valuation premises
  obtain ⟨cube, member, truth⟩ := sound valuation premises
  simp only [List.mem_cons] at member
  rcases member with rfl | rfl | member
  · exact ⟨Cube.mk [disjunction], by simp,
      (singleton_cube_holds valuation disjunction).mpr ((meaning valuation).mpr
        (Or.inl ((singleton_cube_holds valuation p).mp truth)))⟩
  · exact ⟨Cube.mk [disjunction], by simp,
      (singleton_cube_holds valuation disjunction).mpr ((meaning valuation).mpr
        (Or.inr ((singleton_cube_holds valuation q).mp truth)))⟩
  · exact ⟨cube, by simp [member], truth⟩

theorem impLeft {leftPrem rightPrem : List (Clause Atom)}
    {leftConc rightConc : List (Cube Atom)} (p q implication : Lit Atom)
    (meaning : ∀ valuation, implication.Holds valuation ↔
      (p.Holds valuation → q.Holds valuation))
    (leftSound : (Sequent.mk (Cnf.mk leftPrem)
      (Dnf.mk (Cube.mk [p] :: leftConc))).Sound)
    (rightSound : (Sequent.mk (Cnf.mk (Clause.mk [q] :: rightPrem))
      (Dnf.mk rightConc)).Sound) :
    (Sequent.mk (Cnf.mk (Clause.mk [implication] :: leftPrem ++ rightPrem))
      (Dnf.mk (leftConc ++ rightConc))).Sound := by
  intro valuation premises
  have implicationTruth := (meaning valuation).mp
    ((singleton_clause_holds valuation implication).mp
      (premises (Clause.mk [implication]) (by simp)))
  obtain ⟨cube, member, truth⟩ := leftSound valuation (by
    intro clause member
    exact premises clause (by simp [member]))
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · have pTruth := (singleton_cube_holds valuation p).mp truth
    obtain ⟨cube, member, truth⟩ := rightSound valuation (by
      intro clause member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact (singleton_clause_holds valuation q).mpr (implicationTruth pTruth)
      · exact premises clause (by simp [member]))
    exact ⟨cube, List.mem_append_right _ member, truth⟩
  · exact ⟨cube, List.mem_append_left _ member, truth⟩

theorem impRight {left : List (Clause Atom)} {right : List (Cube Atom)}
    (p q implication : Lit Atom)
    (meaning : ∀ valuation, implication.Holds valuation ↔
      (p.Holds valuation → q.Holds valuation))
    (sound : (Sequent.mk (Cnf.mk (Clause.mk [p] :: left))
      (Dnf.mk (Cube.mk [q] :: right))).Sound) :
    (Sequent.mk (Cnf.mk left) (Dnf.mk (Cube.mk [implication] :: right))).Sound := by
  intro valuation premises
  by_cases implicationTruth : implication.Holds valuation
  · exact ⟨Cube.mk [implication], by simp,
      (singleton_cube_holds valuation implication).mpr implicationTruth⟩
  · have pTruth : p.Holds valuation := by
      by_contra pFalse
      exact implicationTruth ((meaning valuation).mpr (fun truth => (pFalse truth).elim))
    obtain ⟨cube, member, truth⟩ := sound valuation (by
      intro clause member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact (singleton_clause_holds valuation p).mpr pTruth
      · exact premises clause member)
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · have qTruth := (singleton_cube_holds valuation q).mp truth
      exact (implicationTruth ((meaning valuation).mpr (fun _ => qTruth))).elim
    · exact ⟨cube, by simp [member], truth⟩

/-! ## Theorem slots and free-list lifecycle -/

/-- Public classical indices are one-based nonzero signed-32-bit values.  The
list arena below continues to use `Nat` only for its private zero-based physical
offsets. -/
structure StructuralId (Kind : Type) where
  value : Nat
  positive : 0 < value
  bounded : value ≤ 2_147_483_647
  deriving DecidableEq

inductive ThmKind
inductive ClauseKind
inductive CubeKind

/-- The three nominally distinct public structural handle types. -/
abbrev ThmId := StructuralId ThmKind
abbrev ClauseId := StructuralId ClauseKind
abbrev CubeId := StructuralId CubeKind

/-- Convert a public one-based index to its private list offset. -/
def StructuralId.offset {Kind : Type} (id : StructuralId Kind) : Nat := id.value - 1

theorem StructuralId.offset_lt_max {Kind : Type} (id : StructuralId Kind) :
    id.offset < 2_147_483_647 := by
  simp only [StructuralId.offset]
  have := id.positive
  have := id.bounded
  omega

theorem StructuralId.value_eq_offset_add_one {Kind : Type} (id : StructuralId Kind) :
    id.value = id.offset + 1 := by
  simp only [StructuralId.offset]
  have := id.positive
  omega

theorem StructuralId.offset_injective {Kind : Type} :
    Function.Injective (StructuralId.offset (Kind := Kind)) := by
  intro left right equal
  cases left with
  | mk leftValue leftPositive leftBounded =>
      cases right with
      | mk rightValue rightPositive rightBounded =>
          simp only [StructuralId.offset] at equal
          congr
          omega

/-- Construct a public handle exactly when a physical offset fits in positive
`i32`. -/
def StructuralId.ofOffset? {Kind : Type} (offset : Nat) : Option (StructuralId Kind) :=
  if bounded : offset < 2_147_483_647 then
    some ⟨offset + 1, by omega, by omega⟩
  else none

@[simp] theorem StructuralId.ofOffset?_offset {Kind : Type} {offset : Nat}
    (bounded : offset < 2_147_483_647) :
    (StructuralId.ofOffset? (Kind := Kind) offset).map StructuralId.offset = some offset := by
  simp [StructuralId.ofOffset?, bounded, StructuralId.offset]

theorem StructuralId.ofOffset?_eq_none {Kind : Type} {offset : Nat}
    (tooLarge : 2_147_483_647 ≤ offset) :
    StructuralId.ofOffset? (Kind := Kind) offset = none := by
  simp [StructuralId.ofOffset?, Nat.not_lt.mpr tooLarge]

structure Store (Atom : Type) where
  slots : List (Option (Sequent Atom))
  free : List Nat

def Store.lookup (store : Store Atom) (id : Nat) : Option (Sequent Atom) :=
  store.slots[id]?.join

/-- Public theorem lookup uses a bounded, one-based handle. -/
def Store.lookupThm (store : Store Atom) (id : ThmId) : Option (Sequent Atom) :=
  store.lookup id.offset

def Store.WellFormed (store : Store Atom) : Prop :=
  store.free.Nodup ∧ ∀ id ∈ store.free, id < store.slots.length ∧ store.lookup id = none

def Store.LiveSound (store : Store Atom) : Prop :=
  ∀ id fact, store.lookup id = some fact → fact.Sound

theorem Store.lookupThm_sound {store : Store Atom} (storeSound : store.LiveSound)
    {id : ThmId} {fact : Sequent Atom} (live : store.lookupThm id = some fact) : fact.Sound :=
  storeSound id.offset fact live

/-- Empty storage has no live logical claims. -/
def Store.empty : Store Atom := ⟨[], []⟩

/-- Append is the fresh-slot branch of theorem allocation. -/
def Store.append (store : Store Atom) (fact : Sequent Atom) : Nat × Store Atom :=
  (store.slots.length, { store with slots := store.slots ++ [some fact] })

/-- Remove exactly one live theorem and add its slot to the free list. -/
def Store.delete? (store : Store Atom) (id : Nat) : Option (Store Atom) :=
  match store.lookup id with
  | none => none
  | some _ => some { slots := store.slots.set id none, free := id :: store.free }

/-- Reuse the most recently removed slot. -/
def Store.reuse? (store : Store Atom) (fact : Sequent Atom) : Option (Nat × Store Atom) :=
  match store.free with
  | [] => none
  | id :: rest =>
      if id < store.slots.length ∧ store.lookup id = none then
        some (id, { slots := store.slots.set id (some fact), free := rest })
      else none

/-- Allocate from the free list when possible and append otherwise. -/
def Store.insert (store : Store Atom) (fact : Sequent Atom) : Nat × Store Atom :=
  match store.reuse? fact with
  | some result => result
  | none => store.append fact

/-- Persistent theorem copy: the source remains live and allocation follows
the same free-list policy as ordinary insertion. -/
def Store.copy? (store : Store Atom) (source : Nat) : Option (Nat × Store Atom) :=
  (store.lookup source).map store.insert

/-- Atomic checked replacement of one live theorem. -/
def Store.mutate? (store : Store Atom) (id : Nat) (replacement : Sequent Atom) :
    Option (Store Atom) :=
  match store.lookup id with
  | none => none
  | some _ => some { store with slots := store.slots.set id (some replacement) }

/-- Normalization is exposed as a semantics-preserving in-place mutation. -/
def Store.normalize? [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (store : Store Atom) (id : Nat) : Option (Store Atom) :=
  (store.lookup id).bind fun fact => store.mutate? id fact.normalize

/-! Public lifecycle operations translate bounded one-based `ThmId`s at the
arena boundary.  Allocation fails rather than manufacturing an out-of-range
handle when all positive `i32` indices are exhausted. -/

def Store.insertThm? (store : Store Atom) (fact : Sequent Atom) : Option (ThmId × Store Atom) :=
  let result := store.insert fact
  (StructuralId.ofOffset? (Kind := ThmKind) result.1).map fun id => (id, result.2)

def Store.deleteThm? (store : Store Atom) (id : ThmId) : Option (Store Atom) :=
  store.delete? id.offset

def Store.copyThm? (store : Store Atom) (source : ThmId) : Option (ThmId × Store Atom) :=
  (store.lookupThm source).bind store.insertThm?

def Store.mutateThm? (store : Store Atom) (id : ThmId) (replacement : Sequent Atom) :
    Option (Store Atom) :=
  store.mutate? id.offset replacement

def Store.normalizeThm? [DecidableEq Atom] [LinearOrder (Lit Atom)]
    (store : Store Atom) (id : ThmId) : Option (Store Atom) :=
  store.normalize? id.offset

@[simp] theorem Store.empty_live_sound : (Store.empty : Store Atom).LiveSound := by
  simp [Store.LiveSound, Store.empty, Store.lookup]

private theorem Store.lookup_set_self (store : Store Atom) (id : Nat)
    (value : Option (Sequent Atom)) (inBounds : id < store.slots.length) :
    ({ store with slots := store.slots.set id value }).lookup id = value := by
  simp [Store.lookup, List.getElem?_set_eq_of_lt value inBounds]

private theorem Store.lookup_set_other (store : Store Atom) (target id : Nat)
    (value : Option (Sequent Atom)) (targetInBounds : target < store.slots.length)
    (different : id ≠ target) :
    ({ store with slots := store.slots.set target value }).lookup id = store.lookup id := by
  rw [Store.lookup, Store.lookup, List.getElem?_set_of_lt' value store.slots targetInBounds]
  simp [Ne.symm different]

theorem Store.append_lookup_new (store : Store Atom) (fact : Sequent Atom) :
    (store.append fact).2.lookup (store.append fact).1 = some fact := by
  simp [Store.append, Store.lookup]

theorem Store.append_lookup_old (store : Store Atom) (fact : Sequent Atom) (id : Nat)
    (different : id ≠ store.slots.length) :
    (store.append fact).2.lookup id = store.lookup id := by
  simp only [Store.append, Store.lookup]
  by_cases inBounds : id < store.slots.length
  · rw [List.getElem?_append_left inBounds]
  · rw [List.getElem?_append]
    have beyond : store.slots.length < id := by omega
    have offset : 0 < id - store.slots.length := by omega
    obtain ⟨offset, offsetEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt offset)
    simp [inBounds, offsetEq]

theorem Store.delete_lookup_target {store after : Store Atom} {id : Nat}
    (deleted : store.delete? id = some after) : after.lookup id = none := by
  simp only [Store.delete?] at deleted
  split at deleted
  · contradiction
  · rename_i fact lookupFact
    simp only [Option.some.injEq] at deleted
    subst after
    have inBounds : id < store.slots.length := by
      unfold Store.lookup at lookupFact
      cases get : store.slots[id]? with
      | none => simp [get] at lookupFact
      | some slot => exact (List.getElem?_eq_some_iff.mp get).1
    exact Store.lookup_set_self store id none inBounds

theorem Store.delete_lookup_other {store after : Store Atom} {target : Nat}
    (deleted : store.delete? target = some after) {id : Nat} (different : id ≠ target) :
    after.lookup id = store.lookup id := by
  simp only [Store.delete?] at deleted
  split at deleted
  · contradiction
  · rename_i fact lookupFact
    simp only [Option.some.injEq] at deleted
    subst after
    have inBounds : target < store.slots.length := by
      unfold Store.lookup at lookupFact
      cases get : store.slots[target]? with
      | none => simp [get] at lookupFact
      | some slot => exact (List.getElem?_eq_some_iff.mp get).1
    exact Store.lookup_set_other store target id none inBounds different

/-- Storage reuse is logically sound whenever it inserts a checked theorem and
preserves all other live lookups. This isolates free-list allocation from the
calculus: dead slot contents and free-list order have no logical meaning. -/
theorem reuse_preserves_live_sound {before after : Store Atom} {reused : Nat}
    {replacement : Sequent Atom} (beforeSound : before.LiveSound)
    (replacementSound : replacement.Sound)
    (inserted : after.lookup reused = some replacement)
    (preserved : ∀ id, id ≠ reused → after.lookup id = before.lookup id) :
    after.LiveSound := by
  intro id fact live
  by_cases same : id = reused
  · subst id
    have equal := Option.some.inj (inserted.symm.trans live)
    subst fact
    exact replacementSound
  · exact beforeSound id fact ((preserved id same).symm.trans live)

/-- The logical contract shared by every checked in-place rule. -/
theorem mutation_preserves_live_sound {before after : Store Atom} {target : Nat}
    {replacement : Sequent Atom} (beforeSound : before.LiveSound)
    (replacementSound : replacement.Sound)
    (inserted : after.lookup target = some replacement)
    (preserved : ∀ id, id ≠ target → after.lookup id = before.lookup id) :
    after.LiveSound :=
  reuse_preserves_live_sound beforeSound replacementSound inserted preserved

/-- Sorting and duplicate removal supply the checked replacement required by
the generic mutation theorem. -/
theorem normalization_replacement_sound [DecidableEq Atom] [LinearOrder (Lit Atom)]
    {fact : Sequent Atom} (sound : fact.Sound) : fact.normalize.Sound :=
  (normalize_sound_iff fact).mpr sound

/-- Deleting one theorem is sound because it cannot create a live lookup. -/
theorem deletion_preserves_live_sound {before after : Store Atom}
    (beforeSound : before.LiveSound)
    (onlyRemoves : ∀ id fact, after.lookup id = some fact →
      before.lookup id = some fact) :
    after.LiveSound := by
  intro id fact live
  exact beforeSound id fact (onlyRemoves id fact live)

/-- Copying a theorem has exactly the same logical obligation as reuse: the
copied statement was already live and hence sound. -/
theorem copy_preserves_live_sound {before after : Store Atom} {source copied : Nat}
    {fact : Sequent Atom} (beforeSound : before.LiveSound)
    (sourceLive : before.lookup source = some fact)
    (copiedLive : after.lookup copied = some fact)
    (preserved : ∀ id, id ≠ copied → after.lookup id = before.lookup id) :
    after.LiveSound :=
  reuse_preserves_live_sound beforeSound (beforeSound source fact sourceLive)
    copiedLive preserved

/-! The following theorems discharge the abstract lookup contracts above for
the concrete list-and-free-list implementation. -/

theorem Store.append_live_sound (store : Store Atom) (fact : Sequent Atom)
    (storeSound : store.LiveSound) (factSound : fact.Sound) :
    (store.append fact).2.LiveSound := by
  apply reuse_preserves_live_sound storeSound factSound
  · exact Store.append_lookup_new store fact
  · intro id different
    exact Store.append_lookup_old store fact id different

theorem Store.delete_live_sound {store after : Store Atom} {id : Nat}
    (storeSound : store.LiveSound) (deleted : store.delete? id = some after) :
    after.LiveSound := by
  apply deletion_preserves_live_sound storeSound
  intro candidate fact live
  by_cases same : candidate = id
  · subst candidate
    rw [Store.delete_lookup_target deleted] at live
    contradiction
  · exact (Store.delete_lookup_other deleted same).symm.trans live

theorem Store.reuse_lookup_new {store after : Store Atom} {fact : Sequent Atom} {id : Nat}
    (reused : store.reuse? fact = some (id, after)) : after.lookup id = some fact := by
  simp only [Store.reuse?] at reused
  split at reused
  · contradiction
  · rename_i freeId rest freeEq
    split at reused
    · rename_i available
      simp only [Option.some.injEq, Prod.mk.injEq] at reused
      rcases reused with ⟨rfl, rfl⟩
      exact Store.lookup_set_self store freeId (some fact) available.1
    · contradiction

theorem Store.reuse_lookup_other {store after : Store Atom} {fact : Sequent Atom} {target : Nat}
    (reused : store.reuse? fact = some (target, after)) {id : Nat} (different : id ≠ target) :
    after.lookup id = store.lookup id := by
  simp only [Store.reuse?] at reused
  split at reused
  · contradiction
  · rename_i freeId rest freeEq
    split at reused
    · rename_i available
      simp only [Option.some.injEq, Prod.mk.injEq] at reused
      rcases reused with ⟨rfl, rfl⟩
      exact Store.lookup_set_other store freeId id (some fact) available.1 different
    · contradiction

theorem Store.reuse_live_sound {store after : Store Atom} {fact : Sequent Atom} {id : Nat}
    (storeSound : store.LiveSound) (factSound : fact.Sound)
    (reused : store.reuse? fact = some (id, after)) : after.LiveSound := by
  apply reuse_preserves_live_sound storeSound factSound
  · exact Store.reuse_lookup_new reused
  · intro candidate different
    exact Store.reuse_lookup_other reused different

theorem Store.insert_lookup_new (store : Store Atom) (fact : Sequent Atom) :
    (store.insert fact).2.lookup (store.insert fact).1 = some fact := by
  simp only [Store.insert]
  split
  · rename_i result reused
    obtain ⟨id, after⟩ := result
    exact Store.reuse_lookup_new reused
  · exact Store.append_lookup_new store fact

theorem Store.insert_lookup_other (store : Store Atom) (fact : Sequent Atom) (id : Nat)
    (different : id ≠ (store.insert fact).1) :
    (store.insert fact).2.lookup id = store.lookup id := by
  simp only [Store.insert] at different ⊢
  split
  · rename_i result reused
    obtain ⟨target, after⟩ := result
    have targetDifferent : id ≠ target := by
      simpa [Store.insert, reused] using different
    exact Store.reuse_lookup_other reused targetDifferent
  · rename_i noReuse
    have appendDifferent : id ≠ store.slots.length := by
      simpa [Store.insert, noReuse, Store.append] using different
    exact Store.append_lookup_old store fact id appendDifferent

theorem Store.insert_live_sound (store : Store Atom) (fact : Sequent Atom)
    (storeSound : store.LiveSound) (factSound : fact.Sound) :
    (store.insert fact).2.LiveSound := by
  apply reuse_preserves_live_sound storeSound factSound
  · exact Store.insert_lookup_new store fact
  · intro id different
    exact Store.insert_lookup_other store fact id different

theorem Store.copy_lookup_source {store after : Store Atom} {source copied : Nat}
    (copiedResult : store.copy? source = some (copied, after)) :
    ∃ fact, store.lookup source = some fact ∧ after.lookup copied = some fact := by
  simp only [Store.copy?, Option.map_eq_some_iff] at copiedResult
  obtain ⟨fact, sourceLive, inserted⟩ := copiedResult
  have copiedLive := Store.insert_lookup_new store fact
  rw [inserted] at copiedLive
  exact ⟨fact, sourceLive, copiedLive⟩

theorem Store.copy_live_sound {store after : Store Atom} {source copied : Nat}
    (storeSound : store.LiveSound)
    (copiedResult : store.copy? source = some (copied, after)) : after.LiveSound := by
  obtain ⟨fact, sourceLive, copiedLive⟩ := Store.copy_lookup_source copiedResult
  apply copy_preserves_live_sound storeSound sourceLive copiedLive
  intro id different
  simp only [Store.copy?, Option.map_eq_some_iff] at copiedResult
  obtain ⟨sourceFact, sourceFactLive, inserted⟩ := copiedResult
  have copiedId : (store.insert sourceFact).1 = copied := congrArg Prod.fst inserted
  have afterStore : (store.insert sourceFact).2 = after := congrArg Prod.snd inserted
  have sourceDifferent : id ≠ (store.insert sourceFact).1 := by
    simpa [copiedId] using different
  rw [← afterStore]
  exact Store.insert_lookup_other store sourceFact id sourceDifferent

theorem Store.mutate_lookup_target {store after : Store Atom} {id : Nat}
    {replacement : Sequent Atom} (mutated : store.mutate? id replacement = some after) :
    after.lookup id = some replacement := by
  simp only [Store.mutate?] at mutated
  split at mutated
  · contradiction
  · rename_i old lookupOld
    simp only [Option.some.injEq] at mutated
    subst after
    have inBounds : id < store.slots.length := by
      unfold Store.lookup at lookupOld
      cases get : store.slots[id]? with
      | none => simp [get] at lookupOld
      | some slot => exact (List.getElem?_eq_some_iff.mp get).1
    exact Store.lookup_set_self store id (some replacement) inBounds

theorem Store.mutate_lookup_other {store after : Store Atom} {target : Nat}
    {replacement : Sequent Atom} (mutated : store.mutate? target replacement = some after)
    {id : Nat} (different : id ≠ target) : after.lookup id = store.lookup id := by
  simp only [Store.mutate?] at mutated
  split at mutated
  · contradiction
  · rename_i old lookupOld
    simp only [Option.some.injEq] at mutated
    subst after
    have inBounds : target < store.slots.length := by
      unfold Store.lookup at lookupOld
      cases get : store.slots[target]? with
      | none => simp [get] at lookupOld
      | some slot => exact (List.getElem?_eq_some_iff.mp get).1
    exact Store.lookup_set_other store target id (some replacement) inBounds different

theorem Store.mutate_live_sound {store after : Store Atom} {id : Nat}
    {replacement : Sequent Atom} (storeSound : store.LiveSound)
    (replacementSound : replacement.Sound)
    (mutated : store.mutate? id replacement = some after) : after.LiveSound := by
  apply mutation_preserves_live_sound storeSound replacementSound
  · exact Store.mutate_lookup_target mutated
  · intro candidate different
    exact Store.mutate_lookup_other mutated different

theorem Store.normalize_live_sound [DecidableEq Atom] [LinearOrder (Lit Atom)]
    {store after : Store Atom} {id : Nat} (storeSound : store.LiveSound)
    (normalized : store.normalize? id = some after) : after.LiveSound := by
  simp only [Store.normalize?, Option.bind_eq_some_iff] at normalized
  obtain ⟨fact, factLive, mutated⟩ := normalized
  exact Store.mutate_live_sound storeSound
    (normalization_replacement_sound (storeSound id fact factLive)) mutated

theorem Store.insertThm_live_sound {store after : Store Atom} {fact : Sequent Atom}
    {id : ThmId} (storeSound : store.LiveSound) (factSound : fact.Sound)
    (inserted : store.insertThm? fact = some (id, after)) : after.LiveSound := by
  unfold Store.insertThm? at inserted
  generalize resultEq : store.insert fact = result at inserted
  obtain ⟨offset, resultStore⟩ := result
  simp only at inserted
  cases handleEq : StructuralId.ofOffset? (Kind := ThmKind) offset with
  | none => simp only [handleEq, Option.map_none, reduceCtorEq] at inserted
  | some handle =>
      simp only [handleEq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at inserted
      obtain ⟨rfl, rfl⟩ := inserted
      simpa [resultEq] using Store.insert_live_sound store fact storeSound factSound

theorem Store.deleteThm_live_sound {store after : Store Atom} {id : ThmId}
    (storeSound : store.LiveSound) (deleted : store.deleteThm? id = some after) :
    after.LiveSound :=
  Store.delete_live_sound storeSound deleted

theorem Store.copyThm_live_sound {store after : Store Atom} {source copied : ThmId}
    (storeSound : store.LiveSound) (copiedResult : store.copyThm? source = some (copied, after)) :
    after.LiveSound := by
  simp only [Store.copyThm?, Option.bind_eq_some_iff] at copiedResult
  obtain ⟨fact, sourceLive, inserted⟩ := copiedResult
  exact Store.insertThm_live_sound storeSound
    (Store.lookupThm_sound storeSound sourceLive) inserted

theorem Store.mutateThm_live_sound {store after : Store Atom} {id : ThmId}
    {replacement : Sequent Atom} (storeSound : store.LiveSound)
    (replacementSound : replacement.Sound)
    (mutated : store.mutateThm? id replacement = some after) : after.LiveSound :=
  Store.mutate_live_sound storeSound replacementSound mutated

theorem Store.normalizeThm_live_sound [DecidableEq Atom] [LinearOrder (Lit Atom)]
    {store after : Store Atom} {id : ThmId} (storeSound : store.LiveSound)
    (normalized : store.normalizeThm? id = some after) : after.LiveSound :=
  Store.normalize_live_sound storeSound normalized

/-! ## Why the right side is DNF, not CNF -/

/-- Interpreting both sides as CNF invalidates clause transfer. With `p = true`,
`true -> (p ∧ ¬p)` is false, while `(true ∧ p) -> p` is true. The latter is
what naive pointwise transfer of the `¬p` clause would produce. -/
theorem rhs_cnf_transfer_counterexample :
    let p : Lit Unit := ((), false)
    let notP : Lit Unit := p.neg
    let valuation : Valuation Unit := fun _ => True
    ¬((Cnf.mk []).Holds valuation →
        (Cnf.mk [Clause.mk [p], Clause.mk [notP]]).Holds valuation) ∧
      ((Cnf.mk [Clause.mk [p]]).Holds valuation →
        (Cnf.mk [Clause.mk [p]]).Holds valuation) := by
  simp [Cnf.Holds, Clause.Holds, Lit.Holds, Lit.neg]

/-! ## Representative shared vectors -/

/-- A compact representative row suitable for mirroring in Rust tests:
`(p ∨ ¬q) ∧ r ⊢ (p ∧ r) ∨ ¬q`. -/
def representative : Sequent Nat :=
  { left := Cnf.mk [
      Clause.mk [(1, false), (2, true)],
      Clause.mk [(3, false)]]
    right := Dnf.mk [
      Cube.mk [(1, false), (3, false)],
      Cube.mk [(2, true)]] }

example : representative.left.clauses.length = 2 := rfl
example : representative.right.cubes.length = 2 := rfl

end Nucleus.Hol.Ethane.ClassicalMatrix
