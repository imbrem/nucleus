import Nucleus.Classical.Alternating.Abstract
import Nucleus.Classical.Tagged.Abstract
import Nucleus.Hol.Ethane.ClassicalRefutation

/-!
# Classical refutations as a separate semantic layer

This module relates the existing CNF/LRAT specification to both experimental
classical-expression designs.  CNF atoms are uninterpreted Boolean variables.
In particular, a `sat` assertion chooses a fresh total Boolean assignment; it
does not inspect an ambient partial assignment or inherit a HOL interpretation.

RUP and RAT deliberately retain different contracts.  RUP proves logical
consequence.  General RAT supplies model transport, and hence preserves
satisfiability and unsatisfiability, but does not assert that its learned clause
is a consequence of the current formula.
-/

namespace Nucleus.Classical.Refutation

namespace Matrix

open Nucleus.Hol.Ethane.ClassicalMatrix

variable {Atom : Type}

/-- Read a Boolean assignment as a valuation of uninterpreted CNF atoms. -/
def boolValuation (assignment : Assignment Atom) : Valuation Atom :=
  fun atom => assignment atom = true

/-- Convert the matrix representation's polarity convention exactly. -/
def literal (value : Lit Atom) : Literal Atom :=
  ⟨value.1, value.2⟩

@[simp] theorem literal_eval (assignment : Assignment Atom) (value : Lit Atom) :
    (literal value).eval assignment = true ↔
      value.Holds (boolValuation assignment) := by
  cases value with
  | mk atom negative =>
      cases negative <;> simp [literal, Literal.eval, Lit.Holds, boolValuation]

/-- Satisfiability using a fresh total Boolean assignment. -/
def BooleanSatisfiable (cnf : Cnf Atom) : Prop :=
  ∃ fresh : Assignment Atom, cnf.Holds (boolValuation fresh)

/-- Unsatisfiability over every total Boolean assignment. -/
def BooleanUnsat (cnf : Cnf Atom) : Prop :=
  ∀ fresh : Assignment Atom, ¬cnf.Holds (boolValuation fresh)

@[simp] theorem booleanUnsat_iff_not_satisfiable (cnf : Cnf Atom) :
    BooleanUnsat cnf ↔ ¬BooleanSatisfiable cnf := by
  simp [BooleanUnsat, BooleanSatisfiable]

/-- The Boolean and proposition-valued presentations quantify over the same
assignments.  This is the bridge to the existing LRAT development. -/
theorem booleanSatisfiable_iff_legacy (cnf : Cnf Atom) :
    BooleanSatisfiable cnf ↔
      Nucleus.Hol.Ethane.ClassicalRefutation.Satisfiable cnf := by
  constructor
  · rintro ⟨assignment, truth⟩
    exact ⟨boolValuation assignment, truth⟩
  · rintro ⟨valuation, truth⟩
    classical
    let assignment : Assignment Atom := fun atom => decide (valuation atom)
    refine ⟨assignment, ?_⟩
    intro clause member
    obtain ⟨value, valueMember, valueTruth⟩ := truth clause member
    refine ⟨value, valueMember, ?_⟩
    cases value with
    | mk atom negative =>
        cases negative <;>
          simpa [Lit.Holds, boolValuation, assignment] using valueTruth

theorem booleanUnsat_iff_legacy (cnf : Cnf Atom) :
    BooleanUnsat cnf ↔ Nucleus.Hol.Ethane.ClassicalRefutation.Unsat cnf := by
  rw [booleanUnsat_iff_not_satisfiable, booleanSatisfiable_iff_legacy]
  simp [Nucleus.Hol.Ethane.ClassicalRefutation.Unsat,
    Nucleus.Hol.Ethane.ClassicalRefutation.Satisfiable]

end Matrix

namespace Tagged

open Nucleus.Hol.Ethane.ClassicalMatrix

variable {Atom : Type}

/-- A disjunctive CNF clause in the tagged formula language. -/
def clause (value : Clause Atom) : Tagged.Formula Atom :=
  Tagged.Formula.disjunction
    (value.literals.map fun literal => .literal (Matrix.literal literal))

/-- A CNF as a conjunction of disjunctive clauses. -/
def cnf (value : Cnf Atom) : Tagged.Formula Atom :=
  Tagged.Formula.conjunction (value.clauses.map clause)

/-- A conjunctive DNF cube in the tagged formula language. -/
def cube (value : Cube Atom) : Tagged.Formula Atom :=
  Tagged.Formula.conjunction
    (value.literals.map fun literal => .literal (Matrix.literal literal))

/-- A DNF as a disjunction of conjunctive cubes. -/
def dnf (value : Dnf Atom) : Tagged.Formula Atom :=
  Tagged.Formula.disjunction (value.cubes.map cube)

/-- The complete depth-two matrix sequent embedded in tagged syntax. -/
def matrixSequent (value : Nucleus.Hol.Ethane.ClassicalMatrix.Sequent Atom) :
    Tagged.Sequent Atom :=
  ⟨cnf value.left, dnf value.right⟩

/-- A closed SAT assertion for a CNF.  Its assignment is fresh. -/
def sat (value : Cnf Atom) : Tagged.Formula Atom :=
  Tagged.Formula.satisfiable (value.clauses.map clause)

/-- Falsity in the tagged language. -/
def falsity (Atom : Type) : Tagged.Formula Atom :=
  Tagged.Formula.disjunction []

/-- The ordinary universal refutation sequent `CNF ⊢ false`. -/
def sequent (value : Cnf Atom) : Tagged.Sequent Atom :=
  ⟨cnf value, falsity Atom⟩

/-- A closed formulation of refutation, `sat(CNF) ⊢ false`. -/
def satSequent (value : Cnf Atom) : Tagged.Sequent Atom :=
  ⟨sat value, falsity Atom⟩

@[simp] theorem clause_eval (assignment : Assignment Atom) (value : Clause Atom) :
    (clause value).Eval assignment ↔
      value.Holds (Matrix.boolValuation assignment) := by
  simp only [clause, Tagged.Formula.eval_disjunction]
  constructor
  · rintro ⟨child, childMember, childTruth⟩
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp childMember
    exact ⟨source, sourceMember, (Matrix.literal_eval assignment source).mp
      ((Tagged.Formula.eval_literal assignment (Matrix.literal source)).mp childTruth)⟩
  · rintro ⟨source, sourceMember, sourceTruth⟩
    exact ⟨.literal (Matrix.literal source),
      List.mem_map.mpr ⟨source, sourceMember, rfl⟩,
      (Tagged.Formula.eval_literal assignment (Matrix.literal source)).mpr
        ((Matrix.literal_eval assignment source).mpr sourceTruth)⟩

@[simp] theorem cnf_eval (assignment : Assignment Atom) (value : Cnf Atom) :
    (cnf value).Eval assignment ↔
      value.Holds (Matrix.boolValuation assignment) := by
  simp [cnf, Cnf.Holds]

@[simp] theorem cube_eval (assignment : Assignment Atom) (value : Cube Atom) :
    (cube value).Eval assignment ↔
      value.Holds (Matrix.boolValuation assignment) := by
  rw [cube, Tagged.Formula.eval_conjunction]
  constructor
  · intro truth source member
    have childTruth := truth (.literal (Matrix.literal source))
      (List.mem_map.mpr ⟨source, member, rfl⟩)
    exact (Matrix.literal_eval assignment source).mp
      ((Tagged.Formula.eval_literal assignment (Matrix.literal source)).mp childTruth)
  · intro truth child member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact (Tagged.Formula.eval_literal assignment (Matrix.literal source)).mpr
      ((Matrix.literal_eval assignment source).mpr (truth source sourceMember))

@[simp] theorem dnf_eval (assignment : Assignment Atom) (value : Dnf Atom) :
    (dnf value).Eval assignment ↔
      value.Holds (Matrix.boolValuation assignment) := by
  simp [dnf, Dnf.Holds]

@[simp] theorem matrixSequent_holds (assignment : Assignment Atom)
    (value : Nucleus.Hol.Ethane.ClassicalMatrix.Sequent Atom) :
    (matrixSequent value).Holds assignment ↔
      value.Holds (Matrix.boolValuation assignment) := by
  simp [matrixSequent, Tagged.Sequent.Holds,
    Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.Holds]

/-- General depth-two compatibility, not only the empty-DNF refutation case. -/
theorem matrixSequent_syllogism_iff
    (value : Nucleus.Hol.Ethane.ClassicalMatrix.Sequent Atom) :
    (matrixSequent value).EntailsAt (bottom : PartialAssignment Atom) ↔
      value.Sound := by
  rw [Tagged.Sequent.EntailsAt, under_bottom_iff]
  constructor
  · intro holds valuation
    classical
    let assignment : Assignment Atom := fun atom => decide (valuation atom)
    have same : Matrix.boolValuation assignment = valuation := by
      funext atom
      apply propext
      simp [Matrix.boolValuation, assignment]
    rw [← same]
    exact (matrixSequent_holds assignment value).mp (holds assignment)
  · intro sound assignment
    exact (matrixSequent_holds assignment value).mpr
      (sound (Matrix.boolValuation assignment))

/-- The SAT node quantifies over a fresh assignment and ignores `ambient`. -/
@[simp] theorem sat_eval (ambient : Assignment Atom) (value : Cnf Atom) :
    (sat value).Eval ambient ↔ Matrix.BooleanSatisfiable value := by
  simp only [sat, Tagged.Formula.eval_satisfiable]
  change (∃ fresh, ∀ child ∈ value.clauses.map clause, child.Eval fresh) ↔
    (∃ fresh, ∀ source ∈ value.clauses,
      source.Holds (Matrix.boolValuation fresh))
  constructor
  · rintro ⟨fresh, truth⟩
    refine ⟨fresh, ?_⟩
    intro source member
    exact (clause_eval fresh source).mp
      (truth (clause source) (List.mem_map.mpr ⟨source, member, rfl⟩))
  · rintro ⟨fresh, truth⟩
    refine ⟨fresh, ?_⟩
    intro child member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact (clause_eval fresh source).mpr (truth source sourceMember)

theorem sat_eval_independent (value : Cnf Atom)
    (left right : Assignment Atom) :
    (sat value).Eval left ↔ (sat value).Eval right := by
  simp

@[simp] theorem falsity_eval (assignment : Assignment Atom) :
    ¬(falsity Atom).Eval assignment := by
  simp [falsity]

@[simp] theorem sequent_holds (assignment : Assignment Atom) (value : Cnf Atom) :
    (sequent value).Holds assignment ↔
      ¬value.Holds (Matrix.boolValuation assignment) := by
  simp [sequent, Tagged.Sequent.Holds]

@[simp] theorem satSequent_holds (assignment : Assignment Atom) (value : Cnf Atom) :
    (satSequent value).Holds assignment ↔ Matrix.BooleanUnsat value := by
  simp [satSequent, Tagged.Sequent.Holds,
    Matrix.booleanUnsat_iff_not_satisfiable]

/-- A universal tagged CNF refutation is exactly CNF unsatisfiability. -/
theorem sequent_syllogism_iff (value : Cnf Atom) :
    (sequent value).EntailsAt (bottom : PartialAssignment Atom) ↔
      Matrix.BooleanUnsat value := by
  simp [Tagged.Sequent.EntailsAt, Under, Matrix.BooleanUnsat]

/-- Because `sat(CNF)` is closed, its refutation has the same meaning under
every ambient partial assignment. -/
theorem satSequent_entailsAt_iff (known : PartialAssignment Atom)
    (value : Cnf Atom) :
    (satSequent value).EntailsAt known ↔ Matrix.BooleanUnsat value := by
  constructor
  · intro holds
    obtain ⟨completion, completes⟩ := known.exists_completion
    exact (satSequent_holds completion value).mp (holds completion completes)
  · intro unsat _ _
    exact (satSequent_holds _ value).mpr unsat

/-- Exact bridge to the existing empty-DNF refutation theorem. -/
theorem sequent_syllogism_iff_legacy (value : Cnf Atom) :
    (sequent value).EntailsAt (bottom : PartialAssignment Atom) ↔
      (Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.mk value
        (Dnf.mk [])).Sound := by
  rw [sequent_syllogism_iff, Matrix.booleanUnsat_iff_legacy]
  exact Nucleus.Hol.Ethane.ClassicalRefutation.sound_empty_dnf_iff_unsat value |>.symm

end Tagged

namespace Alternating

open Nucleus.Hol.Ethane.ClassicalMatrix

variable {Atom : Type}

/-- A clause is an untagged array occurring in disjunctive mode. -/
def clause (value : Clause Atom) : Alternating.Expr Atom :=
  Alternating.Expr.array false
    (value.literals.map fun literal => .literal (Matrix.literal literal))

/-- The outer array is conjunctive; its clause children inherit disjunctive
mode from the alternating edge. -/
def cnf (value : Cnf Atom) : Alternating.Expr Atom :=
  Alternating.Expr.array false (value.clauses.map clause)

/-- A DNF cube is read conjunctively at a right-root child position. -/
def cube (value : Cube Atom) : Alternating.Expr Atom :=
  Alternating.Expr.array false
    (value.literals.map fun literal => .literal (Matrix.literal literal))

/-- A right-root disjunction of conjunctive cubes. -/
def dnf (value : Dnf Atom) : Alternating.Expr Atom :=
  Alternating.Expr.array false (value.cubes.map cube)

/-- The complete depth-two matrix sequent embedded in alternating syntax. -/
def matrixSequent (value : Nucleus.Hol.Ethane.ClassicalMatrix.Sequent Atom) :
    Alternating.Sequent Atom :=
  ⟨cnf value.left, dnf value.right⟩

/-- Falsity is the empty array read in the right root's disjunctive mode. -/
def falsity (Atom : Type) : Alternating.Expr Atom :=
  Alternating.Expr.array false []

def sequent (value : Cnf Atom) : Alternating.Sequent Atom :=
  ⟨cnf value, falsity Atom⟩

/-- Satisfiability of an alternating expression always chooses a fresh total
assignment.  It is not evaluation under an ambient HOL assignment. -/
def Satisfiable (value : Alternating.Expr Atom) : Prop :=
  ∃ fresh : Assignment Atom, value.eval fresh .all = true

/-- An ambient-indexed view of `Satisfiable`; the ambient argument is
deliberately unused. -/
def SatAt (value : Alternating.Expr Atom) (_ambient : Assignment Atom) : Prop :=
  Satisfiable value

theorem satAt_independent (value : Alternating.Expr Atom)
    (left right : Assignment Atom) : SatAt value left ↔ SatAt value right :=
  Iff.rfl

@[simp] theorem clause_eval (assignment : Assignment Atom) (value : Clause Atom) :
    (clause value).eval assignment .any = true ↔
      value.Holds (Matrix.boolValuation assignment) := by
  simp [clause, Clause.Holds, Matrix.literal_eval,
    Alternating.Mode.aggregate]

@[simp] theorem cnf_eval (assignment : Assignment Atom) (value : Cnf Atom) :
    (cnf value).eval assignment .all = true ↔
      value.Holds (Matrix.boolValuation assignment) := by
  simp only [cnf, Alternating.Expr.eval_array_positive, List.map_map,
    Alternating.Mode.aggregate, Alternating.Mode.flip, List.all_map,
    List.all_eq_true, Function.comp_apply, id_eq]
  change (∀ source ∈ value.clauses,
    (clause source).eval assignment .any = true) ↔ _
  simp only [clause_eval]
  rfl

@[simp] theorem cube_eval (assignment : Assignment Atom) (value : Cube Atom) :
    (cube value).eval assignment .all = true ↔
      value.Holds (Matrix.boolValuation assignment) := by
  simp [cube, Cube.Holds, Matrix.literal_eval,
    Alternating.Mode.aggregate]

@[simp] theorem dnf_eval (assignment : Assignment Atom) (value : Dnf Atom) :
    (dnf value).eval assignment .any = true ↔
      value.Holds (Matrix.boolValuation assignment) := by
  simp only [dnf, Alternating.Expr.eval_array_positive, List.map_map,
    Alternating.Mode.aggregate, Alternating.Mode.flip, List.any_map,
    List.any_eq_true, Function.comp_apply, id_eq]
  change (∃ source ∈ value.cubes,
    (cube source).eval assignment .all = true) ↔ _
  simp only [cube_eval]
  rfl

@[simp] theorem matrixSequent_holds (assignment : Assignment Atom)
    (value : Nucleus.Hol.Ethane.ClassicalMatrix.Sequent Atom) :
    (matrixSequent value).Holds assignment ↔
      value.Holds (Matrix.boolValuation assignment) := by
  simp [matrixSequent, Alternating.Sequent.Holds,
    Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.Holds]

/-- General depth-two compatibility, not only the empty-DNF refutation case. -/
theorem matrixSequent_syllogism_iff
    (value : Nucleus.Hol.Ethane.ClassicalMatrix.Sequent Atom) :
    (matrixSequent value).IsSyllogism ↔ value.Sound := by
  rw [Alternating.Sequent.isSyllogism_iff]
  constructor
  · intro holds valuation
    classical
    let assignment : Assignment Atom := fun atom => decide (valuation atom)
    have same : Matrix.boolValuation assignment = valuation := by
      funext atom
      apply propext
      simp [Matrix.boolValuation, assignment]
    rw [← same]
    exact (matrixSequent_holds assignment value).mp (holds assignment)
  · intro sound assignment
    exact (matrixSequent_holds assignment value).mpr
      (sound (Matrix.boolValuation assignment))

@[simp] theorem cnf_satisfiable (value : Cnf Atom) :
    Satisfiable (cnf value) ↔ Matrix.BooleanSatisfiable value := by
  simp [Satisfiable, Matrix.BooleanSatisfiable]

@[simp] theorem falsity_eval (assignment : Assignment Atom) :
    (falsity Atom).eval assignment .any = false := by
  simp [falsity]

@[simp] theorem sequent_holds (assignment : Assignment Atom) (value : Cnf Atom) :
    (sequent value).Holds assignment ↔
      ¬value.Holds (Matrix.boolValuation assignment) := by
  simp [sequent, Alternating.Sequent.Holds]

/-- An alternating CNF refutation is exactly unsatisfiability at the null
partial assignment. -/
theorem sequent_syllogism_iff (value : Cnf Atom) :
    (sequent value).IsSyllogism ↔ Matrix.BooleanUnsat value := by
  simp [Alternating.Sequent.IsSyllogism, Syllogism,
    Matrix.BooleanUnsat]

/-- Exact bridge from the alternating design to the existing refuter result. -/
theorem sequent_syllogism_iff_legacy (value : Cnf Atom) :
    (sequent value).IsSyllogism ↔
      (Nucleus.Hol.Ethane.ClassicalMatrix.Sequent.mk value
        (Dnf.mk [])).Sound := by
  rw [sequent_syllogism_iff, Matrix.booleanUnsat_iff_legacy]
  exact Nucleus.Hol.Ethane.ClassicalRefutation.sound_empty_dnf_iff_unsat value |>.symm

end Alternating

/-! ## Certificate contracts

These theorems expose the existing LRAT semantics without conflating general
RAT with consequence. -/

namespace Certificate

open Nucleus.Hol.Ethane.ClassicalMatrix

variable {Atom : Type}

def learned (formula : Cnf Atom) (clause : Clause Atom) : Cnf Atom :=
  Cnf.mk (formula.clauses ++ [clause])

/-- RUP proves the learned clause as a logical consequence. -/
theorem rup_entails {formula : Cnf Atom} {clause : Clause Atom}
    (rup : Nucleus.Hol.Ethane.ClassicalRefutation.Rup formula clause) :
    Nucleus.Hol.Ethane.ClassicalRefutation.Entails formula clause :=
  rup.entails

/-- General RAT's exact semantic promise is model transport. -/
theorem rat_preserves_satisfiability {formula : Cnf Atom} {clause : Clause Atom}
    (rat : Nucleus.Hol.Ethane.ClassicalRefutation.Rat formula clause) :
    Nucleus.Hol.Ethane.ClassicalRefutation.Satisfiable formula →
      Nucleus.Hol.Ethane.ClassicalRefutation.Satisfiable
        (learned formula clause) := by
  simpa only [Nucleus.Hol.Ethane.ClassicalRefutation.Rat,
    Nucleus.Hol.Ethane.ClassicalRefutation.PreservesSatisfiability,
    learned] using rat

/-- Structural inclusion supplies the reverse model implication, so a checked
RAT step preserves satisfiability in both directions.  This does not make the
learned clause a consequence. -/
theorem rat_satisfiable_iff {formula : Cnf Atom} {clause : Clause Atom}
    (rat : Nucleus.Hol.Ethane.ClassicalRefutation.Rat formula clause) :
    Nucleus.Hol.Ethane.ClassicalRefutation.Satisfiable
        (learned formula clause) ↔
      Nucleus.Hol.Ethane.ClassicalRefutation.Satisfiable formula := by
  constructor
  · rintro ⟨valuation, truth⟩
    refine ⟨valuation, ?_⟩
    intro candidate member
    exact truth candidate (List.mem_append.mpr (Or.inl member))
  · exact rat_preserves_satisfiability rat

/-- Equivalently, a checked RAT step preserves unsatisfiability. -/
theorem rat_unsat_iff {formula : Cnf Atom} {clause : Clause Atom}
    (rat : Nucleus.Hol.Ethane.ClassicalRefutation.Rat formula clause) :
    Nucleus.Hol.Ethane.ClassicalRefutation.Unsat
        (learned formula clause) ↔
      Nucleus.Hol.Ethane.ClassicalRefutation.Unsat formula := by
  constructor
  · intro learnedUnsat valuation formulaTruth
    obtain ⟨learnedValuation, learnedTruth⟩ :=
      rat_preserves_satisfiability rat ⟨valuation, formulaTruth⟩
    exact learnedUnsat learnedValuation learnedTruth
  · intro formulaUnsat valuation learnedTruth
    apply formulaUnsat valuation
    intro candidate member
    exact learnedTruth candidate (List.mem_append.mpr (Or.inl member))

/-- RUP is the consequence-producing special case of RAT. -/
theorem rup_satisfiable_iff {formula : Cnf Atom} {clause : Clause Atom}
    (rup : Nucleus.Hol.Ethane.ClassicalRefutation.Rup formula clause) :
    Nucleus.Hol.Ethane.ClassicalRefutation.Satisfiable
        (learned formula clause) ↔
      Nucleus.Hol.Ethane.ClassicalRefutation.Satisfiable formula :=
  rat_satisfiable_iff
    (Nucleus.Hol.Ethane.ClassicalRefutation.rat_of_rup rup)

theorem rup_unsat_iff {formula : Cnf Atom} {clause : Clause Atom}
    (rup : Nucleus.Hol.Ethane.ClassicalRefutation.Rup formula clause) :
    Nucleus.Hol.Ethane.ClassicalRefutation.Unsat
        (learned formula clause) ↔
      Nucleus.Hol.Ethane.ClassicalRefutation.Unsat formula :=
  rat_unsat_iff (Nucleus.Hol.Ethane.ClassicalRefutation.rat_of_rup rup)

end Certificate

end Nucleus.Classical.Refutation
