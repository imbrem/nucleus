import Nucleus.Hol.Ethane.ClassicalMatrix

/-!
# Classical CNF refutation

This module specifies the proof-producing boundary used by the userspace LRAT
loader.  Reverse unit propagation and RAT operate on arbitrary atoms; no atom
is assumed to be a Boolean variable stored in a HOL arena.  Successful
completion yields exactly the universally sound sequent `goal ⊢ []`.
-/

namespace Nucleus.Hol.Ethane.ClassicalRefutation

open Nucleus.Hol.Ethane.ClassicalMatrix

variable {Atom : Type}

def Unsat (cnf : Cnf Atom) : Prop :=
  ∀ valuation, ¬cnf.Holds valuation

def Satisfiable (cnf : Cnf Atom) : Prop :=
  ∃ valuation, cnf.Holds valuation

/-- The invariant carried by the Rust refuter: every model of the original
goal can be transported to a model of the current clause state. -/
def PreservesSatisfiability (goal state : Cnf Atom) : Prop :=
  Satisfiable goal → Satisfiable state

theorem PreservesSatisfiability.refl (cnf : Cnf Atom) :
    PreservesSatisfiability cnf cnf := fun satisfiable => satisfiable

theorem PreservesSatisfiability.trans {first second third : Cnf Atom}
    (firstSecond : PreservesSatisfiability first second)
    (secondThird : PreservesSatisfiability second third) :
    PreservesSatisfiability first third := fun satisfiable => secondThird (firstSecond satisfiable)

theorem PreservesSatisfiability.unsat {goal state : Cnf Atom}
    (preserves : PreservesSatisfiability goal state) (stateUnsat : Unsat state) : Unsat goal := by
  intro valuation goalTruth
  obtain ⟨stateValuation, stateTruth⟩ := preserves ⟨valuation, goalTruth⟩
  exact stateUnsat stateValuation stateTruth

theorem sound_empty_dnf_iff_unsat (cnf : Cnf Atom) :
    (Sequent.mk cnf (Dnf.mk [])).Sound ↔ Unsat cnf := by
  simp [Sequent.Sound, Sequent.Holds, Unsat]

theorem contains_empty_clause_unsat {cnf : Cnf Atom}
    (contains : Clause.mk [] ∈ cnf.clauses) : Unsat cnf := by
  intro valuation truth
  exact empty_clause_false valuation (truth (Clause.mk []) contains)

/-- Semantic transport underlying refutation completion. -/
theorem of_state_unsat {goal state : Cnf Atom}
    (preserves : PreservesSatisfiability goal state) (stateUnsat : Unsat state) :
    (Sequent.mk goal (Dnf.mk [])).Sound :=
  (sound_empty_dnf_iff_unsat goal).mpr (preserves.unsat stateUnsat)

theorem done_with_empty_clause {goal state : Cnf Atom}
    (preserves : PreservesSatisfiability goal state)
    (contains : Clause.mk [] ∈ state.clauses) :
    (Sequent.mk goal (Dnf.mk [])).Sound :=
  of_state_unsat preserves (contains_empty_clause_unsat contains)

/-! ## Ordered reverse unit propagation -/

def Trail.Holds (valuation : Valuation Atom) (trail : List (Lit Atom)) : Prop :=
  ∀ literal ∈ trail, literal.Holds valuation

/-- A proof-level mirror of the successful paths through Rust's ordered
`propagate`: an existing clause is conflicting, or has one open literal which
is added before checking the remaining hints. -/
inductive RupTrail (formula : Cnf Atom) : List (Lit Atom) → Prop
  | trailConflict (trail : List (Lit Atom)) (literal : Lit Atom)
      (positive : literal ∈ trail) (negative : literal.neg ∈ trail) : RupTrail formula trail
  | clauseConflict (trail : List (Lit Atom)) (clause : Clause Atom)
      (present : clause ∈ formula.clauses)
      (closed : ∀ literal ∈ clause.literals, literal.neg ∈ trail) :
      RupTrail formula trail
  | unit (trail : List (Lit Atom)) (clause : Clause Atom) (literal : Lit Atom)
      (present : clause ∈ formula.clauses) (member : literal ∈ clause.literals)
      (closed : ∀ other ∈ clause.literals, other ≠ literal → other.neg ∈ trail)
      (next : RupTrail formula (literal :: trail)) : RupTrail formula trail

theorem RupTrail.contradiction {formula : Cnf Atom} {trail : List (Lit Atom)}
    (derivation : RupTrail formula trail) (valuation : Valuation Atom)
    (formulaTruth : formula.Holds valuation)
    (trailTruth : Trail.Holds valuation trail) : False := by
  induction derivation with
  | trailConflict trail literal positive negative =>
      exact ((Lit.holds_neg valuation literal).mp (trailTruth literal.neg negative))
        (trailTruth literal positive)
  | clauseConflict trail clause present closed =>
      obtain ⟨literal, member, truth⟩ := formulaTruth clause present
      exact ((Lit.holds_neg valuation literal).mp (trailTruth literal.neg (closed literal member)))
        truth
  | unit trail clause literal present member closed next ih =>
      obtain ⟨witness, witnessMember, witnessTruth⟩ := formulaTruth clause present
      have literalTruth : literal.Holds valuation := by
        by_cases equal : witness = literal
        · simpa [equal] using witnessTruth
        · exact (((Lit.holds_neg valuation witness).mp
            (trailTruth witness.neg (closed witness witnessMember equal))) witnessTruth).elim
      apply ih
      intro candidate candidateMember
      simp only [List.mem_cons] at candidateMember
      rcases candidateMember with rfl | candidateMember
      · exact literalTruth
      · exact trailTruth candidate candidateMember

/-- The initial RUP trail pointwise falsifies the proposed clause. -/
def falsifyingTrail (clause : Clause Atom) : List (Lit Atom) :=
  clause.literals.map Lit.neg

theorem falsifyingTrail_holds (valuation : Valuation Atom) (clause : Clause Atom) :
    Trail.Holds valuation (falsifyingTrail clause) ↔ ¬clause.Holds valuation := by
  change clause.neg.Holds valuation ↔ ¬clause.Holds valuation
  exact Clause.neg_holds valuation clause

def Rup (formula : Cnf Atom) (clause : Clause Atom) : Prop :=
  RupTrail formula (falsifyingTrail clause)

theorem Rup.entails {formula : Cnf Atom} {clause : Clause Atom}
    (rup : Rup formula clause) (valuation : Valuation Atom)
    (formulaTruth : formula.Holds valuation) : clause.Holds valuation := by
  by_contra clauseFalse
  exact rup.contradiction valuation formulaTruth
    ((falsifyingTrail_holds valuation clause).mpr clauseFalse)

/-- Adding a RUP clause preserves satisfiability using the same valuation. -/
theorem learnRup {formula : Cnf Atom} {clause : Clause Atom} (rup : Rup formula clause) :
    PreservesSatisfiability formula (Cnf.mk (formula.clauses ++ [clause])) := by
  rintro ⟨valuation, formulaTruth⟩
  refine ⟨valuation, ?_⟩
  intro candidate member
  rcases List.mem_append.mp member with member | member
  · exact formulaTruth candidate member
  · have equal : candidate = clause := by simpa using member
    subst candidate
    exact rup.entails valuation formulaTruth

/-! ## State weakening and RAT -/

/-- Clause deletion is represented semantically: every model of the stronger
state is a model of the state after deletion. Stable row IDs and tombstones do
not affect this condition. -/
def WeakensTo (before after : Cnf Atom) : Prop :=
  ∀ valuation, before.Holds valuation → after.Holds valuation

theorem delete (goal before after : Cnf Atom)
    (invariant : PreservesSatisfiability goal before)
    (weakens : WeakensTo before after) : PreservesSatisfiability goal after := by
  apply invariant.trans
  rintro ⟨valuation, truth⟩
  exact ⟨valuation, weakens valuation truth⟩

/-- Semantic content of a successful RAT check.  Unlike RUP, RAT may change
the pivot atom's value, so it promises a model transport rather than logical
entailment of the learned clause. -/
def Rat (formula : Cnf Atom) (clause : Clause Atom) : Prop :=
  PreservesSatisfiability formula (Cnf.mk (formula.clauses ++ [clause]))

def without [DecidableEq Atom] (clause : Clause Atom) (literal : Lit Atom) :
    List (Lit Atom) :=
  clause.literals.filter (fun candidate => candidate ≠ literal)

/-- The non-tautological resolvent checked by one explicit LRAT RAT group. -/
def resolvent [DecidableEq Atom] (learned opposing : Clause Atom) (pivot : Lit Atom) :
    Clause Atom :=
  Clause.mk (without learned pivot ++ without opposing pivot.neg)

def Entails (formula : Cnf Atom) (clause : Clause Atom) : Prop :=
  ∀ valuation, formula.Holds valuation → clause.Holds valuation

def Tautological (clause : Clause Atom) : Prop :=
  ∃ literal, literal ∈ clause.literals ∧ literal.neg ∈ clause.literals

theorem Tautological.holds {clause : Clause Atom} (tautology : Tautological clause)
    (valuation : Valuation Atom) : clause.Holds valuation := by
  obtain ⟨literal, member, complementMember⟩ := tautology
  by_cases truth : literal.Holds valuation
  · exact ⟨literal, member, truth⟩
  · exact ⟨literal.neg, complementMember, (Lit.holds_neg valuation literal).mpr truth⟩

/-- Semantic contract of complete explicit RAT groups: the pivot occurs in
the learned row and every live row containing its complement has a RUP
resolvent. -/
def RatResolvents [DecidableEq Atom] (formula : Cnf Atom) (learned : Clause Atom)
    (pivot : Lit Atom) : Prop :=
  pivot ∈ learned.literals ∧
    ∀ opposing ∈ formula.clauses, pivot.neg ∈ opposing.literals →
      Tautological (resolvent learned opposing pivot) ∨
        Rup formula (resolvent learned opposing pivot)

def flipValuation [DecidableEq Atom] (valuation : Valuation Atom) (atom : Atom) :
    Valuation Atom := fun candidate =>
  if candidate = atom then ¬valuation candidate else valuation candidate

theorem Lit.holds_flip_self [DecidableEq Atom] (valuation : Valuation Atom)
    (literal : Lit Atom) :
    literal.Holds (flipValuation valuation literal.1) ↔ ¬literal.Holds valuation := by
  cases literal with
  | mk atom polarity =>
      cases polarity <;> simp [flipValuation, Lit.Holds]

theorem Lit.holds_flip_other [DecidableEq Atom] (valuation : Valuation Atom)
    (literal : Lit Atom) {atom : Atom} (different : literal.1 ≠ atom) :
    literal.Holds (flipValuation valuation atom) ↔ literal.Holds valuation := by
  cases literal with
  | mk source polarity =>
      cases polarity <;> simp [flipValuation, Lit.Holds, different]

theorem Lit.eq_or_eq_neg_of_same_atom (left right : Lit Atom)
    (same : left.1 = right.1) : left = right ∨ left = right.neg := by
  cases left with
  | mk leftAtom leftPolarity =>
      cases right with
      | mk rightAtom rightPolarity =>
          change leftAtom = rightAtom at same
          subst rightAtom
          cases leftPolarity <;> cases rightPolarity <;> simp [Lit.neg]

private theorem true_before_false_after_flip [DecidableEq Atom]
    (valuation : Valuation Atom) (pivot literal : Lit Atom)
    (pivotFalse : ¬pivot.Holds valuation) (before : literal.Holds valuation)
    (after : ¬literal.Holds (flipValuation valuation pivot.1)) : literal = pivot.neg := by
  by_cases different : literal.1 ≠ pivot.1
  · exact (after ((Lit.holds_flip_other valuation literal different).mpr before)).elim
  · rcases Lit.eq_or_eq_neg_of_same_atom literal pivot (not_ne_iff.mp different) with
      equal | equal
    · subst literal
      exact (pivotFalse before).elim
    · exact equal

private theorem true_before_true_after_flip_unless_complement [DecidableEq Atom]
    (valuation : Valuation Atom) (pivot literal : Lit Atom)
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

/-- The standard RAT model-flipping argument. Complete RUP resolvents imply
the model-transport property required by the stateful refuter. -/
theorem rat_of_resolvents [DecidableEq Atom] {formula : Cnf Atom}
    {learned : Clause Atom} {pivot : Lit Atom}
    (certificate : RatResolvents formula learned pivot) : Rat formula learned := by
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
      exact learnedTruth ⟨pivot, certificate.1, truth⟩
    have learnedFlipped : learned.Holds flipped :=
      ⟨pivot, certificate.1, (Lit.holds_flip_self valuation pivot).mpr pivotFalse⟩
    refine ⟨flipped, ?_⟩
    intro clause member
    rcases List.mem_append.mp member with member | member
    · by_contra clauseFalse
      have complementMember : pivot.neg ∈ clause.literals := by
        obtain ⟨literal, literalMember, literalTruth⟩ := formulaTruth clause member
        exact true_before_false_after_flip valuation pivot literal pivotFalse literalTruth
          (fun truth => clauseFalse ⟨literal, literalMember, truth⟩) ▸ literalMember
      have resolventTruth : (resolvent learned clause pivot).Holds valuation := by
        rcases certificate.2 clause member complementMember with tautology | rup
        · exact tautology.holds valuation
        · exact rup.entails valuation formulaTruth
      obtain ⟨literal, resolventMember, literalTruth⟩ := resolventTruth
      rcases List.mem_append.mp resolventMember with learnedMember | opposingMember
      · have sourceMember := (List.mem_filter.mp learnedMember).1
        exact learnedTruth ⟨literal, sourceMember, literalTruth⟩
      · obtain ⟨sourceMember, notComplement⟩ := List.mem_filter.mp opposingMember
        have afterTruth := true_before_true_after_flip_unless_complement valuation pivot literal
          pivotFalse literalTruth (of_decide_eq_true notComplement)
        exact clauseFalse ⟨literal, sourceMember, afterTruth⟩
    · have equal : clause = learned := by simpa using member
      simpa [equal] using learnedFlipped

theorem learnRat {goal formula : Cnf Atom} {clause : Clause Atom}
    (invariant : PreservesSatisfiability goal formula) (rat : Rat formula clause) :
    PreservesSatisfiability goal (Cnf.mk (formula.clauses ++ [clause])) :=
  invariant.trans rat

theorem rat_of_rup {formula : Cnf Atom} {clause : Clause Atom}
    (rup : Rup formula clause) : Rat formula clause := by
  rintro ⟨valuation, formulaTruth⟩
  refine ⟨valuation, ?_⟩
  intro candidate member
  rcases List.mem_append.mp member with member | member
  · exact formulaTruth candidate member
  · have equal : candidate = clause := by simpa using member
    subst candidate
    exact rup.entails valuation formulaTruth

/-! ## Universal refutations and HOL sealing -/

/-- Matching a universal CNF refutation to a HOL proposition is sound when
the checked opcode spine gives exactly the same truth condition. -/
theorem sealCnfRefutation {cnf : Cnf Atom} {formula : Lit Atom}
    (refutation : (Sequent.mk cnf (Dnf.mk [])).Sound)
    (meaning : ∀ valuation, formula.Holds valuation ↔ cnf.Holds valuation) :
    (Sequent.mk (Cnf.mk [Clause.mk [formula]]) (Dnf.mk [])).Sound := by
  intro valuation premise
  have formulaTruth := (singleton_clause_holds valuation formula).mp
    (premise (Clause.mk [formula]) (by simp))
  exact ((sound_empty_dnf_iff_unsat cnf).mp refutation valuation
    ((meaning valuation).mp formulaTruth)).elim

end Nucleus.Hol.Ethane.ClassicalRefutation
