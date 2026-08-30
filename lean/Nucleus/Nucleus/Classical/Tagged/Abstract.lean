import Nucleus.Classical.Semantics
import Mathlib.Data.Finset.Basic

/-!
# Abstract tagged classical formulas

This design gives every connective an explicit tag and sign.  A `sat` node
binds the atoms in its children as fresh, uninterpreted Boolean variables and
asserts that their conjunction is satisfiable.  It therefore has no free atoms
and does not inspect the assignment in which the surrounding formula is read.

Free renaming and substitution stop at `sat`.  Renaming bound SAT atoms would
require an equivalence, not an arbitrary atom map, and is intentionally absent.
-/

namespace Nucleus.Classical.Tagged

universe u

variable {Atom : Type u}

/-- Apply the sign bit carried by a formula node. -/
def Signed (negative : Bool) (claim : Prop) : Prop :=
  if negative then ¬ claim else claim

/-- A signed literal or signed n-ary tagged connective.  `sat children` means
that the conjunction of `children` is satisfiable under a fresh assignment. -/
inductive Formula (Atom : Type u) where
  | literal (value : Classical.Literal Atom)
  | and (negative : Bool) (children : List (Formula Atom))
  | or (negative : Bool) (children : List (Formula Atom))
  | sat (negative : Bool) (children : List (Formula Atom))

namespace Formula

/-- A positive literal. -/
def atom (value : Atom) : Formula Atom :=
  .literal ⟨value, false⟩

/-- A positive n-ary conjunction. -/
def conjunction (children : List (Formula Atom)) : Formula Atom :=
  .and false children

/-- A positive n-ary disjunction. -/
def disjunction (children : List (Formula Atom)) : Formula Atom :=
  .or false children

/-- A positive satisfiability assertion for an implicit conjunction. -/
def satisfiable (children : List (Formula Atom)) : Formula Atom :=
  .sat false children

/-- Complement the sign of a formula without traversing its children. -/
def neg : Formula Atom → Formula Atom
  | .literal value => .literal value.neg
  | .and negative children => .and (!negative) children
  | .or negative children => .or (!negative) children
  | .sat negative children => .sat (!negative) children

@[simp] theorem neg_neg (formula : Formula Atom) : formula.neg.neg = formula := by
  cases formula <;> simp [neg, Classical.Literal.neg_neg]

/- Evaluate a formula under a total assignment.  A `sat` node deliberately
ignores `ambient` and quantifies over a fresh total assignment. -/
mutual
  /-- Evaluate a tagged formula under a total assignment. -/
  def Eval : Formula Atom → Classical.Assignment Atom → Prop
    | .literal value, ambient => value.eval ambient = true
    | .and negative children, ambient =>
        Signed negative (EvalAll children ambient)
    | .or negative children, ambient =>
        Signed negative (EvalAny children ambient)
    | .sat negative children, _ =>
        Signed negative (∃ fresh : Classical.Assignment Atom,
          EvalAll children fresh)
    termination_by formula _ => sizeOf formula

  /-- Every formula in a child list evaluates to true. -/
  def EvalAll : List (Formula Atom) → Classical.Assignment Atom → Prop
    | [], _ => True
    | child :: children, ambient => child.Eval ambient ∧ EvalAll children ambient
    termination_by children _ => sizeOf children

  /-- Some formula in a child list evaluates to true. -/
  def EvalAny : List (Formula Atom) → Classical.Assignment Atom → Prop
    | [], _ => False
    | child :: children, ambient => child.Eval ambient ∨ EvalAny children ambient
    termination_by children _ => sizeOf children
end

theorem evalAll_iff (ambient : Classical.Assignment Atom)
    (children : List (Formula Atom)) :
    EvalAll children ambient ↔ ∀ child ∈ children, child.Eval ambient := by
  induction children with
  | nil => simp [EvalAll]
  | cons child children ih => simp [EvalAll, ih]

theorem evalAny_iff (ambient : Classical.Assignment Atom)
    (children : List (Formula Atom)) :
    EvalAny children ambient ↔ ∃ child ∈ children, child.Eval ambient := by
  induction children with
  | nil => simp [EvalAny]
  | cons child children ih => simp [EvalAny, ih]

@[simp] theorem eval_literal (ambient : Classical.Assignment Atom)
    (value : Classical.Literal Atom) :
    Eval (.literal value) ambient ↔ value.eval ambient = true := by
  simp [Eval]

@[simp] theorem eval_conjunction (ambient : Classical.Assignment Atom)
    (children : List (Formula Atom)) :
    Eval (conjunction children) ambient ↔
      ∀ child ∈ children, child.Eval ambient := by
  simp [Eval, conjunction, Signed, evalAll_iff]

@[simp] theorem eval_disjunction (ambient : Classical.Assignment Atom)
    (children : List (Formula Atom)) :
    Eval (disjunction children) ambient ↔
      ∃ child ∈ children, child.Eval ambient := by
  simp [Eval, disjunction, Signed, evalAny_iff]

@[simp] theorem eval_satisfiable (ambient : Classical.Assignment Atom)
    (children : List (Formula Atom)) :
    Eval (satisfiable children) ambient ↔
      ∃ fresh : Classical.Assignment Atom,
        ∀ child ∈ children, child.Eval fresh := by
  simp [Eval, satisfiable, Signed, evalAll_iff]

/-- A SAT node is closed with respect to the surrounding assignment. -/
theorem eval_sat_independent (negative : Bool) (children : List (Formula Atom))
    (left right : Classical.Assignment Atom) :
    Eval (.sat negative children) left ↔ Eval (.sat negative children) right := by
  simp [Eval]

/-- Interpret one formula relative to a partial ambient assignment.  This is
the public valuation semantics; `Eval` is its total-completion worker. -/
def EvalAt (known : Classical.PartialAssignment Atom) (formula : Formula Atom) : Prop :=
  Classical.Under known formula.Eval

theorem EvalAt.mono {less more : Classical.PartialAssignment Atom}
    {formula : Formula Atom} (holds : formula.EvalAt less)
    (refines : Classical.Refines less more) : formula.EvalAt more :=
  Classical.Under.mono holds refines

/-- A SAT node has the same meaning at every partial ambient assignment. -/
theorem evalAt_sat_iff (known : Classical.PartialAssignment Atom)
    (negative : Bool) (children : List (Formula Atom))
    (ambient : Classical.Assignment Atom) :
    EvalAt known (.sat negative children) ↔ Eval (.sat negative children) ambient := by
  constructor
  · intro holds
    exact (eval_sat_independent negative children (known.complete ambient) ambient).mp
      (holds (known.complete ambient) (known.complete_completes ambient))
  · intro holds total _
    exact (eval_sat_independent negative children ambient total).mp holds

/-- Negating a signed node complements its semantics. -/
theorem eval_neg (formula : Formula Atom) (ambient : Classical.Assignment Atom) :
    formula.neg.Eval ambient ↔ ¬ formula.Eval ambient := by
  classical
  cases formula with
  | literal value =>
      simp only [neg, Eval, Classical.Literal.eval_neg]
      cases value.eval ambient <;> simp
  | and negative children | or negative children | sat negative children =>
      cases negative <;> simp [neg, Eval, Signed]

/-- Free atoms of a formula.  Atoms below `sat` are bound by its fresh
assignment and are therefore omitted wholesale. -/
def freeAtoms [DecidableEq Atom] : Formula Atom → Finset Atom
  | .literal value => {value.atom}
  | .and _ children | .or _ children =>
      children.foldl (fun atoms child => atoms ∪ child.freeAtoms) ∅
  | .sat _ _ => ∅

@[simp] theorem freeAtoms_literal [DecidableEq Atom]
    (value : Classical.Literal Atom) :
    freeAtoms (.literal value) = {value.atom} := by
  simp [freeAtoms]

@[simp] theorem freeAtoms_sat [DecidableEq Atom]
    (negative : Bool) (children : List (Formula Atom)) :
    freeAtoms (.sat negative children) = ∅ := by
  simp [freeAtoms]

/-- Rename free atoms.  A SAT node is an opaque binding boundary. -/
def renameFree (rename : Atom → Atom) : Formula Atom → Formula Atom
  | .literal value => .literal ⟨rename value.atom, value.negative⟩
  | .and negative children => .and negative (children.map (renameFree rename))
  | .or negative children => .or negative (children.map (renameFree rename))
  | .sat negative children => .sat negative children

@[simp] theorem renameFree_sat (rename : Atom → Atom) (negative : Bool)
    (children : List (Formula Atom)) :
    renameFree rename (.sat negative children) = .sat negative children := by
  simp [renameFree]

/-- Substitute for free atoms.  The sign of a literal is applied to the
replacement, and a SAT node remains opaque. -/
def substFree (replace : Atom → Formula Atom) : Formula Atom → Formula Atom
  | .literal value =>
      if value.negative then (replace value.atom).neg else replace value.atom
  | .and negative children => .and negative (children.map (substFree replace))
  | .or negative children => .or negative (children.map (substFree replace))
  | .sat negative children => .sat negative children

@[simp] theorem substFree_sat (replace : Atom → Formula Atom) (negative : Bool)
    (children : List (Formula Atom)) :
    substFree replace (.sat negative children) = .sat negative children := by
  simp [substFree]

end Formula

/-- One implication between tagged formulas. -/
structure Sequent (Atom : Type u) where
  premise : Formula Atom
  conclusion : Formula Atom

namespace Sequent

/-- Truth of a sequent under one total assignment. -/
def Holds (sequent : Sequent Atom) (assignment : Classical.Assignment Atom) : Prop :=
  sequent.premise.Eval assignment → sequent.conclusion.Eval assignment

/-- Truth of one sequent under every completion of a partial assignment. -/
def EntailsAt (known : Classical.PartialAssignment Atom) (sequent : Sequent Atom) : Prop :=
  Classical.Under known sequent.Holds

end Sequent

/-- Every sequent in a list holds under one total assignment. -/
def Holds (sequents : List (Sequent Atom))
    (assignment : Classical.Assignment Atom) : Prop :=
  ∀ sequent ∈ sequents, sequent.Holds assignment

/-- Every sequent holds under every completion of `known`. -/
def EntailsAt (known : Classical.PartialAssignment Atom)
    (sequents : List (Sequent Atom)) : Prop :=
  Classical.Under known (Holds sequents)

/-- A list of syllogisms: every sequent holds under the null assignment, hence
under every total assignment. -/
def Syllogism (sequents : List (Sequent Atom)) : Prop :=
  EntailsAt Classical.bottom sequents

@[simp] theorem syllogism_iff (sequents : List (Sequent Atom)) :
    Syllogism sequents ↔ ∀ assignment, Holds sequents assignment := by
  simp [Syllogism, EntailsAt, Classical.under_bottom_iff]

theorem EntailsAt.mono {less more : Classical.PartialAssignment Atom}
    {sequents : List (Sequent Atom)} (holds : EntailsAt less sequents)
    (refines : Classical.Refines less more) : EntailsAt more sequents :=
  Classical.Under.mono holds refines

end Nucleus.Classical.Tagged
