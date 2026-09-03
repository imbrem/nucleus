import Nucleus.Metamath.Database

/-!
# Axiom sets and propositional metatheory

This module records three small, explicit metatheorems used when auditing a
Metamath development:

* derivability, and hence the set of derivable expressions, is monotone in the
  set of usable database assertions;
* the classical implicational propositional calculus is sound for its ordinary
  truth semantics;
* adding fresh propositional names with explicit, nonrecursive definitions is
  conservative over the original language.

The last result is deliberately about the explicit definition calculus below.
It does not classify `df-*` assertions in an arbitrary Metamath database as
definitions, nor prove those assertions conservative. Such a claim requires a
checked bridge from the database's concrete formulas to this criterion.
-/

namespace Nucleus.Metamath

/-- Expressions derivable when exactly `usable` database positions may be
cited. The surrounding Metamath hypotheses remain explicit in `ctx`. -/
def TheoremsUnder (db : Database) (usable : Nat → Prop) (ctx : Frame) : Set Expr :=
  {e | Provable db usable ctx e}

/-- Enlarging an axiom set can only enlarge its set of derivable expressions. -/
theorem theoremsUnder_mono {db : Database} {small large : Nat → Prop} {ctx : Frame}
    (h : ∀ i, small i → large i) :
    TheoremsUnder db small ctx ⊆ TheoremsUnder db large ctx := by
  intro e derivation
  exact derivation.mono h

namespace Propositional

/-- Formulas over a caller-selected set of atomic propositions. -/
inductive Formula (Atom : Type) where
  | atom (name : Atom)
  | falsum
  | imp (left right : Formula Atom)
  deriving DecidableEq, Repr

namespace Formula

/-- Classical truth semantics for propositional formulas. -/
def Holds {Atom : Type} (valuation : Atom → Prop) : Formula Atom → Prop
  | .atom name => valuation name
  | .falsum => False
  | .imp left right => Holds valuation left → Holds valuation right

/-- Negation encoded using implication and falsity. -/
def neg {Atom : Type} (p : Formula Atom) : Formula Atom := .imp p .falsum

end Formula

/-- Hilbert derivations from a set of assumptions, using `K`, `S`, classical
contraposition, and modus ponens. -/
inductive Derivable {Atom : Type} (assumptions : Formula Atom → Prop) : Formula Atom → Prop where
  | assumption {p : Formula Atom} (member : assumptions p) : Derivable assumptions p
  | k (p q : Formula Atom) : Derivable assumptions (.imp p (.imp q p))
  | s (p q r : Formula Atom) :
      Derivable assumptions
        (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r)))
  | classical (p q : Formula Atom) :
      Derivable assumptions (.imp (.imp p.neg q.neg) (.imp q p))
  | mp {p q : Formula Atom} :
      Derivable assumptions (.imp p q) → Derivable assumptions p → Derivable assumptions q

/-- Propositional derivability is monotone in its assumptions. -/
theorem Derivable.mono {Atom : Type} {small large : Formula Atom → Prop}
    (h : ∀ p, small p → large p) {p : Formula Atom} :
    Derivable small p → Derivable large p := by
  intro derivation
  induction derivation with
  | assumption member => exact .assumption (h _ member)
  | k p q => exact .k p q
  | s p q r => exact .s p q r
  | classical p q => exact .classical p q
  | mp _ _ implication premise => exact .mp implication premise

/-- Replace every use of an assumption by a derivation from another theory. -/
theorem Derivable.mapAssumptions {Atom : Type} {source target : Formula Atom → Prop}
    (replace : ∀ p, source p → Derivable target p) {p : Formula Atom} :
    Derivable source p → Derivable target p := by
  intro derivation
  induction derivation with
  | assumption member => exact replace _ member
  | k p q => exact .k p q
  | s p q r => exact .s p q r
  | classical p q => exact .classical p q
  | mp _ _ implication premise => exact .mp implication premise

/-- Every Hilbert derivation preserves truth. -/
theorem Derivable.sound {Atom : Type} {assumptions : Formula Atom → Prop}
    {p : Formula Atom} (derivation : Derivable assumptions p)
    (valuation : Atom → Prop)
    (assumptionsTrue : ∀ q, assumptions q → q.Holds valuation) :
    p.Holds valuation := by
  induction derivation with
  | assumption member => exact assumptionsTrue _ member
  | k _ _ => exact fun hp _ => hp
  | s _ _ _ => exact fun hpqr hpq hp => hpqr hp (hpq hp)
  | classical p q =>
      intro hcontra hq
      by_contra hp
      exact hcontra (fun hp' => hp hp') hq
  | mp _ _ implication premise => exact implication premise

/-- In particular, every theorem of the propositional axiom set is true under
every valuation. -/
theorem theorem_true {Atom : Type} {p : Formula Atom}
    (derivation : Derivable (fun _ => False) p) (valuation : Atom → Prop) :
    p.Holds valuation :=
  derivation.sound valuation (fun _ impossible => False.elim impossible)

/-- An axiom set is consistent when it cannot derive falsity. -/
def Consistent {Atom : Type} (axioms : Formula Atom → Prop) : Prop :=
  ¬ Derivable axioms .falsum

/-- Ordinary propositional logic, with no premises beyond its Hilbert schemes,
is consistent. -/
theorem propositional_consistent {Atom : Type} :
    Consistent (Atom := Atom) (fun _ => False) := by
  intro derivation
  exact theorem_true derivation (fun _ => True)

/-- The intentionally wrong theory that postulates falsity is inconsistent. -/
theorem falsum_axiom_inconsistent {Atom : Type} :
    ¬ Consistent (Atom := Atom) (fun p => p = .falsum) := by
  intro consistent
  exact consistent (.assumption rfl)

/-- A subset of a consistent axiom set is consistent. -/
theorem consistent_of_subset {Atom : Type} {small large : Formula Atom → Prop}
    (subset : ∀ p, small p → large p) (consistent : Consistent large) :
    Consistent small := by
  intro contradiction
  exact consistent (contradiction.mono subset)

/-- Adding an already derivable proposition preserves and reflects
consistency. -/
theorem consistent_add_derived_iff {Atom : Type} {axioms : Formula Atom → Prop}
    {p : Formula Atom} (hp : Derivable axioms p) :
    Consistent (fun q => axioms q ∨ q = p) ↔ Consistent axioms := by
  constructor
  · exact consistent_of_subset (fun _ member => Or.inl member)
  · intro consistent contradiction
    apply consistent
    exact contradiction.mapAssumptions fun q member => by
      rcases member with member | rfl
      · exact .assumption member
      · exact hp

/-- `p` is independent of `axioms` when adjoining either `p` or its negation
preserves consistency. This proof-theoretic definition makes no completeness
claim. -/
def Independent {Atom : Type} (axioms : Formula Atom → Prop) (p : Formula Atom) : Prop :=
  Consistent (fun q => axioms q ∨ q = p) ∧
    Consistent (fun q => axioms q ∨ q = p.neg)

/-- Two models, differing on `p`, certify proof-theoretic independence. -/
theorem independent_of_models {Atom : Type} {axioms : Formula Atom → Prop}
    {p : Formula Atom} {trueModel falseModel : Atom → Prop}
    (axiomsTrue : ∀ q, axioms q → q.Holds trueModel)
    (axiomsFalse : ∀ q, axioms q → q.Holds falseModel)
    (pTrue : p.Holds trueModel) (pFalse : ¬ p.Holds falseModel) :
    Independent axioms p := by
  constructor
  · intro contradiction
    exact contradiction.sound trueModel
      (fun q member => member.elim (axiomsTrue q) (fun h => h ▸ pTrue))
  · intro contradiction
    have falseNeg : p.neg.Holds falseModel := fun hp => pFalse hp
    exact contradiction.sound falseModel
      (fun q member => member.elim (axiomsFalse q) (fun h => h ▸ falseNeg))

/-- A concrete independence sanity check: one unconstrained proposition is
independent of pure propositional logic. -/
theorem fresh_proposition_independent :
    Independent (fun _ : Formula Unit => False) (.atom ()) := by
  apply independent_of_models (trueModel := fun _ => True) (falseModel := fun _ => False)
  · exact fun _ impossible => False.elim impossible
  · exact fun _ impossible => False.elim impossible
  · trivial
  · simp [Formula.Holds]

/-- Embed a base formula into a language with fresh defined proposition names. -/
def lift {Base Defined : Type} : Formula Base → Formula (Sum Base Defined)
  | .atom name => .atom (.inl name)
  | .falsum => .falsum
  | .imp left right => .imp (lift left) (lift right)

/-- Expand every fresh name to its defining formula in the base language. -/
def expand {Base Defined : Type} (definitions : Defined → Formula Base) :
    Formula (Sum Base Defined) → Formula Base
  | .atom (.inl name) => .atom name
  | .atom (.inr name) => definitions name
  | .falsum => .falsum
  | .imp left right => .imp (expand definitions left) (expand definitions right)

@[simp]
theorem expand_lift {Base Defined : Type} (definitions : Defined → Formula Base)
    (p : Formula Base) : expand definitions (lift (Defined := Defined) p) = p := by
  induction p with
  | atom _ => rfl
  | falsum => rfl
  | imp _ _ left right => simp [lift, expand, left, right]

/-- A definitional extension: base assumptions and propositional logic, plus
both directions of each explicit definition. Definition bodies mention only
base atoms, which rules out recursive definitions by construction. -/
inductive DefinitionalDerivable {Base Defined : Type}
    (assumptions : Formula Base → Prop) (definitions : Defined → Formula Base) :
    Formula (Sum Base Defined) → Prop where
  | assumption {p : Formula Base} (member : assumptions p) :
      DefinitionalDerivable assumptions definitions (lift p)
  | k (p q : Formula (Sum Base Defined)) :
      DefinitionalDerivable assumptions definitions (.imp p (.imp q p))
  | s (p q r : Formula (Sum Base Defined)) :
      DefinitionalDerivable assumptions definitions
        (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r)))
  | classical (p q : Formula (Sum Base Defined)) :
      DefinitionalDerivable assumptions definitions (.imp (.imp p.neg q.neg) (.imp q p))
  | definitionForward (name : Defined) :
      DefinitionalDerivable assumptions definitions
        (.imp (.atom (.inr name)) (lift (definitions name)))
  | definitionBackward (name : Defined) :
      DefinitionalDerivable assumptions definitions
        (.imp (lift (definitions name)) (.atom (.inr name)))
  | mp {p q : Formula (Sum Base Defined)} :
      DefinitionalDerivable assumptions definitions (.imp p q) →
      DefinitionalDerivable assumptions definitions p →
      DefinitionalDerivable assumptions definitions q

/-- Identity is derivable in the Hilbert calculus. -/
theorem Derivable.identity {Atom : Type} {assumptions : Formula Atom → Prop}
    (p : Formula Atom) : Derivable assumptions (.imp p p) := by
  exact .mp (.mp (.s p (.imp p p) p) (.k p (.imp p p))) (.k p p)

/-- Expanding definitions translates every extended derivation back to a base
derivation. -/
theorem DefinitionalDerivable.expand {Base Defined : Type}
    {assumptions : Formula Base → Prop} {definitions : Defined → Formula Base}
    {p : Formula (Sum Base Defined)}
    (derivation : DefinitionalDerivable assumptions definitions p) :
    Derivable assumptions (Propositional.expand definitions p) := by
  induction derivation with
  | assumption member => simpa using Derivable.assumption member
  | k p q => exact .k (Propositional.expand definitions p) (Propositional.expand definitions q)
  | s p q r =>
      exact .s (Propositional.expand definitions p) (Propositional.expand definitions q)
        (Propositional.expand definitions r)
  | classical p q =>
      exact .classical (Propositional.expand definitions p) (Propositional.expand definitions q)
  | definitionForward name =>
      simpa [Propositional.expand] using
        (Derivable.identity (assumptions := assumptions) (definitions name))
  | definitionBackward name =>
      simpa [Propositional.expand] using
        (Derivable.identity (assumptions := assumptions) (definitions name))
  | mp _ _ implication premise => exact .mp implication premise

/-- Every base derivation remains available after definitions are added. -/
theorem Derivable.liftDefinitions {Base Defined : Type}
    {assumptions : Formula Base → Prop} {definitions : Defined → Formula Base}
    {p : Formula Base} (derivation : Derivable assumptions p) :
    DefinitionalDerivable assumptions definitions (lift p) := by
  induction derivation with
  | assumption member => exact .assumption member
  | k p q =>
      simpa [lift] using
        DefinitionalDerivable.k (definitions := definitions) (lift p) (lift q)
  | s p q r =>
      simpa [lift] using
        DefinitionalDerivable.s (definitions := definitions) (lift p) (lift q) (lift r)
  | classical p q =>
      simpa [lift, Formula.neg] using
        DefinitionalDerivable.classical (definitions := definitions) (lift p) (lift q)
  | mp _ _ implication premise =>
      simpa [lift] using DefinitionalDerivable.mp implication premise

/-- Explicit nonrecursive definitions are conservative: an extended proof of
a base-language formula yields a base proof of the same formula. -/
theorem definitions_conservative {Base Defined : Type}
    {assumptions : Formula Base → Prop} {definitions : Defined → Formula Base}
    {p : Formula Base}
    (derivation : DefinitionalDerivable assumptions definitions (lift p)) :
    Derivable assumptions p := by
  simpa using derivation.expand

/-- Consistency for the explicit definitional-extension calculus. -/
def DefinitionalConsistent {Base Defined : Type}
    (assumptions : Formula Base → Prop) (definitions : Defined → Formula Base) : Prop :=
  ¬ DefinitionalDerivable assumptions definitions .falsum

/-- Adding explicit nonrecursive definitions preserves and reflects
consistency. -/
theorem definitions_consistent_iff {Base Defined : Type}
    {assumptions : Formula Base → Prop} {definitions : Defined → Formula Base} :
    DefinitionalConsistent assumptions definitions ↔ Consistent assumptions := by
  constructor
  · intro extended contradiction
    apply extended
    simpa [lift] using contradiction.liftDefinitions (definitions := definitions)
  · intro base contradiction
    exact base contradiction.expand

end Propositional

end Nucleus.Metamath
