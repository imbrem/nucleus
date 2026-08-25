import Nucleus.Hol.Ethane.ClassicalMatrix

/-!
# Ambient (`amb`) logic

This file starts the representation-independent semantics of the outer
assertion language. Runtime arenas currently use signed 32-bit indices, but
the logical model deliberately quantifies over an arbitrary reference type.
The final section gives an unbounded integer model of the current wire
convention; fixed i16/i32/i64 representations are refinements of that model.
-/

namespace Nucleus.Hol.Ethane.Amb

open Nucleus.Hol.Ethane.ClassicalMatrix

/-- The ambient predicate constructors implemented by the first `amb`
refactor.  The source is an import-table index, not the imported object
itself.  Logical connectives deliberately do not occur here yet: arbitrary
classical relationships between these atoms live in `amb.ctx`, `amb.thm`, and
`pred.syl`. -/
inductive Pred (Object Ref : Type)
  | arenaOk (object : Object)
  | holSort (object : Object) (term sort : Ref)
  deriving DecidableEq

/-- Denotation of one predicate row relative to object validity and the
denotations assigned to referenced predicate rows. -/
def Pred.Holds {Object Ref : Type} (objectOk : Object → Prop)
    (holSort : Object → Ref → Ref → Prop) : Pred Object Ref → Prop
  | .arenaOk object => objectOk object
  | .holSort object term sort => holSort object term sort

@[simp] theorem Pred.holds_arenaOk {Object Ref : Type}
    (objectOk : Object → Prop) (holSort : Object → Ref → Ref → Prop)
    (object : Object) :
    (Pred.arenaOk object : Pred Object Ref).Holds objectOk holSort ↔
      objectOk object := Iff.rfl

@[simp] theorem Pred.holds_holSort {Object Ref : Type}
    (objectOk : Object → Prop) (holSort : Object → Ref → Ref → Prop)
    (object : Object) (term sort : Ref) :
    (Pred.holSort object term sort : Pred Object Ref).Holds objectOk holSort ↔
      holSort object term sort := Iff.rfl

/-- The ambient data needed to interpret definitions, named primitive
assumptions, exact propositional assumptions, and checked consequences.

`ax` deliberately contains names rather than formulas.  A name has no
propositional denotation merely by occurring here: its meaning is supplied by
the checked rule that recognizes it, just as for HOL axiom names.  Storage and
index width are intentionally absent. -/
structure Theory (Object Ref : Type) where
  ax : Finset String
  defs : Ref → Option (Pred Object Ref)
  ctx : Cnf Ref

/-- A valuation respects every resident predicate definition. Missing
references remain uninterpreted rather than becoming false. -/
def Theory.Respects {Object Ref : Type} (theory : Theory Object Ref)
    (objectOk : Object → Prop) (holSort : Object → Ref → Ref → Prop)
    (valuation : Valuation Ref) : Prop :=
  ∀ ref predicate, theory.defs ref = some predicate →
    (valuation ref ↔ predicate.Holds objectOk holSort)

/-- Valuations admitted by the ambient definitions and exact local context.
Named axioms are intentionally absent: a string does not itself denote a
proposition. -/
def Theory.Admits {Object Ref : Type} (theory : Theory Object Ref)
    (objectOk : Object → Prop) (holSort : Object → Ref → Ref → Prop)
    (valuation : Valuation Ref) : Prop :=
  theory.Respects objectOk holSort valuation ∧
    theory.ctx.Holds valuation

/-- Every named axiom in a theory must be accepted by the external catalogue
of checked primitive rules. -/
def Theory.AllowsAxioms {Object Ref : Type} (theory : Theory Object Ref)
    (allowed : String → Prop) : Prop :=
  ∀ name ∈ theory.ax, allowed name

/-- An `amb.thm` is sound precisely when its CNF-to-DNF sequent holds under
every valuation admitted by `amb.defs` and `amb.ctx`. Checked rules may
separately require a name in `amb.ax`; the name is not a formula. -/
def Theory.Proves {Object Ref : Type} (theory : Theory Object Ref)
    (objectOk : Object → Prop) (holSort : Object → Ref → Ref → Prop)
    (fact : Sequent Ref) : Prop :=
  ∀ valuation, theory.Admits objectOk holSort valuation → fact.Holds valuation

theorem Theory.proves_weaken {Object Ref : Type} {theory : Theory Object Ref}
    {objectOk : Object → Prop} {sourceLeft extraLeft : List (Clause Ref)}
    {sourceRight extraRight : List (Cube Ref)}
    {holSort : Object → Ref → Ref → Prop}
    (proved : theory.Proves objectOk holSort
      (Sequent.mk (Cnf.mk sourceLeft) (Dnf.mk sourceRight))) :
    theory.Proves objectOk holSort
      (Sequent.mk (Cnf.mk (sourceLeft ++ extraLeft))
        (Dnf.mk (sourceRight ++ extraRight))) := by
  intro valuation admitted targetLeft
  obtain ⟨cube, member, truth⟩ := proved valuation admitted (by
    intro clause member
    exact targetLeft clause (List.mem_append_left _ member))
  exact ⟨cube, List.mem_append_left _ member, truth⟩

/-! ## Unbounded wire-index model

Overflow is deliberately absent here. A concrete fixed-width decoder either
produces one of these values or returns an error; returning an error cannot
add a theorem. -/

/-- Positive, one-based references before choosing an i16/i32/i64 runtime
representation. -/
abbrev IntRef := { value : Int // 0 < value }

/-- Nonzero signed literals before choosing a fixed runtime width. Negative
values denote positive predicates, matching the Ethane convention. -/
abbrev IntLit := { value : Int // value ≠ 0 }

def IntLit.neg (literal : IntLit) : IntLit :=
  ⟨-literal.val, by simpa using literal.property⟩

@[simp] theorem IntLit.neg_val (literal : IntLit) : literal.neg.val = -literal.val := rfl

@[simp] theorem IntLit.neg_neg (literal : IntLit) : literal.neg.neg = literal := by
  apply Subtype.ext
  simp [IntLit.neg]

def IntLit.positive (reference : IntRef) : IntLit :=
  ⟨-reference.val, by omega⟩

@[simp] theorem IntLit.positive_val (reference : IntRef) :
    (IntLit.positive reference).val = -reference.val := rfl

/-- A fixed-width representation is sound when decoding injects its resident
references and literals into the unbounded integer model. -/
structure Encoding (Ref Lit : Type) where
  refToInt : Ref → IntRef
  litToInt : Lit → IntLit
  ref_injective : Function.Injective refToInt
  lit_injective : Function.Injective litToInt
  positive : Ref → Lit
  positive_commutes : ∀ reference,
    litToInt (positive reference) = IntLit.positive (refToInt reference)
  neg : Lit → Lit
  neg_commutes : ∀ literal, litToInt (neg literal) = (litToInt literal).neg

theorem Encoding.neg_involutive {Ref Lit : Type} (encoding : Encoding Ref Lit)
    (literal : Lit) : encoding.neg (encoding.neg literal) = literal := by
  apply encoding.lit_injective
  rw [encoding.neg_commutes, encoding.neg_commutes]
  simp

end Nucleus.Hol.Ethane.Amb
