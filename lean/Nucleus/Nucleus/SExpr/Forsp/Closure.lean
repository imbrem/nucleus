import Nucleus.SExpr.Forsp.Tree

/-!
# Concrete and extensional Forsp closures

Concrete closures retain code plus a lexical environment and may themselves
be stored behind an improper `(index . closure-magic)` S-expression.  Their
extensional interpretation is the fuel-indexed state transformer obtained by
running that captured computation.  Equivalence is pointwise equality on all
fuel bounds and machine states.
-/

namespace Nucleus.SExpr2.Forsp.Closure

open Nucleus.SExpr2.Forsp

/-- The ordinary closure representation used by the tree evaluator. -/
structure Concrete where
  body : Object
  environment : Tree.Environment
  deriving DecidableEq, Repr

/-- A table of closures, addressed by improper S-expression handles. -/
abbrev Table := List Concrete

def reference (index : Nat) : Object := literalReference index .closure

def Table.allocate (table : Table) (closure : Concrete) : Table × Object :=
  (table ++ [closure], reference table.length)

def Table.decode? (table : Table) : Object → Option Concrete
  | .cons (.atom (.index index)) (.atom (.magic .closure)) => table[index]?
  | _ => none

@[simp] theorem Table.decode?_allocate (table : Table) (closure : Concrete) :
    (table.allocate closure).1.decode? (table.allocate closure).2 = some closure := by
  simp [Table.allocate, Table.decode?, reference, literalReference]

theorem Table.allocate_preserves (table : Table) (closure : Concrete)
    {index : Nat} {existing : Concrete} (h : table[index]? = some existing) :
    (table.allocate closure).1[index]? = some existing := by
  have hi : index < table.length := List.getElem?_eq_some_iff.mp h |>.1
  simpa [Table.allocate, List.getElem?_append_left hi] using h

/-- The extensional view of a closure.  Fuel remains explicit so divergent
closures are represented without a partial-function quotient. -/
structure Abstract where
  run : Nat → Tree.State → Except Tree.Error Tree.State

def Concrete.abstract (closure : Concrete) : Abstract where
  run fuel state := (Tree.compute fuel closure.body closure.environment state).map Prod.snd

/-- Pointwise observational equivalence between code/environment and
state-transformer closures. -/
def Equivalent (concrete : Concrete) (abstract : Abstract) : Prop :=
  ∀ fuel state,
    abstract.run fuel state =
      (Tree.compute fuel concrete.body concrete.environment state).map Prod.snd

@[simp] theorem abstract_equivalent (closure : Concrete) :
    Equivalent closure closure.abstract := by
  intro fuel state
  rfl

theorem equivalent_ext {concrete : Concrete} {left right : Abstract}
    (hleft : Equivalent concrete left) (hright : Equivalent concrete right) :
    left.run = right.run := by
  funext fuel state
  rw [hleft, hright]

/-- Applying the extensional closure agrees with forcing the corresponding
concrete runtime closure, modulo the caller environment which Forsp preserves. -/
theorem abstract_run_eq_concrete_force (closure : Concrete) (fuel : Nat)
    (state : Tree.State) :
    closure.abstract.run fuel state =
      (Tree.compute fuel closure.body closure.environment state).map Prod.snd :=
  rfl

end Nucleus.SExpr2.Forsp.Closure
