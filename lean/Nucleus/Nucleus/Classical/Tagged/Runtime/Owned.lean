import Nucleus.Classical.Tagged.Runtime.AllocatorLaws
import Nucleus.Classical.Mutation.Operations

/-!
# Owned runtime access

Paths identify nested arrays without exposing block addresses. They remain
stable with reference-counted copy-on-write storage.
-/

namespace Nucleus.Classical.Tagged.Runtime.Owned

open Nucleus.Classical.Packed
open Nucleus.Classical.Tagged

universe u v

variable {Atom : Type u} {Raw : Type v}

/-- A root side followed by child indices. -/
structure Path where
  side : Nucleus.Classical.Mutation.Operations.Side
  children : List Nat
  deriving DecidableEq, Repr

def descend? : Formula Atom → List Nat → Option (Formula Atom)
  | formula, [] => some formula
  | .literal _, _ :: _ => none
  | .and _ children, index :: rest
  | .or _ children, index :: rest
  | .sat _ children, index :: rest => do
      let child ← children[index]?
      descend? child rest

def Path.resolve? (path : Path) (sequent : Sequent Atom) : Option (Formula Atom) :=
  descend? (match path.side with
    | .left => sequent.premise
    | .right => sequent.conclusion) path.children

def Path.Valid (path : Path) (sequent : Sequent Atom) : Prop :=
  ∃ formula, path.resolve? sequent = some formula

theorem Path.valid_iff (path : Path) (sequent : Sequent Atom) :
    path.Valid sequent ↔ ∃ formula, path.resolve? sequent = some formula :=
  Iff.rfl

/-- Compare raw references first and decode only on a miss. -/
def pointerFirstEqual [DecidableEq (Formula Atom)] [DecidableEq Raw]
    (decode : Raw → Option (Formula Atom)) (left right : Raw) : Bool :=
  if left = right then true
  else
    match decode left, decode right with
    | some leftFormula, some rightFormula => decide (leftFormula = rightFormula)
    | _, _ => false

theorem pointerFirstEqual_eq_true [DecidableEq (Formula Atom)] [DecidableEq Raw]
    {decode : Raw → Option (Formula Atom)} {left right : Raw} :
    pointerFirstEqual decode left right = true ↔
      left = right ∨ ∃ leftFormula rightFormula,
        decode left = some leftFormula ∧ decode right = some rightFormula ∧
          leftFormula = rightFormula := by
  unfold pointerFirstEqual
  by_cases equal : left = right
  · simp [equal]
  · simp only [equal, ↓reduceIte, false_or]
    cases leftDecoded : decode left with
    | none => simp
    | some leftFormula =>
        cases rightDecoded : decode right with
        | none => simp
        | some rightFormula => simp [eq_comm]

end Nucleus.Classical.Tagged.Runtime.Owned
