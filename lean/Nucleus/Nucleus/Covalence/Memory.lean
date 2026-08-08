import Mathlib
import Nucleus.Covalence

/-!
# Depth-bounded unfolding of persistent Covalence rows

This module uses `Covalence.HolTag`, `Row`, and `Image` verbatim.  Depth is a
dereference budget, not cycle detection: zero performs no lookup; successor
performs one lookup and gives each referenced child the predecessor budget.

The current Covalence API has no relation repairing an untyped recursive
`Hol` into `SortedHol`.  Consequently this module proves the complete generic
row/unfold/refinement layer.  Memory derivability must wait for that one
integration operation; it is not simulated by a second tag or sorted-tree
language here.
-/

universe u v

namespace Nucleus.Covalence.Memory

open Nucleus.Covalence

abbrev Memory (Base : Type u) (Index : Type v) := Image Base Index

/-- Runtime-facing lazy reference.  Constructing a cursor is O(1); it does
not unfold or traverse memory. -/
structure Cursor (Base : Type u) (Index : Type v) where
  mem : Memory Base Index
  index : Index
  depth : Nat

def Cursor.fetch (c : Cursor Base Index) : Option (Row Base Index) :=
  match c.depth with
  | 0 => none
  | _ + 1 => c.mem c.index

def Cursor.child (c : Cursor Base Index) : Option Index → Option (Cursor Base Index)
  | none => none
  | some i => match c.depth with
    | 0 => none
    | d + 1 => some ⟨c.mem, i, d⟩

/-- A locally checked rule node stores only its direct fetch and child
references.  No constructor recursively unfolds a child. -/
structure LocalNode (Base : Type u) (Index : Type v) where
  cursor : Cursor Base Index
  row : Option (Row Base Index)
  checked : row = cursor.fetch

def Cursor.local (c : Cursor Base Index) : LocalNode Base Index := ⟨c, c.fetch, rfl⟩

/-- The stable injection into the current persisted hole-name representation.
It is kept explicit: unfolding never invents, shifts, or conflates names. -/
structure Naming (Index : Type v) where
  holeName : Index → Nat
  injective : Function.Injective holeName

def hole (names : Naming Index) (i : Index) : Hol Base :=
  .node (.hole (names.holeName i)) none none none

/-- Which coordinates are required by each stored tag.  Missing required
coordinates become the hole named by the row being unfolded; genuinely
unused coordinates remain absent. -/
def requirements : HolTag Base → Bool × Bool × Bool
  | .hole _ | .atom _ | .tyVar | .tyBool | .tmVar | .tmBool => (false, false, false)
  | .tyLam | .tyAll | .tmTyLam => (true, false, false)
  | .tyApp | .tyArr | .tmApp => (true, true, false)
  | .tySub | .tmLam | .tmTyApp | .tmEps => (true, false, true)
  | .tmEq | .tmAbs | .tmRep => (true, true, true)

def child (names : Naming Index) (go : Index → Hol Base) (parent : Index)
    (required : Bool) : Option Index → Option (Hol Base)
  | some i => some (go i)
  | none => if required then some (hole names parent) else none

/-- Exact dereference-budget unfolding.  There is deliberately no visited
set and no acyclicity premise. -/
def unfold (names : Naming Index) (mem : Memory Base Index) : Nat → Index → Hol Base
  | 0, i => hole names i
  | d + 1, i =>
      match mem i with
      | none => hole names i
      | some (tag, lhs, rhs, ty) =>
        let req := requirements tag
        .node tag
          (child names (unfold names mem d) i req.1 lhs)
          (child names (unfold names mem d) i req.2.1 rhs)
          (child names (unfold names mem d) i req.2.2 ty)

@[simp] theorem unfold_zero (names : Naming Index) (mem : Memory Base Index) (i : Index) :
    unfold names mem 0 i = hole names i := rfl

theorem unfold_succ_missing (names : Naming Index) (mem : Memory Base Index)
    (h : mem i = none) : unfold names mem (d + 1) i = hole names i := by
  simp [unfold, h]

/-- One-step fold/view law: a fetched persistent row becomes precisely one
recursive node, with field order unchanged. -/
theorem unfold_succ_view (names : Naming Index) (mem : Memory Base Index)
    (h : mem i = some (tag, lhs, rhs, ty)) :
    (unfold names mem (d + 1) i).view =
      (tag,
        child names (unfold names mem d) i (requirements tag).1 lhs,
        child names (unfold names mem d) i (requirements tag).2.1 rhs,
        child names (unfold names mem d) i (requirements tag).2.2 ty) := by
  simp [unfold, h, Hol.view]

inductive OptionRefines : Option (Hol Base) → Option (Hol Base) → Prop
  | none : OptionRefines none none
  | some : Refines a b → OptionRefines (some a) (some b)

/-- Untyped tree information order.  Cutoff/missing holes are bottom; fetched
matching rows refine componentwise. -/
inductive Refines : Hol Base → Hol Base → Prop
  | hole : Refines (Hol.node (.hole name) none none none) t
  | node : OptionRefines lhs lhs' → OptionRefines rhs rhs' → OptionRefines ty ty' →
      Refines (.node tag lhs rhs ty) (.node tag lhs' rhs' ty')

notation:50 x " ⊑ " y => Refines x y

theorem Refines.refl (t : Hol Base) : t ⊑ t := by
  cases t
  exact .node (by cases ‹Option (Hol Base)› <;> aesop)
    (by cases ‹Option (Hol Base)› <;> aesop)
    (by cases ‹Option (Hol Base)› <;> aesop)

theorem Refines.trans {a b c : Hol Base} : a ⊑ b → b ⊑ c → a ⊑ c := by
  intro hab hbc
  induction hab generalizing c with
  | hole => exact .hole
  | node hl hr ht ihl ihr iht =>
    cases hbc with
    | node hl' hr' ht' =>
      exact .node (by cases hl <;> cases hl' <;> aesop)
        (by cases hr <;> cases hr' <;> aesop)
        (by cases ht <;> cases ht' <;> aesop)

theorem child_refines (names : Naming Index) {f g : Index → Hol Base}
    (hfg : ∀ i, f i ⊑ g i) (parent : Index) (required : Bool) (oi : Option Index) :
    OptionRefines (child names f parent required oi) (child names g parent required oi) := by
  cases oi with
  | some i => exact .some (hfg i)
  | none => cases required <;> simp [child] <;> aesop (add safe constructors OptionRefines Refines)

/-- Mandatory one-step refinement theorem. -/
theorem unfold_step (names : Naming Index) (mem : Memory Base Index) (d : Nat) (i : Index) :
    unfold names mem d i ⊑ unfold names mem (d + 1) i := by
  induction d generalizing i with
  | zero => exact .hole
  | succ d ih =>
    simp only [unfold]
    split
    · exact .refl _
    · exact .node (child_refines names ih _ _ _)
        (child_refines names ih _ _ _) (child_refines names ih _ _ _)

theorem unfold_mono (names : Naming Index) (mem : Memory Base Index)
    {d e : Nat} (hde : d ≤ e) (i : Index) :
    unfold names mem d i ⊑ unfold names mem e i := by
  induction hde with
  | refl => exact .refl _
  | @step e _ ih => exact Refines.trans ih (unfold_step names mem e i)

/-- Unfolding preserves the locally nameless identity of every cutoff: the
stored free/hole name is exactly the injected index and is never shifted. -/
theorem cutoff_name (names : Naming Index) (mem : Memory Base Index) (i : Index) :
    unfold names mem 0 i = .node (.hole (names.holeName i)) none none none := rfl

theorem distinct_cutoff_names (names : Naming Index) (hij : i ≠ j) :
    names.holeName i ≠ names.holeName j := fun h => hij (names.injective h)

/-- The recursive specification is the semantics of a lazy cursor, never its
runtime representation. -/
def Cursor.denote (names : Naming Index) (c : Cursor Base Index) : Hol Base :=
  unfold names c.mem c.depth c.index

end Nucleus.Covalence.Memory
