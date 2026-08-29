import Nucleus.Classical.Alternating.Abstract
import Nucleus.Classical.Tagged.Abstract

/-!
# Embedding alternating formulas into tagged formulas

An untagged alternating array obtains its connective from its position.  This
embedding records that connective explicitly: an `all` occurrence becomes a
tagged conjunction, an `any` occurrence becomes a tagged disjunction, and the
mode flips at every array edge.  Literal and node signs are unchanged.  The
image contains no `sat` nodes.
-/

namespace Nucleus.Classical.Embedding.AlternatingToTagged

universe u

open Nucleus.Classical

variable {Atom : Type u}

/- Embed an alternating expression at the connective selected by its root
position. -/
mutual
  def formula : Alternating.Mode → Alternating.Expr Atom → Tagged.Formula Atom
    | _, .literal literal => .literal literal
    | .all, .node negative children =>
        .and negative (formulas .any children)
    | .any, .node negative children =>
        .or negative (formulas .all children)

  /-- Embed a proper child list, using one mode for every sibling. -/
  def formulas : Alternating.Mode → Alternating.Children Atom →
      List (Tagged.Formula Atom)
    | _, .nil => []
    | mode, .cons head tail => formula mode head :: formulas mode tail
end

@[simp] theorem formulas_nil (mode : Alternating.Mode) :
    formulas (Atom := Atom) mode .nil = [] := by
  simp [formulas]

@[simp] theorem formulas_cons (mode : Alternating.Mode)
    (head : Alternating.Expr Atom) (tail : Alternating.Children Atom) :
    formulas mode (.cons head tail) = formula mode head :: formulas mode tail := by
  simp [formulas]

@[simp] theorem formulas_ofList (mode : Alternating.Mode)
    (children : List (Alternating.Expr Atom)) :
    formulas mode (Alternating.Children.ofList children) =
      children.map (formula mode) := by
  induction children with
  | nil => simp [Alternating.Children.ofList]
  | cons head tail ih => simp [Alternating.Children.ofList, ih]

@[simp] theorem formula_array (mode : Alternating.Mode) (negative : Bool)
    (children : List (Alternating.Expr Atom)) :
    formula mode (Alternating.Expr.array negative children) =
      match mode with
      | .all => .and negative (children.map (formula .any))
      | .any => .or negative (children.map (formula .all)) := by
  cases mode <;> simp [formula, Alternating.Expr.array]

private theorem signed_iff (negative value : Bool) (claim : Prop)
    (equivalent : claim ↔ value = true) :
    Tagged.Signed negative claim ↔
      (if negative then !value else value) = true := by
  cases negative <;> cases value <;> simp_all [Tagged.Signed]

/- The embedding preserves evaluation of expressions and child folds. -/
mutual
  @[simp] theorem eval_formula (assignment : Assignment Atom) :
      ∀ (mode : Alternating.Mode) (expr : Alternating.Expr Atom),
        (formula mode expr).Eval assignment ↔
          expr.eval assignment mode = true
    | _, .literal literal => by
        simp [formula]
    | .all, .node negative children => by
        simp only [formula, Tagged.Formula.Eval, Alternating.Expr.eval,
          Alternating.Mode.flip]
        exact signed_iff negative _ _ (eval_all assignment .any children)
    | .any, .node negative children => by
        simp only [formula, Tagged.Formula.Eval, Alternating.Expr.eval,
          Alternating.Mode.flip]
        exact signed_iff negative _ _ (eval_any assignment .all children)

  theorem eval_all (assignment : Assignment Atom) :
      ∀ (mode : Alternating.Mode) (children : Alternating.Children Atom),
        Tagged.Formula.EvalAll (formulas mode children) assignment ↔
          Alternating.Mode.aggregate .all
            (Alternating.Expr.evalChildren assignment mode children) = true
    | _, .nil => by
        simp only [formulas, Tagged.Formula.EvalAll,
          Alternating.Expr.evalChildren, Alternating.Mode.aggregate, List.all]
    | mode, .cons head tail => by
        simp only [formulas, Tagged.Formula.EvalAll,
          Alternating.Expr.evalChildren, Alternating.Mode.aggregate,
          List.all, eval_formula assignment mode head,
          eval_all assignment mode tail]
        simp

  theorem eval_any (assignment : Assignment Atom) :
      ∀ (mode : Alternating.Mode) (children : Alternating.Children Atom),
        Tagged.Formula.EvalAny (formulas mode children) assignment ↔
          Alternating.Mode.aggregate .any
            (Alternating.Expr.evalChildren assignment mode children) = true
    | _, .nil => by
        simp only [formulas, Tagged.Formula.EvalAny,
          Alternating.Expr.evalChildren, Alternating.Mode.aggregate, List.any]
        simp
    | mode, .cons head tail => by
        simp only [formulas, Tagged.Formula.EvalAny,
          Alternating.Expr.evalChildren, Alternating.Mode.aggregate,
          List.any, eval_formula assignment mode head,
          eval_any assignment mode tail]
        simp
end

/-- Record the alternating root modes in a tagged sequent. -/
def sequent (value : Alternating.Sequent Atom) : Tagged.Sequent Atom where
  premise := formula .all value.left
  conclusion := formula .any value.right

/-- Embed every sequent in an alternating arena. -/
def arena (value : Alternating.Arena Atom) : List (Tagged.Sequent Atom) :=
  value.map sequent

@[simp] theorem sequent_holds_iff (assignment : Assignment Atom)
    (value : Alternating.Sequent Atom) :
    (sequent value).Holds assignment ↔ value.Holds assignment := by
  simp [sequent, Tagged.Sequent.Holds, Alternating.Sequent.Holds]

@[simp] theorem sequent_entailsAt_iff (known : PartialAssignment Atom)
    (value : Alternating.Sequent Atom) :
    (sequent value).EntailsAt known ↔ value.EntailsAt known := by
  simp only [Tagged.Sequent.EntailsAt, Alternating.Sequent.EntailsAt, Under]
  constructor
  · intro holds assignment completes
    exact sequent_holds_iff assignment value |>.mp (holds assignment completes)
  · intro holds assignment completes
    exact sequent_holds_iff assignment value |>.mpr (holds assignment completes)

@[simp] theorem arena_holds_iff (assignment : Assignment Atom)
    (value : Alternating.Arena Atom) :
    Tagged.Holds (arena value) assignment ↔
      ∀ item ∈ value, item.Holds assignment := by
  simp [Tagged.Holds, arena]

@[simp] theorem arena_entailsAt_iff (known : PartialAssignment Atom)
    (value : Alternating.Arena Atom) :
    Tagged.EntailsAt known (arena value) ↔ value.EntailsAt known := by
  constructor
  · intro holds item member assignment completes
    have embedded : (sequent item).Holds assignment :=
      holds assignment completes (sequent item)
        (List.mem_map.mpr ⟨item, member, rfl⟩)
    exact (sequent_holds_iff assignment item).mp embedded
  · intro holds assignment completes item member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp member
    exact (sequent_holds_iff assignment source).mpr
      (holds source sourceMember assignment completes)

/-- Null-assignment validity is preserved for one sequent. -/
@[simp] theorem sequent_syllogism_iff (value : Alternating.Sequent Atom) :
    Tagged.Syllogism [sequent value] ↔ value.IsSyllogism := by
  rw [Tagged.syllogism_iff, Alternating.Sequent.isSyllogism_iff]
  constructor
  · intro holds assignment
    exact (sequent_holds_iff assignment value).mp
      (holds assignment (sequent value) (by simp))
  · intro holds assignment item member
    have equal : item = sequent value := by simpa using member
    subst item
    exact (sequent_holds_iff assignment value).mpr (holds assignment)

/-- Null-assignment validity is preserved for a whole arena. -/
@[simp] theorem arena_syllogism_iff (value : Alternating.Arena Atom) :
    Tagged.Syllogism (arena value) ↔ value.Syllogistic := by
  rw [Tagged.syllogism_iff]
  simp only [arena_holds_iff, Alternating.Arena.Syllogistic,
    Alternating.Sequent.isSyllogism_iff]
  constructor
  · intro holds item member assignment
    exact holds assignment item member
  · intro holds assignment item member
    exact holds item member assignment

end Nucleus.Classical.Embedding.AlternatingToTagged
