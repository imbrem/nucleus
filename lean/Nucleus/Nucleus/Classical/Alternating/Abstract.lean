import Nucleus.Classical.Semantics
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Perm.Basic

/-!
# Untagged alternating classical expressions

An array has no stored connective tag.  Its root position supplies either
conjunction (`all`) or disjunction (`any`), and every array edge flips that
mode.  Literals and arrays carry independent complement bits.  This is the
abstract tree model for a packed representation in which the same distinction
is recovered from an owned root path.
-/

namespace Nucleus.Classical.Alternating

universe u v w

/-- The connective expected at one untagged array occurrence. -/
inductive Mode where
  | all
  | any
  deriving DecidableEq, Repr

namespace Mode

variable {mode : Mode}

/-- Child arrays use the other connective. -/
def flip : Mode → Mode
  | .all => .any
  | .any => .all

@[simp] theorem flip_flip (mode : Mode) : mode.flip.flip = mode := by
  cases mode <;> rfl

/-- Fold child truth values using the connective selected by `mode`. -/
def aggregate : Mode → List Bool → Bool
  | .all, values => values.all id
  | .any, values => values.any id

@[simp] theorem aggregate_nil_all : aggregate .all [] = true := rfl

@[simp] theorem aggregate_nil_any : aggregate .any [] = false := rfl

@[simp] theorem aggregate_cons (mode : Mode) (value : Bool) (values : List Bool) :
    aggregate mode (value :: values) =
      match mode with
      | .all => value && aggregate .all values
      | .any => value || aggregate .any values := by
  cases mode <;> rfl

@[simp] theorem aggregate_append (mode : Mode) (left right : List Bool) :
    aggregate mode (left ++ right) =
      match mode with
      | .all => aggregate .all left && aggregate .all right
      | .any => aggregate .any left || aggregate .any right := by
  cases mode <;> simp [aggregate]

theorem aggregate_eq_of_perm {left right : List Bool}
    (permutation : left.Perm right) :
    aggregate mode left = aggregate mode right := by
  induction permutation with
  | nil => rfl
  | cons value permutation ih =>
      cases mode <;> simp_all [aggregate]
  | swap left right values =>
      cases mode with
      | all => simp [aggregate, Bool.and_left_comm]
      | any => simp [aggregate, Bool.or_left_comm]
  | trans first second ihFirst ihSecond =>
      exact ihFirst.trans ihSecond

theorem aggregate_eq_of_mem_iff {left right : List Bool}
    (same : ∀ value, value ∈ left ↔ value ∈ right) :
    aggregate mode left = aggregate mode right := by
  cases mode with
  | all =>
      rw [Bool.eq_iff_iff]
      simp only [aggregate, List.all_eq_true]
      constructor
      · intro holds value member
        exact holds value ((same value).mpr member)
      · intro holds value member
        exact holds value ((same value).mp member)
  | any =>
      rw [Bool.eq_iff_iff]
      simp only [aggregate, List.any_eq_true]
      constructor
      · rintro ⟨value, member, truth⟩
        exact ⟨value, (same value).mp member, truth⟩
      · rintro ⟨value, member, truth⟩
        exact ⟨value, (same value).mpr member, truth⟩

end Mode

variable {Atom : Type u} {Other : Type v} {Third : Type w}

/-- Grammar sorts for one expression or a proper child list.  The explicit
tail sort avoids a nested inductive while remaining isomorphic to `List`. -/
inductive Ix where
  | expr
  | children
  deriving DecidableEq, Repr

/-- A signed atom or signed untagged n-ary array, with proper child lists. -/
inductive Syn (Atom : Type u) : Ix → Type u where
  | literal (value : Literal Atom) : Syn Atom .expr
  | node (negative : Bool) (children : Syn Atom .children) : Syn Atom .expr
  | nil : Syn Atom .children
  | cons (head : Syn Atom .expr) (tail : Syn Atom .children) : Syn Atom .children

abbrev Expr (Atom : Type u) := Syn Atom .expr
abbrev Children (Atom : Type u) := Syn Atom .children

namespace Children

/-- Build the intrinsic child tail corresponding to a list. -/
def ofList : List (Expr Atom) → Children Atom
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

/-- View an intrinsic child tail as an ordinary list. -/
def toList : Children Atom → List (Expr Atom)
  | .nil => []
  | .cons head tail => head :: toList tail

@[simp] theorem toList_ofList (children : List (Expr Atom)) :
    (ofList children).toList = children := by
  induction children <;> simp [ofList, toList, *]

@[simp] theorem ofList_toList (children : Children Atom) :
    ofList children.toList = children := by
  cases children with
  | nil => simp [ofList, toList]
  | cons head tail => simp [ofList, toList, ofList_toList tail]

end Children

namespace Expr

/-- Construct an n-ary array from an ordinary list of children. -/
def array (negative : Bool) (children : List (Expr Atom)) : Expr Atom :=
  .node negative (Children.ofList children)

@[simp] theorem node_toList (negative : Bool) (children : Children Atom) :
    array negative children.toList = .node negative children := by
  simp [array]

/-- Complement an expression without traversing its array children. -/
def neg : Expr Atom → Expr Atom
  | .literal literal => .literal literal.neg
  | .node negative children => .node (!negative) children

@[simp] theorem neg_neg (expr : Expr Atom) : expr.neg.neg = expr := by
  cases expr with
  | literal literal => simp [neg]
  | node negative children => cases negative <;> rfl

/- Rename every unsigned atom while retaining signs and array structure. -/
mutual
def map (rename : Atom → Other) : Expr Atom → Expr Other
  | .literal literal => .literal ⟨rename literal.atom, literal.negative⟩
  | .node negative children => .node negative (mapChildren rename children)

def mapChildren (rename : Atom → Other) : Children Atom → Children Other
  | .nil => .nil
  | .cons head tail => .cons (map rename head) (mapChildren rename tail)
end

mutual
@[simp] theorem map_id_expr : ∀ expr : Expr Atom, expr.map id = expr
  | .literal literal => by cases literal; simp [map]
  | .node negative children => by
      simp only [map, map_id_children children]

@[simp] theorem map_id_children : ∀ children : Children Atom,
    mapChildren id children = children
  | .nil => by simp [mapChildren]
  | .cons head tail => by
      simp only [mapChildren, map_id_expr head, map_id_children tail]
end

mutual
theorem map_comp_expr (first : Atom → Other) (second : Other → Third)
    : ∀ expr : Expr Atom,
    (expr.map first).map second = expr.map (second ∘ first)
  | .literal literal => by cases literal; simp [map, Function.comp_apply]
  | .node negative children => by
      simp only [map, map_comp_children first second children]

theorem map_comp_children (first : Atom → Other) (second : Other → Third)
    : ∀ children : Children Atom,
    mapChildren second (mapChildren first children) =
      mapChildren (second ∘ first) children
  | .nil => by simp [mapChildren]
  | .cons head tail => by
      simp only [mapChildren, map_comp_expr first second head,
        map_comp_children first second tail]
end

/- The unsigned atoms occurring in an expression, in traversal order. -/
mutual
def fv : Expr Atom → List Atom
  | .literal literal => [literal.atom]
  | .node _ children => fvChildren children

def fvChildren : Children Atom → List Atom
  | .nil => []
  | .cons head tail => fv head ++ fvChildren tail
end

@[simp] theorem fv_neg (expr : Expr Atom) : expr.neg.fv = expr.fv := by
  cases expr with
  | literal literal => cases literal; simp [neg, fv]
  | node negative children => simp [neg, fv]

mutual
@[simp] theorem fv_map_expr (rename : Atom → Other) : ∀ expr : Expr Atom,
    (expr.map rename).fv = expr.fv.map rename
  | .literal literal => by simp [map, fv]
  | .node negative children => by
      simp only [map, fv, fv_map_children rename children]

@[simp] theorem fv_map_children (rename : Atom → Other) : ∀ children : Children Atom,
    fvChildren (mapChildren rename children) = (fvChildren children).map rename
  | .nil => by simp [mapChildren, fvChildren]
  | .cons head tail => by
      simp only [mapChildren, fvChildren, fv_map_expr rename head,
        fv_map_children rename tail, List.map_append]
end

/- Boolean evaluation.  An array's children are evaluated in the opposite
mode; its sign complements the resulting n-ary connective. -/
mutual
def eval (assignment : Assignment Atom) : Mode → Expr Atom → Bool
  | _, .literal literal => literal.eval assignment
  | mode, .node negative children =>
      let value := mode.aggregate (evalChildren assignment mode.flip children)
      if negative then !value else value

def evalChildren (assignment : Assignment Atom) (mode : Mode) : Children Atom → List Bool
  | .nil => []
  | .cons head tail => eval assignment mode head :: evalChildren assignment mode tail
end

@[simp] theorem eval_literal (assignment : Assignment Atom) (mode : Mode)
    (literal : Literal Atom) :
    eval assignment mode (.literal literal) = literal.eval assignment := by
  simp [eval]

@[simp] theorem evalChildren_ofList (assignment : Assignment Atom) (mode : Mode) :
    ∀ children : List (Expr Atom),
      evalChildren assignment mode (Children.ofList children) =
        children.map (eval assignment mode)
  | [] => by simp [Children.ofList, evalChildren]
  | head :: tail => by
      simp only [Children.ofList, evalChildren, List.map_cons,
        evalChildren_ofList assignment mode tail]

@[simp] theorem evalChildren_eq_map_toList (assignment : Assignment Atom)
    (mode : Mode) : ∀ children : Children Atom,
      evalChildren assignment mode children =
        children.toList.map (eval assignment mode)
  | .nil => by simp [evalChildren, Children.toList]
  | .cons head tail => by
      simp only [evalChildren, Children.toList, List.map_cons,
        evalChildren_eq_map_toList assignment mode tail]

@[simp] theorem eval_array_positive (assignment : Assignment Atom) (mode : Mode)
    (children : List (Expr Atom)) :
    eval assignment mode (array false children) =
      mode.aggregate (children.map (eval assignment mode.flip)) := by
  simp [array, eval]

@[simp] theorem eval_array_negative (assignment : Assignment Atom) (mode : Mode)
    (children : List (Expr Atom)) :
    eval assignment mode (array true children) =
      !mode.aggregate (children.map (eval assignment mode.flip)) := by
  simp [array, eval]

@[simp] theorem eval_neg (assignment : Assignment Atom) (mode : Mode)
    (expr : Expr Atom) :
    expr.neg.eval assignment mode = !expr.eval assignment mode := by
  cases expr with
  | literal literal => simp [neg]
  | node negative children => cases negative <;> simp [neg, eval]

/-- Interpret an expression relative to a partial assignment.  Total Boolean
evaluation is the worker used for each compatible completion. -/
def EvalAt (known : PartialAssignment Atom) (mode : Mode) (expr : Expr Atom) : Prop :=
  Under known fun assignment ↦ expr.eval assignment mode = true

theorem EvalAt.mono {less more : PartialAssignment Atom} {mode : Mode}
    {expr : Expr Atom} (holds : expr.EvalAt less mode)
    (refines : Refines less more) : expr.EvalAt more mode :=
  Under.mono holds refines

mutual
@[simp] theorem eval_map_expr (rename : Atom → Other)
    (assignment : Assignment Other) (mode : Mode) : ∀ expr : Expr Atom,
    (expr.map rename).eval assignment mode =
      expr.eval (assignment ∘ rename) mode
  | .literal literal => by cases literal; simp [map, Literal.eval]
  | .node negative children => by
      simp only [map, eval, eval_map_children rename assignment mode.flip children]

@[simp] theorem eval_map_children (rename : Atom → Other)
    (assignment : Assignment Other) (mode : Mode) : ∀ children : Children Atom,
    evalChildren assignment mode (mapChildren rename children) =
      evalChildren (assignment ∘ rename) mode children
  | .nil => by
      simp only [mapChildren, evalChildren_eq_map_toList, Children.toList,
        List.map_nil]
  | .cons head tail => by
      simp only [mapChildren, evalChildren, eval_map_expr rename assignment mode head,
        eval_map_children rename assignment mode tail]
end

/-- Add one alternating level without changing the child itself. -/
def shift (expr : Expr Atom) : Expr Atom := array false [expr]

@[simp] theorem eval_shift (assignment : Assignment Atom) (mode : Mode)
    (expr : Expr Atom) :
    expr.shift.eval assignment mode = expr.eval assignment mode.flip := by
  cases mode <;> simp [shift, Mode.aggregate]

@[simp] theorem eval_shift_shift (assignment : Assignment Atom) (mode : Mode)
    (expr : Expr Atom) :
    expr.shift.shift.eval assignment mode = expr.eval assignment mode := by
  simp

/-- Remove duplicates only from the selected array.  Descendants are left
untouched so this is the exact abstract effect of one in-place operation. -/
def dedupeTop [DecidableEq (Expr Atom)] : Expr Atom → Expr Atom
  | .literal literal => .literal literal
  | .node negative children => array negative (Children.toList children).dedup

@[simp] theorem eval_dedupeTop [DecidableEq (Expr Atom)]
    (assignment : Assignment Atom) (mode : Mode) (expr : Expr Atom) :
    expr.dedupeTop.eval assignment mode = expr.eval assignment mode := by
  cases expr with
  | literal literal => simp [dedupeTop]
  | node negative children =>
      cases negative with
      | false =>
          simp only [dedupeTop, eval_array_positive, eval]
          rw [evalChildren_eq_map_toList]
          apply Mode.aggregate_eq_of_mem_iff
          intro value
          simp
      | true =>
          simp only [dedupeTop, eval_array_negative, eval]
          rw [evalChildren_eq_map_toList]
          congr 1
          apply Mode.aggregate_eq_of_mem_iff
          intro value
          simp

end Expr

/-- One implication between alternating roots. -/
structure Sequent (Atom : Type u) where
  left : Expr Atom
  right : Expr Atom

namespace Sequent

/-- The left root is conjunctive and the right root is disjunctive. -/
def Holds (assignment : Assignment Atom) (sequent : Sequent Atom) : Prop :=
  sequent.left.eval assignment .all = true →
    sequent.right.eval assignment .any = true

/-- Validity relative to the information in a partial assignment. -/
def EntailsAt (known : PartialAssignment Atom) (sequent : Sequent Atom) : Prop :=
  Under known fun assignment ↦ sequent.Holds assignment

/-- A valuation-independent alternating sequent. -/
def IsSyllogism (sequent : Sequent Atom) : Prop :=
  Syllogism fun assignment ↦ sequent.Holds assignment

/-- A syllogism is exactly validity at the null (everywhere unknown) partial
assignment. -/
@[simp] theorem isSyllogism_iff_entailsAt_bottom (sequent : Sequent Atom) :
    sequent.IsSyllogism ↔ sequent.EntailsAt bottom :=
  Iff.rfl

@[simp] theorem isSyllogism_iff (sequent : Sequent Atom) :
    sequent.IsSyllogism ↔ ∀ assignment, sequent.Holds assignment :=
  syllogism_iff _

theorem EntailsAt.mono {less more : PartialAssignment Atom}
    {sequent : Sequent Atom} (entails : sequent.EntailsAt less)
    (refines : Refines less more) : sequent.EntailsAt more :=
  Under.mono entails refines

end Sequent

/-- The abstract prover state is a list of sequents. -/
abbrev Arena (Atom : Type u) := List (Sequent Atom)

namespace Arena

/-- Every resident sequent is valid under the same partial assignment. -/
def EntailsAt (known : PartialAssignment Atom) (arena : Arena Atom) : Prop :=
  ∀ sequent ∈ arena, sequent.EntailsAt known

/-- Every resident sequent is a syllogism. -/
def Syllogistic (arena : Arena Atom) : Prop :=
  ∀ sequent ∈ arena, sequent.IsSyllogism

end Arena

end Nucleus.Classical.Alternating
