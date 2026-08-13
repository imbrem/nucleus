import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Embedding.Basic

/-!
# Binary trees and dotted S-expressions

`Tree2` has binary branches and atom leaves. `SExpr2` adds the distinguished
leaf `nil`, retaining dotted/improper pairs. Thus `SExpr2 α` is definitionally
the same shape as `Tree2 (Option α)`.
-/

namespace Nucleus

universe u v w

/-- Full binary trees with labelled leaves. -/
inductive Tree2 (Atom : Type u) where
  | atom (value : Atom)
  | cons (left right : Tree2 Atom)
  deriving DecidableEq, Repr

/-- Lisp S-expressions including dotted pairs. -/
inductive SExpr2 (Atom : Type u) where
  | nil
  | atom (value : Atom)
  | cons (car cdr : SExpr2 Atom)
  deriving DecidableEq, Repr

instance : EmptyCollection (SExpr2 α) := ⟨.nil⟩
instance : Inhabited (SExpr2 α) := ⟨.nil⟩
instance [Inhabited α] : Inhabited (Tree2 α) := ⟨.atom default⟩

namespace Tree2

def map (f : α → β) : Tree2 α → Tree2 β
  | .atom value => .atom (f value)
  | .cons left right => .cons (map f left) (map f right)

def bind (tree : Tree2 α) (f : α → Tree2 β) : Tree2 β :=
  match tree with
  | .atom value => f value
  | .cons left right => .cons (bind left f) (bind right f)

@[simp] theorem bind_atom (value : α) (f : α → Tree2 β) :
    bind (.atom value) f = f value := rfl

@[simp] theorem bind_cons (left right : Tree2 α) (f : α → Tree2 β) :
    bind (.cons left right) f = .cons (bind left f) (bind right f) := rfl

@[simp] theorem bind_pure : ∀ tree : Tree2 α, bind tree .atom = tree
  | .atom _ => rfl
  | .cons left right => by simp [bind_pure left, bind_pure right]

@[simp] theorem pure_bind (value : α) (f : α → Tree2 β) :
    bind (.atom value) f = f value := rfl

theorem bind_assoc (tree : Tree2 α) (f : α → Tree2 β)
    (g : β → Tree2 γ) : bind (bind tree f) g = bind tree fun x => bind (f x) g := by
  induction tree with
  | atom value => rfl
  | cons left right ihLeft ihRight => simp [bind, ihLeft, ihRight]

instance : Monad Tree2 where
  pure := .atom
  bind := bind

instance : LawfulMonad Tree2 := LawfulMonad.mk' _
  (fun tree => by change bind tree (fun x => .atom (id x)) = tree; simp)
  (fun value f => pure_bind value f)
  (fun tree f g => bind_assoc tree f g)

/-- Attach children from left to right using binary cons cells. -/
def ofHeadChildren (head : α) (children : List (Tree2 α)) : Tree2 α :=
  children.foldl .cons (.atom head)

/-- Recover the leftmost atom and the ordered list of right branches. -/
def headChildren : Tree2 α → α × List (Tree2 α)
  | .atom value => (value, [])
  | .cons left right =>
      let (head, children) := headChildren left
      (head, children ++ [right])

theorem map_ofHeadChildren (f : α → β) (head : α) (children : List (Tree2 α)) :
    map f (ofHeadChildren head children) =
      ofHeadChildren (f head) (children.map (map f)) := by
  have aux (start : Tree2 α) (xs : List (Tree2 α)) :
      map f (xs.foldl .cons start) = (xs.map (map f)).foldl .cons (map f start) := by
    induction xs generalizing start with
    | nil => rfl
    | cons child xs ih =>
        simp only [List.foldl, List.map_cons]
        rw [ih]
        rfl
  exact aux (.atom head) children

private theorem foldl_cons_append (start : Tree2 α)
    (xs ys : List (Tree2 α)) :
    (xs ++ ys).foldl .cons start = ys.foldl .cons (xs.foldl .cons start) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp [List.foldl, ih]

@[simp] theorem ofHeadChildren_headChildren : ∀ tree : Tree2 α,
    ofHeadChildren tree.headChildren.1 tree.headChildren.2 = tree := by
  intro tree
  induction tree with
  | atom value => rfl
  | cons left right ih =>
      simp only [headChildren, ofHeadChildren, List.foldl_append]
      change Tree2.cons (ofHeadChildren left.headChildren.1 left.headChildren.2) right = _
      rw [ih]

@[simp] theorem headChildren_ofHeadChildren (head : α) (children : List (Tree2 α)) :
    headChildren (ofHeadChildren head children) = (head, children) := by
  induction children using List.reverseRecOn with
  | nil => rfl
  | append_singleton children child ih =>
      rw [show ofHeadChildren head (children ++ [child]) =
        .cons (ofHeadChildren head children) child by
          simp [ofHeadChildren, List.foldl_append]]
      simp [headChildren, ih]

/-- Binary trees are nonempty rose trees: a root label and ordered children. -/
def equivHeadChildren (α : Type u) : Tree2 α ≃ α × List (Tree2 α) where
  toFun := headChildren
  invFun pair := ofHeadChildren pair.1 pair.2
  left_inv := ofHeadChildren_headChildren
  right_inv pair := by cases pair; simp

end Tree2

namespace SExpr2

def isNil : SExpr2 α → Bool
  | .nil => true
  | _ => false

/-- Lisp spelling retained as an alias. -/
abbrev isnil := @isNil

/-- Lisp-style projection, totalized by returning `nil` off cons cells. -/
def car : SExpr2 α → SExpr2 α
  | .cons car _ => car
  | _ => .nil

/-- Lisp-style projection, totalized by returning `nil` off cons cells. -/
def cdr : SExpr2 α → SExpr2 α
  | .cons _ cdr => cdr
  | _ => .nil

@[simp] theorem car_nil : car (nil : SExpr2 α) = nil := rfl
@[simp] theorem cdr_nil : cdr (nil : SExpr2 α) = nil := rfl
@[simp] theorem isNil_eq_true (expr : SExpr2 α) : isNil expr = true ↔ expr = nil := by
  cases expr <;> simp [isNil]

def map (f : α → β) : SExpr2 α → SExpr2 β
  | .nil => .nil
  | .atom value => .atom (f value)
  | .cons car cdr => .cons (map f car) (map f cdr)

def bind (expr : SExpr2 α) (f : α → SExpr2 β) : SExpr2 β :=
  match expr with
  | .nil => .nil
  | .atom value => f value
  | .cons car cdr => .cons (bind car f) (bind cdr f)

@[simp] theorem bind_pure : ∀ expr : SExpr2 α, bind expr .atom = expr
  | .nil => rfl
  | .atom _ => rfl
  | .cons car cdr => congrArg₂ SExpr2.cons (bind_pure car) (bind_pure cdr)

theorem bind_assoc (expr : SExpr2 α) (f : α → SExpr2 β)
    (g : β → SExpr2 γ) : bind (bind expr f) g = bind expr fun x => bind (f x) g := by
  induction expr with
  | nil | atom => rfl
  | cons car cdr ihCar ihCdr => simp [bind, ihCar, ihCdr]

instance : Monad SExpr2 where
  pure := .atom
  bind := bind

instance : LawfulMonad SExpr2 := LawfulMonad.mk' _
  (fun expr => by change bind expr (fun x => .atom (id x)) = expr; simp)
  (fun _ _ => rfl)
  (fun expr f g => bind_assoc expr f g)

/-- The usual proper-list embedding, ending in `nil`. -/
def ofList : List (SExpr2 α) → SExpr2 α
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

theorem ofList_injective :
    Function.Injective (ofList : List (SExpr2 α) → SExpr2 α) := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> cases h; rfl
  | cons head tail ih =>
      intro ys h
      cases ys with
      | nil => cases h
      | cons head' tail' =>
          injection h with hh ht
          exact congrArg₂ List.cons hh (ih ht)

/-- Lists of expressions embed as nil-terminated cons spines. -/
def ofListEmbedding (α : Type u) : List (SExpr2 α) ↪ SExpr2 α :=
  ⟨ofList, ofList_injective⟩

/-- Embed a list of atoms as a proper S-expression list. -/
def ofAtoms (values : List α) : SExpr2 α := ofList (values.map .atom)

theorem ofAtoms_injective : Function.Injective (ofAtoms : List α → SExpr2 α) := by
  intro xs ys h
  have hm := ofList_injective h
  exact ((List.map_injective_iff).2 fun _ _ h => SExpr2.atom.inj h) hm

def ofAtomsEmbedding (α : Type u) : List α ↪ SExpr2 α :=
  ⟨ofAtoms, ofAtoms_injective⟩

@[simp] theorem bind_ofList (xs : List (SExpr2 α)) (f : α → SExpr2 β) :
    bind (ofList xs) f = ofList (xs.map fun x => bind x f) := by
  induction xs with
  | nil => rfl
  | cons head tail ih => simp [ofList, bind, ih]

/-- The two possible kinds of intrinsically proper expression. -/
inductive ProperKind where
  | atom
  | list
  deriving DecidableEq

/-- A single inductive family distinguishes proper atoms from proper lists. -/
inductive Proper : ProperKind → SExpr2 α → Prop where
  | atom (value : α) : Proper .atom (.atom value)
  | nil : Proper .list .nil
  | cons {car cdr : SExpr2 α} {carKind : ProperKind} :
      Proper carKind car → Proper .list cdr →
      Proper .list (.cons car cdr)

instance instDecidableProper : ∀ (kind : ProperKind) (value : SExpr2 α),
    Decidable (Proper kind value)
  | .atom, .atom value => isTrue (.atom value)
  | .atom, .nil => isFalse (by intro h; cases h)
  | .atom, .cons _ _ => isFalse (by intro h; cases h)
  | .list, .atom _ => isFalse (by intro h; cases h)
  | .list, .nil => isTrue .nil
  | .list, .cons car cdr =>
      match instDecidableProper .list cdr with
      | isFalse htail => isFalse (by intro h; cases h with | cons _ tail => exact htail tail)
      | isTrue htail =>
          match instDecidableProper .atom car with
          | isTrue hcar => isTrue (.cons hcar htail)
          | isFalse hatom =>
              match instDecidableProper .list car with
              | isTrue hcar => isTrue (.cons hcar htail)
              | isFalse hlist => isFalse (by
                  intro h
                  cases h with
                  | @cons _ _ kind hcar _ =>
                      cases kind with
                      | atom => exact hatom hcar
                      | list => exact hlist hcar)

abbrev ProperAtom (value : SExpr2 α) : Prop := Proper .atom value
abbrev ProperList (value : SExpr2 α) : Prop := Proper .list value

/-- Being proper means being either a proper atom or a proper list. -/
abbrev IsProper (value : SExpr2 α) : Prop := ProperAtom value ∨ ProperList value

instance (value : SExpr2 α) : Decidable (IsProper value) := inferInstance

theorem properList_ofList {xs : List (SExpr2 α)} (h : ∀ x ∈ xs, IsProper x) :
    ProperList (ofList xs) := by
  induction xs with
  | nil => exact Proper.nil
  | cons head tail ih =>
      rcases h head (by simp) with hhead | hhead
      · exact Proper.cons hhead (ih fun x hx => h x (by simp [hx]))
      · exact Proper.cons hhead (ih fun x hx => h x (by simp [hx]))

/-- Replace `nil` by the `none` leaf. -/
def toTreeOption : SExpr2 α → Tree2 (Option α)
  | .nil => .atom none
  | .atom value => .atom (some value)
  | .cons car cdr => .cons (toTreeOption car) (toTreeOption cdr)

def ofTreeOption : Tree2 (Option α) → SExpr2 α
  | .atom none => .nil
  | .atom (some value) => .atom value
  | .cons left right => .cons (ofTreeOption left) (ofTreeOption right)

@[simp] theorem ofTreeOption_toTreeOption : ∀ expr : SExpr2 α,
    ofTreeOption expr.toTreeOption = expr
  | .nil | .atom _ => rfl
  | .cons car cdr => by
      change SExpr2.cons (ofTreeOption (toTreeOption car))
        (ofTreeOption (toTreeOption cdr)) = SExpr2.cons car cdr
      rw [ofTreeOption_toTreeOption car, ofTreeOption_toTreeOption cdr]

@[simp] theorem toTreeOption_ofTreeOption : ∀ tree : Tree2 (Option α),
    toTreeOption (ofTreeOption tree) = tree
  | .atom none | .atom (some _) => rfl
  | .cons left right => by
      change Tree2.cons (toTreeOption (ofTreeOption left))
        (toTreeOption (ofTreeOption right)) = Tree2.cons left right
      rw [toTreeOption_ofTreeOption left, toTreeOption_ofTreeOption right]

/-- Dotted S-expressions are exactly option-labelled binary trees. -/
def equivTreeOption (α : Type u) : SExpr2 α ≃ Tree2 (Option α) where
  toFun := toTreeOption
  invFun := ofTreeOption
  left_inv := ofTreeOption_toTreeOption
  right_inv := toTreeOption_ofTreeOption

/-- The correct tagged-spine decomposition inherited through
`Tree2 (Option α)`. -/
def equivHeadChildren (α : Type u) :
    SExpr2 α ≃ Option α × List (Tree2 (Option α)) :=
  (equivTreeOption α).trans (Tree2.equivHeadChildren (Option α))

private def mapTreeList : List (Tree2 (Option α)) → List (SExpr2 α) :=
  List.map ofTreeOption

private def mapExprList : List (SExpr2 α) → List (Tree2 (Option α)) :=
  List.map toTreeOption

private theorem mapExpr_mapTree (xs : List (Tree2 (Option α))) :
    mapExprList (mapTreeList xs) = xs := by
  simp [mapExprList, mapTreeList, Function.comp_def]

private theorem mapTree_mapExpr (xs : List (SExpr2 α)) :
    mapTreeList (mapExprList xs) = xs := by
  simp [mapExprList, mapTreeList, Function.comp_def]

/-- Dotted S-expressions decompose into an optional head atom and a list of
dotted S-expression children. -/
def equivOptionalHeadChildren (α : Type u) :
    SExpr2 α ≃ Option α × List (SExpr2 α) where
  toFun expr :=
    let pair := equivHeadChildren α expr
    (pair.1, mapTreeList pair.2)
  invFun pair := (equivHeadChildren α).symm (pair.1, mapExprList pair.2)
  left_inv expr := by
    change (equivHeadChildren α).symm
      (((equivHeadChildren α) expr).1,
        mapExprList (mapTreeList ((equivHeadChildren α expr).2))) = expr
    rw [mapExpr_mapTree]
    exact (equivHeadChildren α).left_inv expr
  right_inv pair := by
    rcases pair with ⟨head, children⟩
    simp [mapTree_mapExpr]

/-- Embed a binary tree without using `nil`. -/
def ofTree : Tree2 α → SExpr2 α
  | .atom value => .atom value
  | .cons left right => .cons (ofTree left) (ofTree right)

@[simp] theorem ofTree_ne_nil (tree : Tree2 α) : ofTree tree ≠ .nil := by
  cases tree <;> simp [ofTree]

theorem proper_ofTree_iff : ∀ tree : Tree2 α,
    IsProper (ofTree tree) ↔ ∃ value, tree = .atom value := by
  have notList : ∀ tree : Tree2 α, ¬ ProperList (ofTree tree) := by
    intro tree
    induction tree with
    | atom value => intro h; cases h
    | cons left right ihLeft ihRight =>
        intro h
        cases h with
        | cons _ htail => exact ihRight htail
  intro tree
  constructor
  · intro h
    cases tree with
    | atom value => exact ⟨value, rfl⟩
    | cons left right =>
        rcases h with h | h
        · cases h
        · exact False.elim ((notList (.cons left right)) h)
  · rintro ⟨value, rfl⟩
    exact Or.inl (Proper.atom value)

/-- Both encodings commute with atom mapping. -/
theorem toTreeOption_map (f : α → β) (expr : SExpr2 α) :
    toTreeOption (map f expr) = Tree2.map (Option.map f) (toTreeOption expr) := by
  induction expr <;> simp_all [map, toTreeOption, Tree2.map]

/-- The nil-free tree embedding commutes with monadic substitution. -/
theorem ofTree_bind (tree : Tree2 α) (f : α → Tree2 β) :
    ofTree (Tree2.bind tree f) = SExpr2.bind (ofTree tree) (ofTree ∘ f) := by
  induction tree with
  | atom => rfl
  | cons left right ihLeft ihRight => simp [Tree2.bind, SExpr2.bind, ofTree, ihLeft, ihRight]

end SExpr2

end Nucleus
