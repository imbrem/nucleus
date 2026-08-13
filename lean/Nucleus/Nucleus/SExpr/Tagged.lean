import Nucleus.SExpr.Proper

/-!
# Tagged S-expressions

Both recursive expression types in this file are ordinary (non-nested)
inductives. `TNode` describes one layer of either fixed point; it is not used
as the recursive argument of their constructors.
-/

namespace Nucleus

universe u v w

/-- One tagged node layer. -/
structure TNode (Tag : Type u) (Child : Type v) where
  tag : Tag
  children : List Child
  deriving DecidableEq, Repr

namespace TNode

def map (f : α → β) (node : TNode τ α) : TNode τ β :=
  ⟨node.tag, node.children.map f⟩

def mapTag (f : τ → υ) (node : TNode τ α) : TNode υ α :=
  ⟨f node.tag, node.children⟩

end TNode

/-- Tagged expressions with an additional, independently-labelled atom case. -/
inductive TExpr (Tag : Type u) (Atom : Type v) where
  | atom (value : Atom)
  | tag (value : Tag) (n : Nat) (children : Fin n → TExpr Tag Atom)

/-- Atom-free tagged expressions reuse the regular inductive `TExpr` at an
empty atom type. Zero-child tags are their leaves. -/
abbrev TExpr1 (Tag : Type u) := TExpr Tag Empty

namespace TExpr

def map (f : α → β) : TExpr τ α → TExpr τ β
  | .atom value => .atom (f value)
  | .tag value n children => .tag value n fun i => map f (children i)

def mapTag (f : τ → υ) : TExpr τ α → TExpr υ α
  | .atom value => .atom value
  | .tag value n children => .tag (f value) n fun i => mapTag f (children i)

@[simp] theorem mapTag_id : ∀ expr : TExpr τ α, mapTag id expr = expr := by
  intro expr
  induction expr with
  | atom => rfl
  | tag value n children ih =>
      apply congrArg (TExpr.tag value n)
      funext i
      exact ih i

theorem mapTag_comp (f : τ → υ) (g : υ → φ) (expr : TExpr τ α) :
    mapTag g (mapTag f expr) = mapTag (g ∘ f) expr := by
  induction expr with
  | atom => rfl
  | tag value n children ih =>
      apply congrArg (TExpr.tag (g (f value)) n)
      funext i
      exact ih i

def bind (expr : TExpr τ α) (f : α → TExpr τ β) : TExpr τ β :=
  match expr with
  | .atom value => f value
  | .tag value n children => .tag value n fun i => bind (children i) f

@[simp] theorem bind_pure : ∀ expr : TExpr τ α, bind expr .atom = expr := by
  intro expr
  induction expr with
  | atom => rfl
  | tag value n children ih =>
      apply congrArg (TExpr.tag value n)
      funext i
      exact ih i

theorem bind_assoc (expr : TExpr τ α) (f : α → TExpr τ β)
    (g : β → TExpr τ γ) : bind (bind expr f) g = bind expr fun x => bind (f x) g := by
  induction expr with
  | atom => rfl
  | tag value n children ih =>
      apply congrArg (TExpr.tag value n)
      funext i
      exact ih i

instance : Monad (TExpr τ) where
  pure := .atom
  bind := bind

instance : LawfulMonad (TExpr τ) := LawfulMonad.mk' _
  (fun expr => by change bind expr (fun x => .atom (id x)) = expr; simp)
  (fun _ _ => rfl)
  (fun expr f g => bind_assoc expr f g)

/-- A default tag gives the zero-child tagged expression. -/
instance [Inhabited τ] : Inhabited (TExpr τ α) :=
  ⟨.tag default 0 Fin.elim0⟩

instance [Nonempty α] : Nonempty (TExpr τ α) :=
  Nonempty.map TExpr.atom (inferInstance : Nonempty α)

/-- Fold atoms and tagged operations. This is the operation-shaped analogue
of substitution in the tag parameter. -/
def fold (atom : α → β) (operation : τ → List β → β) : TExpr τ α → β
  | .atom value => atom value
  | .tag value _ children => operation value (List.ofFn fun i => fold atom operation (children i))

def node : TExpr τ α → α ⊕ TNode τ (TExpr τ α)
  | .atom value => .inl value
  | .tag value _ children => .inr ⟨value, List.ofFn children⟩

def ofNode : α ⊕ TNode τ (TExpr τ α) → TExpr τ α
  | .inl value => .atom value
  | .inr node => .tag node.tag node.children.length node.children.get

/-- For a fixed tag, lists of children embed as tagged nodes. -/
def ofList (value : τ) (children : List (TExpr τ α)) : TExpr τ α :=
  .tag value children.length children.get

theorem ofList_injective (value : τ) :
    Function.Injective (ofList value : List (TExpr τ α) → TExpr τ α) := by
  intro xs ys h
  have hn := congrArg node h
  simpa [ofList, node] using congrArg TNode.children (Sum.inr.inj hn)

def ofListEmbedding (value : τ) : List (TExpr τ α) ↪ TExpr τ α :=
  ⟨ofList value, ofList_injective value⟩

private theorem ofNode_node : ∀ expr : TExpr τ α, ofNode expr.node = expr := by
  intro expr
  cases expr with
  | atom => rfl
  | tag value n children =>
      change TExpr.tag value (List.ofFn children).length (List.ofFn children).get =
        TExpr.tag value n children
      have hlen : (List.ofFn children).length = n := by simp
      have hchildren : (List.ofFn children).get ≍ children :=
        (Fin.heq_fun_iff hlen).2 (by intro i; simp)
      let a : Σ n, Fin n → TExpr τ α := ⟨_, (List.ofFn children).get⟩
      let b : Σ n, Fin n → TExpr τ α := ⟨n, children⟩
      have hab : a = b := Sigma.ext hlen hchildren
      exact congrArg (fun p : Σ n, Fin n → TExpr τ α => TExpr.tag value p.1 p.2)
        hab

@[simp] private theorem node_ofNode (shape : α ⊕ TNode τ (TExpr τ α)) :
    node (ofNode shape) = shape := by
  cases shape with
  | inl => rfl
  | inr node => cases node; simp [ofNode, node]

/-- `TExpr` is the least fixed point of atoms plus the tagged-node functor. -/
def equivNode (τ : Type u) (α : Type v) :
    TExpr τ α ≃ α ⊕ TNode τ (TExpr τ α) where
  toFun := node
  invFun := ofNode
  left_inv := ofNode_node
  right_inv := node_ofNode

end TExpr

namespace TExpr1

def mapTag (f : τ → υ) : TExpr1 τ → TExpr1 υ
  | .atom value => nomatch value
  | .tag value n children => .tag (f value) n fun i => mapTag f (children i)

@[simp] theorem mapTag_id : ∀ expr : TExpr1 τ, mapTag id expr = expr := by
  intro expr
  induction expr with
  | atom value => exact nomatch value
  | tag value n children ih =>
      apply congrArg (TExpr.tag value n)
      funext i
      exact ih i

theorem mapTag_comp (f : τ → υ) (g : υ → φ) (expr : TExpr1 τ) :
    mapTag g (mapTag f expr) = mapTag (g ∘ f) expr := by
  induction expr with
  | atom value => exact nomatch value
  | tag value n children ih =>
      apply congrArg (TExpr.tag (g (f value)) n)
      funext i
      exact ih i

def node : TExpr1 τ → TNode τ (TExpr1 τ)
  | .atom value => nomatch value
  | .tag value _ children => ⟨value, List.ofFn children⟩

def ofNode (node : TNode τ (TExpr1 τ)) : TExpr1 τ :=
  .tag node.tag node.children.length node.children.get

def ofList (value : τ) (children : List (TExpr1 τ)) : TExpr1 τ :=
  .tag value children.length children.get

theorem ofList_injective (value : τ) :
    Function.Injective (ofList value : List (TExpr1 τ) → TExpr1 τ) := by
  intro xs ys h
  have hn := congrArg node h
  simpa [ofList, node] using congrArg TNode.children hn

def ofListEmbedding (value : τ) : List (TExpr1 τ) ↪ TExpr1 τ :=
  ⟨ofList value, ofList_injective value⟩

private theorem ofNode_node : ∀ expr : TExpr1 τ, ofNode expr.node = expr := by
  intro expr
  cases expr with
  | atom value => exact nomatch value
  | tag value n children =>
      change TExpr.tag value (List.ofFn children).length (List.ofFn children).get =
        TExpr.tag value n children
      have hlen : (List.ofFn children).length = n := by simp
      have hchildren : (List.ofFn children).get ≍ children :=
        (Fin.heq_fun_iff hlen).2 (by intro i; simp)
      let a : Σ n, Fin n → TExpr1 τ := ⟨_, (List.ofFn children).get⟩
      let b : Σ n, Fin n → TExpr1 τ := ⟨n, children⟩
      have hab : a = b := Sigma.ext hlen hchildren
      exact congrArg (fun p : Σ n, Fin n → TExpr1 τ => TExpr.tag value p.1 p.2)
        hab

@[simp] private theorem node_ofNode (shape : TNode τ (TExpr1 τ)) :
    node (ofNode shape) = shape := by cases shape; simp [ofNode, node]

/-- The atom-free regular inductive is the least fixed point of `TNode`. -/
def equivNode (τ : Type u) : TExpr1 τ ≃ TNode τ (TExpr1 τ) where
  toFun := node
  invFun := ofNode
  left_inv := ofNode_node
  right_inv := node_ofNode

def toTree2 : TExpr1 α → Tree2 α
  | .atom value => nomatch value
  | .tag value _ children =>
      Tree2.ofHeadChildren value (List.ofFn fun i => toTree2 (children i))

private theorem toTree2_eq_node (expr : TExpr1 α) :
    toTree2 expr = Tree2.ofHeadChildren expr.node.tag
      (expr.node.children.map toTree2) := by
  cases expr with
  | atom value => exact nomatch value
  | tag value n children => simp [toTree2, node, List.map_ofFn, Function.comp_def]

def ofTree2 : Tree2 α → TExpr1 α
  | .atom value => .tag value 0 Fin.elim0
  | .cons left right =>
      let leftNode := node (ofTree2 left)
      ofNode ⟨leftNode.tag, leftNode.children ++ [ofTree2 right]⟩

private theorem ofTree2_ofHeadChildren (head : α) (children : List (Tree2 α)) :
    ofTree2 (Tree2.ofHeadChildren head children) =
      ofNode ⟨head, children.map ofTree2⟩ := by
  induction children using List.reverseRecOn with
  | nil =>
      exact (ofNode_node (.tag head 0 Fin.elim0)).symm
  | append_singleton children child ih =>
      rw [show Tree2.ofHeadChildren head (children ++ [child]) =
        .cons (Tree2.ofHeadChildren head children) child by
          simp [Tree2.ofHeadChildren, List.foldl_append]]
      simp [ofTree2, ih, node_ofNode, List.map_append]

-- The inverse laws are proved via the shared head/children destructors.
@[simp] theorem toTree2_ofTree2 : ∀ tree : Tree2 α, toTree2 (ofTree2 tree) = tree := by
  intro tree
  induction tree using Tree2.rec with
  | atom value => simp [ofTree2, toTree2, Tree2.ofHeadChildren]
  | cons left right ihLeft ihRight =>
      rw [ofTree2, toTree2_eq_node]
      simp only [node_ofNode, List.map_append, List.map_singleton]
      rw [show Tree2.ofHeadChildren (ofTree2 left).node.tag
          ((ofTree2 left).node.children.map toTree2 ++ [toTree2 (ofTree2 right)]) =
        .cons (Tree2.ofHeadChildren (ofTree2 left).node.tag
          ((ofTree2 left).node.children.map toTree2)) (toTree2 (ofTree2 right)) by
            simp [Tree2.ofHeadChildren, List.foldl_append]]
      rw [← toTree2_eq_node, ihLeft, ihRight]

@[simp] theorem ofTree2_toTree2 : ∀ expr : TExpr1 α, ofTree2 (toTree2 expr) = expr := by
  intro expr
  induction expr with
  | atom value => exact nomatch value
  | tag value n children ih =>
      rw [toTree2, ofTree2_ofHeadChildren]
      apply (equivNode α).injective
      change node (ofNode ⟨value,
        List.map ofTree2 (List.ofFn fun i => toTree2 (children i))⟩) =
        node (.tag value n children)
      rw [node_ofNode]
      change TNode.mk value _ = TNode.mk value (List.ofFn children)
      congr 2
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      exact ih i

def equivTree2 (α : Type u) : TExpr1 α ≃ Tree2 α where
  toFun := toTree2
  invFun := ofTree2
  left_inv := ofTree2_toTree2
  right_inv := toTree2_ofTree2

theorem toTree2_mapTag (f : α → β) (expr : TExpr1 α) :
    toTree2 (mapTag f expr) = Tree2.map f (toTree2 expr) := by
  induction expr with
  | atom value => exact nomatch value
  | tag value n children ih =>
      rw [mapTag, toTree2, toTree2, Tree2.map_ofHeadChildren]
      congr 2
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      exact ih i

/-- Option tags recover dotted S-expressions through their binary-tree view. -/
def equivSExpr2 (α : Type u) : TExpr1 (Option α) ≃ SExpr2 α :=
  (equivTree2 (Option α)).trans (SExpr2.equivTreeOption α).symm

end TExpr1

namespace TExpr

def toSExpr : TExpr Unit α → SExpr α
  | .atom value => .atom value
  | .tag _ n children => .list n fun i => toSExpr (children i)

def ofSExpr : SExpr α → TExpr Unit α
  | .atom value => .atom value
  | .list n children => .tag () n fun i => ofSExpr (children i)

@[simp] theorem toSExpr_ofSExpr : ∀ expr : SExpr α, toSExpr (ofSExpr expr) = expr := by
  intro expr
  induction expr with
  | atom => rfl
  | list n children ih =>
      apply congrArg (SExpr.list n)
      funext i
      exact ih i

@[simp] theorem ofSExpr_toSExpr : ∀ expr : TExpr Unit α, ofSExpr (toSExpr expr) = expr := by
  intro expr
  induction expr with
  | atom => rfl
  | tag value n children ih =>
      cases value
      apply congrArg (TExpr.tag () n)
      funext i
      exact ih i

/-- Unit-tagged expressions are precisely intrinsically proper S-expressions. -/
def equivSExpr (α : Type u) : TExpr Unit α ≃ SExpr α where
  toFun := toSExpr
  invFun := ofSExpr
  left_inv := ofSExpr_toSExpr
  right_inv := toSExpr_ofSExpr

@[simp] theorem toSExpr_bind (expr : TExpr Unit α) (f : α → TExpr Unit β) :
    toSExpr (bind expr f) = SExpr.bind (toSExpr expr) (toSExpr ∘ f) := by
  induction expr with
  | atom => rfl
  | tag value n children ih =>
      cases value
      apply congrArg (SExpr.list n)
      funext i
      exact ih i

end TExpr

end Nucleus
