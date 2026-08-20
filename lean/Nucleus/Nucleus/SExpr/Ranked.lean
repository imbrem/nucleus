import Nucleus.SExpr.Tagged

/-!
# Ranked tagged nodes

`TNode` is the common list-based representation of one tagged node layer.
This file equips tag types with an arity and packages the nodes whose child
lists have exactly that arity.  It deliberately contains no assumptions about
finiteness, acyclicity, or the type used for child references.
-/

namespace Nucleus

universe u v w

/-- A ranked tag determines the number of recursive children of its nodes. -/
class HasArity (Tag : Type u) where
  numChildren : Tag → Nat

namespace TNode

variable {Tag : Type u} {Child : Type v}

/-- A tagged node is well-formed when its child list has the tag's arity. -/
def WellFormed [HasArity Tag] (node : TNode Tag Child) : Prop :=
  node.children.length = HasArity.numChildren node.tag

instance [HasArity Tag] (node : TNode Tag Child) : Decidable node.WellFormed :=
  by unfold WellFormed; infer_instance

@[simp] theorem map_tag (f : α → β) (node : TNode τ α) :
    (node.map f).tag = node.tag := rfl

@[simp] theorem map_children (f : α → β) (node : TNode τ α) :
    (node.map f).children = node.children.map f := rfl

@[simp] theorem map_id (node : TNode τ α) : node.map id = node := by
  cases node
  simp [map]

theorem map_comp (f : α → β) (g : β → γ) (node : TNode τ α) :
    (node.map f).map g = node.map (g ∘ f) := by
  cases node
  simp [map, List.map_map, Function.comp_def]

@[simp] theorem wellFormed_map [HasArity τ] (f : α → β) (node : TNode τ α) :
    (node.map f).WellFormed ↔ node.WellFormed := by
  simp [WellFormed]

end TNode

/-- A tagged node carrying the proof that its child list has the tag's arity. -/
abbrev RankedNode (Tag : Type u) (Child : Type v) [HasArity Tag] :=
  { node : TNode Tag Child // node.WellFormed }

namespace RankedNode

/-- Map child references without changing a ranked node's tag or arity. -/
def map [HasArity τ] (f : α → β) (node : RankedNode τ α) : RankedNode τ β :=
  ⟨node.1.map f, (TNode.wellFormed_map f node.1).2 node.2⟩

@[simp] theorem val_map [HasArity τ] (f : α → β) (node : RankedNode τ α) :
    (node.map f).1 = node.1.map f := rfl

@[simp] theorem map_id [HasArity τ] (node : RankedNode τ α) : node.map id = node := by
  apply Subtype.ext
  simp

theorem map_comp [HasArity τ] (f : α → β) (g : β → γ)
    (node : RankedNode τ α) : (node.map f).map g = node.map (g ∘ f) := by
  apply Subtype.ext
  exact TNode.map_comp f g node.1

end RankedNode

end Nucleus
