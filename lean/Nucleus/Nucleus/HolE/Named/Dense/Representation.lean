import Nucleus.HolE.Named.Dense.Indexed

/-!
# Finite representations of named expressions

These first representation results deliberately use the generic `HolE` entry
instance.  They establish the list/offset/finite-forest bookkeeping without
committing the later node encoder to a numbering strategy.
-/

namespace Nucleus.HolE.Named.Unsorted.Dense

universe u
set_option relaxedAutoImplicit true

def emptyForest : Forest Nat α := ⟨fun _ => none⟩

/-- A tree is a valid one-entry dense arena through the generic tree instance. -/
def singleton (tree : HolE Sig Name) : List (Option (HolE Sig Name)) := [some tree]

@[simp] theorem elaborateList_singleton (tree : HolE Sig Name) (offset : Nat) :
    elaborateList emptyForest (singleton tree) offset = [some tree] := rfl

/-- A list of trees is already a dense arena through the same generic instance. -/
def ofTrees (trees : List (HolE Sig Name)) : List (Option (HolE Sig Name)) :=
  trees.map some

/-- The roots corresponding to a list of trees in an arena at `offset`. -/
def roots (offset : Nat) (trees : List (HolE Sig Name)) : List Nat :=
  (List.range trees.length).map (offset + ·)

theorem roots_length (offset : Nat) (trees : List (HolE Sig Name)) :
    (roots offset trees).length = trees.length := by simp [roots]

/-- The finite forest directly induced by a list. -/
def finiteForestOfTrees (trees : List (HolE Sig Name)) (offset : Nat) :
    FiniteForest Nat (HolE Sig Name) := by
  refine ⟨⟨fun index => if offset ≤ index then trees[index - offset]? else none⟩,
    ⟨List.range (offset + trees.length), ?_⟩⟩
  intro index value lookup
  dsimp only at lookup
  split at lookup
  · rename_i above
    obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp lookup
    apply List.mem_range.mpr
    have shifted := Nat.add_lt_add_left bounded offset
    simpa [Nat.add_sub_of_le above] using shifted
  · contradiction

/-- Every unsorted named tree has a finite-support forest representation and a
root index which retrieves it. -/
theorem exists_tree_finite_representation (tree : HolE Sig Name) :
    ∃ forest : FiniteForest Nat (HolE Sig Name), ∃ root, forest root = some tree := by
  refine ⟨finiteForestOfTrees [tree] 0, 0, ?_⟩
  rfl

/-- In particular, every sorted named expression has such a representation
after erasing its sort index. -/
theorem Named.exists_finite_representation
    (expression : Named.Expr Sig Name sort) :
    ∃ forest : FiniteForest Nat (HolE Sig Name), ∃ root,
      forest root = some (Unsorted.erase expression) :=
  exists_tree_finite_representation (Unsorted.erase expression)

/-- A whole list is represented by one larger arena together with one root per
input tree. -/
theorem exists_list_representation (trees : List (HolE Sig Name)) :
    ∃ _forest : FiniteForest Nat (HolE Sig Name), ∃ indices : List Nat,
      indices.length = trees.length := by
  exact ⟨finiteForestOfTrees trees 0, roots 0 trees, roots_length 0 trees⟩

/-- Common output of an arena encoder, independent of its private state. -/
structure EncodingResult (Sig : Signature.{u}) (Name : Type) where
  offset : Nat
  nodes : List (Node Sig Name Nat)
  root : Nat
  next : Nat

/-- Output of a list encoder.  Unlike `EncodingResult`, no distinguished root
is manufactured: every public root is returned, in input order. -/
structure ListEncodingResult (Sig : Signature.{u}) (Name : Type) where
  offset : Nat
  nodes : List (Node Sig Name Nat)
  roots : List Nat
  next : Nat

/-- State/storage interface shared by the single-value and list capabilities. -/
class EncoderStorage (E : Type) (Sig : Signature.{u}) (Name : Type) where
  State : Type
  initial : Nat → State
  nodes : State → List (Node Sig Name Nat)
  next : State → Nat

/-- Capability for encoding one value, possibly with failure. -/
class FallibleEncoder (E : Type) (Sig : Signature.{u}) (Name : Type)
    [EncoderStorage E Sig Name] where
  encode? : HolE Sig Name → EncoderStorage.State E Sig Name →
    Option (Nat × EncoderStorage.State E Sig Name)

/-- Encoding a list is a separate capability: implementations may batch,
share, or reject across element boundaries instead of merely iterating. -/
class FallibleListEncoder (E : Type) (Sig : Signature.{u}) (Name : Type)
    [EncoderStorage E Sig Name] where
  encodeList? : List (HolE Sig Name) →
    EncoderStorage.State E Sig Name → Option (List Nat × EncoderStorage.State E Sig Name)

namespace FallibleEncoder

def run? (E : Type) [storage : EncoderStorage E Sig Name]
    [encoder : FallibleEncoder E Sig Name]
    (tree : HolE Sig Name) (offset : Nat := 0) : Option (EncodingResult Sig Name) := do
  let (root, state) ← encoder.encode? tree (storage.initial offset)
  return ⟨offset, storage.nodes state, root, storage.next state⟩

end FallibleEncoder

namespace FallibleListEncoder

def runList? (E : Type) [storage : EncoderStorage E Sig Name]
    [listEncoder : FallibleListEncoder E Sig Name]
    (trees : List (HolE Sig Name)) (offset : Nat := 0) :
    Option (ListEncodingResult Sig Name) := do
  let (indices, state) ← listEncoder.encodeList? trees (storage.initial offset)
  return ⟨offset, storage.nodes state, indices, storage.next state⟩

end FallibleListEncoder

/-- An infallible encoder is a fallible encoder equipped with a total
implementation and a proof that both views agree. -/
class InfallibleEncoder (E : Type) (Sig : Signature.{u}) (Name : Type)
    [EncoderStorage E Sig Name]
    extends FallibleEncoder E Sig Name where
  encode : HolE Sig Name → EncoderStorage.State E Sig Name →
    Nat × EncoderStorage.State E Sig Name
  encode?_eq : ∀ tree state, encode? tree state = some (encode tree state)

class InfallibleListEncoder (E : Type) (Sig : Signature.{u}) (Name : Type)
    [EncoderStorage E Sig Name] [InfallibleEncoder E Sig Name]
    [FallibleListEncoder E Sig Name] where
  encodeList : List (HolE Sig Name) →
    EncoderStorage.State E Sig Name → List Nat × EncoderStorage.State E Sig Name
  encodeList?_eq : ∀ trees state,
    FallibleListEncoder.encodeList? (E := E) trees state =
      some (encodeList trees state)

namespace InfallibleEncoder

def run (E : Type) [storage : EncoderStorage E Sig Name]
    [encoder : InfallibleEncoder E Sig Name]
    (tree : HolE Sig Name) (offset : Nat := 0) : EncodingResult Sig Name :=
  let (root, state) := encoder.encode tree (storage.initial offset)
  ⟨offset, storage.nodes state, root, storage.next state⟩

@[simp] theorem run?_eq_some_run (E : Type) [EncoderStorage E Sig Name]
    [encoder : InfallibleEncoder E Sig Name]
    (tree : HolE Sig Name) (offset : Nat) :
    FallibleEncoder.run? E tree offset = some (run E tree offset) := by
  simp [FallibleEncoder.run?, run, encoder.encode?_eq]

end InfallibleEncoder

namespace InfallibleListEncoder

def runList (E : Type) [storage : EncoderStorage E Sig Name]
    [encoder : InfallibleEncoder E Sig Name]
    [FallibleListEncoder E Sig Name] [listEncoder : InfallibleListEncoder E Sig Name]
    (trees : List (HolE Sig Name)) (offset : Nat := 0) :
    ListEncodingResult Sig Name :=
  let (indices, state) := listEncoder.encodeList trees (storage.initial offset)
  ⟨offset, storage.nodes state, indices, storage.next state⟩

@[simp] theorem runList?_eq_some_runList
    (E : Type) [EncoderStorage E Sig Name] [encoder : InfallibleEncoder E Sig Name]
    [FallibleListEncoder E Sig Name] [listEncoder : InfallibleListEncoder E Sig Name]
    (trees : List (HolE Sig Name)) (offset : Nat) :
    FallibleListEncoder.runList? E trees offset = some (runList E trees offset) := by
  simp [FallibleListEncoder.runList?, runList, listEncoder.encodeList?_eq]

end InfallibleListEncoder

namespace Encoder

/-- Marker selecting the concrete postorder encoder. -/
inductive Postorder

/-- State of the numbering-preserving postorder encoder.  `next` is the next
free absolute arena index; `nodes` contains rows beginning at the caller's
offset. -/
structure State (Sig : Signature.{u}) (Name : Type) where
  next : Nat
  nodes : List (Node Sig Name Nat)

abbrev M (Sig : Signature.{u}) (Name : Type) := StateM (State Sig Name)

private def emit (tag : Tag Sig Name) (children : List Nat) : M Sig Name Nat :=
  fun state => (state.next,
    { next := state.next + 1, nodes := state.nodes ++ [⟨tag, children⟩] })

/-- Encode a named tree in postorder.  Every recursive reference therefore
points below the node containing it.  Binder occurrences are emitted as
ordinary `tyVar`/`tmVar` nodes before their abstraction node. -/
def encode : HolE Sig Name → M Sig Name Nat
  | .boolTy => emit .tyBool []
  | .arr domain codomain => do
      let domainIndex ← encode domain
      let codomainIndex ← encode codomain
      emit .tyArr [domainIndex, codomainIndex]
  | .tyApp domain codomain function argument => do
      let functionIndex ← encode function
      let argumentIndex ← encode argument
      emit (.tyApp domain codomain) [functionIndex, argumentIndex]
  | .tyLam domain codomain name body => do
      let variableIndex ← emit (.tyVar name domain) []
      let bodyIndex ← encode body
      emit (.tyAbs domain codomain) [variableIndex, bodyIndex]
  | .tyFv name kind => emit (.tyVar name kind) []
  | .sub carrier name predicate => do
      let carrierIndex ← encode carrier
      let variableIndex ← emit (.tmVar name) [carrierIndex]
      let predicateIndex ← encode predicate
      emit .tySub [carrierIndex, variableIndex, predicateIndex]
  | .tyExists name predicate => do
      let variableIndex ← emit (.tyVar name .star) []
      let predicateIndex ← encode predicate
      emit .tyExists [variableIndex, predicateIndex]
  | .model name predicate => do
      let variableIndex ← emit (.tyVar name .star) []
      let predicateIndex ← encode predicate
      emit .tyModel [variableIndex, predicateIndex]
  | .primFam kind symbol => emit (.primFam kind symbol) []
  | .primTm symbol => emit (.primTm symbol) []
  | .tmFv name type => do
      let typeIndex ← encode type
      emit (.tmVar name) [typeIndex]
  | .app function argument => do
      let functionIndex ← encode function
      let argumentIndex ← encode argument
      emit .tmApp [functionIndex, argumentIndex]
  | .lam name domain body => do
      let domainIndex ← encode domain
      let variableIndex ← emit (.tmVar name) [domainIndex]
      let bodyIndex ← encode body
      emit .tmAbs [variableIndex, bodyIndex]
  | .bool value => emit (.tmBool value) []
  | .eq type left right => do
      let typeIndex ← encode type
      let leftIndex ← encode left
      let rightIndex ← encode right
      emit .tmEq [typeIndex, leftIndex, rightIndex]
  | .eps type predicate => do
      let typeIndex ← encode type
      let predicateIndex ← encode predicate
      emit .tmEps [typeIndex, predicateIndex]
  | .abs carrier name predicate value => do
      let carrierIndex ← encode carrier
      let variableIndex ← emit (.tmVar name) [carrierIndex]
      let predicateIndex ← encode predicate
      let valueIndex ← encode value
      emit .tmQuotAbs [carrierIndex, variableIndex, predicateIndex, valueIndex]
  | .rep carrier name predicate value => do
      let carrierIndex ← encode carrier
      let variableIndex ← emit (.tmVar name) [carrierIndex]
      let predicateIndex ← encode predicate
      let valueIndex ← encode value
      emit .tmQuotRep [carrierIndex, variableIndex, predicateIndex, valueIndex]

instance postorderStorage : EncoderStorage Postorder Sig Name where
  State := State Sig Name
  initial offset := ⟨offset, []⟩
  nodes := State.nodes
  next := State.next

instance : FallibleEncoder Postorder Sig Name where
  encode? := fun tree (state : State Sig Name) => some (encode tree state)

instance : InfallibleEncoder Postorder Sig Name where
  encode := fun tree (state : State Sig Name) => encode tree state
  encode?_eq _ _ := rfl

private def encodeList : List (HolE Sig Name) → M Sig Name (List Nat)
  | [] => fun state => ([], state)
  | tree :: trees => fun state =>
      let (index, state) := encode tree state
      let (indices, state) := encodeList trees state
      (index :: indices, state)

instance : FallibleListEncoder Postorder Sig Name where
  encodeList? := fun trees (state : State Sig Name) => some (encodeList trees state)

instance : InfallibleListEncoder Postorder Sig Name where
  encodeList := fun trees (state : State Sig Name) => encodeList trees state
  encodeList?_eq _ _ := rfl

/-- Encode several trees into one shared numbering space and return their
roots in input order. -/
def runList (trees : List (HolE Sig Name)) (offset : Nat := 0) :
    ListEncodingResult Sig Name :=
  InfallibleListEncoder.runList Postorder trees offset

theorem encodeList_roots_length (trees : List (HolE Sig Name)) (state : State Sig Name) :
    (encodeList trees state).1.length = trees.length := by
  induction trees generalizing state with
  | nil => rfl
  | cons tree trees ih =>
      cases encoded : encode tree state with
      | mk root nextState =>
          cases restEncoded : encodeList trees nextState with
          | mk roots finalState =>
              have restLength := ih nextState
              rw [restEncoded] at restLength
              simp [encodeList, encoded, restEncoded, restLength]

@[simp] theorem runList_roots_length (trees : List (HolE Sig Name)) (offset : Nat) :
    (runList trees offset).roots.length = trees.length := by
  simp only [runList, InfallibleListEncoder.runList]
  exact encodeList_roots_length trees ⟨offset, []⟩

/-- Result of encoding one tree at an absolute offset. -/
abbrev Result := EncodingResult

def run (tree : HolE Sig Name) (offset : Nat := 0) : Result Sig Name :=
  let (_, state) := encode tree ⟨offset, []⟩
  let next := offset + state.nodes.length
  ⟨offset, state.nodes, next - 1, next⟩

theorem run_next (tree : HolE Sig Name) (offset : Nat) :
    (run tree offset).next = offset + (run tree offset).nodes.length := by
  unfold run
  cases encode tree ⟨offset, []⟩
  rfl

/-- Postorder makes the root the final emitted row. -/
theorem run_root (tree : HolE Sig Name) (offset : Nat) :
    (run tree offset).root = (run tree offset).next - 1 := by
  unfold run
  cases encode tree ⟨offset, []⟩
  rfl

end Encoder

end Nucleus.HolE.Named.Unsorted.Dense
