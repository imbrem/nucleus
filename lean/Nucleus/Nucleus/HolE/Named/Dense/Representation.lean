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

@[simp] private theorem bind_apply (action : M Sig Name α) (next : α → M Sig Name β)
    (state : State Sig Name) :
    (action >>= next) state =
      let (value, state) := action state
      next value state := rfl

private def emit (tag : Tag Sig Name) (children : List Nat) : M Sig Name Nat :=
  fun state => (state.next,
    { next := state.next + 1, nodes := state.nodes ++ [⟨tag, children⟩] })

private def encodeTmVar (name : Name) (typeAction : M Sig Name Nat) : M Sig Name Nat := do
  let typeIndex ← typeAction
  emit (.tmVar name) [typeIndex]

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
      let variableIndex ← encodeTmVar name (encode carrier)
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
  | .tmFv name type => encodeTmVar name (encode type)
  | .app function argument => do
      let functionIndex ← encode function
      let argumentIndex ← encode argument
      emit .tmApp [functionIndex, argumentIndex]
  | .lam name domain body => do
      let variableIndex ← encodeTmVar name (encode domain)
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
      let variableIndex ← encodeTmVar name (encode carrier)
      let predicateIndex ← encode predicate
      let valueIndex ← encode value
      emit .tmQuotAbs [carrierIndex, variableIndex, predicateIndex, valueIndex]
  | .rep carrier name predicate value => do
      let carrierIndex ← encode carrier
      let variableIndex ← encodeTmVar name (encode carrier)
      let predicateIndex ← encode predicate
      let valueIndex ← encode value
      emit .tmQuotRep [carrierIndex, variableIndex, predicateIndex, valueIndex]

/-- Number of rows emitted by the concrete encoder.  Binder variables are
rows in their own right. -/
def nodeCount : HolE Sig Name → Nat
  | .boolTy | .tyFv .. | .primFam .. | .primTm .. | .bool .. => 1
  | .arr left right | .tyApp _ _ left right | .app left right |
      .eps left right => nodeCount left + nodeCount right + 1
  | .tyLam _ _ _ body | .tyExists _ body | .model _ body => nodeCount body + 2
  | .sub carrier _ predicate =>
      nodeCount carrier + nodeCount carrier + nodeCount predicate + 2
  | .lam _ carrier predicate => nodeCount carrier + nodeCount predicate + 2
  | .tmFv _ type => nodeCount type + 1
  | .eq type left right => nodeCount type + nodeCount left + nodeCount right + 1
  | .abs carrier _ predicate value | .rep carrier _ predicate value =>
      nodeCount carrier + nodeCount carrier + nodeCount predicate + nodeCount value + 2

theorem encode_root (tree : HolE Sig Name) (state : State Sig Name) :
    (encode tree state).1 + 1 = (encode tree state).2.next := by
  cases tree <;>
    simp [encode, encodeTmVar, emit, bind_apply] <;>
    repeat' split <;> rfl

/-- Elaborate only a freshly emitted suffix, starting in an arbitrary forest.
This is the compositional form needed to reason about stateful encoders. -/
def elaborateSuffix (forest : Forest Nat (HolE Sig Name)) (next : Nat) :
    List (Node Sig Name Nat) → Forest Nat (HolE Sig Name)
  | [] => forest
  | node :: nodes =>
      let value := Node.elaborate forest node
      elaborateSuffix (forest.set next value) (next + 1) nodes

@[simp] theorem elaborateSuffix_nil (forest : Forest Nat (HolE Sig Name)) (next : Nat) :
    elaborateSuffix forest next [] = forest := rfl

theorem elaborateSuffix_append (forest : Forest Nat (HolE Sig Name)) (next : Nat)
    (initialNodes suffix : List (Node Sig Name Nat)) :
    elaborateSuffix forest next (initialNodes ++ suffix) =
      elaborateSuffix (elaborateSuffix forest next initialNodes)
        (next + initialNodes.length) suffix := by
  induction initialNodes generalizing forest next with
  | nil => rfl
  | cons node initialNodes ih =>
      simp only [List.cons_append, elaborateSuffix, List.length_cons]
      rw [ih]
      congr 1
      omega

/-- Extending at `next` never changes an earlier absolute index. -/
theorem elaborateSuffix_of_lt (forest : Forest Nat (HolE Sig Name)) (next : Nat)
    (nodes : List (Node Sig Name Nat)) (index : Nat) (below : index < next) :
    elaborateSuffix forest next nodes index = forest index := by
  induction nodes generalizing forest next with
  | nil => rfl
  | cons node nodes ih =>
      simp only [elaborateSuffix]
      rw [ih (forest.set next (Node.elaborate forest node)) (next + 1) (by omega)]
      simp [Forest.set, Nat.ne_of_lt below]

theorem elaborateList_go_getElem?_join
    (forest : Forest Nat (HolE Sig Name)) (next : Nat)
    (nodes : List (Node Sig Name Nat)) (position : Nat) (bounded : position < nodes.length) :
    (elaborateList.go forest next nodes)[position]?.join =
      elaborateSuffix forest next nodes (next + position) := by
  induction nodes generalizing forest next position with
  | nil => simp at bounded
  | cons node nodes ih =>
      cases position with
      | zero =>
          simp only [elaborateList.go, List.getElem?_cons_zero, Option.join_some,
            elaborateSuffix, Nat.add_zero]
          rw [elaborateSuffix_of_lt _ (next + 1) nodes next (by omega)]
          simp [Forest.set]
          rfl
      | succ position =>
          simp only [elaborateList.go, List.getElem?_cons_succ, elaborateSuffix]
          change
            (elaborateList.go (forest.set next (Node.elaborate forest node))
              (next + 1) nodes)[position]?.join =
            elaborateSuffix (forest.set next (Node.elaborate forest node))
              (next + 1) nodes (next + (position + 1))
          rw [show next + (position + 1) = (next + 1) + position by omega]
          apply ih
          simpa using bounded

theorem elaborateForest_eq_elaborateSuffix
    (nodes : List (Node Sig Name Nat)) (offset index : Nat)
    (above : offset ≤ index) (below : index < offset + nodes.length) :
    elaborateForest emptyForest nodes offset index =
      elaborateSuffix emptyForest offset nodes index := by
  simp only [elaborateForest, above, below, and_self, if_true]
  unfold elaborateList
  rw [elaborateList_go_getElem?_join]
  · rw [show emptyForest.mask offset nodes.length =
      (emptyForest : Forest Nat (HolE Sig Name)) by
          apply congrArg Forest.mk
          funext wanted
          simp [emptyForest]]
    rw [Nat.add_sub_of_le above]
  · omega

/-- Structural contract used by the semantic correctness proof: an action
appends a suffix, advances by exactly its length, and its returned index
denotes the expected expression after elaborating that suffix. -/
def Encodes (action : M Sig Name Nat) (expression : HolE Sig Name) : Prop :=
  ∀ (state : State Sig Name) (forest : Forest Nat (HolE Sig Name)),
    ∃ suffix : List (Node Sig Name Nat),
      (action state).2.nodes = state.nodes ++ suffix ∧
      (action state).2.next = state.next + suffix.length ∧
      elaborateSuffix forest state.next suffix (action state).1 = some expression

private theorem encodes_emit (node : Node Sig Name Nat) (expression : HolE Sig Name)
    (elaborates : ∀ forest : Forest Nat (HolE Sig Name),
      Node.elaborate forest node = some expression) :
    Encodes (emit node.tag node.children) expression := by
  intro state forest
  refine ⟨[node], by simp [emit], by simp [emit], ?_⟩
  simp [emit, elaborateSuffix, Forest.set, elaborates]

private theorem encodes_binary
    (left right output : HolE Sig Name) (tag : Tag Sig Name)
    (leftCorrect : Encodes (encode left) left)
    (rightCorrect : Encodes (encode right) right)
    (elaborates : ∀ (forest : Forest Nat (HolE Sig Name)) leftIndex rightIndex,
      forest leftIndex = some left → forest rightIndex = some right →
      Node.elaborate forest ⟨tag, [leftIndex, rightIndex]⟩ = some output) :
    Encodes (do
      let leftIndex ← encode left
      let rightIndex ← encode right
      emit tag [leftIndex, rightIndex]) output := by
  intro state forest
  cases leftEncoded : encode left state with
  | mk leftIndex leftState =>
    obtain ⟨leftNodes, leftNodesEq, leftNextEq, leftLookup⟩ := leftCorrect state forest
    rw [leftEncoded] at leftNodesEq leftNextEq leftLookup
    simp at leftNodesEq leftNextEq leftLookup
    let leftForest := elaborateSuffix forest state.next leftNodes
    cases rightEncoded : encode right leftState with
    | mk rightIndex rightState =>
      obtain ⟨rightNodes, rightNodesEq, rightNextEq, rightLookup⟩ :=
        rightCorrect leftState leftForest
      rw [rightEncoded] at rightNodesEq rightNextEq rightLookup
      simp at rightNodesEq rightNextEq rightLookup
      let rightForest := elaborateSuffix leftForest leftState.next rightNodes
      have leftBelow : leftIndex < leftState.next := by
        have := encode_root left state
        rw [leftEncoded] at this
        simp at this
        omega
      have leftLookup' : rightForest leftIndex = some left := by
        exact (elaborateSuffix_of_lt leftForest leftState.next rightNodes leftIndex
          leftBelow).trans leftLookup
      let parent : Node Sig Name Nat := ⟨tag, [leftIndex, rightIndex]⟩
      refine ⟨leftNodes ++ rightNodes ++ [parent], ?_, ?_, ?_⟩
      · simp only [bind_apply, leftEncoded, rightEncoded, emit]
        rw [rightNodesEq, leftNodesEq]
        simp [parent, List.append_assoc]
      · simp only [bind_apply, leftEncoded, rightEncoded, emit]
        simp only [List.length_append, List.length_singleton]
        omega
      · rw [elaborateSuffix_append, elaborateSuffix_append]
        simp only [List.length_append]
        simp only [bind_apply, leftEncoded, rightEncoded, emit]
        change elaborateSuffix
          (elaborateSuffix leftForest (state.next + leftNodes.length) rightNodes)
          (state.next + (leftNodes.length + rightNodes.length)) [parent]
          rightState.next = some output
        rw [← leftNextEq]
        change elaborateSuffix rightForest
          (state.next + (leftNodes.length + rightNodes.length)) [parent]
          rightState.next = some output
        rw [show state.next + (leftNodes.length + rightNodes.length) = rightState.next by omega]
        change elaborateSuffix rightForest rightState.next [parent] rightState.next = some output
        simp [elaborateSuffix, Forest.set, parent,
          elaborates rightForest leftIndex rightIndex leftLookup' rightLookup]

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

/-- Decode a concrete encoder result using the ordinary left-to-right dense
arena elaborator and no ambient forest. -/
def Result.decode (result : Result Sig Name) : Option (HolE Sig Name) :=
  elaborateForest emptyForest result.nodes result.offset result.root

/-- Decode the raw unsorted syntax represented by a postorder result.  Unlike
`Result.decode`, this inverse does not reject an otherwise faithful encoding
merely because the unsorted tree is ill-sorted. -/
def Result.decodeSyntax (result : Result Sig Name) : Option (HolE Sig Name) :=
  elaborateForest emptyForest (result.nodes.map SyntaxNode.mk)
    result.offset result.root

/-! ## Raw syntactic correctness -/

/-- Elaborate a freshly emitted suffix without imposing sort checking. -/
def elaborateSyntaxSuffix (forest : Forest Nat (HolE Sig Name)) (next : Nat) :
    List (Node Sig Name Nat) → Forest Nat (HolE Sig Name)
  | [] => forest
  | node :: nodes =>
      elaborateSyntaxSuffix (forest.set next (Node.elaborateSyntax forest node))
        (next + 1) nodes

@[simp] theorem elaborateSyntaxSuffix_nil
    (forest : Forest Nat (HolE Sig Name)) (next : Nat) :
    elaborateSyntaxSuffix forest next [] = forest := rfl

theorem elaborateSyntaxSuffix_append
    (forest : Forest Nat (HolE Sig Name)) (next : Nat)
    (initialNodes suffix : List (Node Sig Name Nat)) :
    elaborateSyntaxSuffix forest next (initialNodes ++ suffix) =
      elaborateSyntaxSuffix (elaborateSyntaxSuffix forest next initialNodes)
        (next + initialNodes.length) suffix := by
  induction initialNodes generalizing forest next with
  | nil => rfl
  | cons node initialNodes ih =>
      simp only [List.cons_append, elaborateSyntaxSuffix, List.length_cons]
      rw [ih]
      congr 1
      omega

theorem elaborateSyntaxSuffix_of_lt
    (forest : Forest Nat (HolE Sig Name)) (next : Nat)
    (nodes : List (Node Sig Name Nat)) (index : Nat) (below : index < next) :
    elaborateSyntaxSuffix forest next nodes index = forest index := by
  induction nodes generalizing forest next with
  | nil => rfl
  | cons node nodes ih =>
      simp only [elaborateSyntaxSuffix]
      rw [ih (forest.set next (Node.elaborateSyntax forest node)) (next + 1) (by omega)]
      simp [Forest.set, Nat.ne_of_lt below]

theorem elaborateSyntaxList_go_getElem?_join
    (forest : Forest Nat (HolE Sig Name)) (next : Nat)
    (nodes : List (Node Sig Name Nat)) (position : Nat) (bounded : position < nodes.length) :
    (elaborateList.go forest next (nodes.map SyntaxNode.mk))[position]?.join =
      elaborateSyntaxSuffix forest next nodes (next + position) := by
  induction nodes generalizing forest next position with
  | nil => simp at bounded
  | cons node nodes ih =>
      cases position with
      | zero =>
          simp only [List.map_cons, elaborateList.go, List.getElem?_cons_zero,
            Option.join_some, elaborateSyntaxSuffix, Nat.add_zero]
          rw [elaborateSyntaxSuffix_of_lt _ (next + 1) nodes next (by omega)]
          change Node.elaborateSyntax forest node = _
          simp [Forest.set]
      | succ position =>
          simp only [List.map_cons, elaborateList.go, List.getElem?_cons_succ,
            elaborateSyntaxSuffix]
          change
            (elaborateList.go
              (forest.set next (Node.elaborateSyntax forest node))
              (next + 1) (nodes.map SyntaxNode.mk))[position]?.join =
            elaborateSyntaxSuffix
              (forest.set next (Node.elaborateSyntax forest node))
              (next + 1) nodes (next + (position + 1))
          rw [show next + (position + 1) = (next + 1) + position by omega]
          exact ih _ _ _ (by simpa using bounded)

theorem elaborateSyntaxForest_eq_suffix
    (nodes : List (Node Sig Name Nat)) (offset index : Nat)
    (above : offset ≤ index) (below : index < offset + nodes.length) :
    elaborateForest emptyForest (nodes.map SyntaxNode.mk) offset index =
      elaborateSyntaxSuffix emptyForest offset nodes index := by
  simp only [elaborateForest, List.length_map, above, below, and_self, if_true]
  unfold elaborateList
  rw [elaborateSyntaxList_go_getElem?_join]
  · simp only [List.length_map]
    change elaborateSyntaxSuffix (emptyForest.mask offset nodes.length)
      offset nodes (offset + (index - offset)) = _
    rw [show emptyForest.mask offset nodes.length =
      (emptyForest : Forest Nat (HolE Sig Name)) by
          apply congrArg Forest.mk
          funext wanted
          simp [emptyForest]]
    rw [Nat.add_sub_of_le above]
  · omega

/-- The raw semantic contract of the postorder encoder. -/
def SyntaxEncodes (action : M Sig Name Nat) (expression : HolE Sig Name) : Prop :=
  ∀ (state : State Sig Name) (forest : Forest Nat (HolE Sig Name)),
    ∃ suffix : List (Node Sig Name Nat),
      (action state).2.nodes = state.nodes ++ suffix ∧
      (action state).2.next = state.next + suffix.length ∧
      elaborateSyntaxSuffix forest state.next suffix (action state).1 = some expression

private theorem syntaxEncodes_emit
    (node : Node Sig Name Nat) (expression : HolE Sig Name)
    (elaborates : ∀ forest : Forest Nat (HolE Sig Name),
      Node.elaborateSyntax forest node = some expression) :
    SyntaxEncodes (emit node.tag node.children) expression := by
  intro state forest
  refine ⟨[node], by simp [emit], by simp [emit], ?_⟩
  simp [emit, elaborateSyntaxSuffix, Forest.set, elaborates]

private theorem syntaxEncodes_unary
    (child output : HolE Sig Name) (tag : Tag Sig Name)
    (childCorrect : SyntaxEncodes (encode child) child)
    (elaborates : ∀ (forest : Forest Nat (HolE Sig Name)) childIndex,
      forest childIndex = some child →
      Node.elaborateSyntax forest ⟨tag, [childIndex]⟩ = some output) :
    SyntaxEncodes (do
      let childIndex ← encode child
      emit tag [childIndex]) output := by
  intro state forest
  cases childEncoded : encode child state with
  | mk childIndex childState =>
    obtain ⟨childNodes, childNodesEq, childNextEq, childLookup⟩ :=
      childCorrect state forest
    rw [childEncoded] at childNodesEq childNextEq childLookup
    simp at childNodesEq childNextEq childLookup
    let parent : Node Sig Name Nat := ⟨tag, [childIndex]⟩
    refine ⟨childNodes ++ [parent], ?_, ?_, ?_⟩
    · simp only [bind_apply, childEncoded, emit]
      rw [childNodesEq]
      simp [parent, List.append_assoc]
    · simp only [bind_apply, childEncoded, emit, List.length_append,
        List.length_singleton]
      omega
    · rw [elaborateSyntaxSuffix_append]
      simp only [bind_apply, childEncoded, emit]
      change elaborateSyntaxSuffix
        (elaborateSyntaxSuffix forest state.next childNodes)
        (state.next + childNodes.length) [parent] childState.next = some output
      rw [← childNextEq]
      simp [elaborateSyntaxSuffix, Forest.set, parent,
        elaborates _ childIndex childLookup]

private theorem syntaxEncodes_binary
    (left right output : HolE Sig Name) (tag : Tag Sig Name)
    (leftCorrect : SyntaxEncodes (encode left) left)
    (rightCorrect : SyntaxEncodes (encode right) right)
    (elaborates : ∀ (forest : Forest Nat (HolE Sig Name)) leftIndex rightIndex,
      forest leftIndex = some left → forest rightIndex = some right →
      Node.elaborateSyntax forest ⟨tag, [leftIndex, rightIndex]⟩ = some output) :
    SyntaxEncodes (do
      let leftIndex ← encode left
      let rightIndex ← encode right
      emit tag [leftIndex, rightIndex]) output := by
  intro state forest
  cases leftEncoded : encode left state with
  | mk leftIndex leftState =>
    obtain ⟨leftNodes, leftNodesEq, leftNextEq, leftLookup⟩ :=
      leftCorrect state forest
    rw [leftEncoded] at leftNodesEq leftNextEq leftLookup
    simp at leftNodesEq leftNextEq leftLookup
    let leftForest := elaborateSyntaxSuffix forest state.next leftNodes
    cases rightEncoded : encode right leftState with
    | mk rightIndex rightState =>
      obtain ⟨rightNodes, rightNodesEq, rightNextEq, rightLookup⟩ :=
        rightCorrect leftState leftForest
      rw [rightEncoded] at rightNodesEq rightNextEq rightLookup
      simp at rightNodesEq rightNextEq rightLookup
      let rightForest := elaborateSyntaxSuffix leftForest leftState.next rightNodes
      have leftBelow : leftIndex < leftState.next := by
        have root := encode_root left state
        rw [leftEncoded] at root
        simp at root
        omega
      have leftLookup' : rightForest leftIndex = some left :=
        (elaborateSyntaxSuffix_of_lt leftForest leftState.next rightNodes
          leftIndex leftBelow).trans leftLookup
      let parent : Node Sig Name Nat := ⟨tag, [leftIndex, rightIndex]⟩
      refine ⟨leftNodes ++ rightNodes ++ [parent], ?_, ?_, ?_⟩
      · simp only [bind_apply, leftEncoded, rightEncoded, emit]
        rw [rightNodesEq, leftNodesEq]
        simp [parent, List.append_assoc]
      · simp only [bind_apply, leftEncoded, rightEncoded, emit,
          List.length_append, List.length_singleton]
        omega
      · rw [elaborateSyntaxSuffix_append, elaborateSyntaxSuffix_append]
        simp only [List.length_append, bind_apply, leftEncoded, rightEncoded, emit]
        change elaborateSyntaxSuffix
          (elaborateSyntaxSuffix leftForest (state.next + leftNodes.length) rightNodes)
          (state.next + (leftNodes.length + rightNodes.length)) [parent]
          rightState.next = some output
        rw [← leftNextEq]
        change elaborateSyntaxSuffix rightForest
          (state.next + (leftNodes.length + rightNodes.length)) [parent]
          rightState.next = some output
        rw [show state.next + (leftNodes.length + rightNodes.length) =
          rightState.next by omega]
        simp [elaborateSyntaxSuffix, Forest.set, parent,
          elaborates rightForest leftIndex rightIndex leftLookup' rightLookup]

private theorem syntaxEncodes_ternary
    (first second third output : HolE Sig Name) (tag : Tag Sig Name)
    (firstCorrect : SyntaxEncodes (encode first) first)
    (secondCorrect : SyntaxEncodes (encode second) second)
    (thirdCorrect : SyntaxEncodes (encode third) third)
    (elaborates : ∀ (forest : Forest Nat (HolE Sig Name)) i j k,
      forest i = some first → forest j = some second → forest k = some third →
      Node.elaborateSyntax forest ⟨tag, [i, j, k]⟩ = some output) :
    SyntaxEncodes (do
      let i ← encode first
      let j ← encode second
      let k ← encode third
      emit tag [i, j, k]) output := by
  intro state forest
  cases firstEncoded : encode first state with
  | mk i firstState =>
    obtain ⟨firstNodes, firstNodesEq, firstNextEq, firstLookup⟩ :=
      firstCorrect state forest
    rw [firstEncoded] at firstNodesEq firstNextEq firstLookup
    simp at firstNodesEq firstNextEq firstLookup
    let firstForest := elaborateSyntaxSuffix forest state.next firstNodes
    cases secondEncoded : encode second firstState with
    | mk j secondState =>
      obtain ⟨secondNodes, secondNodesEq, secondNextEq, secondLookup⟩ :=
        secondCorrect firstState firstForest
      rw [secondEncoded] at secondNodesEq secondNextEq secondLookup
      simp at secondNodesEq secondNextEq secondLookup
      let secondForest := elaborateSyntaxSuffix firstForest firstState.next secondNodes
      cases thirdEncoded : encode third secondState with
      | mk k thirdState =>
        obtain ⟨thirdNodes, thirdNodesEq, thirdNextEq, thirdLookup⟩ :=
          thirdCorrect secondState secondForest
        rw [thirdEncoded] at thirdNodesEq thirdNextEq thirdLookup
        simp at thirdNodesEq thirdNextEq thirdLookup
        let thirdForest := elaborateSyntaxSuffix secondForest secondState.next thirdNodes
        have iBelowFirst : i < firstState.next := by
          have root := encode_root first state
          rw [firstEncoded] at root
          simp at root
          omega
        have jBelowSecond : j < secondState.next := by
          have root := encode_root second firstState
          rw [secondEncoded] at root
          simp at root
          omega
        have iBelowSecond : i < secondState.next := by omega
        have iLookupSecond : secondForest i = some first :=
          (elaborateSyntaxSuffix_of_lt firstForest firstState.next secondNodes
            i iBelowFirst).trans firstLookup
        have iLookupThird : thirdForest i = some first :=
          (elaborateSyntaxSuffix_of_lt secondForest secondState.next thirdNodes
            i iBelowSecond).trans iLookupSecond
        have jLookupThird : thirdForest j = some second :=
          (elaborateSyntaxSuffix_of_lt secondForest secondState.next thirdNodes
            j jBelowSecond).trans secondLookup
        let parent : Node Sig Name Nat := ⟨tag, [i, j, k]⟩
        refine ⟨firstNodes ++ secondNodes ++ thirdNodes ++ [parent], ?_, ?_, ?_⟩
        · simp only [bind_apply, firstEncoded, secondEncoded, thirdEncoded, emit]
          rw [thirdNodesEq, secondNodesEq, firstNodesEq]
          simp [parent, List.append_assoc]
        · simp only [bind_apply, firstEncoded, secondEncoded, thirdEncoded, emit,
            List.length_append, List.length_singleton]
          omega
        · rw [elaborateSyntaxSuffix_append, elaborateSyntaxSuffix_append,
            elaborateSyntaxSuffix_append]
          simp only [List.length_append, bind_apply, firstEncoded, secondEncoded,
            thirdEncoded, emit]
          change elaborateSyntaxSuffix
            (elaborateSyntaxSuffix
              (elaborateSyntaxSuffix firstForest
                (state.next + firstNodes.length) secondNodes)
              (state.next + (firstNodes.length + secondNodes.length)) thirdNodes)
            (state.next + (firstNodes.length + secondNodes.length + thirdNodes.length))
            [parent] thirdState.next = some output
          rw [← firstNextEq]
          change elaborateSyntaxSuffix
            (elaborateSyntaxSuffix secondForest
              (state.next + (firstNodes.length + secondNodes.length)) thirdNodes)
            (state.next + (firstNodes.length + secondNodes.length + thirdNodes.length))
            [parent] thirdState.next = some output
          rw [show state.next + (firstNodes.length + secondNodes.length) =
            secondState.next by omega]
          change elaborateSyntaxSuffix thirdForest
            (state.next + (firstNodes.length + secondNodes.length + thirdNodes.length))
            [parent] thirdState.next = some output
          rw [show state.next +
            (firstNodes.length + secondNodes.length + thirdNodes.length) =
              thirdState.next by omega]
          simp [elaborateSyntaxSuffix, Forest.set, parent,
            elaborates thirdForest i j k iLookupThird jLookupThird thirdLookup]

private theorem syntaxEncodes_quaternary
    (a b c d output : HolE Sig Name) (tag : Tag Sig Name)
    (ha : SyntaxEncodes (encode a) a) (hb : SyntaxEncodes (encode b) b)
    (hc : SyntaxEncodes (encode c) c) (hd : SyntaxEncodes (encode d) d)
    (elaborates : ∀ (forest : Forest Nat (HolE Sig Name)) i j k l,
      forest i = some a → forest j = some b → forest k = some c →
      forest l = some d →
      Node.elaborateSyntax forest ⟨tag, [i, j, k, l]⟩ = some output) :
    SyntaxEncodes (do
      let i ← encode a
      let j ← encode b
      let k ← encode c
      let l ← encode d
      emit tag [i, j, k, l]) output := by
  intro state forest
  cases ea : encode a state with
  | mk i sa =>
    obtain ⟨na, hna, hsa, la⟩ := ha state forest
    rw [ea] at hna hsa la
    simp at hna hsa la
    let fa := elaborateSyntaxSuffix forest state.next na
    cases eb : encode b sa with
    | mk j sb =>
      obtain ⟨nb, hnb, hsb, lb⟩ := hb sa fa
      rw [eb] at hnb hsb lb
      simp at hnb hsb lb
      let fb := elaborateSyntaxSuffix fa sa.next nb
      cases ec : encode c sb with
      | mk k sc =>
        obtain ⟨nc, hnc, hsc, lc⟩ := hc sb fb
        rw [ec] at hnc hsc lc
        simp at hnc hsc lc
        let fc := elaborateSyntaxSuffix fb sb.next nc
        cases ed : encode d sc with
        | mk l sd =>
          obtain ⟨nd, hnd, hsd, ld⟩ := hd sc fc
          rw [ed] at hnd hsd ld
          simp at hnd hsd ld
          let fd := elaborateSyntaxSuffix fc sc.next nd
          have ia : i < sa.next := by
            have h := encode_root a state
            rw [ea] at h
            simp at h
            omega
          have jb : j < sb.next := by
            have h := encode_root b sa
            rw [eb] at h
            simp at h
            omega
          have kc : k < sc.next := by
            have h := encode_root c sb
            rw [ec] at h
            simp at h
            omega
          have i_fb : fb i = some a :=
            (elaborateSyntaxSuffix_of_lt fa sa.next nb i ia).trans la
          have i_fc : fc i = some a :=
            (elaborateSyntaxSuffix_of_lt fb sb.next nc i (by omega)).trans i_fb
          have j_fc : fc j = some b :=
            (elaborateSyntaxSuffix_of_lt fb sb.next nc j jb).trans lb
          have i_fd : fd i = some a :=
            (elaborateSyntaxSuffix_of_lt fc sc.next nd i (by omega)).trans i_fc
          have j_fd : fd j = some b :=
            (elaborateSyntaxSuffix_of_lt fc sc.next nd j (by omega)).trans j_fc
          have k_fd : fd k = some c :=
            (elaborateSyntaxSuffix_of_lt fc sc.next nd k kc).trans lc
          let parent : Node Sig Name Nat := ⟨tag, [i, j, k, l]⟩
          refine ⟨na ++ nb ++ nc ++ nd ++ [parent], ?_, ?_, ?_⟩
          · simp only [bind_apply, ea, eb, ec, ed, emit]
            rw [hnd, hnc, hnb, hna]
            simp [parent, List.append_assoc]
          · simp only [bind_apply, ea, eb, ec, ed, emit, List.length_append,
              List.length_singleton]
            omega
          · rw [elaborateSyntaxSuffix_append, elaborateSyntaxSuffix_append,
              elaborateSyntaxSuffix_append, elaborateSyntaxSuffix_append]
            simp only [List.length_append, bind_apply, ea, eb, ec, ed, emit]
            change elaborateSyntaxSuffix
              (elaborateSyntaxSuffix
                (elaborateSyntaxSuffix
                  (elaborateSyntaxSuffix fa (state.next + na.length) nb)
                  (state.next + (na.length + nb.length)) nc)
                (state.next + (na.length + nb.length + nc.length)) nd)
              (state.next + (na.length + nb.length + nc.length + nd.length))
              [parent] sd.next = some output
            rw [← hsa]
            change elaborateSyntaxSuffix
              (elaborateSyntaxSuffix
                (elaborateSyntaxSuffix fb
                  (state.next + (na.length + nb.length)) nc)
                (state.next + (na.length + nb.length + nc.length)) nd)
              _ [parent] sd.next = some output
            rw [show state.next + (na.length + nb.length) = sb.next by omega]
            change elaborateSyntaxSuffix
              (elaborateSyntaxSuffix fc
                (state.next + (na.length + nb.length + nc.length)) nd)
              _ [parent] sd.next = some output
            rw [show state.next + (na.length + nb.length + nc.length) = sc.next by omega]
            change elaborateSyntaxSuffix fd
              (state.next + (na.length + nb.length + nc.length + nd.length))
              [parent] sd.next = some output
            rw [show state.next + (na.length + nb.length + nc.length + nd.length) =
              sd.next by omega]
            simp [elaborateSyntaxSuffix, Forest.set, parent,
              elaborates fd i j k l i_fd j_fd k_fd ld]

/-- Every named unsorted tree is recovered by raw elaboration of the suffix
emitted by the postorder encoder. -/
theorem encode_syntaxCorrect (tree : HolE Sig Name) :
    SyntaxEncodes (encode tree) tree := by
  induction tree with
  | boolTy =>
      exact syntaxEncodes_emit ⟨.tyBool, []⟩ .boolTy (fun _ => rfl)
  | arr domain codomain domainIH codomainIH =>
      apply syntaxEncodes_binary domain codomain (.arr domain codomain) .tyArr
        domainIH codomainIH
      intro forest i j hi hj
      simp [Node.elaborateSyntax, hi, hj]
  | tyApp domain codomain function argument functionIH argumentIH =>
      apply syntaxEncodes_binary function argument
        (.tyApp domain codomain function argument) (.tyApp domain codomain)
        functionIH argumentIH
      intro forest i j hi hj
      simp [Node.elaborateSyntax, hi, hj]
  | tyLam domain codomain name body bodyIH =>
      have variableCorrect : SyntaxEncodes
          (encode (.tyFv name domain : HolE Sig Name)) (.tyFv name domain) :=
        syntaxEncodes_emit ⟨.tyVar name domain, []⟩ (.tyFv name domain) (fun _ => rfl)
      simpa only [encode, encodeTmVar] using
        syntaxEncodes_binary (.tyFv name domain) body
          (.tyLam domain codomain name body) (.tyAbs domain codomain)
          variableCorrect bodyIH (by
            intro forest i j hi hj
            simp [Node.elaborateSyntax, hi, hj])
  | tyFv name kind =>
      exact syntaxEncodes_emit ⟨.tyVar name kind, []⟩ (.tyFv name kind) (fun _ => rfl)
  | sub carrier name predicate carrierIH predicateIH =>
      have variableCorrect : SyntaxEncodes
          (encode (.tmFv name carrier : HolE Sig Name)) (.tmFv name carrier) := by
        simpa only [encode, encodeTmVar] using
          syntaxEncodes_unary carrier (.tmFv name carrier) (.tmVar name) carrierIH (by
            intro forest i hi
            simp [Node.elaborateSyntax, hi])
      simpa only [encode, encodeTmVar] using
        syntaxEncodes_ternary carrier (.tmFv name carrier) predicate
          (.sub carrier name predicate) .tySub carrierIH variableCorrect predicateIH (by
            intro forest i j k hi hj hk
            simp [Node.elaborateSyntax, hi, hj, hk])
  | tyExists name predicate predicateIH =>
      have variableCorrect : SyntaxEncodes
          (encode (.tyFv name .star : HolE Sig Name)) (.tyFv name .star) :=
        syntaxEncodes_emit ⟨.tyVar name .star, []⟩ (.tyFv name .star) (fun _ => rfl)
      simpa only [encode, encodeTmVar] using
        syntaxEncodes_binary (.tyFv name .star) predicate (.tyExists name predicate)
          .tyExists variableCorrect predicateIH (by
            intro forest i j hi hj
            simp [Node.elaborateSyntax, hi, hj])
  | model name predicate predicateIH =>
      have variableCorrect : SyntaxEncodes
          (encode (.tyFv name .star : HolE Sig Name)) (.tyFv name .star) :=
        syntaxEncodes_emit ⟨.tyVar name .star, []⟩ (.tyFv name .star) (fun _ => rfl)
      simpa only [encode, encodeTmVar] using
        syntaxEncodes_binary (.tyFv name .star) predicate (.model name predicate)
          .tyModel variableCorrect predicateIH (by
            intro forest i j hi hj
            simp [Node.elaborateSyntax, hi, hj])
  | primFam kind symbol =>
      exact syntaxEncodes_emit ⟨.primFam kind symbol, []⟩ (.primFam kind symbol) (fun _ => rfl)
  | primTm symbol =>
      exact syntaxEncodes_emit ⟨.primTm symbol, []⟩ (.primTm symbol) (fun _ => rfl)
  | tmFv name type typeIH =>
      simpa only [encode, encodeTmVar] using
        syntaxEncodes_unary type (.tmFv name type) (.tmVar name) typeIH (by
          intro forest i hi
          simp [Node.elaborateSyntax, hi])
  | app function argument functionIH argumentIH =>
      apply syntaxEncodes_binary function argument (.app function argument) .tmApp
        functionIH argumentIH
      intro forest i j hi hj
      simp [Node.elaborateSyntax, hi, hj]
  | lam name domain body domainIH bodyIH =>
      have variableCorrect : SyntaxEncodes
          (encode (.tmFv name domain : HolE Sig Name)) (.tmFv name domain) := by
        simpa only [encode, encodeTmVar] using
          syntaxEncodes_unary domain (.tmFv name domain) (.tmVar name) domainIH (by
            intro forest i hi
            simp [Node.elaborateSyntax, hi])
      simpa only [encode, encodeTmVar] using
        syntaxEncodes_binary (.tmFv name domain) body (.lam name domain body)
          .tmAbs variableCorrect bodyIH (by
            intro forest i j hi hj
            simp [Node.elaborateSyntax, hi, hj])
  | bool value =>
      exact syntaxEncodes_emit ⟨.tmBool value, []⟩ (.bool value) (fun _ => rfl)
  | eq type left right typeIH leftIH rightIH =>
      apply syntaxEncodes_ternary type left right (.eq type left right) .tmEq
        typeIH leftIH rightIH
      intro forest i j k hi hj hk
      simp [Node.elaborateSyntax, hi, hj, hk]
  | eps type predicate typeIH predicateIH =>
      apply syntaxEncodes_binary type predicate (.eps type predicate) .tmEps
        typeIH predicateIH
      intro forest i j hi hj
      simp [Node.elaborateSyntax, hi, hj]
  | abs carrier name predicate value carrierIH predicateIH valueIH =>
      have variableCorrect : SyntaxEncodes
          (encode (.tmFv name carrier : HolE Sig Name)) (.tmFv name carrier) := by
        simpa only [encode, encodeTmVar] using
          syntaxEncodes_unary carrier (.tmFv name carrier) (.tmVar name) carrierIH (by
            intro forest i hi
            simp [Node.elaborateSyntax, hi])
      simpa only [encode, encodeTmVar] using
        syntaxEncodes_quaternary carrier (.tmFv name carrier) predicate value
          (.abs carrier name predicate value) .tmQuotAbs carrierIH variableCorrect
          predicateIH valueIH (by
            intro forest i j k l hi hj hk hl
            simp [Node.elaborateSyntax, hi, hj, hk, hl])
  | rep carrier name predicate value carrierIH predicateIH valueIH =>
      have variableCorrect : SyntaxEncodes
          (encode (.tmFv name carrier : HolE Sig Name)) (.tmFv name carrier) := by
        simpa only [encode, encodeTmVar] using
          syntaxEncodes_unary carrier (.tmFv name carrier) (.tmVar name) carrierIH (by
            intro forest i hi
            simp [Node.elaborateSyntax, hi])
      simpa only [encode, encodeTmVar] using
        syntaxEncodes_quaternary carrier (.tmFv name carrier) predicate value
          (.rep carrier name predicate value) .tmQuotRep carrierIH variableCorrect
          predicateIH valueIH (by
            intro forest i j k l hi hj hk hl
            simp [Node.elaborateSyntax, hi, hj, hk, hl])

/-- Raw decoding is a left inverse of postorder encoding at every absolute
offset. -/
@[simp] theorem decodeSyntax_run (tree : HolE Sig Name) (offset : Nat) :
    (run tree offset).decodeSyntax = some tree := by
  let initial : State Sig Name := ⟨offset, []⟩
  cases encoded : encode tree initial with
  | mk root state =>
    obtain ⟨suffix, nodesEq, nextEq, lookup⟩ :=
      encode_syntaxCorrect tree initial emptyForest
    rw [encoded] at nodesEq nextEq lookup
    simp [initial] at nodesEq nextEq lookup
    have rootGe : offset ≤ root := by
      by_cases above : offset ≤ root
      · exact above
      · have below : root < offset := Nat.lt_of_not_ge above
        have unchanged := elaborateSyntaxSuffix_of_lt emptyForest offset suffix root below
        rw [unchanged] at lookup
        simp [emptyForest] at lookup
    have rootEq : root = offset + suffix.length - 1 := by
      have rootNext := encode_root tree initial
      rw [encoded] at rootNext
      simp at rootNext
      omega
    have nonempty : 0 < suffix.length := by
      have rootNext := encode_root tree initial
      rw [encoded] at rootNext
      simp at rootNext
      omega
    have above : offset ≤ offset + suffix.length - 1 := by omega
    have below : offset + suffix.length - 1 < offset + suffix.length := by omega
    unfold Result.decodeSyntax run
    rw [encoded]
    simp only
    rw [nodesEq]
    change elaborateForest emptyForest (suffix.map SyntaxNode.mk) offset
      (offset + suffix.length - 1) = some tree
    rw [elaborateSyntaxForest_eq_suffix suffix offset
      (offset + suffix.length - 1) above below]
    rw [← rootEq]
    exact lookup

/-! ## The concrete postorder equivalence -/

/-- A finite node-list encoding with one distinguished root. -/
abbrev RootEncoding := Result

/-- Encode a tree at the canonical zero offset. -/
def postorder (tree : HolE Sig Name) : RootEncoding Sig Name := run tree 0

/-- Decode the raw tree carried by a finite root encoding. -/
def unpostorder (encoding : RootEncoding Sig Name) : Option (HolE Sig Name) :=
  encoding.decodeSyntax

@[simp] theorem unpostorder_postorder (tree : HolE Sig Name) :
    unpostorder (postorder tree) = some tree := decodeSyntax_run tree 0

theorem postorder_injective :
    Function.Injective (@postorder Sig Name) := by
  intro left right equality
  have := congrArg unpostorder equality
  simpa using this

/-- The postorder map bundled with its injectivity proof. -/
structure PostorderEmbedding (Sig : Signature.{u}) (Name : Type) where
  toFun : HolE Sig Name → RootEncoding Sig Name
  injective : Function.Injective toFun

def postorderEmbedding : PostorderEmbedding Sig Name :=
  ⟨postorder, postorder_injective⟩

/-- Root encodings which decode to a finite named tree. -/
def ValidRootEncoding (Sig : Signature.{u}) (Name : Type) :=
  { encoding : RootEncoding Sig Name // ∃ tree, unpostorder encoding = some tree }

/-- Decoding equivalence on valid finite root encodings. -/
def ValidRootEncoding.Equivalent
    (left right : ValidRootEncoding Sig Name) : Prop :=
  unpostorder left.val = unpostorder right.val

def ValidRootEncoding.decodingSetoid : Setoid (ValidRootEncoding Sig Name) where
  r := ValidRootEncoding.Equivalent
  iseqv := ⟨fun _ => rfl, fun equality => equality.symm,
    fun left middle => left.trans middle⟩

abbrev PostorderQuotient (Sig : Signature.{u}) (Name : Type) :=
  Quotient (ValidRootEncoding.decodingSetoid (Sig := Sig) (Name := Name))

def postorderValid (tree : HolE Sig Name) : ValidRootEncoding Sig Name :=
  ⟨postorder tree, tree, unpostorder_postorder tree⟩

/-- Every valid finite root encoding is decoding-equivalent to a canonical
postorder encoding. -/
theorem postorder_surjective_upToEquivalent
    (encoding : ValidRootEncoding Sig Name) :
    ∃ tree, ValidRootEncoding.Equivalent (postorderValid tree) encoding := by
  obtain ⟨tree, decodes⟩ := encoding.property
  exact ⟨tree, (unpostorder_postorder tree).trans decodes.symm⟩

/-- Postorder is injective on trees and surjective onto valid root encodings
up to decoding equivalence. -/
theorem postorder_bijective_upToEquivalent :
    Function.Injective (@postorder Sig Name) ∧
      ∀ encoding : ValidRootEncoding Sig Name,
        ∃ tree, ValidRootEncoding.Equivalent (postorderValid tree) encoding :=
  ⟨postorder_injective, postorder_surjective_upToEquivalent⟩

def postorderQuotient (tree : HolE Sig Name) : PostorderQuotient Sig Name :=
  Quotient.mk _ (postorderValid tree)

example (offset : Nat) :
    (run (.boolTy : HolE Sig Name) offset).decode = some .boolTy := by
  simp [Result.decode, run, encode, emit, elaborateForest, elaborateList,
    Forest.mask, emptyForest]
  rfl

/-- Absolute numbering is observable at nonzero offsets, including the
ordinary variable row emitted for an abstraction binder. -/
example :
    let result := run (.lam 7 .boolTy (.bool true) : HolE Sig Nat) 10
    result.root = 13 ∧ result.next = 14 ∧
      result.nodes[1]? = some ⟨.tmVar 7, [10]⟩ := by
  simp [run, encode, encodeTmVar, emit, bind_apply]

/-- Batch encoding preserves input order in its public roots. -/
example :
    (runList ([.bool true, .bool false] : List (HolE Sig Nat)) 10).roots = [10, 11] := by
  rfl

end Encoder

end Nucleus.HolE.Named.Unsorted.Dense
