import Nucleus.HolE.Named.Unsorted

/-!
# Dense arenas for named HolE

The generic part of this file only knows how to ask an entry to elaborate
against a partial forest.  `Node` and its `NodeLike` instance provide the
HolE-specific layer.  A dense list shadows the corresponding interval of the
underlying forest and is elaborated from left to right.
-/

namespace Nucleus.HolE.Named.Unsorted.Dense

universe u v w
set_option relaxedAutoImplicit true

abbrev HolE (Sig : Signature.{u}) (Name : Type := Nat) := Unsorted.Expr Sig Name

/-- A partial collection of trees, independently of its index representation. -/
structure Forest (ι : Type v) (α : Type w) where
  get : ι → Option α

instance : CoeFun (Forest ι α) (fun _ => ι → Option α) := ⟨Forest.get⟩

/-- An arena entry which can either already be a tree or elaborate one from a forest. -/
class NodeLike (N : Type w) (ι : Type v) (α : Type u) where
  get : (ι → Option α) → N → Option α

namespace NodeLike

def elaborate [NodeLike N ι α] (forest : Forest ι α) (node : N) : Option α :=
  NodeLike.get forest.get node

instance [NodeLike N ι α] : NodeLike (Option N) ι α where
  get forest node := node.bind (NodeLike.get forest)

instance [NodeLike L ι α] [NodeLike R ι α] : NodeLike (L ⊕ R) ι α where
  get forest
    | .inl left => NodeLike.get forest left
    | .inr right => NodeLike.get forest right

end NodeLike

/-- Payload of one HolE node.  Recursive arguments live exclusively in
`Node.children`.  In particular, both abstraction tags take a variable node
as their first child. -/
inductive Tag (Sig : Signature.{u}) (Name : Type) where
  | tyBool
  | tyArr
  | tyApp (domain codomain : Kind)
  | tyAbs (domain codomain : Kind)
  | tyVar (name : Name) (kind : Kind)
  | tySub
  | tyExists
  | tyModel
  | primFam (kind : Kind) (symbol : Sig (.kind kind))
  | primTm (symbol : Sig .tm)
  | tmVar (name : Name)
  | tmApp
  | tmAbs
  | tmLet
  | tmBool (value : Bool)
  | tmTrue
  | tmFalse
  | tmNot
  | tmAnd (functionName : Name)
  | tmOr (functionName : Name)
  | tmEq
  | tmEps
  | tmQuotAbs
  | tmQuotRep

/-- A tag and a list of references to its recursive children. -/
structure Node (Sig : Signature.{u}) (Name : Type) (ι : Type w) where
  tag : Tag Sig Name
  children : List ι

/-! ## Finite-depth rooted DAGs -/

/-- Node families whose immediate dependencies can be observed. -/
class Children (N : Type u → Type v) where
  children : N ι → List ι

instance : Children (Node Sig Name) where
  children := Node.children

/-- The child-to-parent dependency relation induced by a partial node forest. -/
def dependency [Children N] (forest : ι → Option (N ι)) (child parent : ι) : Prop :=
  ∃ node, forest parent = some node ∧ child ∈ Children.children node

/-- A rooted node forest whose live dependency graph has finite depth.

Only accessibility from `root` is required, so unreachable garbage may be
cyclic or infinite without affecting the represented value. -/
structure RootedDAG (N : Type u → Type v) (ι : Type u) [Children N] where
  forest : ι → Option (N ι)
  root : ι
  finiteDepth : Acc (dependency forest) root

namespace RootedDAG

/-- Observe a rooted DAG through any decoder appropriate to its node family. -/
def decode [Children N] (decoder : (ι → Option (N ι)) → ι → D)
    (dag : RootedDAG N ι) : D :=
  decoder dag.forest dag.root

/-- Two finite-depth DAGs are equivalent when their canonical decodings agree. -/
def Equivalent [Children N] (decoder : (ι → Option (N ι)) → ι → D)
    (left right : RootedDAG N ι) : Prop :=
  left.decode decoder = right.decode decoder

def decodingSetoid [Children N]
    (decoder : (ι → Option (N ι)) → ι → D) : Setoid (RootedDAG N ι) where
  r := Equivalent decoder
  iseqv := ⟨fun _ => rfl, fun equality => equality.symm,
    fun left middle => left.trans middle⟩

end RootedDAG

/-- Arbitrarily indexed finite-depth rooted DAGs modulo canonical decoding. -/
abbrev DAGQuotient (N : Type u → Type v) (ι : Type u) [Children N]
    (decoder : (ι → Option (N ι)) → ι → D) :=
  Quotient (RootedDAG.decodingSetoid decoder)

namespace Node

private def not (proposition : HolE Sig Name) : HolE Sig Name :=
  .eq .boolTy proposition (.bool false)

/-- The standard equality-only HOL encoding of conjunction. -/
private def and (functionName : Name) (left right : HolE Sig Name) : HolE Sig Name :=
  let functionType := Unsorted.Expr.arr .boolTy (.arr .boolTy .boolTy)
  let function := Unsorted.Expr.tmFv functionName functionType
  let lhs := Unsorted.Expr.lam functionName functionType (.app (.app function left) right)
  let rhs := Unsorted.Expr.lam functionName functionType
    (.app (.app function (.bool true)) (.bool true))
  .eq (.arr functionType .boolTy) lhs rhs

private def or (functionName : Name) (left right : HolE Sig Name) : HolE Sig Name :=
  not (and functionName (not left) (not right))

private def resolve (forest : ι → Option (HolE Sig Name)) (children : List ι) :
    Option (List (HolE Sig Name)) :=
  children.mapM forest

@[simp] theorem resolve_nil (forest : ι → Option (HolE Sig Name)) :
    resolve forest [] = some [] := rfl

@[simp] theorem resolve_cons (forest : ι → Option (HolE Sig Name))
    (index : ι) (indices : List ι) :
    resolve forest (index :: indices) = do
      let value ← forest index
      let values ← resolve forest indices
      return value :: values := by
  unfold resolve
  rw [List.mapM_cons]

/-- Elaborate one node as raw unsorted syntax.  Arity mismatches, dangling
references, and non-variable abstraction binders return `none`. -/
def elaborateSyntax (forest : ι → Option (HolE Sig Name)) (node : Node Sig Name ι) :
    Option (HolE Sig Name) := do
  let children ← resolve forest node.children
  match node.tag, children with
    | .tyBool, [] => some .boolTy
    | .tyArr, [domain, codomain] => some (.arr domain codomain)
    | .tyApp domain codomain, [function, argument] =>
        some (.tyApp domain codomain function argument)
    | .tyAbs domain codomain, [.tyFv name kind, body] =>
        if kind = domain then some (.tyLam domain codomain name body) else none
    | .tyVar name kind, [] => some (.tyFv name kind)
    | .tySub, [carrier, .tmFv name _, predicate] => some (.sub carrier name predicate)
    | .tyExists, [.tyFv name .star, predicate] => some (.tyExists name predicate)
    | .tyModel, [.tyFv name .star, predicate] => some (.model name predicate)
    | .primFam kind symbol, [] => some (.primFam kind symbol)
    | .primTm symbol, [] => some (.primTm symbol)
    | .tmVar name, [type] => some (.tmFv name type)
    | .tmApp, [function, argument] => some (.app function argument)
    | .tmAbs, [.tmFv name domain, body] => some (.lam name domain body)
    | .tmLet, [.tmFv name domain, value, body] =>
        some (.app (.lam name domain body) value)
    | .tmBool value, [] => some (.bool value)
    | .tmTrue, [] => some (.bool true)
    | .tmFalse, [] => some (.bool false)
    | .tmNot, [proposition] => some (not proposition)
    | .tmAnd functionName, [left, right] => some (and functionName left right)
    | .tmOr functionName, [left, right] => some (or functionName left right)
    | .tmEq, [type, left, right] => some (.eq type left right)
    | .tmEps, [type, predicate] => some (.eps type predicate)
    | .tmQuotAbs, [carrier, .tmFv name _, predicate, value] =>
        some (.abs carrier name predicate value)
    | .tmQuotRep, [carrier, .tmFv name _, predicate, value] =>
        some (.rep carrier name predicate value)
    | _, _ => none

/-- Elaborate one checked node.  Ill-sorted children are rejected after raw
syntax reconstruction. -/
def elaborate (forest : ι → Option (HolE Sig Name)) (node : Node Sig Name ι) :
    Option (HolE Sig Name) := do
  let expression ← elaborateSyntax forest node
  if (Unsorted.infer expression).isSome then some expression else none

end Node

instance : NodeLike (HolE Sig Name) ι (HolE Sig Name) where
  get _ expression := some expression

instance : NodeLike (Node Sig Name ι) ι (HolE Sig Name) where
  get := Node.elaborate

/-- A node explicitly requesting raw syntax elaboration rather than sort
checking. -/
structure SyntaxNode (Sig : Signature.{u}) (Name : Type) (ι : Type w) where
  node : Node Sig Name ι

instance : NodeLike (SyntaxNode Sig Name ι) ι (HolE Sig Name) where
  get forest node := Node.elaborateSyntax forest node.node

/-- Literal `(tag, children)` rows are interchangeable with `Node`. -/
instance : NodeLike (Tag Sig Name × List ι) ι (HolE Sig Name) where
  get forest row := Node.elaborate forest ⟨row.1, row.2⟩

/-- A forest in which the half-open interval `[offset, offset + length)` is absent. -/
def Forest.mask (forest : Forest Nat α) (offset length : Nat) : Forest Nat α where
  get index := if offset ≤ index ∧ index < offset + length then none else forest index

/-- Override a single forest index. -/
def Forest.set (forest : Forest Nat α) (index : Nat) (value : Option α) : Forest Nat α where
  get wanted := if wanted = index then value else forest wanted

/-- Elaborate a dense list from left to right.  The arena interval is masked
before elaboration, so forward references cannot accidentally fall through to
an identically-numbered tree in the underlying forest. -/
def elaborateList [NodeLike N Nat α] (forest : Forest Nat α) (nodes : List N)
    (offset : Nat) : List (Option α) :=
  let base := forest.mask offset nodes.length
  go base offset nodes
where
  go (current : Forest Nat α) (index : Nat) : List N → List (Option α)
    | [] => []
    | node :: rest =>
        let value := NodeLike.elaborate current node
        value :: go (current.set index value) (index + 1) rest

/-- The forest induced by a dense arena.  Indices outside the arena interval
are delegated to the underlying forest. -/
def elaborateForest [NodeLike N Nat α] (forest : Forest Nat α) (nodes : List N)
    (offset : Nat) : Forest Nat α :=
  let values := elaborateList forest nodes offset
  { get := fun index =>
      if offset ≤ index ∧ index < offset + nodes.length then
        (values[index - offset]?).join
      else forest index }

section Examples

variable (Sig : Signature) (Name : Type) (name : Name)

/-- An abstraction whose binder reference is not a term-variable node fails. -/
example : Node.elaborate (Sig := Sig) (Name := Name)
    (fun _ : Nat => some (.bool true)) ⟨.tmAbs, [0, 0]⟩ = none := rfl

/-- A dense interval shadows the same indices in the underlying forest. -/
example : elaborateList
    (⟨fun _ => some (.bool false)⟩ : Forest Nat (HolE Sig Name))
    ([none] : List (Option (HolE Sig Name))) 3 = [none] := rfl

/-- The induced forest delegates indices outside its dense interval. -/
example : (elaborateForest
    (⟨fun _ => some (.bool false)⟩ : Forest Nat (HolE Sig Name))
    ([none] : List (Option (HolE Sig Name))) 3) 2 = some (.bool false) := rfl

end Examples

end Nucleus.HolE.Named.Unsorted.Dense
