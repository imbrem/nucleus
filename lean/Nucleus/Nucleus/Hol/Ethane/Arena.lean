import Nucleus.Hol.Ethane.Syntax

/-!
# Binary dense arenas for Ethane

Every recursive arena row contains at most two references.  Structural `pair`
rows package the operands of constructors such as type application and term
equality which otherwise need more than two recursive fields.  Pairs and kind
rows are arena infrastructure; decoding exposes only an Ethane `Syn` root.

Rows use absolute natural-number references and are elaborated from left to
right.  A forward, dangling, or sort-inappropriate reference makes that row
invalid without invalidating unrelated later rows.
-/

namespace Nucleus.Hol.Ethane.Arena

universe u
set_option relaxedAutoImplicit true

/-- Values visible while an arena is elaborated. -/
inductive Value (Sig : Signature.{u}) (Name : Type) where
  | syntax (expression : Syn Sig Name)
  | kind (value : Kind)
  | pair (left right : Value Sig Name)

/-- One dense arena row.  Constructors expose at most two recursive indices.
`pair` is the sole structural constructor and never decodes as Ethane syntax. -/
inductive Row (Sig : Signature.{u}) (Name : Type) (ι : Type) where
  | pair (left right : ι)
  | kindStar
  | kindArr (domain codomain : ι)
  | boolTy
  | arr (domain codomain : ι)
  | tyApp (kinds arguments : ι)
  | tyLam (name : Name) (kinds body : ι)
  | tyFv (name : Name) (kind : ι)
  | tyExists (name : Name) (predicate : ι)
  | model (name : Name) (predicate : ι)
  | primFam (symbol : Sig (.kind kind)) (kindNode : ι)
  | primTm (symbol : Sig .tm)
  | tmFv (name : Name) (type : ι)
  | app (function argument : ι)
  | lam (name : Name) (domain body : ι)
  | bool (value : Bool)
  | eq (type operands : ι)
  | eps (type predicate : ι)

namespace Row

/-- Recursive references in wire order. -/
def children : Row Sig Name ι → List ι
  | .pair left right | .kindArr left right | .arr left right |
      .tyApp left right | .app left right | .eq left right | .eps left right =>
      [left, right]
  | .tyLam _ kinds body | .lam _ kinds body => [kinds, body]
  | .tyFv _ kind | .tyExists _ kind | .model _ kind |
      .primFam _ kind | .tmFv _ kind => [kind]
  | .kindStar | .boolTy | .primTm _ | .bool _ => []

/-- Binary arity is enforced by the row datatype. -/
theorem children_length_le_two (row : Row Sig Name ι) : row.children.length ≤ 2 := by
  cases row <;> simp [children]

/-- Change the representation of recursive references. -/
def map (f : ι → κ) : Row Sig Name ι → Row Sig Name κ
  | .pair left right => .pair (f left) (f right)
  | .kindStar => .kindStar
  | .kindArr domain codomain => .kindArr (f domain) (f codomain)
  | .boolTy => .boolTy
  | .arr domain codomain => .arr (f domain) (f codomain)
  | .tyApp kinds arguments => .tyApp (f kinds) (f arguments)
  | .tyLam name kinds body => .tyLam name (f kinds) (f body)
  | .tyFv name kind => .tyFv name (f kind)
  | .tyExists name predicate => .tyExists name (f predicate)
  | .model name predicate => .model name (f predicate)
  | .primFam symbol kind => .primFam symbol (f kind)
  | .primTm symbol => .primTm symbol
  | .tmFv name type => .tmFv name (f type)
  | .app function argument => .app (f function) (f argument)
  | .lam name domain body => .lam name (f domain) (f body)
  | .bool value => .bool value
  | .eq type operands => .eq (f type) (f operands)
  | .eps type predicate => .eps (f type) (f predicate)

/-- Elaborate one row against already available values. -/
def elaborate (forest : ι → Option (Value Sig Name)) :
    Row Sig Name ι → Option (Value Sig Name)
  | .pair left right => return .pair (← forest left) (← forest right)
  | .kindStar => some (.kind .star)
  | .kindArr domain codomain => do
      let domain ← forest domain
      let codomain ← forest codomain
      match domain, codomain with
      | Value.kind domain, Value.kind codomain => some (.kind (.arr domain codomain))
      | _, _ => none
  | .boolTy => some (.syntax .boolTy)
  | .arr domain codomain => do
      let domain ← forest domain
      let codomain ← forest codomain
      match domain, codomain with
      | Value.syntax domain, Value.syntax codomain => some (.syntax (.arr domain codomain))
      | _, _ => none
  | .tyApp kinds arguments => do
      let kinds ← forest kinds
      let arguments ← forest arguments
      match kinds, arguments with
      | Value.pair (Value.kind domain) (Value.kind codomain),
          Value.pair (Value.syntax function) (Value.syntax argument) =>
          some (.syntax (.tyApp domain codomain function argument))
      | _, _ => none
  | .tyLam name kinds body => do
      let kinds ← forest kinds
      let body ← forest body
      match kinds, body with
      | Value.pair (Value.kind domain) (Value.kind codomain), Value.syntax body =>
          some (.syntax (.tyLam domain codomain name body))
      | _, _ => none
  | .tyFv name kind => do
      let kind ← forest kind
      match kind with
      | Value.kind kind => some (.syntax (.tyFv name kind))
      | _ => none
  | .tyExists name predicate => do
      let predicate ← forest predicate
      match predicate with
      | Value.syntax predicate => some (.syntax (.tyExists name predicate))
      | _ => none
  | .model name predicate => do
      let predicate ← forest predicate
      match predicate with
      | Value.syntax predicate => some (.syntax (.model name predicate))
      | _ => none
  | @Row.primFam _ _ _ kind symbol kindNode => do
      let kindNode ← forest kindNode
      match kindNode with
      | Value.kind actual =>
          if equality : actual = kind then
            some (.syntax (.primFam kind (equality ▸ symbol)))
          else none
      | _ => none
  | .primTm symbol => some (.syntax (.primTm symbol))
  | .tmFv name type => do
      let type ← forest type
      match type with
      | Value.syntax type => some (.syntax (.tmFv name type))
      | _ => none
  | .app function argument => do
      let function ← forest function
      let argument ← forest argument
      match function, argument with
      | Value.syntax function, Value.syntax argument => some (.syntax (.app function argument))
      | _, _ => none
  | .lam name domain body => do
      let domain ← forest domain
      let body ← forest body
      match domain, body with
      | Value.syntax domain, Value.syntax body => some (.syntax (.lam name domain body))
      | _, _ => none
  | .bool value => some (.syntax (.bool value))
  | .eq type operands => do
      let type ← forest type
      let operands ← forest operands
      match type, operands with
      | Value.syntax type, Value.pair (Value.syntax left) (Value.syntax right) =>
          some (.syntax (.eq type left right))
      | _, _ => none
  | .eps type predicate => do
      let type ← forest type
      let predicate ← forest predicate
      match type, predicate with
      | Value.syntax type, Value.syntax predicate => some (.syntax (.eps type predicate))
      | _, _ => none

end Row

/-- A raw dense arena plus its public root. -/
structure Rooted (Sig : Signature.{u}) (Name : Type := Nat) where
  rows : List (Row Sig Name Nat)
  root : Nat

namespace Rooted

abbrev Forest (Sig : Signature.{u}) (Name : Type) := Nat → Option (Value Sig Name)

private def emptyForest : Forest Sig Name := fun _ => none

private def set (forest : Forest Sig Name) (index : Nat)
    (value : Option (Value Sig Name)) : Forest Sig Name :=
  fun wanted => if wanted = index then value else forest wanted

/-- Elaborate a suffix at an absolute offset into an existing forest. -/
def elaborateSuffix (forest : Forest Sig Name) (next : Nat) :
    List (Row Sig Name Nat) → Forest Sig Name
  | [] => forest
  | row :: rows =>
      let value := row.elaborate forest
      elaborateSuffix (set forest next value) (next + 1) rows

/-- The partial forest denoted by a self-contained arena. -/
def forest (arena : Rooted Sig Name) : Forest Sig Name :=
  elaborateSuffix emptyForest 0 arena.rows

/-- Elaborate all rows from left to right. -/
def elaborate (arena : Rooted Sig Name) : List (Option (Value Sig Name)) :=
  (List.range arena.rows.length).map arena.forest

/-- Decode the public root only when it elaborates to Ethane syntax. -/
def decode (arena : Rooted Sig Name) : Option (Syn Sig Name) := do
  let value ← arena.forest arena.root
  match value with
  | Value.syntax expression => some expression
  | Value.kind _ | Value.pair _ _ => none

end Rooted

namespace Encoder

/-- State of the absolute-index postorder encoder. -/
structure State (Sig : Signature.{u}) (Name : Type) where
  next : Nat
  rows : List (Row Sig Name Nat)

abbrev M (Sig : Signature.{u}) (Name : Type) := StateM (State Sig Name)

private def emit (row : Row Sig Name Nat) : M Sig Name Nat :=
  fun state =>
    (state.next, ⟨state.next + 1, state.rows ++ [row]⟩)

private def unary (child : M Sig Name Nat)
    (row : Nat → Row Sig Name Nat) : M Sig Name Nat := do
  let child ← child
  emit (row child)

private def binary (left right : M Sig Name Nat)
    (row : Nat → Nat → Row Sig Name Nat) : M Sig Name Nat := do
  let left ← left
  let right ← right
  emit (row left right)

def encodeKind : Kind → M Sig Name Nat
  | .star => emit .kindStar
  | .arr domain codomain =>
      binary (encodeKind domain) (encodeKind codomain) .kindArr

/-- Encode unsorted Ethane syntax in postorder. -/
def encode : Syn Sig Name → M Sig Name Nat
  | .boolTy => emit .boolTy
  | .arr domain codomain => binary (encode domain) (encode codomain) .arr
  | .tyApp domain codomain function argument =>
      binary
        (binary (encodeKind domain) (encodeKind codomain) .pair)
        (binary (encode function) (encode argument) .pair)
        .tyApp
  | .tyLam domain codomain name body =>
      binary (binary (encodeKind domain) (encodeKind codomain) .pair)
        (encode body) (.tyLam name)
  | .tyFv name kind => unary (encodeKind kind) (.tyFv name)
  | .tyExists name predicate => unary (encode predicate) (.tyExists name)
  | .model name predicate => unary (encode predicate) (.model name)
  | .primFam kind symbol => unary (encodeKind kind) (.primFam symbol)
  | .primTm symbol => emit (.primTm symbol)
  | .tmFv name type => unary (encode type) (.tmFv name)
  | .app function argument => binary (encode function) (encode argument) .app
  | .lam name domain body => binary (encode domain) (encode body) (.lam name)
  | .bool value => emit (.bool value)
  | .eq type left right =>
      binary (encode type) (binary (encode left) (encode right) .pair) .eq
  | .eps type predicate => binary (encode type) (encode predicate) .eps

@[simp] private theorem bind_apply (action : M Sig Name α)
    (next : α → M Sig Name β) (state : State Sig Name) :
    (action >>= next) state =
      let (value, state) := action state
      next value state := rfl

private theorem unary_root (child : M Sig Name Nat)
    (row : Nat → Row Sig Name Nat) (state : State Sig Name) :
    (unary child row state).1 + 1 = (unary child row state).2.next := by
  simp only [unary, bind_apply]
  cases child state
  rfl

private theorem binary_root (left right : M Sig Name Nat)
    (row : Nat → Nat → Row Sig Name Nat) (state : State Sig Name) :
    (binary left right row state).1 + 1 = (binary left right row state).2.next := by
  simp only [binary, bind_apply]
  cases left state with
  | mk leftIndex leftState =>
      cases right leftState
      rfl

theorem encodeKind_root (kind : Kind) (state : State Sig Name) :
    (encodeKind kind state).1 + 1 = (encodeKind kind state).2.next := by
  cases kind with
  | star => rfl
  | arr domain codomain => exact binary_root _ _ _ state

theorem encode_root (expression : Syn Sig Name) (state : State Sig Name) :
    (encode expression state).1 + 1 = (encode expression state).2.next := by
  cases expression <;>
    first | rfl | apply unary_root | apply binary_root

theorem elaborateSuffix_append (forest : Rooted.Forest Sig Name) (next : Nat)
    (initial suffix : List (Row Sig Name Nat)) :
    Rooted.elaborateSuffix forest next (initial ++ suffix) =
      Rooted.elaborateSuffix (Rooted.elaborateSuffix forest next initial)
        (next + initial.length) suffix := by
  induction initial generalizing forest next with
  | nil => rfl
  | cons row initial ih =>
      simp only [List.cons_append, Rooted.elaborateSuffix, List.length_cons]
      rw [ih]
      congr 1
      omega

theorem elaborateSuffix_of_lt (forest : Rooted.Forest Sig Name) (next : Nat)
    (rows : List (Row Sig Name Nat)) (index : Nat) (below : index < next) :
    Rooted.elaborateSuffix forest next rows index = forest index := by
  induction rows generalizing forest next with
  | nil => rfl
  | cons row rows ih =>
      simp only [Rooted.elaborateSuffix]
      rw [ih (Rooted.set forest next (row.elaborate forest)) (next + 1) (by omega)]
      simp [Rooted.set, Nat.ne_of_lt below]

/-- Compositional semantic contract for an encoder action. -/
def Encodes (action : M Sig Name Nat) (output : Value Sig Name) : Prop :=
  ∀ (state : State Sig Name) (forest : Rooted.Forest Sig Name),
    ∃ suffix : List (Row Sig Name Nat),
      (action state).2.rows = state.rows ++ suffix ∧
      (action state).2.next = state.next + suffix.length ∧
      (action state).1 + 1 = (action state).2.next ∧
      Rooted.elaborateSuffix forest state.next suffix (action state).1 = some output

private theorem encodes_emit (row : Row Sig Name Nat) (output : Value Sig Name)
    (elaborates : ∀ forest : Rooted.Forest Sig Name,
      row.elaborate forest = some output) : Encodes (emit row) output := by
  intro state forest
  refine ⟨[row], by simp [emit], by simp [emit], rfl, ?_⟩
  simp [emit, Rooted.elaborateSuffix, Rooted.set, elaborates]

private theorem encodes_unary
    (childOutput output : Value Sig Name) (child : M Sig Name Nat)
    (row : Nat → Row Sig Name Nat) (childCorrect : Encodes child childOutput)
    (elaborates : ∀ (forest : Rooted.Forest Sig Name) childIndex,
      forest childIndex = some childOutput →
      (row childIndex).elaborate forest = some output) :
    Encodes (unary child row) output := by
  intro state forest
  cases childEncoded : child state with
  | mk childIndex childState =>
      obtain ⟨childRows, childRowsEq, childNextEq, childRootEq, childLookup⟩ :=
        childCorrect state forest
      rw [childEncoded] at childRowsEq childNextEq childRootEq childLookup
      simp at childRowsEq childNextEq childRootEq childLookup
      let childForest := Rooted.elaborateSuffix forest state.next childRows
      let parent := row childIndex
      refine ⟨childRows ++ [parent], ?_, ?_, ?_, ?_⟩
      · simp only [unary, bind_apply, childEncoded, emit]
        rw [childRowsEq]
        simp [parent, List.append_assoc]
      · simp only [unary, bind_apply, childEncoded, emit, List.length_append,
          List.length_singleton]
        omega
      · exact unary_root child row state
      · rw [elaborateSuffix_append]
        simp only [unary, bind_apply, childEncoded, emit]
        rw [show state.next + childRows.length = childState.next by omega]
        change Rooted.elaborateSuffix childForest childState.next [parent]
          childState.next = some output
        simp [Rooted.elaborateSuffix, Rooted.set, parent,
          elaborates childForest childIndex childLookup]

private theorem encodes_binary
    (leftOutput rightOutput output : Value Sig Name)
    (left right : M Sig Name Nat) (row : Nat → Nat → Row Sig Name Nat)
    (leftCorrect : Encodes left leftOutput) (rightCorrect : Encodes right rightOutput)
    (elaborates : ∀ (forest : Rooted.Forest Sig Name) leftIndex rightIndex,
      forest leftIndex = some leftOutput → forest rightIndex = some rightOutput →
      (row leftIndex rightIndex).elaborate forest = some output) :
    Encodes (binary left right row) output := by
  intro state forest
  cases leftEncoded : left state with
  | mk leftIndex leftState =>
      obtain ⟨leftRows, leftRowsEq, leftNextEq, leftRootEq, leftLookup⟩ :=
        leftCorrect state forest
      rw [leftEncoded] at leftRowsEq leftNextEq leftRootEq leftLookup
      simp at leftRowsEq leftNextEq leftRootEq leftLookup
      let leftForest := Rooted.elaborateSuffix forest state.next leftRows
      cases rightEncoded : right leftState with
      | mk rightIndex rightState =>
          obtain ⟨rightRows, rightRowsEq, rightNextEq, rightRootEq, rightLookup⟩ :=
            rightCorrect leftState leftForest
          rw [rightEncoded] at rightRowsEq rightNextEq rightRootEq rightLookup
          simp at rightRowsEq rightNextEq rightRootEq rightLookup
          let rightForest := Rooted.elaborateSuffix leftForest leftState.next rightRows
          have leftBelow : leftIndex < leftState.next := by omega
          have leftLookup' : rightForest leftIndex = some leftOutput :=
            (elaborateSuffix_of_lt leftForest leftState.next rightRows leftIndex
              leftBelow).trans leftLookup
          let parent := row leftIndex rightIndex
          refine ⟨leftRows ++ rightRows ++ [parent], ?_, ?_, ?_, ?_⟩
          · simp only [binary, bind_apply, leftEncoded, rightEncoded, emit]
            rw [rightRowsEq, leftRowsEq]
            simp [parent, List.append_assoc]
          · simp only [binary, bind_apply, leftEncoded, rightEncoded, emit,
              List.length_append, List.length_singleton]
            omega
          · exact binary_root left right row state
          · rw [elaborateSuffix_append, elaborateSuffix_append]
            simp only [List.length_append]
            simp only [binary, bind_apply, leftEncoded, rightEncoded, emit]
            rw [show state.next + leftRows.length = leftState.next by omega]
            rw [show state.next + (leftRows.length + rightRows.length) =
              leftState.next + rightRows.length by omega]
            change Rooted.elaborateSuffix rightForest
              (leftState.next + rightRows.length) [parent]
              rightState.next = some output
            rw [← rightNextEq]
            simp [Rooted.elaborateSuffix, Rooted.set, parent,
              elaborates rightForest leftIndex rightIndex leftLookup' rightLookup]

theorem encodeKind_correct (kind : Kind) :
    Encodes (encodeKind (Sig := Sig) (Name := Name) kind) (.kind kind) := by
  induction kind with
  | star =>
      apply encodes_emit
      intro forest
      rfl
  | arr domain codomain domainIH codomainIH =>
      apply encodes_binary (.kind domain) (.kind codomain) (.kind (.arr domain codomain))
        _ _ _ domainIH codomainIH
      intro forest domainIndex codomainIndex domainLookup codomainLookup
      simp [Row.elaborate, domainLookup, codomainLookup]

theorem encode_correct (expression : Syn Sig Name) :
    Encodes (encode expression) (.syntax expression) := by
  induction expression with
  | boolTy => exact encodes_emit _ _ fun _ => rfl
  | arr domain codomain domainIH codomainIH =>
      apply encodes_binary (.syntax domain) (.syntax codomain)
        (.syntax (.arr domain codomain)) _ _ _ domainIH codomainIH
      intro forest domainIndex codomainIndex domainLookup codomainLookup
      simp [Row.elaborate, domainLookup, codomainLookup]
  | tyApp domain codomain function argument functionIH argumentIH =>
      have kinds : Encodes (Sig := Sig) (Name := Name)
          (binary (encodeKind (Sig := Sig) (Name := Name) domain)
            (encodeKind codomain) .pair)
          (Value.pair (Sig := Sig) (Name := Name) (.kind domain) (.kind codomain)) := by
        apply encodes_binary (.kind domain) (.kind codomain)
          (.pair (.kind domain) (.kind codomain)) _ _ _
          (encodeKind_correct domain) (encodeKind_correct codomain)
        intro forest domainIndex codomainIndex domainLookup codomainLookup
        simp [Row.elaborate, domainLookup, codomainLookup]
      have arguments : Encodes
          (binary (encode function) (encode argument) .pair)
          (.pair (.syntax function) (.syntax argument)) := by
        apply encodes_binary (.syntax function) (.syntax argument)
          (.pair (.syntax function) (.syntax argument)) _ _ _ functionIH argumentIH
        intro forest functionIndex argumentIndex functionLookup argumentLookup
        simp [Row.elaborate, functionLookup, argumentLookup]
      apply encodes_binary
        (.pair (.kind domain) (.kind codomain))
        (.pair (.syntax function) (.syntax argument))
        (.syntax (.tyApp domain codomain function argument)) _ _ _ kinds arguments
      intro forest kindsIndex argumentsIndex kindsLookup argumentsLookup
      simp [Row.elaborate, kindsLookup, argumentsLookup]
  | tyLam domain codomain name body bodyIH =>
      have kinds : Encodes (Sig := Sig) (Name := Name)
          (binary (encodeKind (Sig := Sig) (Name := Name) domain)
            (encodeKind codomain) .pair)
          (Value.pair (Sig := Sig) (Name := Name) (.kind domain) (.kind codomain)) := by
        apply encodes_binary (.kind domain) (.kind codomain)
          (.pair (.kind domain) (.kind codomain)) _ _ _
          (encodeKind_correct domain) (encodeKind_correct codomain)
        intro forest domainIndex codomainIndex domainLookup codomainLookup
        simp [Row.elaborate, domainLookup, codomainLookup]
      apply encodes_binary (.pair (.kind domain) (.kind codomain)) (.syntax body)
        (.syntax (.tyLam domain codomain name body)) _ _ _ kinds bodyIH
      intro forest kindsIndex bodyIndex kindsLookup bodyLookup
      simp [Row.elaborate, kindsLookup, bodyLookup]
  | tyFv name kind =>
      apply encodes_unary (.kind kind) (.syntax (.tyFv name kind)) _ _
        (encodeKind_correct kind)
      intro forest kindIndex kindLookup
      simp [Row.elaborate, kindLookup]
  | tyExists name predicate predicateIH =>
      apply encodes_unary (.syntax predicate) (.syntax (.tyExists name predicate))
        _ _ predicateIH
      intro forest predicateIndex predicateLookup
      simp [Row.elaborate, predicateLookup]
  | model name predicate predicateIH =>
      apply encodes_unary (.syntax predicate) (.syntax (.model name predicate))
        _ _ predicateIH
      intro forest predicateIndex predicateLookup
      simp [Row.elaborate, predicateLookup]
  | primFam kind symbol =>
      apply encodes_unary (.kind kind) (.syntax (.primFam kind symbol)) _ _
        (encodeKind_correct kind)
      intro forest kindIndex kindLookup
      simp [Row.elaborate, kindLookup]
  | primTm symbol => exact encodes_emit _ _ fun _ => rfl
  | tmFv name type typeIH =>
      apply encodes_unary (.syntax type) (.syntax (.tmFv name type)) _ _ typeIH
      intro forest typeIndex typeLookup
      simp [Row.elaborate, typeLookup]
  | app function argument functionIH argumentIH =>
      apply encodes_binary (.syntax function) (.syntax argument)
        (.syntax (.app function argument)) _ _ _ functionIH argumentIH
      intro forest functionIndex argumentIndex functionLookup argumentLookup
      simp [Row.elaborate, functionLookup, argumentLookup]
  | lam name domain body domainIH bodyIH =>
      apply encodes_binary (.syntax domain) (.syntax body)
        (.syntax (.lam name domain body)) _ _ _ domainIH bodyIH
      intro forest domainIndex bodyIndex domainLookup bodyLookup
      simp [Row.elaborate, domainLookup, bodyLookup]
  | bool value => exact encodes_emit _ _ fun _ => rfl
  | eq type left right typeIH leftIH rightIH =>
      have operands : Encodes (binary (encode left) (encode right) .pair)
          (.pair (.syntax left) (.syntax right)) := by
        apply encodes_binary (.syntax left) (.syntax right)
          (.pair (.syntax left) (.syntax right)) _ _ _ leftIH rightIH
        intro forest leftIndex rightIndex leftLookup rightLookup
        simp [Row.elaborate, leftLookup, rightLookup]
      apply encodes_binary (.syntax type) (.pair (.syntax left) (.syntax right))
        (.syntax (.eq type left right)) _ _ _ typeIH operands
      intro forest typeIndex operandsIndex typeLookup operandsLookup
      simp [Row.elaborate, typeLookup, operandsLookup]
  | eps type predicate typeIH predicateIH =>
      apply encodes_binary (.syntax type) (.syntax predicate)
        (.syntax (.eps type predicate)) _ _ _ typeIH predicateIH
      intro forest typeIndex predicateIndex typeLookup predicateLookup
      simp [Row.elaborate, typeLookup, predicateLookup]

/-- Encode one expression into a self-contained zero-based arena. -/
def run (expression : Syn Sig Name) : Rooted Sig Name :=
  let (root, state) := encode expression ⟨0, []⟩
  ⟨state.rows, root⟩

theorem run_forest_root (expression : Syn Sig Name) :
    (run expression).forest (run expression).root = some (.syntax expression) := by
  let initial : State Sig Name := ⟨0, []⟩
  obtain ⟨suffix, rowsEq, nextEq, rootEq, lookup⟩ :=
    encode_correct expression initial (Rooted.emptyForest (Sig := Sig) (Name := Name))
  simp [initial] at rowsEq lookup
  change Rooted.elaborateSuffix Rooted.emptyForest 0
      (encode expression initial).2.rows (encode expression initial).1 =
    some (.syntax expression)
  rw [rowsEq]
  simpa using lookup

/-- Encoding followed by arena elaboration is the identity. -/
@[simp] theorem decode_run (expression : Syn Sig Name) :
    (run expression).decode = some expression := by
  simp only [Rooted.decode]
  rw [run_forest_root]
  rfl

end Encoder

end Nucleus.Hol.Ethane.Arena
