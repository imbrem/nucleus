import Nucleus.HolLN.Json
import Nucleus.HolLN.Scope

/-!
# Backward-reference arrays for locally nameless HOL

This module separates an untrusted, storage-friendly array from the small
validated representation used by the HOL decoder.

`RawArena Base` is an ordinary `Array (Row Base Nat)`.  Its natural-number
children may point anywhere.  `Arena Base n` is a snoc list of exactly `n`
rows, where the row at position `i` has children in `Fin i`.  Consequently all
children point strictly backwards, by construction.  Validation is the only
bridge from raw indices to those trusted references.

Decoding a selected root is indexed by the expected sort and binder depth,
just like the JSON tree decoder.  Recursion follows a structurally smaller
arena prefix, so it needs no fuel parameter.
-/

namespace Nucleus.HolLN.Array

universe u v w

/-- A single array row. `Ref` selects the physical/reference representation. -/
inductive Row (Base : Type u) (Ref : Type v) : Type (max u v) where
  | tyBase (kind : Kind) (name : Base)
  | tyBool
  | tyInd
  | tyArr (domain codomain : Ref)
  | tyApp (domain codomain : Kind) (function argument : Ref)
  | tySub (carrier predicate : Ref)
  | tmBv (index : Nat)
  | tmFv (name : Nat) (type : Ref)
  | tmApp (function argument : Ref)
  | tmLam (domain body : Ref)
  | tmBool (value : Bool)
  | tmZero
  | tmSucc (value : Ref)
  | tmEq (type left right : Ref)
  | tmEps (type predicate : Ref)
  | tmAbs (carrier predicate value : Ref)
  | tmRep (carrier predicate value : Ref)
  deriving Repr

/-- Apply a representation change uniformly to every child reference. -/
def Row.map {Base : Type u} {R : Type v} {S : Type w} (f : R → S) :
    Row Base R → Row Base S
  | .tyBase kind name => .tyBase kind name
  | .tyBool => .tyBool
  | .tyInd => .tyInd
  | .tyArr domain codomain => .tyArr (f domain) (f codomain)
  | .tyApp domain codomain function argument => .tyApp domain codomain (f function) (f argument)
  | .tySub carrier predicate => .tySub (f carrier) (f predicate)
  | .tmBv index => .tmBv index
  | .tmFv name type => .tmFv name (f type)
  | .tmApp function argument => .tmApp (f function) (f argument)
  | .tmLam domain body => .tmLam (f domain) (f body)
  | .tmBool value => .tmBool value
  | .tmZero => .tmZero
  | .tmSucc value => .tmSucc (f value)
  | .tmEq type left right => .tmEq (f type) (f left) (f right)
  | .tmEps type predicate => .tmEps (f type) (f predicate)
  | .tmAbs carrier predicate value => .tmAbs (f carrier) (f predicate) (f value)
  | .tmRep carrier predicate value => .tmRep (f carrier) (f predicate) (f value)

/-- Child references in their stable, constructor-specific order. -/
def Row.children {Base : Type u} {Ref : Type v} : Row Base Ref → List Ref
  | .tyBase _ _ | .tyBool | .tyInd | .tmBv _ | .tmBool _ | .tmZero => []
  | .tmFv _ type => [type]
  | .tmSucc value => [value]
  | .tyArr domain codomain | .tyApp _ _ domain codomain |
      .tySub domain codomain | .tmApp domain codomain |
      .tmLam domain codomain | .tmEps domain codomain => [domain, codomain]
  | .tmEq type left right | .tmAbs type left right | .tmRep type left right =>
      [type, left, right]

@[simp] theorem Row.children_map {Base : Type u} {R : Type v} {S : Type w} (f : R → S)
    (row : Row Base R) : (row.map f).children = row.children.map f := by
  cases row <;> rfl

/-- Storage representation: a flat array with untrusted natural-number links. -/
abbrev RawArena (Base : Type u) := Array (Row Base Nat)

/-- A validated arena. In `.snoc prefix row`, every child of `row` belongs to
`prefix`; hence cycles and forward references are unrepresentable. -/
inductive Arena (Base : Type u) : Nat → Type u where
  | nil : Arena Base 0
  | snoc {n : Nat} (prior : Arena Base n) (row : Row Base (Fin n)) : Arena Base (n + 1)

/-- Package an arena whose validated length is discovered dynamically. -/
structure SomeArena (Base : Type u) where
  size : Nat
  arena : Arena Base size

/-- An ergonomic package for a HOL LN value whose sort and binder depth are
discovered while elaborating an array. -/
structure Packed (Base : Type u) where
  sort : HolSort
  depth : Nat
  value : Hol Base sort depth
  deriving Repr

/-- A packed term, useful after the sort has been projected successfully. -/
structure PackedTm (Base : Type u) where
  depth : Nat
  value : Tm Base depth
  deriving Repr

def Packed.ofFam {Base : Type u} {kind : Kind} (family : Fam Base kind) : Packed Base :=
  ⟨.kind kind, 0, family⟩

def Packed.ofTy {Base : Type u} (type : Ty Base) : Packed Base := Packed.ofFam type

def Packed.ofTm {Base : Type u} {depth : Nat} (term : Tm Base depth) : Packed Base :=
  ⟨.tm, depth, term⟩

/-- Project a packed entry as a type. -/
def Packed.toTy? {Base : Type u} : Packed Base → Option (Ty Base)
  | ⟨.kind .star, 0, type⟩ => some type
  | _ => none

/-- Project a packed entry as a term while retaining its binder depth. -/
def Packed.toTm? {Base : Type u} : Packed Base → Option (PackedTm Base)
  | ⟨.tm, depth, term⟩ => some ⟨depth, term⟩
  | _ => none

@[simp] theorem Packed.toTy?_ofTy {Base : Type u} (type : Ty Base) :
    (Packed.ofTy type).toTy? = some type := rfl

@[simp] theorem Packed.toTm?_ofTm {Base : Type u} {depth : Nat} (term : Tm Base depth) :
    (Packed.ofTm term).toTm? = some ⟨depth, term⟩ := rfl

/-- Raise a term to any larger binder depth. -/
def PackedTm.raiseTo {Base : Type u} (term : PackedTm Base) (target : Nat)
    (scope : term.depth ≤ target) : Tm Base target :=
  rename (Fin.castLE scope) term.value

private def PackedTm.align2 {Base : Type u} (left right : PackedTm Base)
    (build : {depth : Nat} → Tm Base depth → Tm Base depth → Tm Base depth) : Packed Base :=
  let depth := max left.depth right.depth
  Packed.ofTm (build (left.raiseTo depth (Nat.le_max_left _ _))
    (right.raiseTo depth (Nat.le_max_right _ _)))

private def PackedTm.align3 {Base : Type u} (first second third : PackedTm Base)
    (build : {depth : Nat} → Tm Base depth → Tm Base depth → Tm Base depth → Tm Base depth) :
    Packed Base :=
  let depth := max first.depth (max second.depth third.depth)
  Packed.ofTm (build
    (first.raiseTo depth (Nat.le_max_left _ _))
    (second.raiseTo depth (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)))
    (third.raiseTo depth (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))))

private def validateRow {Base : Type u} (n : Nat) :
    Row Base Nat → Option (Row Base (Fin n))
  | .tyBase kind name => some (.tyBase kind name)
  | .tyBool => some .tyBool
  | .tyInd => some .tyInd
  | .tyArr domain codomain =>
      match ref domain, ref codomain with
      | some domain, some codomain => some (.tyArr domain codomain)
      | _, _ => none
  | .tyApp domain codomain function argument =>
      match ref function, ref argument with
      | some function, some argument => some (.tyApp domain codomain function argument)
      | _, _ => none
  | .tySub carrier predicate =>
      match ref carrier, ref predicate with
      | some carrier, some predicate => some (.tySub carrier predicate)
      | _, _ => none
  | .tmBv index => some (.tmBv index)
  | .tmFv name type =>
      match ref type with
      | some type => some (.tmFv name type)
      | none => none
  | .tmApp function argument =>
      match ref function, ref argument with
      | some function, some argument => some (.tmApp function argument)
      | _, _ => none
  | .tmLam domain body =>
      match ref domain, ref body with
      | some domain, some body => some (.tmLam domain body)
      | _, _ => none
  | .tmBool value => some (.tmBool value)
  | .tmZero => some .tmZero
  | .tmSucc value => (ref value).map .tmSucc
  | .tmEq type left right =>
      match ref type, ref left, ref right with
      | some type, some left, some right => some (.tmEq type left right)
      | _, _, _ => none
  | .tmEps type predicate =>
      match ref type, ref predicate with
      | some type, some predicate => some (.tmEps type predicate)
      | _, _ => none
  | .tmAbs carrier predicate value =>
      match ref carrier, ref predicate, ref value with
      | some carrier, some predicate, some value => some (.tmAbs carrier predicate value)
      | _, _, _ => none
  | .tmRep carrier predicate value =>
      match ref carrier, ref predicate, ref value with
      | some carrier, some predicate, some value => some (.tmRep carrier predicate value)
      | _, _, _ => none
where
  ref (child : Nat) : Option (Fin n) :=
    if h : child < n then some ⟨child, h⟩ else none

private def validateList {Base : Type u} :
    (rows : List (Row Base Nat)) → {n : Nat} → Arena Base n → Option (SomeArena Base)
  | [], n, prior => some ⟨n, prior⟩
  | row :: rows, n, prior => do
      let checked ← validateRow n row
      validateList rows (.snoc prior checked)

/-- Check all raw references in one left-to-right pass. -/
def RawArena.validate {Base : Type u} (rows : RawArena Base) : Option (SomeArena Base) :=
  validateList rows.toList .nil

private def elaborateRow {Base : Type u} {n : Nat}
    (decode : {sort : HolSort} → {depth : Nat} → Fin n → Option (Hol Base sort depth)) :
    Row Base (Fin n) → (sort : HolSort) → (depth : Nat) → Option (Hol Base sort depth)
  | .tyBase actual name, .kind expected, 0 =>
      if equality : actual = expected then some (equality ▸ .base name) else none
  | .tyBool, .kind .star, 0 => some .boolTy
  | .tyInd, .kind .star, 0 => some .natTy
  | .tyArr domain codomain, .kind .star, 0 =>
      return .arr (← decode domain) (← decode codomain)
  | .tyApp domain codomain function argument, .kind expected, 0 =>
      if equality : codomain = expected then
        return equality ▸ .tyApp (← decode (sort := .kind (.arr domain codomain)) function)
          (← decode (sort := .kind domain) argument)
      else none
  | .tySub carrier predicate, .kind .star, 0 =>
      return .sub (← decode carrier) (← decode (depth := 1) predicate)
  | .tmBv index, .tm, depth =>
      if h : index < depth then some (.bv ⟨index, h⟩) else none
  | .tmFv name type, .tm, _ => return .fv name (← decode (sort := .kind .star) type)
  | .tmApp function argument, .tm, depth =>
      return .app (← decode (depth := depth) function) (← decode (depth := depth) argument)
  | .tmLam domain body, .tm, depth =>
      return .lam (← decode domain) (← decode (depth := depth + 1) body)
  | .tmBool value, .tm, _ => some (.bool value)
  | .tmZero, .tm, _ => some .zero
  | .tmSucc value, .tm, depth => return .succ (← decode (depth := depth) value)
  | .tmEq type left right, .tm, depth =>
      return .eq (← decode type) (← decode (depth := depth) left)
        (← decode (depth := depth) right)
  | .tmEps type predicate, .tm, depth =>
      return .eps (← decode type) (← decode (depth := depth) predicate)
  | .tmAbs carrier predicate value, .tm, depth =>
      return .abs (← decode carrier) (← decode (depth := 1) predicate)
        (← decode (depth := depth) value)
  | .tmRep carrier predicate value, .tm, depth =>
      return .rep (← decode carrier) (← decode (depth := 1) predicate)
        (← decode (depth := depth) value)
  | _, _, _ => none

/-- Decode a root from a validated arena. The recursive call always receives
the strict prefix containing the selected row's children. -/
def Arena.decodeOpen {Base : Type u} : {n : Nat} → Arena Base n →
    (root : Fin n) → (sort : HolSort) → (depth : Nat) → Option (Hol Base sort depth)
  | _ + 1, .snoc prior row, root, sort, depth =>
      Fin.lastCases
        (elaborateRow
          (fun {sort} {depth} child => Arena.decodeOpen prior child sort depth)
          row sort depth)
        (fun child => Arena.decodeOpen prior child sort depth)
        root

/-- Decode a closed type root. -/
def Arena.decodeTy {Base : Type u} {n : Nat} (arena : Arena Base n) (root : Fin n) :
    Option (Ty Base) := arena.decodeOpen root (.kind .star) 0

/-- Decode a closed term root. -/
def Arena.decodeTm {Base : Type u} {n : Nat} (arena : Arena Base n) (root : Fin n) :
    Option (ClosedTm Base) := arena.decodeOpen root .tm 0

/-- Validate a raw array and decode a selected open root. -/
def RawArena.decodeOpen {Base : Type u} (rows : RawArena Base) (root : Nat)
    (sort : HolSort) (depth : Nat) : Option (Hol Base sort depth) := do
  let checked ← rows.validate
  if h : root < checked.size then
    checked.arena.decodeOpen ⟨root, h⟩ sort depth
  else none

/-- Validate a raw array and decode a selected closed type root. -/
def RawArena.decodeTy {Base : Type u} (rows : RawArena Base) (root : Nat) : Option (Ty Base) :=
  rows.decodeOpen root (.kind .star) 0

/-- Validate a raw array and decode a selected closed term root. -/
def RawArena.decodeTm {Base : Type u} (rows : RawArena Base) (root : Nat) :
    Option (ClosedTm Base) := rows.decodeOpen root .tm 0

private def packedTy {Base : Type u} (get : Nat → Option (Packed Base)) (index : Nat) :
    Option (Ty Base) := do
  (← get index).toTy?

private def packedFam {Base : Type u} (get : Nat → Option (Packed Base))
    (kind : Kind) (index : Nat) : Option (Fam Base kind) := do
  let entry ← get index
  match entry with
  | ⟨.kind actual, 0, family⟩ =>
      if equality : actual = kind then some (equality ▸ family) else none
  | _ => none

private def packedTm {Base : Type u} (get : Nat → Option (Packed Base)) (index : Nat) :
    Option (PackedTm Base) := do
  (← get index).toTm?

/-- Elaborate one row from previously elaborated entries. The resulting term
uses the least binder depth required by its children. -/
private def elaboratePackedRow {Base : Type u} (get : Nat → Option (Packed Base)) :
    Row Base Nat → Option (Packed Base)
  | .tyBase kind name => some (Packed.ofFam (.base name : Fam Base kind))
  | .tyBool => some (Packed.ofTy .boolTy)
  | .tyInd => some (Packed.ofTy .natTy)
  | .tyArr domain codomain =>
      return Packed.ofTy (.arr (← packedTy get domain) (← packedTy get codomain))
  | .tyApp domain codomain function argument =>
      return Packed.ofFam (.tyApp (← packedFam get (.arr domain codomain) function)
        (← packedFam get domain argument))
  | .tySub carrier predicate => do
      let carrier ← packedTy get carrier
      let predicate ← packedTm get predicate
      if scope : predicate.depth ≤ 1 then
        some (Packed.ofTy (.sub carrier (predicate.raiseTo 1 scope)))
      else none
  | .tmBv index =>
      some (Packed.ofTm (.bv ⟨index, Nat.lt_succ_self index⟩))
  | .tmFv name type => return Packed.ofTm (.fv name (← packedTy get type) : Tm Base 0)
  | .tmApp function argument => do
      let function ← packedTm get function
      let argument ← packedTm get argument
      some (PackedTm.align2 function argument .app)
  | .tmLam domain body => do
      let domain ← packedTy get domain
      let body ← packedTm get body
      let depth := body.depth.pred
      have scope : body.depth ≤ depth + 1 := by
        dsimp [depth]
        cases body.depth <;> simp
      some (Packed.ofTm (.lam domain (body.raiseTo (depth + 1) scope)))
  | .tmBool value => some (Packed.ofTm (.bool value : Tm Base 0))
  | .tmZero => some (Packed.ofTm (.zero : Tm Base 0))
  | .tmSucc value => do
      let value ← packedTm get value
      some (Packed.ofTm (.succ value.value))
  | .tmEq type left right => do
      let type ← packedTy get type
      let left ← packedTm get left
      let right ← packedTm get right
      some (PackedTm.align2 left right fun left right => .eq type left right)
  | .tmEps type predicate => do
      let type ← packedTy get type
      let predicate ← packedTm get predicate
      some (Packed.ofTm (.eps type predicate.value))
  | .tmAbs carrier predicate value => do
      let carrier ← packedTy get carrier
      let predicate ← packedTm get predicate
      let value ← packedTm get value
      if scope : predicate.depth ≤ 1 then
        some (Packed.ofTm (.abs carrier (predicate.raiseTo 1 scope) value.value))
      else none
  | .tmRep carrier predicate value => do
      let carrier ← packedTy get carrier
      let predicate ← packedTm get predicate
      let value ← packedTm get value
      if scope : predicate.depth ≤ 1 then
        some (Packed.ofTm (.rep carrier (predicate.raiseTo 1 scope) value.value))
      else none

private def elaboratePackedList {Base : Type u} :
    List (Row Base Nat) → Array (Packed Base) → Option (Array (Packed Base))
  | [], entries => some entries
  | row :: rows, entries => do
      let entry ← elaboratePackedRow (fun child => entries[child]?) row
      elaboratePackedList rows (entries.push entry)

/-- Elaborate every row in order. A child is available only after an earlier
row has produced it, so forward references, cycles, and sort mismatches fail. -/
def RawArena.elaborate {Base : Type u} (rows : RawArena Base) : Option (Array (Packed Base)) :=
  elaboratePackedList rows.toList #[]

/-! ## JSON array interchange

Rows use the compact positional form `[tag, payload-or-child, ...]`; an arena
is a JSON array of such rows.  This is intentionally an injection into JSON,
not a claim that every JSON value denotes an arena.
-/

namespace Json

abbrev Tree (Base : Type u) := HolLN.Json.Tree Base

private def string {Base : Type u} (value : String) : Tree Base :=
  .scalar (.string value)

private def nat {Base : Type u} (value : Nat) : Tree Base :=
  .scalar (.nat value)

private def bool {Base : Type u} (value : Bool) : Tree Base :=
  .scalar (.bool value)

private def kind {Base : Type u} (value : Kind) : Tree Base :=
  .scalar (.kind value)

private def base {Base : Type u} (value : Base) : Tree Base :=
  .scalar (.base value)

private def array {Base : Type u} (values : List (Tree Base)) : Tree Base :=
  .list (RawSyn.ofList values)

/-- Encode one parsed row as a compact positional JSON array. -/
def encodeRow {Base : Type u} : Row Base Nat → Tree Base
  | .tyBase familyKind name => array [string "ty.base", kind familyKind, base name]
  | .tyBool => array [string "ty.bool"]
  | .tyInd => array [string "ty.ind"]
  | .tyArr domain codomain => array [string "ty.arr", nat domain, nat codomain]
  | .tyApp domain codomain function argument =>
      array [string "ty.app", kind domain, kind codomain, nat function, nat argument]
  | .tySub carrier predicate => array [string "ty.sub", nat carrier, nat predicate]
  | .tmBv index => array [string "tm.bv", nat index]
  | .tmFv name type => array [string "tm.fv", nat name, nat type]
  | .tmApp function argument => array [string "tm.app", nat function, nat argument]
  | .tmLam domain body => array [string "tm.lam", nat domain, nat body]
  | .tmBool value => array [string "tm.bool", bool value]
  | .tmZero => array [string "tm.zero"]
  | .tmSucc value => array [string "tm.succ", nat value]
  | .tmEq type left right => array [string "tm.eq", nat type, nat left, nat right]
  | .tmEps type predicate => array [string "tm.eps", nat type, nat predicate]
  | .tmAbs carrier predicate value =>
      array [string "tm.abs", nat carrier, nat predicate, nat value]
  | .tmRep carrier predicate value =>
      array [string "tm.rep", nat carrier, nat predicate, nat value]

/-- Parse exactly the canonical positional shape of one row. -/
def decodeRow {Base : Type u} : Tree Base → Option (Row Base Nat)
  | .list values =>
      match values.toList with
      | [.scalar (.string "ty.base"), .scalar (.kind familyKind), .scalar (.base name)] =>
          some (.tyBase familyKind name)
      | [.scalar (.string "ty.bool")] => some .tyBool
      | [.scalar (.string "ty.ind")] => some .tyInd
      | [.scalar (.string "ty.arr"), .scalar (.nat domain), .scalar (.nat codomain)] =>
          some (.tyArr domain codomain)
      | [.scalar (.string "ty.app"), .scalar (.kind domain), .scalar (.kind codomain),
          .scalar (.nat function), .scalar (.nat argument)] =>
          some (.tyApp domain codomain function argument)
      | [.scalar (.string "ty.sub"), .scalar (.nat carrier), .scalar (.nat predicate)] =>
          some (.tySub carrier predicate)
      | [.scalar (.string "tm.bv"), .scalar (.nat index)] => some (.tmBv index)
      | [.scalar (.string "tm.fv"), .scalar (.nat name), .scalar (.nat type)] =>
          some (.tmFv name type)
      | [.scalar (.string "tm.app"), .scalar (.nat function), .scalar (.nat argument)] =>
          some (.tmApp function argument)
      | [.scalar (.string "tm.lam"), .scalar (.nat domain), .scalar (.nat body)] =>
          some (.tmLam domain body)
      | [.scalar (.string "tm.bool"), .scalar (.bool value)] => some (.tmBool value)
      | [.scalar (.string "tm.zero")] => some .tmZero
      | [.scalar (.string "tm.succ"), .scalar (.nat value)] => some (.tmSucc value)
      | [.scalar (.string "tm.eq"), .scalar (.nat type), .scalar (.nat left),
          .scalar (.nat right)] => some (.tmEq type left right)
      | [.scalar (.string "tm.eps"), .scalar (.nat type), .scalar (.nat predicate)] =>
          some (.tmEps type predicate)
      | [.scalar (.string "tm.abs"), .scalar (.nat carrier), .scalar (.nat predicate),
          .scalar (.nat value)] => some (.tmAbs carrier predicate value)
      | [.scalar (.string "tm.rep"), .scalar (.nat carrier), .scalar (.nat predicate),
          .scalar (.nat value)] => some (.tmRep carrier predicate value)
      | _ => none
  | _ => none

@[simp] theorem decodeRow_encodeRow {Base : Type u} (row : Row Base Nat) :
    decodeRow (encodeRow row) = some row := by
  cases row <;> simp [encodeRow, decodeRow, array, string, nat, bool, kind, base]

theorem encodeRow_injective {Base : Type u} :
    Function.Injective (encodeRow (Base := Base)) := by
  intro left right h
  have := congrArg decodeRow h
  simpa using this

private def decodeRows {Base : Type u} : List (Tree Base) → Option (List (Row Base Nat))
  | [] => some []
  | value :: values => return (← decodeRow value) :: (← decodeRows values)

/-- Encode a raw arena as an outer JSON array of positional row arrays. -/
def encode {Base : Type u} (rows : RawArena Base) : Tree Base :=
  array (rows.toList.map encodeRow)

/-- Parse an outer JSON array into raw rows. Backward-reference validation is
kept separate, so callers can inspect parsed but invalid arenas. -/
def decode {Base : Type u} : Tree Base → Option (RawArena Base)
  | .list values => return (← decodeRows values.toList).toArray
  | _ => none

private theorem decodeRows_map_encodeRow {Base : Type u} (rows : List (Row Base Nat)) :
    decodeRows (rows.map encodeRow) = some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [decodeRows, ih]

/-- The array JSON codec is a left inverse on every raw arena. -/
@[simp] theorem decode_encode {Base : Type u} (rows : RawArena Base) :
    decode (encode rows) = some rows := by
  simp [decode, encode, array, decodeRows_map_encodeRow]

/-- Distinct raw arenas always have distinct canonical JSON encodings. -/
theorem encode_injective {Base : Type u} : Function.Injective (encode (Base := Base)) :=
  by
    intro left right h
    have := congrArg decode h
    simpa using this

/-- Parse JSON, check backward references, then decode an open selected root. -/
def decodeOpen {Base : Type u} (json : Tree Base) (root : Nat)
    (sort : HolSort) (depth : Nat) : Option (Hol Base sort depth) := do
  let rows ← decode json
  rows.decodeOpen root sort depth

/-- Parse JSON, validate it, and decode a selected closed type. -/
def decodeTy {Base : Type u} (json : Tree Base) (root : Nat) : Option (Ty Base) :=
  decodeOpen json root (.kind .star) 0

/-- Parse JSON, validate it, and decode a selected closed term. -/
def decodeTm {Base : Type u} (json : Tree Base) (root : Nat) : Option (ClosedTm Base) :=
  decodeOpen json root .tm 0

/-- Parse an array of JSON rows and elaborate every row to a packed HOL LN
entry. This is the main whole-document decoder. -/
def elaborate {Base : Type u} (json : Tree Base) : Option (Array (Packed Base)) := do
  let rows ← decode json
  rows.elaborate

end Json

end Nucleus.HolLN.Array
