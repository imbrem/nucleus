import Nucleus.Cbor.General
import Nucleus.Hol.Ethane.Arena
import Nucleus.HolE.Semantics

/-!
# CBOR representation of binary Ethane arenas

The preferred representation is an array of string-tagged rows.  Scalar
payloads may add array fields, but the only recursive arena references are the
at-most-two indices exposed by `Row.children`.

Names and signature symbols are intentionally codec parameters.  This keeps
the arena format independent of a particular identifier policy while making
the exact round-trip obligations explicit.  Natural-number references use
CBOR unsigned integers and are therefore checked against the 64-bit CBOR
major-type argument used by this data model.
-/

namespace Nucleus.Hol.Ethane.Arena.Cbor

open Nucleus
universe u
set_option relaxedAutoImplicit true

private def arrayItems : List Nucleus.Cbor → CborSyn .array
  | [] => .arrayNil
  | value :: values => .arrayCons value (arrayItems values)

def array (values : List Nucleus.Cbor) : Nucleus.Cbor := .array (arrayItems values)

def text (value : String) : Nucleus.Cbor := .primitive (.text value)

def unsigned (value : Nat) : Nucleus.Cbor :=
  .primitive (.integer (.unsigned (UInt64.ofNat value)))

private def asArray? : Nucleus.Cbor → Option (List Nucleus.Cbor)
  | .array values => some values.toArrayList
  | _ => none

private def asNat? : Nucleus.Cbor → Option Nat
  | .primitive (.integer (.unsigned value)) => some value.toNat
  | _ => none

private def asBool? : Nucleus.Cbor → Option Bool
  | .primitive (.simple 20) => some false
  | .primitive (.simple 21) => some true
  | _ => none

private def encodeBool : Bool → Nucleus.Cbor
  | false => .primitive .false
  | true => .primitive .true

/-- A total CBOR codec for variable names. -/
structure NameCodec (Name : Type) where
  encode : Name → Nucleus.Cbor
  decode : Nucleus.Cbor → Option Name
  decode_encode : ∀ name, decode (encode name) = some name

/-- CBOR codecs for the two signature-symbol families. -/
structure SignatureCodec (Sig : Signature.{u}) where
  encodeFam : (Σ kind, Sig (.kind kind)) → Nucleus.Cbor
  decodeFam : Nucleus.Cbor → Option (Σ kind, Sig (.kind kind))
  decodeFam_encode : ∀ symbol, decodeFam (encodeFam symbol) = some symbol
  encodeTm : Sig .tm → Nucleus.Cbor
  decodeTm : Nucleus.Cbor → Option (Sig .tm)
  decodeTm_encode : ∀ symbol, decodeTm (encodeTm symbol) = some symbol

/-- The implementation-oriented name codec uses one unsigned 64-bit value. -/
def uint64Names : NameCodec UInt64 where
  encode name := .primitive (.integer (.unsigned name))
  decode
    | .primitive (.integer (.unsigned name)) => some name
    | _ => none
  decode_encode _ := rfl

/-- Empty Ethane has no signature symbols, so every symbol decoder rejects. -/
def emptySymbols : SignatureCodec Nucleus.HolE.EmptySig where
  encodeFam symbol := nomatch symbol.2
  decodeFam _ := none
  decodeFam_encode symbol := nomatch symbol.2
  encodeTm symbol := nomatch symbol
  decodeTm _ := none
  decodeTm_encode symbol := nomatch symbol

@[simp] private theorem arrayItems_toArrayList (values : List Nucleus.Cbor) :
    (arrayItems values).toArrayList = values := by
  induction values with
  | nil => simp [arrayItems, CborSyn.toArrayList]
  | cons value values ih => simp [arrayItems, CborSyn.toArrayList, ih]

@[simp] private theorem asArray?_array (values : List Nucleus.Cbor) :
    asArray? (array values) = some values := by simp [array, asArray?]

/-- The direct recursive references of a row fit CBOR's unsigned argument. -/
def FitsRow (row : Row Sig Name Nat) : Prop :=
  ∀ index, index ∈ row.children → index < 2 ^ 64

def encodeRow (names : NameCodec Name) (symbols : SignatureCodec Sig) :
    Row Sig Name Nat → Nucleus.Cbor
  | .pair left right => array [text "PAIR", unsigned left, unsigned right]
  | .kindStar => array [text "KIND_STAR"]
  | .kindArr domain codomain => array [text "KIND_ARR", unsigned domain, unsigned codomain]
  | .boolTy => array [text "TY_BOOL"]
  | .arr domain codomain => array [text "TY_ARR", unsigned domain, unsigned codomain]
  | .tyApp kinds arguments => array [text "TY_APP", unsigned kinds, unsigned arguments]
  | .tyLam name kinds body =>
      array [text "TY_LAM", names.encode name, unsigned kinds, unsigned body]
  | .tyFv name kind => array [text "TY_FV", names.encode name, unsigned kind]
  | .tyExists name predicate =>
      array [text "TM_TY_EXISTS", names.encode name, unsigned predicate]
  | .model name predicate =>
      array [text "TY_MODEL", names.encode name, unsigned predicate]
  | @Row.primFam _ _ _ kind symbol kindNode =>
      array [text "PRIM_FAM", symbols.encodeFam ⟨kind, symbol⟩, unsigned kindNode]
  | .primTm symbol => array [text "PRIM_TM", symbols.encodeTm symbol]
  | .tmFv name type => array [text "TM_FV", names.encode name, unsigned type]
  | .app function argument => array [text "TM_APP", unsigned function, unsigned argument]
  | .lam name domain body =>
      array [text "TM_LAM", names.encode name, unsigned domain, unsigned body]
  | .bool value => array [text "TM_BOOL", encodeBool value]
  | .eq type operands => array [text "TM_EQ", unsigned type, unsigned operands]
  | .eps type predicate => array [text "TM_EPS", unsigned type, unsigned predicate]

def decodeRow? (names : NameCodec Name) (symbols : SignatureCodec Sig)
    (value : Nucleus.Cbor) : Option (Row Sig Name Nat) := do
  match ← asArray? value with
  | [.primitive (.text "PAIR"), left, right] =>
      return .pair (← asNat? left) (← asNat? right)
  | [.primitive (.text "KIND_STAR")] => some .kindStar
  | [.primitive (.text "KIND_ARR"), domain, codomain] =>
      return .kindArr (← asNat? domain) (← asNat? codomain)
  | [.primitive (.text "TY_BOOL")] => some .boolTy
  | [.primitive (.text "TY_ARR"), domain, codomain] =>
      return .arr (← asNat? domain) (← asNat? codomain)
  | [.primitive (.text "TY_APP"), kinds, arguments] =>
      return .tyApp (← asNat? kinds) (← asNat? arguments)
  | [.primitive (.text "TY_LAM"), name, kinds, body] =>
      return .tyLam (← names.decode name) (← asNat? kinds) (← asNat? body)
  | [.primitive (.text "TY_FV"), name, kind] =>
      return .tyFv (← names.decode name) (← asNat? kind)
  | [.primitive (.text "TM_TY_EXISTS"), name, predicate] =>
      return .tyExists (← names.decode name) (← asNat? predicate)
  | [.primitive (.text "TY_MODEL"), name, predicate] =>
      return .model (← names.decode name) (← asNat? predicate)
  | [.primitive (.text "PRIM_FAM"), symbolValue, kindNode] =>
      let ⟨_kind, symbol⟩ ← symbols.decodeFam symbolValue
      return .primFam symbol (← asNat? kindNode)
  | [.primitive (.text "PRIM_TM"), symbol] =>
      return .primTm (← symbols.decodeTm symbol)
  | [.primitive (.text "TM_FV"), name, type] =>
      return .tmFv (← names.decode name) (← asNat? type)
  | [.primitive (.text "TM_APP"), function, argument] =>
      return .app (← asNat? function) (← asNat? argument)
  | [.primitive (.text "TM_LAM"), name, domain, body] =>
      return .lam (← names.decode name) (← asNat? domain) (← asNat? body)
  | [.primitive (.text "TM_BOOL"), value] => return .bool (← asBool? value)
  | [.primitive (.text "TM_EQ"), type, operands] =>
      return .eq (← asNat? type) (← asNat? operands)
  | [.primitive (.text "TM_EPS"), type, predicate] =>
      return .eps (← asNat? type) (← asNat? predicate)
  | _ => none

private theorem uint64_ofNat_toNat (value : Nat) (fits : value < 2 ^ 64) :
    (UInt64.ofNat value).toNat = value := by
  change value % 2 ^ 64 = value
  exact Nat.mod_eq_of_lt fits

@[simp] private theorem asNat?_unsigned (value : Nat) (fits : value < 2 ^ 64) :
    asNat? (unsigned value) = some value := by
  simp [asNat?, unsigned, uint64_ofNat_toNat value fits]

set_option maxHeartbeats 1000000 in
-- The dependent primitive-family row makes the exhaustive codec proof expensive.
@[simp] theorem decodeRow?_encode (names : NameCodec Name)
    (symbols : SignatureCodec Sig) (row : Row Sig Name Nat) (fits : FitsRow row) :
    decodeRow? names symbols (encodeRow names symbols row) = some row := by
  cases row <;>
    simp_all only [FitsRow, Row.children, List.mem_cons, List.not_mem_nil,
      or_false, Nat.reducePow, forall_eq_or_imp, forall_eq, IsEmpty.forall_iff,
      implies_true, decodeRow?, encodeRow, text, encodeBool, asArray?_array,
      Option.pure_def, Option.bind_eq_bind, asBool?, Option.bind_some,
      names.decode_encode, symbols.decodeFam_encode, symbols.decodeTm_encode,
      asNat?_unsigned]
  case bool value => cases value <;> rfl

private def traverse {α : Type} (decode : Nucleus.Cbor → Option α) :
    List Nucleus.Cbor → Option (List α)
  | [] => some []
  | value :: values => return (← decode value) :: (← traverse decode values)

/-- A rooted arena fits this concrete CBOR representation. -/
def FitsRooted (arena : Rooted Sig Name) : Prop :=
  arena.root < 2 ^ 64 ∧ ∀ row ∈ arena.rows, FitsRow row

def encodeRooted (names : NameCodec Name) (symbols : SignatureCodec Sig)
    (arena : Rooted Sig Name) : Nucleus.Cbor :=
  array [text "ETHANE_ARENA_V0", unsigned arena.root,
    array (arena.rows.map (encodeRow names symbols))]

def decodeRooted? (names : NameCodec Name) (symbols : SignatureCodec Sig)
    (value : Nucleus.Cbor) : Option (Rooted Sig Name) := do
  match ← asArray? value with
  | [.primitive (.text "ETHANE_ARENA_V0"), root, rows] =>
      return ⟨← traverse (decodeRow? names symbols) (← asArray? rows), ← asNat? root⟩
  | _ => none

private theorem traverse_encodeRows (names : NameCodec Name)
    (symbols : SignatureCodec Sig) (rows : List (Row Sig Name Nat))
    (fits : ∀ row ∈ rows, FitsRow row) :
    traverse (decodeRow? names symbols) (rows.map (encodeRow names symbols)) = some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [traverse, decodeRow?_encode names symbols row (fits row (by simp)),
        ih (fun item member => fits item (by simp [member]))]

@[simp] theorem decodeRooted?_encode (names : NameCodec Name)
    (symbols : SignatureCodec Sig) (arena : Rooted Sig Name) (fits : FitsRooted arena) :
    decodeRooted? names symbols (encodeRooted names symbols arena) = some arena := by
  rcases arena with ⟨rows, root⟩
  rcases fits with ⟨rootFits, rowsFit⟩
  simp [encodeRooted, decodeRooted?, text,
    traverse_encodeRows names symbols rows rowsFit,
    asNat?_unsigned root rootFits]

/-- Encode one Ethane expression through its canonical dense arena. -/
def encodeExpression (names : NameCodec Name) (symbols : SignatureCodec Sig)
    (expression : Syn Sig Name) : Nucleus.Cbor :=
  encodeRooted names symbols (Encoder.run expression)

/-- Decode an Ethane expression by validating the CBOR arena and elaborating
its public root. -/
def decodeExpression? (names : NameCodec Name) (symbols : SignatureCodec Sig)
    (value : Nucleus.Cbor) : Option (Syn Sig Name) :=
  match decodeRooted? names symbols value with
  | none => none
  | some arena => Rooted.decode arena

/-- The complete syntax-to-CBOR path round-trips whenever its natural-number
indices fit the concrete 64-bit CBOR representation. -/
@[simp] theorem decodeExpression?_encode (names : NameCodec Name)
    (symbols : SignatureCodec Sig) (expression : Syn Sig Name)
    (fits : FitsRooted (Encoder.run expression)) :
    decodeExpression? names symbols (encodeExpression names symbols expression) =
      some expression := by
  unfold decodeExpression? encodeExpression
  rw [decodeRooted?_encode names symbols (Encoder.run expression) fits]
  exact Encoder.decode_run expression

end Nucleus.Hol.Ethane.Arena.Cbor
