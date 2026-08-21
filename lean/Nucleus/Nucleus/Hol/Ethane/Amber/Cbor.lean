import Nucleus.Hol.Ethane.Amber.Syntax
import Nucleus.Hol.Ethane.Arena.Cbor
import Nucleus.Cbor.Containers
import Nucleus.O256.Basic

/-!
# Amber CBOR

Rows have the uniform CBOR shape

`[tag, [child, ...], [extra, ...]]`.

A dense forest is

`["ETHANE_AMBER_DENSE", parent-or-null, [row, ...]]`,

where a parent is `[key, size]`.  The size makes edge validation independent
of CAS availability.  Keys use a fixed codec supplied by `CasKey`; the O256
instance is exactly one 32-byte CBOR byte string.
-/

namespace Nucleus.Hol.Ethane.Amber.Cbor

open Nucleus Nucleus.Hol.Ethane
universe u v w x
set_option relaxedAutoImplicit true

def array (values : List Nucleus.Cbor) : Nucleus.Cbor :=
  Nucleus.Cbor.arrayOfList values
def text (value : String) : Nucleus.Cbor := .primitive (.text value)
def null : Nucleus.Cbor := .primitive .null

def unsigned (value : Nat) : Nucleus.Cbor :=
  .primitive (.integer (.unsigned (UInt64.ofNat value)))

private def asArray? : Nucleus.Cbor → Option (List Nucleus.Cbor) :=
  Nucleus.Cbor.asArray?

private def asNat? : Nucleus.Cbor → Option Nat
  | .primitive (.integer (.unsigned value)) => some value.toNat
  | _ => none

private def asBool? : Nucleus.Cbor → Option Bool
  | .primitive (.simple 20) => some false
  | .primitive (.simple 21) => some true
  | _ => none

private def bool : Bool → Nucleus.Cbor
  | false => .primitive .false
  | true => .primitive .true

@[simp] private theorem asArray?_array (values : List Nucleus.Cbor) :
    asArray? (array values) = some values := by
  simp [array, asArray?]

private theorem uint64_ofNat_toNat (value : Nat) (fits : value < 2 ^ 64) :
    (UInt64.ofNat value).toNat = value := by
  change value % 2 ^ 64 = value
  exact Nat.mod_eq_of_lt fits

@[simp] private theorem asNat?_unsigned (value : Nat) (fits : value < 2 ^ 64) :
    asNat? (unsigned value) = some value := by
  simp [asNat?, unsigned, uint64_ofNat_toNat value fits]

/-- A fixed semantic CBOR codec.  Decoding is functional; `decode_encode`
makes the encoder a section but does not require every accepted input to be
canonical. -/
structure Codec (α : Type u) where
  encode : α → Nucleus.Cbor
  decode? : Nucleus.Cbor → Option α
  decode_encode : ∀ value, decode? (encode value) = some value

/-- CAS keys have one fixed CBOR representation for a given forest format. -/
class CasKey (Key : Type u) where
  codec : Codec Key

namespace CasKey

def encode [CasKey Key] (key : Key) : Nucleus.Cbor := CasKey.codec.encode key
def decode? [CasKey Key] (value : Nucleus.Cbor) : Option Key := CasKey.codec.decode? value

@[simp] theorem decode_encode [CasKey Key] (key : Key) :
    decode? (encode key) = some key := CasKey.codec.decode_encode key

end CasKey

private def bytesOfO256 (value : O256) : Bytes :=
  ⟨value.bytes.toByteArray⟩

private def o256OfBytes? (value : Bytes) : Option O256 :=
  O256.ofList? value.data.data.toList

/-- The CAS specialization used by Rust: O256 is a bare 32-byte CBOR value.
The hashing algorithm remains outside the Lean model. -/
instance : CasKey O256 where
  codec :=
    { encode := fun value => .primitive (.bytes (bytesOfO256 value))
      decode? := fun value => match value with
        | .primitive (.bytes bytes) => o256OfBytes? bytes
        | _ => none
      decode_encode := by
        intro value
        simp [o256OfBytes?, bytesOfO256] }

private def traverse (decode : Nucleus.Cbor → Option α) :
    List Nucleus.Cbor → Option (List α)
  | [] => some []
  | value :: values => return (← decode value) :: (← traverse decode values)

private theorem traverse_encode (codec : Codec α) (values : List α) :
    traverse codec.decode? (values.map codec.encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [traverse, codec.decode_encode, ih]

/-- A view fits the concrete unsigned-64 reference representation. -/
def FitsView (row : Row.View Tag Nat Extra) : Prop :=
  ∀ child ∈ row.children, child < 2 ^ 64

/-- Encode any row view.  The split between children and extras remains
visible in CBOR. -/
def encodeView (tag : Codec Tag) (extra : Codec Extra)
    (row : Row.View Tag Nat Extra) : Nucleus.Cbor :=
  array [tag.encode row.tag, array (row.children.map unsigned),
    array (row.extra.map extra.encode)]

/-- Decode the common row envelope without knowing an Ethane constructor. -/
def decodeView? (tag : Codec Tag) (extra : Codec Extra)
    (value : Nucleus.Cbor) : Option (Row.View Tag Nat Extra) := do
  match ← asArray? value with
  | [tagValue, childrenValue, extraValue] =>
      return ⟨← tag.decode? tagValue,
        ← traverse asNat? (← asArray? childrenValue),
        ← traverse extra.decode? (← asArray? extraValue)⟩
  | _ => none

private theorem traverse_unsigned (values : List Nat)
    (fits : ∀ value ∈ values, value < 2 ^ 64) :
    traverse asNat? (values.map unsigned) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [traverse, asNat?_unsigned value (fits value (by simp)),
        ih (fun item member => fits item (by simp [member]))]

@[simp] theorem decodeView?_encode (tag : Codec Tag) (extra : Codec Extra)
    (row : Row.View Tag Nat Extra) (fits : FitsView row) :
    decodeView? tag extra (encodeView tag extra row) = some row := by
  rcases row with ⟨rowTag, children, fields⟩
  simp [decodeView?, encodeView, tag.decode_encode,
    traverse_unsigned children fits, traverse_encode extra fields]

/-- String codec for the closed Ethane constructor vocabulary. -/
def syntaxTag : Codec SyntaxTag where
  encode
    | .pair => text "PAIR"
    | .kindStar => text "KIND_STAR"
    | .kindArr => text "KIND_ARR"
    | .boolTy => text "TY_BOOL"
    | .arr => text "TY_ARR"
    | .tyApp => text "TY_APP"
    | .tyLam => text "TY_LAM"
    | .tyFv => text "TY_FV"
    | .tyExists => text "TM_TY_EXISTS"
    | .model => text "TY_MODEL"
    | .primFam => text "PRIM_FAM"
    | .primTm => text "PRIM_TM"
    | .tmFv => text "TM_FV"
    | .app => text "TM_APP"
    | .lam => text "TM_LAM"
    | .bool => text "TM_BOOL"
    | .eq => text "TM_EQ"
    | .eps => text "TM_EPS"
  decode?
    | .primitive (.text "PAIR") => some .pair
    | .primitive (.text "KIND_STAR") => some .kindStar
    | .primitive (.text "KIND_ARR") => some .kindArr
    | .primitive (.text "TY_BOOL") => some .boolTy
    | .primitive (.text "TY_ARR") => some .arr
    | .primitive (.text "TY_APP") => some .tyApp
    | .primitive (.text "TY_LAM") => some .tyLam
    | .primitive (.text "TY_FV") => some .tyFv
    | .primitive (.text "TM_TY_EXISTS") => some .tyExists
    | .primitive (.text "TY_MODEL") => some .model
    | .primitive (.text "PRIM_FAM") => some .primFam
    | .primitive (.text "PRIM_TM") => some .primTm
    | .primitive (.text "TM_FV") => some .tmFv
    | .primitive (.text "TM_APP") => some .app
    | .primitive (.text "TM_LAM") => some .lam
    | .primitive (.text "TM_BOOL") => some .bool
    | .primitive (.text "TM_EQ") => some .eq
    | .primitive (.text "TM_EPS") => some .eps
    | _ => none
  decode_encode := by intro value; cases value <;> rfl

/-- Codec for Ethane's non-recursive row fields. -/
def syntaxExtra
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig) : Codec (SyntaxExtra Sig Name) where
  encode
    | .name value => array [text "NAME", names.encode value]
    | .fam value => array [text "FAM", symbols.encodeFam value]
    | .tm value => array [text "TM", symbols.encodeTm value]
    | .bool value => array [text "BOOL", bool value]
  decode? value := do
    match ← asArray? value with
    | [.primitive (.text "NAME"), value] => return .name (← names.decode value)
    | [.primitive (.text "FAM"), value] => return .fam (← symbols.decodeFam value)
    | [.primitive (.text "TM"), value] => return .tm (← symbols.decodeTm value)
    | [.primitive (.text "BOOL"), value] => return .bool (← asBool? value)
    | _ => none
  decode_encode := by
    intro value
    cases value with
    | name value => simp [text, names.decode_encode]
    | fam value => simp [text, symbols.decodeFam_encode]
    | tm value => simp [text, symbols.decodeTm_encode]
    | bool value => cases value <;>
        simp [text, bool, asBool?, CborPrimitive.false, CborPrimitive.true]

/-- Encode one constructor enum through the generic row envelope. -/
def encodeSyntaxRow (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (row : Arena.Row Sig Name Nat) : Nucleus.Cbor :=
  encodeView syntaxTag (syntaxExtra names symbols) (Row.view row)

/-- Decode the generic envelope and then validate the exact Ethane arity. -/
def decodeSyntaxRow? (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (value : Nucleus.Cbor) : Option (Arena.Row Sig Name Nat) := do
  SyntaxRow.ofView? (← decodeView? syntaxTag (syntaxExtra names symbols) value)

@[simp] theorem decodeSyntaxRow?_encode (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig) (row : Arena.Row Sig Name Nat)
    (fits : FitsView (Row.view row)) :
    decodeSyntaxRow? names symbols (encodeSyntaxRow names symbols row) = some row := by
  simp [decodeSyntaxRow?, encodeSyntaxRow,
    decodeView?_encode syntaxTag (syntaxExtra names symbols) (Row.view row) fits]

/-- Parent links use null for the root forest and `[key, size]` otherwise. -/
def encodeParent [CasKey Key] : Option (Parent Key) → Nucleus.Cbor
  | none => null
  | some parent => array [CasKey.encode parent.key, unsigned parent.size]

def decodeParent? [CasKey Key] (value : Nucleus.Cbor) : Option (Option (Parent Key)) :=
  match value with
  | .primitive (.simple 22) => some none
  | value => do
      match ← asArray? value with
      | [key, size] => return some ⟨← CasKey.decode? key, ← asNat? size⟩
      | _ => none

def FitsParent : Option (Parent Key) → Prop
  | none => True
  | some parent => parent.size < 2 ^ 64

@[simp] theorem decodeParent?_encode [CasKey Key] (parent : Option (Parent Key))
    (fits : FitsParent parent) : decodeParent? (encodeParent parent) = some parent := by
  cases parent with
  | none => rfl
  | some parent =>
      simp [encodeParent, decodeParent?, array, asArray?,
        Nucleus.Cbor.arrayOfList, Nucleus.Cbor.asArray?,
        ArrayLike.observe_construct, CasKey.decode_encode,
        asNat?_unsigned parent.size fits]

/-- All unsigned references in a dense forest fit CBOR. -/
def FitsDense [Row R Tag Nat Extra] (forest : Dense Key R) : Prop :=
  FitsParent forest.parent ∧ ∀ row ∈ forest.rows, FitsView (Row.view row)

/-- Generic dense-forest encoder. -/
def encodeDense [CasKey Key] [Row R Tag Nat Extra]
    (tag : Codec Tag) (extra : Codec Extra) (forest : Dense Key R) : Nucleus.Cbor :=
  array [text "ETHANE_AMBER_DENSE", encodeParent forest.parent,
    array (forest.rows.map fun row => encodeView tag extra (Row.view row))]

/-- Generic dense-forest decoder.  `ofView?` is the constructor-specific
arity checker. -/
def decodeDense? [CasKey Key] (tag : Codec Tag) (extra : Codec Extra)
    (ofView? : Row.View Tag Nat Extra → Option R) (value : Nucleus.Cbor) :
    Option (Dense Key R) := do
  match ← asArray? value with
  | [.primitive (.text "ETHANE_AMBER_DENSE"), parent, rows] =>
      return ⟨← decodeParent? parent,
        ← traverse (fun value => (decodeView? tag extra value).bind ofView?)
          (← asArray? rows)⟩
  | _ => none

private theorem traverse_encodeRows [Row R Tag Nat Extra]
    (tag : Codec Tag) (extra : Codec Extra)
    (ofView? : Row.View Tag Nat Extra → Option R)
    (ofView_view : ∀ row : R, ofView? (Row.view row) = some row)
    (rows : List R) (fits : ∀ row ∈ rows, FitsView (Row.view row)) :
    traverse (fun value => (decodeView? tag extra value).bind ofView?)
      (rows.map fun row => encodeView tag extra (Row.view row)) = some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [traverse, decodeView?_encode tag extra (Row.view row)
          (fits row (by simp)), ofView_view,
        ih (fun item member => fits item (by simp [member]))]

@[simp] theorem decodeDense?_encode [CasKey Key] [Row R Tag Nat Extra]
    (tag : Codec Tag) (extra : Codec Extra)
    (ofView? : Row.View Tag Nat Extra → Option R)
    (ofView_view : ∀ row : R, ofView? (Row.view row) = some row)
    (forest : Dense Key R) (fits : FitsDense forest) :
    decodeDense? tag extra ofView? (encodeDense tag extra forest) = some forest := by
  rcases forest with ⟨parent, rows⟩
  rcases fits with ⟨parentFits, rowsFit⟩
  simp [decodeDense?, encodeDense, text, decodeParent?_encode parent parentFits,
    traverse_encodeRows tag extra ofView? ofView_view rows rowsFit]

/-- Exact Ethane forest encoder. -/
def encodeSyntaxForest [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (forest : SyntaxForest Key Sig Name) : Nucleus.Cbor :=
  encodeDense syntaxTag (syntaxExtra names symbols) forest

/-- Interpret CBOR first as a generic row forest and then as checked Ethane
constructor rows.  No CAS access occurs here. -/
def decodeSyntaxForest? [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (value : Nucleus.Cbor) : Option (SyntaxForest Key Sig Name) :=
  decodeDense? syntaxTag (syntaxExtra names symbols) SyntaxRow.ofView? value

@[simp] theorem decodeSyntaxForest?_encode [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (forest : SyntaxForest Key Sig Name) (fits : FitsDense forest) :
    decodeSyntaxForest? names symbols (encodeSyntaxForest names symbols forest) =
      some forest := by
  exact decodeDense?_encode syntaxTag (syntaxExtra names symbols)
    SyntaxRow.ofView? SyntaxRow.ofView?_view forest fits

/-- Resolve and elaborate a CBOR value as an Ethane forest. -/
def interpretSyntaxForest? [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (resolve : Dense.Resolver Key (Arena.Value Sig Name))
    (value : Nucleus.Cbor) : Option (Dense.Denotation (Arena.Value Sig Name)) :=
  match decodeSyntaxForest? (Key := Key) names symbols value with
  | none => none
  | some forest => Dense.denote? resolve forest

/-- CBOR interpretation agrees exactly with direct forest interpretation. -/
@[simp] theorem interpretSyntaxForest?_encode [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (resolve : Dense.Resolver Key (Arena.Value Sig Name))
    (forest : SyntaxForest Key Sig Name) (fits : FitsDense forest) :
    interpretSyntaxForest? names symbols resolve
      (encodeSyntaxForest names symbols forest) = forest.denote? resolve := by
  unfold interpretSyntaxForest?
  rw [decodeSyntaxForest?_encode names symbols forest fits]

/-- Encode one expression as a self-contained Amber forest. -/
def encodeExpression [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (expression : Syn Sig Name) : Nucleus.Cbor :=
  encodeSyntaxForest names symbols (SyntaxForest.ofSyn (Key := Key) expression)

/-- Decode the final row of a self-contained forest as one Ethane expression.
Parented forests are decoded by `decodeSyntaxForest?` and interpreted with an
explicit resolver instead. -/
def decodeExpression? [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (value : Nucleus.Cbor) : Option (Syn Sig Name) :=
  match decodeSyntaxForest? (Key := Key) names symbols value with
  | none => none
  | some ⟨some _, _⟩ => none
  | some ⟨none, rows⟩ =>
      Arena.Rooted.decode ⟨rows, rows.length - 1⟩

/-- The complete Ethane-to-forest-to-CBOR path is a left inverse whenever
the generated natural-number references fit CBOR's unsigned width. -/
@[simp] theorem decodeExpression?_encode [CasKey Key]
    (names : Arena.Cbor.NameCodec Name)
    (symbols : Arena.Cbor.SignatureCodec Sig)
    (expression : Syn Sig Name)
    (fits : FitsDense (SyntaxForest.ofSyn (Key := Key) expression)) :
    decodeExpression? (Key := Key) names symbols
      (encodeExpression (Key := Key) names symbols expression) = some expression := by
  unfold decodeExpression? encodeExpression
  rw [decodeSyntaxForest?_encode names symbols
    (SyntaxForest.ofSyn (Key := Key) expression) fits]
  simp only [SyntaxForest.ofSyn]
  rw [← SyntaxForest.encoder_root_eq_last expression]
  exact Arena.Encoder.decode_run expression

end Nucleus.Hol.Ethane.Amber.Cbor
