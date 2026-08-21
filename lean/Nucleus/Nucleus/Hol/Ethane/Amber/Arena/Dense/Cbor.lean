import Nucleus.Hol.Ethane.Amber.Arena.Dense
import Nucleus.Hol.Ethane.Arena.Cbor
import Nucleus.Cbor.Containers

/-!
# CBOR objects for dense Amber arenas

The checked semantic value is `Arena.Dense`; CBOR is only its wire object.
The concrete field names, object discriminator, syntax names, and index
representation all come from a serialization strategy.
-/

namespace Nucleus.Hol.Ethane.Amber.Arena.Dense.Cbor

open Nucleus Nucleus.Hol.Ethane Nucleus.Hol.Ethane.Amber
open Nucleus.Hol.Ethane.Amber.Serialization
universe u v w x y
set_option relaxedAutoImplicit true

variable {S : Type u}

def array (values : List Nucleus.Cbor) : Nucleus.Cbor :=
  ArrayLike.array values

def object (fields : List (String × Nucleus.Cbor)) : Nucleus.Cbor :=
  ObjectLike.object fields

def text (value : String) : Nucleus.Cbor := .primitive (.text value)
def null : Nucleus.Cbor := .primitive .null

def asArray? (value : Nucleus.Cbor) : Option (List Nucleus.Cbor) :=
  ArrayLike.array? value

def asObject? (value : Nucleus.Cbor) : Option (List (String × Nucleus.Cbor)) :=
  ObjectLike.object? value

private def traverse (decode : Nucleus.Cbor → Option α) :
    List Nucleus.Cbor → Option (List α)
  | [] => some []
  | value :: values => return (← decode value) :: (← traverse decode values)

@[simp] private theorem asArray?_array (values : List Nucleus.Cbor) :
    asArray? (array values) = some values := ArrayLike.observe_construct values

@[simp] private theorem asObject?_object
    (fields : List (String × Nucleus.Cbor)) :
    asObject? (object fields) = some fields := ObjectLike.observe_construct fields

private theorem traverse_encode (codec : Codec α) (values : List α) :
    traverse codec.decode? (values.map codec.encode) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [traverse, codec.decode_encode, ih]

private theorem traverse_hasCodec [HasCodec S α] (values : List α) :
    traverse (HasCodec.decode? (S := S))
      (values.map (HasCodec.encode (S := S))) = some values := by
  change traverse (HasCodec.codec (S := S) (α := α)).decode?
    (values.map (HasCodec.codec (S := S) (α := α)).encode) = some values
  exact traverse_encode (HasCodec.codec (S := S) (α := α)) values

/-- All index-bearing parts of a row fit the selected strategy. -/
def FitsView [Strategy S Ix] (row : Row.View Tag Ix Extra) : Prop :=
  ∀ child ∈ row.children, Strategy.IndexFits (S := S) child

/-- Uniform row envelope.  Tags and scalar extras use total codecs; recursive
indices use the strategy's possibly bounded index codec. -/
def encodeView [Strategy S Ix] [HasCodec S Tag]
    [HasCodec S Extra] (row : Row.View Tag Ix Extra) : Nucleus.Cbor :=
  array [HasCodec.encode (S := S) row.tag,
    array (row.children.map (Strategy.encodeIndex (S := S))),
    array (row.extra.map (HasCodec.encode (S := S)))]

def decodeView? [Strategy S Ix] [HasCodec S Tag]
    [HasCodec S Extra] (value : Nucleus.Cbor) :
    Option (Row.View Tag Ix Extra) := do
  match ← asArray? value with
  | [tag, children, extra] =>
      return ⟨← HasCodec.decode? (S := S) tag,
        ← traverse (Strategy.decodeIndex? (S := S)) (← asArray? children),
        ← traverse (HasCodec.decode? (S := S)) (← asArray? extra)⟩
  | _ => none

private theorem traverse_indices [Strategy S Ix]
    (values : List Ix)
    (fits : ∀ value ∈ values, Strategy.IndexFits (S := S) value) :
    traverse (Strategy.decodeIndex? (S := S))
      (values.map (Strategy.encodeIndex (S := S))) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [traverse, Strategy.decodeIndex?_encode value (fits value (by simp)),
        ih (fun item member => fits item (by simp [member]))]

@[simp] theorem decodeView?_encode [Strategy S Ix]
    [HasCodec S Tag] [HasCodec S Extra]
    (row : Row.View Tag Ix Extra) (fits : FitsView (S := S) row) :
    decodeView? (S := S) (encodeView (S := S) row) = some row := by
  rcases row with ⟨tag, children, extra⟩
  simp [decodeView?, encodeView, HasCodec.decode_encode,
    traverse_indices children fits,
    traverse_hasCodec (S := S) extra]

/-- Parent fields are either null or a singleton key array.  The singleton
envelope prevents a key codec that accepts or emits null from colliding with
the absent-parent representation. -/
def encodeParent [HasCodec S Key] : Option Key → Nucleus.Cbor
  | none => null
  | some key => array [HasCodec.encode (S := S) key]

def decodeParent? [HasCodec S Key]
    (value : Nucleus.Cbor) : Option (Option Key) :=
  match value with
  | .primitive (.simple 22) => some none
  | value => do
      match ← asArray? value with
      | [key] => return some (← HasCodec.decode? (S := S) key)
      | _ => none

@[simp] theorem decodeParent?_encode [HasCodec S Key]
    (parent : Option Key) :
    decodeParent? (S := S) (encodeParent (S := S) parent) =
      some parent := by
  cases parent with
  | none => rfl
  | some key =>
      simp [encodeParent, decodeParent?, array, asArray?, HasCodec.decode_encode]

/-- The selected index representation covers the offset and every child. -/
def Fits [Strategy S Ix] [Row R Tag Ix Extra]
    (arena : Arena.Dense Key R Ix) : Prop :=
  Strategy.IndexFits (S := S) arena.offset ∧
    ∀ row ∈ arena.defs.toList, FitsView (S := S) (Row.view row)

private def schema (S : Type u) (Ix : Type v) [Strategy S Ix] :
    ObjectSchema := Strategy.objects (S := S) (Ix := Ix)

/-- Encode the implementation-facing arena as a tagged CBOR dictionary. -/
def encode [Strategy S Ix] [HasCodec S Key]
    [HasCodec S Tag] [HasCodec S Extra] [Row R Tag Ix Extra]
    (arena : Arena.Dense Key R Ix) : Nucleus.Cbor :=
  let names := schema S Ix
  object [
    (names.tagField, text names.denseTag),
    (names.parentField, encodeParent (S := S) arena.parent),
    (names.offsetField, Strategy.encodeIndex (S := S) arena.offset),
    (names.defsField,
      array (arena.defs.toList.map fun row => encodeView (S := S) (Row.view row)))]

/-- Decode a dictionary into the typed dense arena.  All map keys must be text
and duplicate keys are rejected.  Unknown unique fields are reserved for
future metadata and ignored by this base decoder. -/
def decode? [Strategy S Ix] [HasCodec S Key]
    [HasCodec S Tag] [HasCodec S Extra]
    (ofView? : Row.View Tag Ix Extra → Option R)
    (value : Nucleus.Cbor) : Option (Arena.Dense Key R Ix) := do
  let fields ← asObject? value
  if _ : ¬Fields.Unique fields then none else
  let names := schema S Ix
  let tag ← Fields.lookup? names.tagField fields
  if tag != text names.denseTag then none else
  let parent ← decodeParent? (S := S)
    (← Fields.lookup? names.parentField fields)
  let offset ← Strategy.decodeIndex? (S := S)
    (← Fields.lookup? names.offsetField fields)
  let defs ← traverse
    (fun value => (decodeView? (S := S) value).bind ofView?)
    (← asArray? (← Fields.lookup? names.defsField fields))
  return ⟨parent, offset, defs.toArray⟩

private theorem traverse_encodeRows [Strategy S Ix]
    [HasCodec S Tag] [HasCodec S Extra] [Row R Tag Ix Extra]
    (ofView? : Row.View Tag Ix Extra → Option R)
    (ofView_view : ∀ row : R, ofView? (Row.view row) = some row)
    (rows : List R)
    (fits : ∀ row ∈ rows, FitsView (S := S) (Row.view row)) :
    traverse (fun value => (decodeView? (S := S) value).bind ofView?)
      (rows.map fun row => encodeView (S := S) (Row.view row)) = some rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp [traverse, decodeView?_encode (S := S) (Row.view row)
          (fits row (by simp)), ofView_view,
        ih (fun item member => fits item (by simp [member]))]

/- The generic round-trip theorem follows solely from the strategy laws and
the row constructor's checked inverse. -/
@[simp] theorem decode?_encode [Strategy S Ix] [HasCodec S Key]
    [HasCodec S Tag] [HasCodec S Extra] [Row R Tag Ix Extra]
    (ofView? : Row.View Tag Ix Extra → Option R)
    (ofView_view : ∀ row : R, ofView? (Row.view row) = some row)
    (arena : Arena.Dense Key R Ix) (fits : Fits (S := S) arena) :
    decode? (S := S) ofView? (encode (S := S) arena) =
      some arena := by
  rcases arena with ⟨parent, offset, defs⟩
  rcases fits with ⟨offsetFits, defsFit⟩
  have schemaValid := Strategy.objects_valid (S := S) (Ix := Ix)
  simp only [ObjectSchema.Valid, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at schemaValid
  simp [decode?, encode, schema, Fields.Unique, Fields.keys, Fields.lookup?,
    schemaValid, offsetFits, decodeParent?_encode,
    Strategy.decodeIndex?_encode,
    traverse_encodeRows (S := S) ofView? ofView_view defs.toList defsFit]

/-! ## Ethane syntax specialization -/

private def encodeBool : Bool → Nucleus.Cbor
  | false => .primitive .false
  | true => .primitive .true

private def decodeBool? : Nucleus.Cbor → Option Bool
  | .primitive (.simple 20) => some false
  | .primitive (.simple 21) => some true
  | _ => none

/-- Constructor tags are interpreted through the active vocabulary rather
than hard-coded in the generic arena codec. -/
def syntaxTag [Strategy S Ix] : Codec SyntaxTag :=
  let names := Strategy.syntaxVocabulary (S := S) (Ix := Ix)
  { encode := fun
      | .pair => text names.pair
      | .kindStar => text names.kindStar
      | .kindArr => text names.kindArr
      | .boolTy => text names.boolTy
      | .arr => text names.arr
      | .tyApp => text names.tyApp
      | .tyLam => text names.tyLam
      | .tyFv => text names.tyFv
      | .tyExists => text names.tyExists
      | .model => text names.model
      | .primFam => text names.primFam
      | .primTm => text names.primTm
      | .tmFv => text names.tmFv
      | .app => text names.app
      | .lam => text names.lam
      | .bool => text names.bool
      | .eq => text names.eq
      | .eps => text names.eps
    decode? := fun value =>
      if value = text names.pair then some .pair
      else if value = text names.kindStar then some .kindStar
      else if value = text names.kindArr then some .kindArr
      else if value = text names.boolTy then some .boolTy
      else if value = text names.arr then some .arr
      else if value = text names.tyApp then some .tyApp
      else if value = text names.tyLam then some .tyLam
      else if value = text names.tyFv then some .tyFv
      else if value = text names.tyExists then some .tyExists
      else if value = text names.model then some .model
      else if value = text names.primFam then some .primFam
      else if value = text names.primTm then some .primTm
      else if value = text names.tmFv then some .tmFv
      else if value = text names.app then some .app
      else if value = text names.lam then some .lam
      else if value = text names.bool then some .bool
      else if value = text names.eq then some .eq
      else if value = text names.eps then some .eps
      else none
    decode_encode := by
      intro tag
      cases tag <;>
        simp [text, SyntaxVocabulary.pair, SyntaxVocabulary.kindStar,
          SyntaxVocabulary.kindArr, SyntaxVocabulary.boolTy,
          SyntaxVocabulary.arr, SyntaxVocabulary.tyApp,
          SyntaxVocabulary.tyLam, SyntaxVocabulary.tyFv,
          SyntaxVocabulary.tyExists, SyntaxVocabulary.model,
          SyntaxVocabulary.primFam, SyntaxVocabulary.primTm,
          SyntaxVocabulary.tmFv, SyntaxVocabulary.app,
          SyntaxVocabulary.lam, SyntaxVocabulary.bool,
          SyntaxVocabulary.eq, SyntaxVocabulary.eps] }

/-- Non-recursive syntax fields retain caller-selected name and signature
codecs while their discriminant strings come from the strategy. -/
def syntaxExtra [Strategy S Ix]
    (names : Nucleus.Hol.Ethane.Arena.Cbor.NameCodec Name)
    (symbols : Nucleus.Hol.Ethane.Arena.Cbor.SignatureCodec Sig) :
    Codec (SyntaxExtra Sig Name) :=
  let vocabulary := Strategy.syntaxVocabulary (S := S) (Ix := Ix)
  { encode := fun
      | .name value => array [text vocabulary.nameExtra, names.encode value]
      | .fam value => array [text vocabulary.famExtra, symbols.encodeFam value]
      | .tm value => array [text vocabulary.tmExtra, symbols.encodeTm value]
      | .bool value => array [text vocabulary.boolExtra, encodeBool value]
    decode? := fun value => do
      match ← asArray? value with
      | [tag, value] =>
          if tag = text vocabulary.nameExtra then return .name (← names.decode value)
          else if tag = text vocabulary.famExtra then return .fam (← symbols.decodeFam value)
          else if tag = text vocabulary.tmExtra then return .tm (← symbols.decodeTm value)
          else if tag = text vocabulary.boolExtra then return .bool (← decodeBool? value)
          else none
      | _ => none
    decode_encode := by
      intro value
      cases value with
      | name value =>
          simp [text, SyntaxVocabulary.nameExtra, names.decode_encode]
      | fam value =>
          simp [text, SyntaxVocabulary.nameExtra, SyntaxVocabulary.famExtra,
            symbols.decodeFam_encode]
      | tm value =>
          simp [text, SyntaxVocabulary.nameExtra, SyntaxVocabulary.famExtra,
            SyntaxVocabulary.tmExtra, symbols.decodeTm_encode]
      | bool value =>
          cases value <;>
            simp [text, SyntaxVocabulary.nameExtra, SyntaxVocabulary.famExtra,
              SyntaxVocabulary.tmExtra, SyntaxVocabulary.boolExtra,
              encodeBool, decodeBool?, CborPrimitive.false, CborPrimitive.true] }

/-- Exact signed-indexed Ethane syntax arena. -/
abbrev Syntax (Key : Type) (Sig : Signature.{u}) (Name : Type := Nat)
    (Ix : Type := Int) := Arena.Dense.Syntax Key Sig Name Ix

def SyntaxFits [Strategy S Ix]
    (arena : Syntax Key Sig Name Ix) : Prop := Fits (S := S) arena

def encodeSyntax [Strategy S Ix] [HasCodec S Key]
    (names : Nucleus.Hol.Ethane.Arena.Cbor.NameCodec Name)
    (symbols : Nucleus.Hol.Ethane.Arena.Cbor.SignatureCodec Sig)
    (arena : Syntax Key Sig Name Ix) : Nucleus.Cbor :=
  letI : HasCodec S SyntaxTag := ⟨syntaxTag (S := S) (Ix := Ix)⟩
  letI : HasCodec S (SyntaxExtra Sig Name) :=
    ⟨syntaxExtra (S := S) (Ix := Ix) names symbols⟩
  encode (S := S) arena

def decodeSyntax? [Strategy S Ix] [HasCodec S Key]
    (names : Nucleus.Hol.Ethane.Arena.Cbor.NameCodec Name)
    (symbols : Nucleus.Hol.Ethane.Arena.Cbor.SignatureCodec Sig)
    (value : Nucleus.Cbor) : Option (Syntax Key Sig Name Ix) :=
  letI : HasCodec S SyntaxTag := ⟨syntaxTag (S := S) (Ix := Ix)⟩
  letI : HasCodec S (SyntaxExtra Sig Name) :=
    ⟨syntaxExtra (S := S) (Ix := Ix) names symbols⟩
  decode? (S := S) SyntaxRow.ofView? value

@[simp] theorem decodeSyntax?_encode [Strategy S Ix] [HasCodec S Key]
    (names : Nucleus.Hol.Ethane.Arena.Cbor.NameCodec Name)
    (symbols : Nucleus.Hol.Ethane.Arena.Cbor.SignatureCodec Sig)
    (arena : Syntax Key Sig Name Ix) (fits : SyntaxFits (S := S) arena) :
    decodeSyntax? (S := S) names symbols (encodeSyntax (S := S) names symbols arena) =
      some arena := by
  letI : HasCodec S SyntaxTag := ⟨syntaxTag (S := S) (Ix := Ix)⟩
  letI : HasCodec S (SyntaxExtra Sig Name) :=
    ⟨syntaxExtra (S := S) (Ix := Ix) names symbols⟩
  exact decode?_encode (S := S) SyntaxRow.ofView? SyntaxRow.ofView?_view arena fits

end Nucleus.Hol.Ethane.Amber.Arena.Dense.Cbor
