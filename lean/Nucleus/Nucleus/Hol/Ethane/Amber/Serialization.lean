import Nucleus.Cbor.General
import Nucleus.O256.Basic

/-!
# Amber serialization strategies

The semantic arena types do not choose their wire vocabulary.  A phantom
strategy supplies the object-field names, object tags, syntax-constructor
names, and index codec.  Independent `HasCodec` instances supply codecs for
keys and other scalar types.

This separation lets two formats serialize the same arena differently while
sharing all structural and round-trip proofs.
-/

namespace Nucleus.Hol.Ethane.Amber.Serialization

open Nucleus
universe u v

variable {S : Type u} {Ix α : Type v}

/-- A total semantic codec into the general CBOR model.  Accepted inputs need
not be canonical; encoding followed by decoding is exact. -/
structure Codec (α : Type u) where
  encode : α → Nucleus.Cbor
  decode? : Nucleus.Cbor → Option α
  decode_encode : ∀ value, decode? (encode value) = some value

/-- A codec whose concrete representation covers a stated subset.  Arena
indices use this interface because CBOR's primitive integer range is bounded. -/
structure PartialCodec (α : Type u) where
  encode : α → Nucleus.Cbor
  decode? : Nucleus.Cbor → Option α
  Fits : α → Prop
  decode_encode : ∀ value, Fits value → decode? (encode value) = some value

/-- Reserved object fields and semantic object discriminants. -/
structure ObjectSchema where
  tagField : String
  parentField : String
  offsetField : String
  defsField : String
  metadataField : String
  denseTag : String
  segmentTag : String
  deriving DecidableEq

namespace ObjectSchema

/-- Reserved fields must remain distinct even when an object decoder accepts
additional extension fields. -/
def Valid (schema : ObjectSchema) : Prop :=
  [schema.tagField, schema.parentField, schema.offsetField,
    schema.defsField, schema.metadataField].Nodup

end ObjectSchema

/-- Every named constant in the closed Ethane row vocabulary. -/
inductive SyntaxConstant where
  | pair
  | kindStar
  | kindArr
  | boolTy
  | arr
  | tyApp
  | tyLam
  | tyFv
  | tyExists
  | model
  | primFam
  | primTm
  | tmFv
  | app
  | lam
  | bool
  | eq
  | eps
  | nameExtra
  | famExtra
  | tmExtra
  | boolExtra
  deriving DecidableEq

/-- An injective assignment of wire names to syntax constants. -/
structure SyntaxVocabulary where
  name : SyntaxConstant → String
  name_injective : Function.Injective name

namespace SyntaxVocabulary

@[simp] theorem name_inj (names : SyntaxVocabulary) {left right : SyntaxConstant} :
    names.name left = names.name right ↔ left = right :=
  names.name_injective.eq_iff

def pair (names : SyntaxVocabulary) := names.name .pair
def kindStar (names : SyntaxVocabulary) := names.name .kindStar
def kindArr (names : SyntaxVocabulary) := names.name .kindArr
def boolTy (names : SyntaxVocabulary) := names.name .boolTy
def arr (names : SyntaxVocabulary) := names.name .arr
def tyApp (names : SyntaxVocabulary) := names.name .tyApp
def tyLam (names : SyntaxVocabulary) := names.name .tyLam
def tyFv (names : SyntaxVocabulary) := names.name .tyFv
def tyExists (names : SyntaxVocabulary) := names.name .tyExists
def model (names : SyntaxVocabulary) := names.name .model
def primFam (names : SyntaxVocabulary) := names.name .primFam
def primTm (names : SyntaxVocabulary) := names.name .primTm
def tmFv (names : SyntaxVocabulary) := names.name .tmFv
def app (names : SyntaxVocabulary) := names.name .app
def lam (names : SyntaxVocabulary) := names.name .lam
def bool (names : SyntaxVocabulary) := names.name .bool
def eq (names : SyntaxVocabulary) := names.name .eq
def eps (names : SyntaxVocabulary) := names.name .eps
def nameExtra (names : SyntaxVocabulary) := names.name .nameExtra
def famExtra (names : SyntaxVocabulary) := names.name .famExtra
def tmExtra (names : SyntaxVocabulary) := names.name .tmExtra
def boolExtra (names : SyntaxVocabulary) := names.name .boolExtra

end SyntaxVocabulary

/-- Build a vocabulary by listing its wire names in `SyntaxConstant` order.
Lean discharges injectivity for the resulting finite function, so duplicate
names are rejected at the definition site. -/
syntax "syntaxVocabulary!" ppLine
  str ppLine str ppLine str ppLine str ppLine str ppLine str ppLine
  str ppLine str ppLine str ppLine str ppLine str ppLine str ppLine
  str ppLine str ppLine str ppLine str ppLine str ppLine str ppLine
  str ppLine str ppLine str ppLine str : term

macro_rules
  | `(syntaxVocabulary!
      $pair:str $kindStar:str $kindArr:str $boolTy:str $arr:str $tyApp:str
      $tyLam:str $tyFv:str $tyExists:str $model:str $primFam:str $primTm:str
      $tmFv:str $app:str $lam:str $bool:str $eq:str $eps:str $nameExtra:str
      $famExtra:str $tmExtra:str $boolExtra:str) =>
    `(SyntaxVocabulary.mk (fun
        | .pair => $pair
        | .kindStar => $kindStar
        | .kindArr => $kindArr
        | .boolTy => $boolTy
        | .arr => $arr
        | .tyApp => $tyApp
        | .tyLam => $tyLam
        | .tyFv => $tyFv
        | .tyExists => $tyExists
        | .model => $model
        | .primFam => $primFam
        | .primTm => $primTm
        | .tmFv => $tmFv
        | .app => $app
        | .lam => $lam
        | .bool => $bool
        | .eq => $eq
        | .eps => $eps
        | .nameExtra => $nameExtra
        | .famExtra => $famExtra
        | .tmExtra => $tmExtra
        | .boolExtra => $boolExtra) (by
          intro left right equal
          cases left <;> cases right <;> simp_all))

/-- A named Amber serialization strategy.  `Strategy` is normally a phantom
marker type; `Ix` is explicit so the same vocabulary can support signed and
natural-number arenas. -/
class Strategy (S : Type u) (Ix : Type v) where
  objects : ObjectSchema
  objects_valid : objects.Valid
  syntaxVocabulary : SyntaxVocabulary
  index : PartialCodec Ix

/-- A strategy-indexed total codec.  The strategy parameter permits several
wire representations of the same semantic type without competing instances. -/
class HasCodec (S : Type u) (α : Type v) where
  codec : Codec α

namespace HasCodec

def encode [HasCodec S α] (value : α) : Nucleus.Cbor :=
  (HasCodec.codec (S := S) (α := α)).encode value

def decode? [HasCodec S α] (value : Nucleus.Cbor) : Option α :=
  (HasCodec.codec (S := S) (α := α)).decode? value

@[simp] theorem decode_encode [HasCodec S α] (value : α) :
    decode? (S := S) (encode (S := S) value) = some value :=
  (HasCodec.codec (S := S) (α := α)).decode_encode value

end HasCodec

namespace Strategy

def encodeIndex [Strategy S Ix] (value : Ix) : Nucleus.Cbor :=
  (Strategy.index (S := S) (Ix := Ix)).encode value

def decodeIndex? [Strategy S Ix] (value : Nucleus.Cbor) : Option Ix :=
  (Strategy.index (S := S) (Ix := Ix)).decode? value

def IndexFits [Strategy S Ix] (value : Ix) : Prop :=
  (Strategy.index (S := S) (Ix := Ix)).Fits value

@[simp] theorem decodeIndex?_encode [Strategy S Ix] (value : Ix)
    (fits : IndexFits (S := S) value) :
    decodeIndex? (S := S) (encodeIndex (S := S) value) =
      some value :=
  (Strategy.index (S := S) (Ix := Ix)).decode_encode value fits

end Strategy

/-- The first concrete string-keyed Amber vocabulary. -/
inductive StringMapV0

def objectSchemaV0 : ObjectSchema where
  tagField := "tag"
  parentField := "parent"
  offsetField := "offset"
  defsField := "defs"
  metadataField := "metadata"
  denseTag := "arena.dense"
  segmentTag := "arena.segment"

def syntaxVocabularyV0 : SyntaxVocabulary := syntaxVocabulary!
  "pair"
  "kind.star"
  "kind.arr"
  "ty.bool"
  "ty.arr"
  "ty.app"
  "ty.lam"
  "ty.fv"
  "tm.ty_exists"
  "ty.model"
  "fam.prim"
  "tm.prim"
  "tm.fv"
  "tm.app"
  "tm.lam"
  "tm.bool"
  "tm.eq"
  "tm.eps"
  "extra.name"
  "extra.fam"
  "extra.tm"
  "extra.bool"

private theorem uint64_ofNat_toNat (value : Nat) (fits : value < 2 ^ 64) :
    (UInt64.ofNat value).toNat = value := by
  change value % 2 ^ 64 = value
  exact Nat.mod_eq_of_lt fits

/-- Unsigned natural-number indices, retained as an alternative useful for
induction and correspondence with the original postorder encoder. -/
def natIndex : PartialCodec Nat where
  encode value := .primitive (.integer (.unsigned (UInt64.ofNat value)))
  decode?
    | .primitive (.integer (.unsigned value)) => some value.toNat
    | _ => none
  Fits value := value < 2 ^ 64
  decode_encode value fits := by
    simp [uint64_ofNat_toNat value fits]

/-- Signed indices use CBOR's native positive and negative integer forms.
`negative n` denotes `-1-n`, exactly matching Lean's `Int.negSucc n`. -/
def intIndex : PartialCodec Int where
  encode
    | .ofNat value => .primitive (.integer (.unsigned (UInt64.ofNat value)))
    | .negSucc value => .primitive (.integer (.negative (UInt64.ofNat value)))
  decode?
    | .primitive (.integer (.unsigned value)) => some (.ofNat value.toNat)
    | .primitive (.integer (.negative value)) => some (.negSucc value.toNat)
    | _ => none
  Fits
    | .ofNat value => value < 2 ^ 64
    | .negSucc value => value < 2 ^ 64
  decode_encode value fits := by
    cases value with
    | ofNat value => simp [uint64_ofNat_toNat value fits]
    | negSucc value => simp [uint64_ofNat_toNat value fits]

instance : Strategy StringMapV0 Int where
  objects := objectSchemaV0
  objects_valid := by simp [ObjectSchema.Valid, objectSchemaV0]
  syntaxVocabulary := syntaxVocabularyV0
  index := intIndex

instance : Strategy StringMapV0 Nat where
  objects := objectSchemaV0
  objects_valid := by simp [ObjectSchema.Valid, objectSchemaV0]
  syntaxVocabulary := syntaxVocabularyV0
  index := natIndex

private def bytesOfO256 (value : O256) : Bytes :=
  ⟨value.bytes.toByteArray⟩

private def o256OfBytes? (value : Bytes) : Option O256 :=
  O256.ofList? value.data.data.toList

/-- O256 remains a bare 32-byte CBOR byte string for every Amber strategy.
The CAS determines the hash function denoted by those bytes. -/
instance : HasCodec S O256 where
  codec :=
    { encode := fun value => .primitive (.bytes (bytesOfO256 value))
      decode? := fun value => match value with
        | .primitive (.bytes bytes) => o256OfBytes? bytes
        | _ => none
      decode_encode := by
        intro value
        simp [o256OfBytes?, bytesOfO256] }

end Nucleus.Hol.Ethane.Amber.Serialization
