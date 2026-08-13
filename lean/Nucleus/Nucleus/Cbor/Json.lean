import Nucleus.Cbor.Reasonable
import Nucleus.Json.Rfc
import Nucleus.Json.Equiv

/-!
# Lossless RFC JSON in CBOR

RFC JSON values in this development retain number lexemes.  Ordinary CBOR
numeric conversion preserves the number but not necessarily its spelling, so
this lossless application profile uses a locally selected application tag over
text for number lexemes.
Strings remain ordinary CBOR text.  The distinction makes the embedding
injective even for spellings such as `1`, `1.0`, and `1e0`.

Map entries are obtained from `Json.toRaw`, hence are duplicate-free and in
Lean's canonical string order.  A future RFC 8949 wire encoder can serialize
this semantic representative using the deterministic encoding rules.
-/

namespace Nucleus

namespace RfcJsonCbor

/-- Locally selected, currently unassigned application tag distinguishing
retained JSON number lexemes from ordinary JSON strings. A deployed protocol
must register or replace it. -/
def numberTag : UInt64 := 55802

private def scalar : RfcJsonScalar → Cbor
  | none => .primitive .null
  | some (.bool false) => .primitive .false
  | some (.bool true) => .primitive .true
  | some (.string value) => .primitive (.text value)
  | some (.number literal) => .tag numberTag (.primitive (.text literal))

private abbrev ix : JsonIx → CborIx
  | .val => .value
  | .arr => .array
  | .obj => .map

private def encodeRaw : {i : JsonIx} →
    RawSyn String RfcJsonScalar i → CborSyn (ix i)
  | _, .scalar value => scalar value
  | _, .list values => .array (encodeRaw values)
  | _, .map entries => .map (encodeRaw entries)
  | _, .nil => .arrayNil
  | _, .cons head tail => .arrayCons (encodeRaw head) (encodeRaw tail)
  | _, .objNil => .mapNil
  | _, .objCons key value tail =>
      .mapCons (.primitive (.text key)) (encodeRaw value) (encodeRaw tail)

/-- Lexeme-preserving CBOR representation of an extensional RFC JSON value. -/
noncomputable def encode (value : RfcJson) : Cbor := encodeRaw value.toRaw

private def decodeScalar? : Cbor → Option RfcJsonScalar
  | .primitive (.simple 22) => some none
  | .primitive (.simple 20) => some (some (.bool false))
  | .primitive (.simple 21) => some (some (.bool true))
  | .primitive (.text value) => some (some (.string value))
  | .tag tag (.primitive (.text literal)) =>
      if tag = numberTag then some (some (.number literal)) else none
  | _ => none

mutual
  private def decodeValue? : Cbor → Option (RawSyn String RfcJsonScalar .val)
    | value@(.primitive _) => .scalar <$> decodeScalar? value
    | value@(.tag _ _) => .scalar <$> decodeScalar? value
    | .array values => .list <$> decodeArray? values
    | .map entries => .map <$> decodeMap? entries

  private def decodeArray? : CborSyn .array → Option (RawSyn String RfcJsonScalar .arr)
    | .arrayNil => some .nil
    | .arrayCons head tail => .cons <$> decodeValue? head <*> decodeArray? tail

  private def decodeMap? : CborSyn .map → Option (RawSyn String RfcJsonScalar .obj)
    | .mapNil => some .objNil
    | .mapCons (.primitive (.text key)) value tail =>
        .objCons key <$> decodeValue? value <*> decodeMap? tail
    | _ => none
end

private theorem decodeScalar_scalar (value : RfcJsonScalar) :
    decodeScalar? (scalar value) = some value := by
  rcases value with _ | value
  · rfl
  · cases value with
    | bool b => cases b <;> rfl
    | string _ => rfl
    | number _ => simp [scalar, decodeScalar?, numberTag]

private theorem decode_encodeRaw : ∀ {i : JsonIx} (raw : RawSyn String RfcJsonScalar i),
    (match i with
      | .val => decodeValue? (encodeRaw raw)
      | .arr => decodeArray? (encodeRaw raw)
      | .obj => decodeMap? (encodeRaw raw)) = some raw := by
  intro i raw
  induction raw with
  | scalar value =>
      rcases value with _ | value
      · simp [encodeRaw, scalar, decodeValue?, decodeScalar?, CborPrimitive.null]
      · cases value with
        | bool b => cases b <;> simp [encodeRaw, scalar, decodeValue?, decodeScalar?,
            CborPrimitive.false, CborPrimitive.true]
        | string _ => simp [encodeRaw, scalar, decodeValue?, decodeScalar?]
        | number _ => simp [encodeRaw, scalar, decodeValue?, decodeScalar?, numberTag]
  | list values ih => simp [encodeRaw, decodeValue?, ih]
  | map entries ih => simp [encodeRaw, decodeValue?, ih]
  | nil => simp [encodeRaw, decodeArray?]
  | cons head tail ihHead ihTail => simp [encodeRaw, decodeArray?, ihHead, ihTail]
  | objNil => simp [encodeRaw, decodeMap?]
  | objCons key value tail ihValue ihTail =>
      simp [encodeRaw, decodeMap?, ihValue, ihTail]

private theorem encodeRaw_injective {i : JsonIx} :
    Function.Injective (encodeRaw : RawSyn String RfcJsonScalar i → CborSyn (ix i)) := by
  intro a b h
  have ha := decode_encodeRaw a
  have hb := decode_encodeRaw b
  cases i <;> simp_all

/-- Losslessness: distinct extensional RFC JSON values have distinct canonical
semantic CBOR representatives. -/
theorem encode_injective : Function.Injective encode := by
  intro a b h
  apply Json.toRaw_injective
  exact encodeRaw_injective h

/-- The image subtype packages exactly the CBOR values produced by the
lossless profile. -/
def Image := {value : Cbor // ∃ json, encode json = value}

/-- RFC JSON values and their lossless CBOR image are in bijection. -/
noncomputable def equivImage : RfcJson ≃ Image where
  toFun json := ⟨encode json, json, rfl⟩
  invFun image := Classical.choose image.property
  left_inv json := encode_injective (Classical.choose_spec
    ((⟨encode json, json, rfl⟩ : Image).property))
  right_inv image := Subtype.ext (Classical.choose_spec image.property)

/-- Decode a value known to belong to the lossless CBOR image. -/
noncomputable def decode (value : Image) : RfcJson := equivImage.symm value

@[simp] theorem decode_encode (json : RfcJson) :
    decode (equivImage json) = json := equivImage.left_inv json

@[simp] theorem encode_decode (value : Image) :
    equivImage (decode value) = value := equivImage.right_inv value

end RfcJsonCbor

end Nucleus
