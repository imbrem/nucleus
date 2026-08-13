import Nucleus.Cbor.Basic
import Nucleus.Cbor.Profiles
import Nucleus.Json.Equiv

/-!
# DAG-CBOR data model

DAG-CBOR is IPLD's linked CBOR profile. Maps have text keys; links are a
distinct semantic leaf rather than arbitrary tags. On the wire, a link is
CBOR tag 42 applied to a byte string containing `0x00` followed by a binary
CID. Other tags are outside this profile.

Wire validity additionally requires definite shortest encodings, sorted map
keys, finite non-negative-zero floats, and exactly one top-level item. Those
are encoding predicates, not constructors of the semantic data model.
-/

namespace Nucleus

variable {Name : Type}

/-- Scalar values admitted by the DAG-CBOR semantic surface. -/
inductive DagCborScalar (Name : Type) where
  | null
  | bool (value : Bool)
  | integer (value : CborInteger)
  | float64 (bits : UInt64)
  | text (value : String)
  | bytes (value : Bytes)
  | link (name : Name)
  deriving DecidableEq

/-- Linked DAG-CBOR with string map keys. -/
abbrev DagCbor (Name : Type) := Json (DagCborScalar Name)

/-- Forget links into a caller-chosen byte representation. The caller owns
CID validation; the leading identity byte and tag 42 belong to wire encoding. -/
def DagCborScalar.eraseLink (encodeCid : Name → Bytes) :
    DagCborScalar Name → StringKeyCborScalar
  | .null => .null
  | .bool value => .bool value
  | .integer value => .integer value
  | .float64 bits => .float64 bits
  | .text value => .text value
  | .bytes value => .bytes value
  | .link name => .bytes (encodeCid name)

/-- The underlying string-key tree after erasing link identity. This is not
the DAG-CBOR wire encoding, because tag 42 is intentionally retained at the
semantic/link layer. -/
def DagCbor.eraseLinks (encodeCid : Name → Bytes) (value : DagCbor Name) :
    StringKeyCbor := value.mapScalar (DagCborScalar.eraseLink encodeCid)

namespace DagCbor

private def scalarToCbor (encodeLink : Name → Bytes) : DagCborScalar Name → Cbor
  | .null => .primitive .null
  | .bool false => .primitive .false
  | .bool true => .primitive .true
  | .integer value => .primitive (.integer value)
  | .float64 bits => .primitive (.float64 bits)
  | .text value => .primitive (.text value)
  | .bytes value => .primitive (.bytes value)
  | .link name => .tag 42 (.primitive (.bytes (encodeLink name)))

private abbrev cborIx : JsonIx → CborIx
  | .val => .value
  | .arr => .array
  | .obj => .map

private def rawToCbor (encodeLink : Name → Bytes) : {i : JsonIx} →
    RawSyn String (DagCborScalar Name) i → CborSyn (cborIx i)
  | _, .scalar value => scalarToCbor encodeLink value
  | _, .list values => .array (rawToCbor encodeLink values)
  | _, .map entries => .map (rawToCbor encodeLink entries)
  | _, .nil => .arrayNil
  | _, .cons head tail =>
      .arrayCons (rawToCbor encodeLink head) (rawToCbor encodeLink tail)
  | _, .objNil => .mapNil
  | _, .objCons key value tail =>
      .mapCons (.primitive (.text key)) (rawToCbor encodeLink value)
        (rawToCbor encodeLink tail)

/-- Embed the DAG-CBOR semantic model into full CBOR. `encodeLink` supplies
the tag-42 byte-string payload, including the required leading identity byte. -/
noncomputable def toCbor (encodeLink : Name → Bytes) (value : DagCbor Name) : Cbor :=
  rawToCbor encodeLink value.toRaw

/-- Full CBOR values belonging to the semantic DAG-CBOR subset. Wire-level
determinism additionally constrains the serialization of this representative. -/
def IsDagCbor (encodeLink : Name → Bytes) (value : Cbor) : Prop :=
  ∃ dag : DagCbor Name, toCbor encodeLink dag = value

/-- DAG-CBOR is represented as an actual refinement of full CBOR. -/
abbrev Subset (encodeLink : Name → Bytes) := {value : Cbor // IsDagCbor encodeLink value}

private theorem raw_not_undefined (encodeLink : Name → Bytes)
    (raw : RawSyn String (DagCborScalar Name) .val) :
    rawToCbor encodeLink raw ≠ .primitive .undefined := by
  cases raw with
  | scalar value =>
      cases value with
      | bool b => cases b <;> simp [rawToCbor, scalarToCbor,
          CborPrimitive.false, CborPrimitive.true, CborPrimitive.undefined]
      | null | integer _ | float64 _ | text _ | bytes _ | link _ =>
          simp [rawToCbor, scalarToCbor, CborPrimitive.null, CborPrimitive.undefined]
  | list _ => simp [rawToCbor, CborPrimitive.undefined]
  | map _ => simp [rawToCbor, CborPrimitive.undefined]

/-- The refinement is strict: CBOR `undefined` is valid full CBOR but is not
an IPLD data-model value and therefore not DAG-CBOR. -/
theorem undefined_not_dag (encodeLink : Name → Bytes) :
    ¬ IsDagCbor encodeLink (.primitive .undefined) := by
  rintro ⟨dag, h⟩
  exact raw_not_undefined encodeLink dag.toRaw h

end DagCbor

end Nucleus
