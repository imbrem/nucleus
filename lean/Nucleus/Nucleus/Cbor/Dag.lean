import Nucleus.Cbor.Basic

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

end Nucleus
