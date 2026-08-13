import Nucleus.Cbor.Bytes
import Nucleus.Json.Extensional
import Nucleus.Json.Sqlite

/-!
# String-key CBOR

This is the JSON-shaped CBOR dialect requested as the first, MessagePack-like
surface: JSON containers and string map keys, plus native byte strings and the
full CBOR integer range.  It is intentionally called “MessagePack-like” rather
than MessagePack: full MessagePack also permits non-string keys and extensions.

The tree is an abbreviation of `Json`, so all generic JSON structural and
monad theorems are reused definitionally.
-/

namespace Nucleus

/-- A CBOR integer, represented exactly as major type 0 or major type 1's
unsigned argument. `negative n` denotes `-1 - n`, reaching `-2^64`. -/
inductive CborInteger where
  | unsigned (argument : UInt64)
  | negative (argument : UInt64)
  deriving DecidableEq

/-- Scalar leaves in the string-key, tag-free CBOR dialect. Float payloads are
kept as binary64 bits so NaNs and signed zero are not silently collapsed. -/
inductive StringKeyCborScalar where
  | null
  | bool (value : Bool)
  | integer (value : CborInteger)
  | float64 (bits : UInt64)
  | text (value : String)
  | bytes (value : Bytes)
  deriving DecidableEq

/-- JSON-shaped CBOR with string keys, native bytes, and no tags. -/
abbrev StringKeyCbor := Json StringKeyCborScalar

/-- Raw ordered syntax for the same dialect, suitable for a later parser. -/
abbrev RawStringKeyCbor := RawJson StringKeyCborScalar

/-- Map keys in the integer-key extension used as a convenient COSE host. -/
inductive CborLabel where
  | text (value : String)
  | integer (value : CborInteger)
  deriving DecidableEq

/-- The tag-free dialect which additionally permits integer map keys. -/
abbrev LabelledCbor := Json StringKeyCborScalar CborLabel

namespace StringKeyCbor

/-- Every generic JSON theorem applies directly to this dialect. -/
example (value : StringKeyCbor) : value.mapScalar id = value :=
  Json.mapScalar_id value

end StringKeyCbor

end Nucleus
