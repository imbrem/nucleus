import Nucleus.Bytes

/-!
# CBOR byte strings

The wrapper keeps CBOR's byte-string type distinct from text while retaining
Lean's compact `ByteArray` runtime representation.  Wire-format modules can
extend this API without exposing representation choices to the data model.
-/

namespace Nucleus
namespace Bytes

/-- The largest argument representable by a CBOR definite-length head. -/
def maxDefiniteLength : Nat := 2 ^ 64 - 1

/-- A byte string can use one definite-length CBOR item. -/
def DefiniteLength (bytes : Bytes) : Prop := bytes.length ≤ maxDefiniteLength

end Bytes

end Nucleus
