import Nucleus.Json.Extensional

/-!
# RFC JSON values

This module fixes the scalar vocabulary of an RFC 8259 JSON tree while retaining
number lexemes.  Strings are represented by their decoded contents (quotes and
escape syntax have already been removed).  `none` means JSON `null`; it is not an
epistemic unknown.  Partial computations should therefore use a separate outer
type such as `WithBot RfcJson`.
-/

namespace Nucleus

/-- Non-null RFC JSON scalar values.  Number spelling is deliberately retained. -/
inductive RfcJsonAtom where
  | bool (value : Bool)
  | string (decoded : String)
  | number (literal : String)
  deriving DecidableEq, Repr

/-- RFC JSON scalars. `none` is the JSON literal `null`. -/
abbrev RfcJsonScalar := Option RfcJsonAtom

/-- An extensional RFC JSON value, with decoded string keys and values. -/
abbrev RfcJson := Json RfcJsonScalar

namespace RfcJsonScalar

def null : RfcJsonScalar := none
def bool (b : Bool) : RfcJsonScalar := some (.bool b)
def string (s : String) : RfcJsonScalar := some (.string s)
def number (s : String) : RfcJsonScalar := some (.number s)

@[simp] theorem null_ne_bool (b : Bool) : null ≠ bool b := by simp [null, bool]
@[simp] theorem null_ne_string (s : String) : null ≠ string s := by simp [null, string]
@[simp] theorem null_ne_number (s : String) : null ≠ number s := by simp [null, number]

end RfcJsonScalar

/-- A partial RFC JSON result. Bottom means unavailable/invalid, whereas a scalar
`none` inside `RfcJson` is the ordinary JSON value `null`. -/
abbrev PartialRfcJson := WithBot RfcJson

end Nucleus
