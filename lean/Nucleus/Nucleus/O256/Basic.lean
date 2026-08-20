import Mathlib.Data.Fin.Basic

/-! # 256-bit objects -/

namespace Nucleus

/-- Exactly 32 octets. -/
abbrev O256 := Fin 32 → UInt8

namespace O256

/-- Octets in index order. -/
def bytes (value : O256) : List UInt8 := List.ofFn value

@[simp] theorem bytes_length (value : O256) : value.bytes.length = 32 := by
  simp [bytes]

end O256

end Nucleus
