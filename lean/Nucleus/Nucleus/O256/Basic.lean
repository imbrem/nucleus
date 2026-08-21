import Mathlib.Data.List.OfFn

/-! # 256-bit objects -/

namespace Nucleus

/-- Exactly 32 octets.  The concrete hash algorithm belongs to the CAS. -/
abbrev O256 := Fin 32 → UInt8

namespace O256

/-- Octets in index order. -/
def bytes (value : O256) : List UInt8 := List.ofFn value

@[simp] theorem bytes_length (value : O256) : value.bytes.length = 32 := by
  simp [bytes]

/-- Check a list for the exact O256 width. -/
def ofList? (values : List UInt8) : Option O256 :=
  if width : values.length = 32 then
    some fun index => values[index.val]'(by rw [width]; exact index.isLt)
  else
    none

@[simp] theorem ofList?_bytes (value : O256) : ofList? value.bytes = some value := by
  unfold ofList?
  rw [dif_pos (bytes_length value)]
  congr 1
  funext index
  change (List.ofFn value)[index.val] = value index
  rw [List.getElem_ofFn]

end O256

end Nucleus
