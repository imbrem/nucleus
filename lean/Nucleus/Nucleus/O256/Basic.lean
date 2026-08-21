import Nucleus.Hash.Basic
import Nucleus.Bytes

/-! # 256-bit objects -/

namespace Nucleus

/-- A 256-bit hash. -/
abbrev O256 := Hash 256

namespace O256

/-- Big-endian bytes, matching unsigned and lexicographic O256 order. -/
def bytes (value : O256) : List UInt8 :=
  List.ofFn fun i : Fin 32 =>
    UInt8.ofBitVec (value.extractLsb' ((31 - i.val) * 8) 8)

@[simp] theorem bytes_length (value : O256) : value.bytes.length = 32 := by
  simp [bytes]

/-- Parse exactly 32 big-endian bytes. -/
def ofList? (values : List UInt8) : Option O256 :=
  if values.length = 32 then
    some <| BitVec.ofNat 256 <| values.foldl (fun value byte => value * 256 + byte.toNat) 0
  else
    none

/-- Compact byte encoding. -/
def encode (value : O256) : Bytes := ⟨value.bytes.toByteArray⟩

@[simp] theorem encode_length (value : O256) : value.encode.length = 32 := by
  simp [encode, Bytes.length, bytes_length]

end O256

end Nucleus
