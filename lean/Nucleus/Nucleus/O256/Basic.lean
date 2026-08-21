import Nucleus.Hash.Basic
import Nucleus.Bytes
import Lean.Elab.Tactic.BVDecide

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
    some <| values.foldl
      (fun value byte => value.extractLsb' 0 248 ++ byte.toBitVec) (0#256)
  else
    none

/-- Parsing the canonical big-endian bytes recovers the original object. -/
@[simp] theorem ofList?_bytes (value : O256) :
    ofList? value.bytes = some value := by
  simp only [ofList?, bytes, List.ofFn_succ, Fin.isValue,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, tsub_zero, Nat.reduceMul,
    Fin.val_succ, Nat.reduceSubDiff, one_mul, Fin.val_eq_zero, zero_add,
    tsub_self, zero_mul, List.ofFn_zero, List.length_cons, List.length_nil,
    Nat.reduceAdd, ↓reduceIte, List.foldl_cons, BitVec.extractLsb'_zero,
    List.foldl_nil, Option.some.injEq]
  bv_decide

/-- Compact byte encoding. -/
def encode (value : O256) : Bytes := ⟨value.bytes.toByteArray⟩

@[simp] theorem encode_length (value : O256) : value.encode.length = 32 := by
  simp [encode, Bytes.length, bytes_length]

end O256

end Nucleus
