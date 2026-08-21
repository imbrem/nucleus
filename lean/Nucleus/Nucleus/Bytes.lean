import Mathlib.Data.Nat.Basic

/-! # Byte strings -/

namespace Nucleus

/-- A compact finite byte string. -/
structure Bytes where
  data : ByteArray
  deriving DecidableEq

namespace Bytes

def length (bytes : Bytes) : Nat := bytes.data.size

def push (bytes : Bytes) (byte : UInt8) : Bytes := ⟨bytes.data.push byte⟩

def empty : Bytes := ⟨ByteArray.empty⟩

def append (left right : Bytes) : Bytes := ⟨left.data.append right.data⟩

end Bytes

end Nucleus
