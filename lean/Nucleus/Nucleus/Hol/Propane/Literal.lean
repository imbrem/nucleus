import Mathlib.Data.BitVec

/-! # Literal values independent of their compact arena representation -/

namespace Nucleus.Hol.Propane

inductive Width where
  | i8 | i16 | i32 | i64
  deriving DecidableEq, Repr

@[reducible] def Width.bits : Width → Nat
  | .i8 => 8 | .i16 => 16 | .i32 => 32 | .i64 => 64

inductive LiteralTy where
  | bool | word (width : Width) | nat | int | bytes
  deriving DecidableEq, Repr

@[reducible] def LiteralTy.denote : LiteralTy → Type
  | .bool => Bool
  | .word width => BitVec width.bits
  | .nat => Nat
  | .int => Int
  | .bytes => List UInt8

def LiteralTy.default : (type : LiteralTy) → type.denote
  | .bool => false
  | .word _ => 0
  | .nat => 0
  | .int => 0
  | .bytes => []

inductive LiteralValue where
  | bool (value : Bool)
  | word (width : Width) (value : BitVec width.bits)
  | nat (value : Nat)
  | int (value : Int)
  | bytes (value : List UInt8)
  deriving DecidableEq, Repr

def LiteralValue.type : LiteralValue → LiteralTy
  | .bool _ => .bool
  | .word width _ => .word width
  | .nat _ => .nat
  | .int _ => .int
  | .bytes _ => .bytes

def LiteralValue.denote : (value : LiteralValue) → value.type.denote
  | .bool value => value
  | .word _ value => value
  | .nat value => value
  | .int value => value
  | .bytes value => value

def LiteralValue.ofDenote : (type : LiteralTy) → type.denote → LiteralValue
  | .bool, value => .bool value
  | .word width, value => .word width value
  | .nat, value => .nat value
  | .int, value => .int value
  | .bytes, value => .bytes value

@[simp] theorem LiteralValue.type_ofDenote (type : LiteralTy) (value : type.denote) :
    (ofDenote type value).type = type := by cases type <;> rfl

@[simp] theorem LiteralValue.ofDenote_denote (value : LiteralValue) :
    ofDenote value.type value.denote = value := by cases value <;> rfl

/-- Type mismatches fail rather than coercing a value to another carrier. -/
def LiteralValue.as (type : LiteralTy) (value : LiteralValue) : Option type.denote :=
  if equal : value.type = type then some (equal ▸ value.denote) else none

@[simp] theorem LiteralValue.as_ofDenote (type : LiteralTy) (value : type.denote) :
    (ofDenote type value).as type = some value := by
  cases type <;> simp [as, ofDenote, LiteralValue.type, denote]

end Nucleus.Hol.Propane
