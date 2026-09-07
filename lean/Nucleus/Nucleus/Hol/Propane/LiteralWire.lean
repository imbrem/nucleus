import Nucleus.Hol.Propane.Literal
import Mathlib.Tactic

/-! # Literal payload decoding

This models the checked fields after CBOR container parsing, not the CBOR
parser. Naturals use minimal unsigned big-endian bytes and integers use
minimal two's-complement bytes. Inline storage is optional: small values are
also valid constant-table entries. A byte link never supplies resident bytes.
-/

namespace Nucleus.Hol.Propane.LiteralWire

def maxPayloadBytes : Nat := 1048576

def unsigned (bytes : List UInt8) : Nat :=
  bytes.foldl (fun value byte => value * 256 + byte.toNat) 0

def signed (bytes : List UInt8) : Int :=
  if bytes.head?.any (fun byte => byte.toNat ≥ 128) then
    (unsigned bytes : Int) - (256 : Int) ^ bytes.length
  else unsigned bytes

def canonicalNat : List UInt8 → Bool
  | [] => false
  | [_] => true
  | first :: _ :: _ => first.toNat != 0

def canonicalInt : List UInt8 → Bool
  | [] => false
  | [_] => true
  | first :: second :: _ =>
    !(first.toNat == 0 && second.toNat < 128) &&
    !(first.toNat == 255 && second.toNat ≥ 128)

inductive RawConstant where
  | nat (payload : List UInt8)
  | int (payload : List UInt8)
  | bytes (payload : List UInt8)
  /-- The separately validated raw-byte CID payload; resolution is deferred. -/
  | linkToBytes (cid : List UInt8)
  deriving DecidableEq, Repr

def RawConstant.type : RawConstant → LiteralTy
  | .nat _ => .nat
  | .int _ => .int
  | .bytes _ | .linkToBytes _ => .bytes

def decodeConstant : RawConstant → Option LiteralValue
  | .nat payload =>
    if payload.length ≤ maxPayloadBytes && canonicalNat payload then
      some (.nat (unsigned payload)) else none
  | .int payload =>
    if payload.length ≤ maxPayloadBytes && canonicalInt payload then
      some (.int (signed payload)) else none
  | .bytes payload =>
    if payload.length ≤ maxPayloadBytes then some (.bytes payload) else none
  | .linkToBytes _ => none

def decodeNatInline (value : Nat) : Option LiteralValue :=
  if value < 2 ^ 63 then some (.nat value) else none

def decodeIntInline (value : Int) : Option LiteralValue :=
  if -(2 ^ 63) ≤ value ∧ value < 2 ^ 63 then some (.int value) else none

def decodeWordInline (width : Width) (value : Int) : Option LiteralValue :=
  if -(2 ^ (width.bits - 1)) ≤ value ∧ value < 2 ^ (width.bits - 1) then
    some (.word width (BitVec.ofInt width.bits value)) else none

def decodeConstantRef (table : List RawConstant) (index : Nat) : Option LiteralValue :=
  if index < 2 ^ 32 then table[index]?.bind decodeConstant else none

theorem decodeConstant_type {constant : RawConstant} {value : LiteralValue}
    (decoded : decodeConstant constant = some value) : value.type = constant.type := by
  cases constant <;> simp only [decodeConstant] at decoded
  all_goals first
    | contradiction
    | (split at decoded
       · obtain rfl := Option.some.inj decoded
         rfl
       · contradiction)

@[simp] theorem linked_bytes_are_not_resident (cid : List UInt8) :
    decodeConstant (.linkToBytes cid) = none := rfl

theorem small_nat_storage_independent (payload : List UInt8)
    (bounded : payload.length ≤ maxPayloadBytes)
    (canonical : canonicalNat payload = true)
    (small : unsigned payload < 2 ^ 63) :
    decodeConstant (.nat payload) = decodeNatInline (unsigned payload) := by
  norm_num at small
  simp [decodeConstant, decodeNatInline, bounded, canonical, small]

theorem small_int_storage_independent (payload : List UInt8)
    (bounded : payload.length ≤ maxPayloadBytes)
    (canonical : canonicalInt payload = true)
    (small : -(2 ^ 63) ≤ signed payload ∧ signed payload < 2 ^ 63) :
    decodeConstant (.int payload) = decodeIntInline (signed payload) := by
  norm_num at small
  simp [decodeConstant, decodeIntInline, bounded, canonical, small]

example : decodeConstant (.nat [0]) = some (.nat 0) := by decide
example : decodeConstant (.int [0]) = some (.int 0) := by decide
example : decodeConstant (.int [255]) = some (.int (-1)) := by decide
example : decodeConstant (.int [128]) = some (.int (-128)) := by decide
example : decodeConstant (.int [0, 128]) = some (.int 128) := by decide
example : decodeConstant (.nat [0, 1]) = none := by decide
example : decodeConstant (.int [255, 255]) = none := by decide
example : decodeNatInline (2 ^ 63) = none := by decide
example : decodeIntInline (-(2 ^ 63)) = some (.int (-(2 ^ 63))) := by decide
example : decodeWordInline .i8 (-1) = some (.word .i8 255) := by decide

end Nucleus.Hol.Propane.LiteralWire
