import Nucleus.Cbor.Bytes
import Mathlib.Logic.Equiv.Defs

/-!
# Indexed HolE syntax arena

This file mirrors the syntax-only portion of `covalence-logic-hol`'s v0 Rust
arena representation. Sequent and relation representations deliberately live
in a higher layer.
-/

namespace Nucleus.HolSurface

noncomputable section

def maxRef : Nat := 2 ^ 31 - 1

/-- Rust `Ix(NonZeroU32)`: exactly the positive `i32` range. -/
structure Ref where
  value : Nat
  positive : 0 < value
  bounded : value ≤ maxRef
  deriving DecidableEq

namespace Ref

def ofNat? (value : Nat) : Option Ref :=
  if positive : 0 < value then
    if bounded : value ≤ maxRef then some ⟨value, positive, bounded⟩ else none
  else none

@[simp] theorem ofNat?_value (value : Ref) : ofNat? value.value = some value := by
  simp [ofNat?, value.positive, value.bounded]

end Ref

inductive Format where | blob | cborDense | cborSparse
  deriving DecidableEq

def Format.tag : Format → Nat
  | .blob => 0 | .cborDense => 1 | .cborSparse => 2

inductive ObjectKind where | bytes | importTable | arena | sequent
  deriving DecidableEq

def ObjectKind.tag : ObjectKind → Nat
  | .bytes => 0 | .importTable => 1 | .arena => 2 | .sequent => 3

/-- A 32-byte object identifier representation and its hashing operation. -/
class Hash32 (α : Type) where
  bytes : α ≃ { value : Nucleus.Bytes // Nucleus.Bytes.length value = 32 }
  hash : Nucleus.Bytes → α

/-- Rust's `O256`, kept opaque together with its concrete hashing algorithm. -/
opaque O256 : Type
axiom O256.hash32 : Hash32 O256
attribute [instance] O256.hash32

instance : DecidableEq O256 := fun left right =>
  decidable_of_iff (Hash32.bytes left = Hash32.bytes right) Hash32.bytes.injective.eq_iff

structure Link where
  addr : O256
  format : Format
  kind : ObjectKind
  deriving DecidableEq

/-- A reference through the flat hash import table. Interpretation metadata is
stored here rather than behind the content hash. -/
structure LinkRef where
  importId : UInt32
  format : Format
  kind : ObjectKind
  deriving DecidableEq

abbrev ImportTable := List O256
abbrev ImportId := UInt32

namespace ImportTable

private def findIndexFrom (address : O256) : List O256 → Nat → Option Nat
  | [], _ => none
  | candidate :: rest, index =>
      if candidate = address then some index else findIndexFrom address rest (index + 1)

def findIndex? (table : ImportTable) (address : O256) : Option Nat :=
  findIndexFrom address table 0

/-- Exact value model of Rust's mutating `ImportTable::push`: reuse an
existing ID, append a new address otherwise, and fail only when the resulting
ID is not representable by `u32`. -/
def push? (table : ImportTable) (address : O256) : Option (ImportTable × ImportId) :=
  let index := (findIndex? table address).getD table.length
  if index ≤ UInt32.size - 1 then
    let updated := if (findIndex? table address).isSome then table else table ++ [address]
    some (updated, UInt32.ofNat index)
  else none

@[simp] theorem push?_empty (address : O256) : push? [] address = some ([address], 0) := by
  simp [push?, findIndex?, findIndexFrom]

@[simp] theorem push?_singleton_same (address : O256) :
    push? [address] address = some ([address], 0) := by
  simp [push?, findIndex?, findIndexFrom]

end ImportTable

structure Segment where
  start : Ref
  «end» : Ref
  link : LinkRef
  sourceStart : Ref
  nonempty : start.value < «end».value
  arenaKind : link.kind = .arena
  /-- Rust checks that translating the final index remains an `Ix`. -/
  sourceBound : sourceStart.value + («end».value - start.value - 1) ≤ maxRef

inductive Expr where
  | kindStar
  | kindArr (domain codomain : Ref)
  | tyBool
  | tyArr (domain codomain : Ref)
  | tyApp (function argument : Ref)
  | tyLam (domain body : Ref)
  | tyBv (index : UInt32)
  | tySub (carrier predicate : Ref)
  | tyModel (predicate : Ref)
  deriving DecidableEq

def Expr.tag : Expr → Nat
  | .kindStar => 0 | .kindArr .. => 1 | .tyBool => 2 | .tyArr .. => 3
  | .tyApp .. => 4 | .tyLam .. => 5 | .tyBv .. => 6
  | .tySub .. => 7 | .tyModel .. => 9

def Expr.children : Expr → List Ref
  | .kindStar | .tyBool | .tyBv _ => []
  | .kindArr a b | .tyArr a b | .tyApp a b | .tyLam a b | .tySub a b => [a, b]
  | .tyModel p => [p]

class TrustedVec (V : Type → Type) where
  toList {α : Type} : V α → List α

instance : TrustedVec List where
  toList := id

/-- Logical model of Rust's immutable slice storage family. -/
structure StaticVec (α : Type) where
  values : List α
  deriving DecidableEq

instance : TrustedVec StaticVec where
  toList := StaticVec.values

structure Arena (V : Type → Type := List) where
  imports : Option O256
  segments : V Segment
  localBase : UInt32
  defs : V Expr

abbrev StaticArena := Arena StaticVec

def Arena.toOwned {V : Type → Type} [TrustedVec V] (arena : Arena V) : Arena :=
  ⟨arena.imports, TrustedVec.toList arena.segments, arena.localBase,
    TrustedVec.toList arena.defs⟩

def StaticArena.empty : StaticArena := ⟨none, ⟨[]⟩, 1, ⟨[]⟩⟩

@[simp] theorem StaticArena.empty_toOwned : StaticArena.empty.toOwned = ⟨none, [], 1, []⟩ := rfl

inductive Resolve where
  | local (expr : Expr)
  | lazy (link : Link) (index : Ref)
  | wrongKind (link : Link)
  | missing

end

end Nucleus.HolSurface
