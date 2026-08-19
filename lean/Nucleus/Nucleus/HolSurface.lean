import Nucleus.Cbor.Bytes
import Mathlib.Logic.Equiv.Defs

/-!
# Indexed HolE arena objects

This file models the indexed syntax and sequent representations implemented by
`covalence-logic-hol`. Wire codecs live in `Nucleus.HolSurface.Cbor`.
-/

namespace Nucleus.HolSurface

noncomputable section

def maxRef : Nat := 2 ^ 31 - 1

/-- Arena indices are nonzero `u32` values bounded by `i32::MAX`. -/
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

/-- A 32-byte object identifier and the hash function used to produce it. -/
class Hash32 (α : Type) where
  bytes : α ≃ { value : Nucleus.Bytes // Nucleus.Bytes.length value = 32 }
  hash : Nucleus.Bytes → α

/-- The object identifier. Its hash algorithm remains abstract in Lean. -/
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

/-- Reuse an existing ID or append a new address. Appending fails when the new
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
  /-- Translating the final index remains within the arena index range. -/
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
  | tyExists (predicate : Ref)
  | tyModel (predicate : Ref)
  | tmBv (index : UInt32)
  | tmFv (name : UInt32) (type : Ref)
  | tmApp (function argument : Ref)
  | tmLam (domain body : Ref)
  | tmBool (value : Bool)
  /-- Equality with its shared operand type inferred by the LCF checker. -/
  | tmEq (left right : Ref)
  | tmEps (type predicate : Ref)
  | tmAbs (carrier predicate value : Ref)
  | tmRep (carrier predicate value : Ref)
  /-- Total surface conversion: identity at equal types, inhabited garbage otherwise. -/
  | tmCast (term target : Ref)
  deriving DecidableEq

def Expr.tag : Expr → Nat
  | .kindStar => 0 | .kindArr .. => 1 | .tyBool => 2 | .tyArr .. => 3
  | .tyApp .. => 4 | .tyLam .. => 5 | .tyBv .. => 6
  | .tySub .. => 7 | .tyExists .. => 8 | .tyModel .. => 9
  | .tmBv .. => 13 | .tmFv .. => 14 | .tmApp .. => 15 | .tmLam .. => 16
  | .tmBool .. => 17 | .tmEq .. => 18 | .tmEps .. => 19
  | .tmAbs .. => 20 | .tmRep .. => 21 | .tmCast .. => 23

def Expr.children : Expr → List Ref
  | .kindStar | .tyBool | .tyBv _ | .tmBv _ | .tmBool _ => []
  | .kindArr a b | .tyArr a b | .tyApp a b | .tyLam a b | .tySub a b
  | .tmApp a b | .tmLam a b | .tmEps a b | .tmCast a b => [a, b]
  | .tyExists p | .tyModel p => [p]
  | .tmFv _ A => [A]
  | .tmEq x y => [x, y]
  | .tmAbs A x y | .tmRep A x y => [A, x, y]

class TrustedVec (V : Type → Type) where
  toList {α : Type} : V α → List α

instance : TrustedVec List where
  toList := id

/-- Logical model of immutable slice storage. -/
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

/-- A signed relation endpoint. `i32::MIN` is excluded because its magnitude is one
larger than the largest arena reference; every remaining value has exactly one
of the null, positive-reference, or negative-reference interpretations. -/
structure SRef where
  raw : Int32
  valid : raw ≠ Int32.minValue
  deriving DecidableEq

/-- Interpretation of a signed relation endpoint. -/
inductive SRefView where | null | pos (ref : Ref) | neg (ref : Ref)
  deriving DecidableEq

def relReserved : UInt32 := 0x80000000

inductive Relation where
  | synEq | convEq | tyEq | hasTy | imp | eq | hasKind | ne
  deriving DecidableEq

def Relation.all : List Relation :=
  [.synEq, .convEq, .tyEq, .hasTy, .imp, .eq, .hasKind, .ne]

def Relation.tag : Relation → Nat
  | .synEq => 0 | .convEq => 1 | .tyEq => 2 | .hasTy => 3
  | .imp => 4 | .eq => 5 | .hasKind => 6 | .ne => 7

def Relation.symmetric : Relation → Bool
  | .synEq | .convEq | .tyEq | .eq | .ne => true
  | .hasTy | .imp | .hasKind => false

/-- The public, relation-indexed view used by the wire format and API. -/
abbrev RelationTable := List (Relation × List (SRef × SRef))

/-- One sparse logical side. The Rust representation stores the same two
fields directly. -/
structure CtxBody where
  sequents : List LinkRef
  relations : RelationTable
  deriving DecidableEq

def CtxBody.empty : CtxBody := ⟨[], []⟩

/-! A heterogeneous logical context. -/
structure Ctx where
  arena : Option LinkRef
  imports : Option O256
  body : CtxBody
  deriving DecidableEq

/-- A sequent with one shared scope and two ordinary context bodies. E-classes
and packed indexes can be derived from this sparse representation. -/
structure Seq where
  arena : Option LinkRef
  imports : Option O256
  premises : CtxBody
  conclusion : CtxBody
  deriving DecidableEq

/-- A `Seq` is a compatible pair of contexts: both sides inhabit the same
arena and import table. -/
structure CompatibleCtxs where
  premises : Ctx
  conclusion : Ctx
  arena_eq : premises.arena = conclusion.arena
  imports_eq : premises.imports = conclusion.imports

namespace Seq

def toContexts (seq : Seq) : CompatibleCtxs where
  premises := ⟨seq.arena, seq.imports, seq.premises⟩
  conclusion := ⟨seq.arena, seq.imports, seq.conclusion⟩
  arena_eq := rfl
  imports_eq := rfl

def ofContexts (contexts : CompatibleCtxs) : Seq where
  arena := contexts.premises.arena
  imports := contexts.premises.imports
  premises := contexts.premises.body
  conclusion := contexts.conclusion.body

def fromPremises (premises : Ctx) : Seq where
  arena := premises.arena
  imports := premises.imports
  premises := premises.body
  conclusion := .empty

def fromConclusion (conclusion : Ctx) : Seq where
  arena := conclusion.arena
  imports := conclusion.imports
  premises := .empty
  conclusion := conclusion.body

@[simp] theorem fromPremises_premises (premises : Ctx) :
    (fromPremises premises).toContexts.premises = premises := rfl

@[simp] theorem fromConclusion_conclusion (conclusion : Ctx) :
    (fromConclusion conclusion).toContexts.conclusion = conclusion := rfl

@[simp] theorem ofContexts_toContexts (seq : Seq) :
    ofContexts seq.toContexts = seq := rfl

theorem toContexts_ofContexts (contexts : CompatibleCtxs) :
    (ofContexts contexts).toContexts = contexts := by
  cases contexts with
  | mk premises conclusion arena_eq imports_eq =>
    cases premises
    cases conclusion
    cases arena_eq
    cases imports_eq
    rfl

end Seq

end

end Nucleus.HolSurface
