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

/-- Relations are presented as premise and conclusion tables. Their packed
representation is private to the implementation. -/
structure Relations where
  premises : RelationTable
  conclusions : RelationTable
  deriving DecidableEq

namespace Internal

/-! The packed representation used to prove correspondence with the Rust
implementation. Clients should use `Relations`, not these masks. -/

abbrev RelationFlags := UInt8

structure RelationEntry where
  left : SRef
  right : SRef
  premiseFlags : RelationFlags
  conclusionFlags : RelationFlags
  deriving DecidableEq

/-- Ordered model of
`BTreeMap<(SRef, SRef), (RelationFlags, RelationFlags)>`. -/
abbrev PackedRelations := List RelationEntry

/-- Whether a byte mask contains the bit assigned to a relation. -/
def RelationFlags.contains (flags : RelationFlags) (relation : Relation) : Bool :=
  (flags.toNat / 2 ^ relation.tag) % 2 == 1

/-- Public projection implemented by `Relations::wire_side`.
`packed` is ordered by `(left, right)`, as a `BTreeMap` is in Rust. -/
def PackedRelations.wireSide (packed : PackedRelations) (conclusion : Bool) : RelationTable :=
  Relation.all.filterMap fun relation =>
    let pairs := packed.filterMap fun entry =>
      let flags := if conclusion then entry.conclusionFlags else entry.premiseFlags
      if flags.contains relation then some (entry.left, entry.right) else none
    if pairs.isEmpty then none else some (relation, pairs)

/-- A public relation table is in Rust's canonical order precisely when it is
the projection of an ordered packed map. Duplicate and order-varying CBOR
tables can still denote the same finite relation before this normalization. -/
def CanonicalRelationTable (table : RelationTable) (conclusion : Bool) : Prop :=
  ∃ packed : PackedRelations, packed.wireSide conclusion = table

end Internal

/-! A heterogeneous logical context. -/
structure Ctx where
  arena : Option LinkRef
  imports : Option O256
  sequents : List LinkRef
  relations : RelationTable
  deriving DecidableEq

/-- The public sequent wire shape. The implementation stores it in ordered
bitflag maps; the corresponding projection is modeled below. -/
structure Seq where
  arena : Option LinkRef
  imports : Option O256
  premiseSequents : List LinkRef
  conclusionSequents : List LinkRef
  premises : RelationTable
  conclusions : RelationTable
  deriving DecidableEq

namespace Internal

abbrev SeqFlags := UInt8

structure ImportedSequentEntry where
  link : LinkRef
  flags : SeqFlags
  deriving DecidableEq

/-- Model of the packed `Seq` representation. Both lists stand for
ordered `BTreeMap`s and therefore contain unique keys. -/
structure PackedSeq where
  arena : Option LinkRef
  imports : Option O256
  sequents : List ImportedSequentEntry
  relations : PackedRelations
  deriving DecidableEq

private def SeqFlags.contains (flags : SeqFlags) (bit : Nat) : Bool :=
  (flags.toNat / 2 ^ bit) % 2 == 1

/-- Projection from packed sequent storage to its public CBOR
fields (`PREMISE = 1`, `CONCLUSION = 2`). -/
def PackedSeq.toPublic (packed : PackedSeq) : Seq where
  arena := packed.arena
  imports := packed.imports
  premiseSequents := packed.sequents.filterMap fun entry =>
    if entry.flags.contains 0 then some entry.link else none
  conclusionSequents := packed.sequents.filterMap fun entry =>
    if entry.flags.contains 1 then some entry.link else none
  premises := packed.relations.wireSide false
  conclusions := packed.relations.wireSide true

end Internal

/-- A `Seq` is a compatible pair of contexts: both sides inhabit the same
arena and import table. -/
structure CompatibleCtxs where
  premises : Ctx
  conclusion : Ctx
  arena_eq : premises.arena = conclusion.arena
  imports_eq : premises.imports = conclusion.imports

namespace Seq

def toContexts (seq : Seq) : CompatibleCtxs where
  premises := ⟨seq.arena, seq.imports, seq.premiseSequents, seq.premises⟩
  conclusion := ⟨seq.arena, seq.imports, seq.conclusionSequents, seq.conclusions⟩
  arena_eq := rfl
  imports_eq := rfl

def ofContexts (contexts : CompatibleCtxs) : Seq where
  arena := contexts.premises.arena
  imports := contexts.premises.imports
  premiseSequents := contexts.premises.sequents
  conclusionSequents := contexts.conclusion.sequents
  premises := contexts.premises.relations
  conclusions := contexts.conclusion.relations

def fromPremises (premises : Ctx) : Seq where
  arena := premises.arena
  imports := premises.imports
  premiseSequents := premises.sequents
  conclusionSequents := []
  premises := premises.relations
  conclusions := []

def fromConclusion (conclusion : Ctx) : Seq where
  arena := conclusion.arena
  imports := conclusion.imports
  premiseSequents := []
  conclusionSequents := conclusion.sequents
  premises := []
  conclusions := conclusion.relations

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
