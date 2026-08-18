/-!
# Indexed HolE arena objects

This file mirrors `covalence-logic-hol`'s v0 Rust representation. Wire codecs
live in `Nucleus.HolSurface.Cbor`.
-/

namespace Nucleus.HolSurface

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

inductive Format where | blob | cbor
  deriving DecidableEq

def Format.tag : Format → Nat | .blob => 0 | .cbor => 1

inductive ObjectKind where | bytes | importTable | arena | theorem
  deriving DecidableEq

def ObjectKind.tag : ObjectKind → Nat
  | .bytes => 0 | .importTable => 1 | .arena => 2 | .theorem => 3

/-- The exact 32-byte Rust `O256` payload, abstracted from hash semantics. -/
structure Hash where
  bytes : ByteArray
  length : bytes.size = 32
  deriving DecidableEq

structure Link where
  addr : Hash
  format : Format
  kind : ObjectKind
  deriving DecidableEq

/-- Rust's typed `Link<T>` pairs a link with the marker-type invariant checked
during deserialization. -/
structure TypedLink (kind : ObjectKind) where
  link : Link
  typed : link.kind = kind
  deriving DecidableEq

abbrev ImportTable := List Link
abbrev ImportId := UInt32

structure Segment where
  start : Ref
  «end» : Ref
  importId : ImportId
  sourceStart : Ref
  nonempty : start.value < «end».value

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

structure Arena where
  imports : TypedLink .importTable
  segments : List Segment
  localBase : UInt32
  defs : List Expr

inductive Resolve where
  | local (expr : Expr)
  | lazy (link : Link) (index : Ref)
  | wrongKind (link : Link)
  | missing

/-- A relation endpoint is a signed literal stored in all 32 bits. `0` and
Rust's reserved `i32::MIN` encoding are null. -/
inductive RelRef where | null | pos (ref : Ref) | neg (ref : Ref)
  deriving DecidableEq

def relReservedNull : UInt32 := 0x80000000

inductive Relation where
  | synEq | convEq | tyEq | hasTy | imp | eq | hasKind | ne
  deriving DecidableEq

def Relation.tag : Relation → Nat
  | .synEq => 0 | .convEq => 1 | .tyEq => 2 | .hasTy => 3
  | .imp => 4 | .eq => 5 | .hasKind => 6 | .ne => 7

def Relation.symmetric : Relation → Bool
  | .synEq | .convEq | .tyEq | .eq | .ne => true
  | .hasTy | .imp | .hasKind => false

/-- The public, relation-indexed view used by the wire format and API. -/
abbrev RelationTable := List (Relation × List (UInt32 × UInt32))

/-- Relations are presented as premise and conclusion tables.  Their packed
Rust representation is deliberately not part of this interface. -/
structure Relations where
  premises : RelationTable
  conclusions : RelationTable
  deriving DecidableEq

namespace Internal

/-! These definitions model the Rust implementation and are used by the
codec correctness proof.  Clients should use `Relations`, not these masks. -/

abbrev RelationFlags := UInt8

structure RelationEntry where
  left : UInt32
  right : UInt32
  premiseFlags : RelationFlags
  conclusionFlags : RelationFlags
  deriving DecidableEq

/-- Ordered model of Rust's private
`BTreeMap<(RelRef, RelRef), (RelationFlags, RelationFlags)>`. -/
abbrev PackedRelations := List RelationEntry

end Internal

/-! `Proposition` is used rather than `Prop`, which is Lean's built-in sort.
Rust calls this type `Prop`. -/
structure Proposition where
  arena : TypedLink .arena
  imports : TypedLink .importTable
  theorems : List ImportId
  relations : RelationTable
  deriving DecidableEq

/-- Rust `Thm`'s exact public/wire data. -/
structure Thm where
  arena : TypedLink .arena
  imports : TypedLink .importTable
  premiseTheorems : List ImportId
  conclusionTheorems : List ImportId
  premises : RelationTable
  conclusions : RelationTable
  deriving DecidableEq

/-- The precise replacement for the informal `Thm ≅ Proposition ×
Proposition`: the two sides must inhabit the same arena and import table. -/
structure CompatibleProps where
  premises : Proposition
  conclusion : Proposition
  arena_eq : premises.arena = conclusion.arena
  imports_eq : premises.imports = conclusion.imports

namespace Thm

def toProps (thm : Thm) : CompatibleProps where
  premises := ⟨thm.arena, thm.imports, thm.premiseTheorems, thm.premises⟩
  conclusion := ⟨thm.arena, thm.imports, thm.conclusionTheorems, thm.conclusions⟩
  arena_eq := rfl
  imports_eq := rfl

def ofProps (props : CompatibleProps) : Thm where
  arena := props.premises.arena
  imports := props.premises.imports
  premiseTheorems := props.premises.theorems
  conclusionTheorems := props.conclusion.theorems
  premises := props.premises.relations
  conclusions := props.conclusion.relations

def fromPremises (premises : Proposition) : Thm where
  arena := premises.arena
  imports := premises.imports
  premiseTheorems := premises.theorems
  conclusionTheorems := []
  premises := premises.relations
  conclusions := []

def fromConclusion (conclusion : Proposition) : Thm where
  arena := conclusion.arena
  imports := conclusion.imports
  premiseTheorems := []
  conclusionTheorems := conclusion.theorems
  premises := []
  conclusions := conclusion.relations

@[simp] theorem fromPremises_premises (premises : Proposition) :
    (fromPremises premises).toProps.premises = premises := rfl

@[simp] theorem fromConclusion_conclusion (conclusion : Proposition) :
    (fromConclusion conclusion).toProps.conclusion = conclusion := rfl

@[simp] theorem ofProps_toProps (thm : Thm) : ofProps thm.toProps = thm := rfl

theorem toProps_ofProps (props : CompatibleProps) : (ofProps props).toProps = props := by
  cases props with
  | mk premises conclusion arena_eq imports_eq =>
    cases premises
    cases conclusion
    cases arena_eq
    cases imports_eq
    rfl

end Thm

end Nucleus.HolSurface
