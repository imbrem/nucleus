import Nucleus.Hol.Propane.Compact
import Nucleus.Hol.Ethane.Semantics
import Nucleus.HolE.ClassicalNaturals

/-!
# Lowering compact Propane values to Ethane

This module is the concrete boundary between Propane's compact userspace
syntax and ordinary closed Ethane terms.  An `InitPackage` contains only
Ethane syntax, its ordinary typing/evaluation evidence, and semantic equations
proved by the init package.  Constructing the package may use an arena
certificate, but lowering itself cannot mint a theorem.

Bytes are presented as finite sequences of `Fin 256`.  `Bytes` remains only a
host representation used by literals and the reference semantics.  Slice is
an ordinary total Ethane epsilon term; its equation is deliberately available
only under `start ≤ stop ≤ len value`.
-/

namespace Nucleus.Hol.Propane.Compact.Ethane

open Nucleus.HolE
open Nucleus.HolE.Named
open Nucleus.HolE.Infinity

abbrev ByteSeq := List (Fin 256)

/-- The ordinary HOL byte carrier is finite sequences of octets. -/
def bytesEquiv : Nucleus.Bytes ≃ ByteSeq where
  toFun bytes := bytes.toList.map UInt8.toFin
  invFun bytes := Nucleus.Bytes.ofList (bytes.map UInt8.ofFin)
  left_inv bytes := by
    apply Nucleus.Bytes.ext
    simp only [Nucleus.Bytes.toList_ofList, List.map_map]
    rw [show UInt8.ofFin ∘ UInt8.toFin = id from funext UInt8.ofFin_toFin]
    simp
  right_inv bytes := by
    simp only [Nucleus.Bytes.toList_ofList, List.map_map]
    rw [show UInt8.toFin ∘ UInt8.ofFin = id from funext UInt8.toFin_ofFin]
    simp

@[simp] theorem bytesEquiv_apply_toList (bytes : Nucleus.Bytes) :
    (bytesEquiv bytes).map UInt8.ofFin = bytes.toList := by
  rw [show (bytesEquiv bytes).map UInt8.ofFin =
    (bytes.toList.map UInt8.toFin).map UInt8.ofFin from rfl, List.map_map]
  rw [show UInt8.ofFin ∘ UInt8.toFin = id from funext UInt8.ofFin_toFin]
  simp

/-- The three semantic carriers used to audit Ethane evaluation evidence. -/
def default : (type : Compact.Ty) → type.denote
  | .bool => false
  | .nat => 0
  | .int => 0
  | .bytes => Nucleus.Bytes.empty

def semantic (type : Compact.Ty) : Pointed := ⟨type.denote, default type⟩

/-- Checked closed Ethane types for the compact base types. -/
structure BaseTypes where
  typeSyntax : Compact.Ty → Nucleus.Hol.Ethane.Ty Nucleus.HolE.EmptySig
  denotes : (type : Compact.Ty) →
    Nucleus.Hol.Ethane.DenotesFam (.nil : TyScope []) emptyTypeEnv
      (typeSyntax type) (semantic type)
  bool_eq : typeSyntax .bool = .boolTy

/-- An ordinary closed Ethane term together with its checked evaluation.  The
evaluation entails typing, so malformed or merely named frontend syntax cannot
inhabit this boundary. -/
structure Term (types : BaseTypes) (type : Compact.Ty) where
  expression : Nucleus.Hol.Ethane.Tm Nucleus.HolE.EmptySig
  value : type.denote
  evaluates : Nucleus.Hol.Ethane.Eval (.nil : TyScope [])
    (.nil : TmScope Nucleus.HolE.EmptySig 0) emptyTypeEnv
    (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx Nucleus.HolE.EmptySig [] 0)
    emptyRawBoundEnv expression (types.typeSyntax type) (semantic type) value

namespace Term

/-- Evaluation evidence exposes ordinary Ethane typing for every lowered
term. -/
theorem hasType {types : BaseTypes} {type : Compact.Ty} (term : Term types type) :
    Nucleus.Hol.Ethane.HasType (.nil : TyScope [])
      (.nil : TmScope Nucleus.HolE.EmptySig 0)
      (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx Nucleus.HolE.EmptySig [] 0)
      term.expression (types.typeSyntax type) :=
  term.evaluates.hasType

end Term

/-- Checked init operations used by compact lowering.  Every constructor
returns an evaluated Ethane term.  The natural bridge records that literals
are iterations of the certified infinity-derived successor, rather than host
constants with an independent meaning. -/
structure InitPackage where
  types : BaseTypes
  naturals : CNatModel
  naturalToNat : naturals.carrier ≃ Nat
  naturalLiteral (value : Nat) : Term types .nat
  naturalLiteral_from_package (value : Nat) :
    (naturalLiteral value).value = naturalToNat (naturals.ofNat value)
  naturalToNat_ofNat (value : Nat) :
    naturalToNat (naturals.ofNat value) = value
  integerLiteral (value : Int) : Term types .int
  integerLiteral_value (value : Int) : (integerLiteral value).value = value
  bool (value : Bool) : Term types .bool
  bytes (literal : Nucleus.Bytes) : Term types .bytes
  bytes_presentation (literal : Nucleus.Bytes) :
    bytesEquiv (bytes literal).value = bytesEquiv literal
  add (left right : Term types .nat) : Term types .nat
  le (left right : Term types .nat) : Term types .bool
  lt (left right : Term types .nat) : Term types .bool
  cat (left right : Term types .bytes) : Term types .bytes
  len (value : Term types .bytes) : Term types .nat
  slicePredicate (value : Term types .bytes) (start stop : Term types .nat) :
    Nucleus.Hol.Ethane.Tm Nucleus.HolE.EmptySig
  slice (value : Term types .bytes) (start stop : Term types .nat) :
    Term types .bytes
  slice_is_epsilon (value : Term types .bytes) (start stop : Term types .nat) :
    (slice value start stop).expression =
      Nucleus.Hol.Ethane.Expr.eps (types.typeSyntax .bytes)
        (slicePredicate value start stop)
  substring (needle haystack : Term types .bytes) : Term types .bool
  bool_value (value : Bool) : (bool value).value = value
  bytes_value (literal : Nucleus.Bytes) : (bytes literal).value = literal
  add_value (left right : Term types .nat) :
    (add left right).value = left.value + right.value
  le_value (left right : Term types .nat) :
    (le left right).value = decide (left.value ≤ right.value)
  lt_value (left right : Term types .nat) :
    (lt left right).value = decide (left.value < right.value)
  cat_value (left right : Term types .bytes) :
    (cat left right).value = left.value.append right.value
  len_value (value : Term types .bytes) :
    (len value).value = value.value.length
  slice_value (value : Term types .bytes) (start stop : Term types .nat)
      (lower : start.value ≤ stop.value)
      (upper : stop.value ≤ value.value.length) :
    (slice value start stop).value =
      Nucleus.Bytes.ofList ((value.value.toList.drop start.value).take
        (stop.value - start.value))
  substring_value (needle haystack : Term types .bytes) :
    (substring needle haystack).value =
      bytesSubstring needle.value haystack.value

namespace InitPackage

/-- Forget checked evidence only after retaining the ordinary Ethane term in
each `Term`; this is the concrete target consumed by generic lowering. -/
def target (package : InitPackage) : Compact.Target where
  Term := Term package.types
  bool := package.bool
  nat := package.naturalLiteral
  int := package.integerLiteral
  bytes := package.bytes
  add := package.add
  le := package.le
  lt := package.lt
  cat := package.cat
  len := package.len
  slice := package.slice
  substring := package.substring

/-- Checked init equations discharge every semantic obligation of the generic
compact lowering interface. -/
def sound (package : InitPackage) : package.target.Sound where
  denote := Term.value
  bool := package.bool_value
  nat := fun value => (package.naturalLiteral_from_package value).trans
    (package.naturalToNat_ofNat value)
  int := package.integerLiteral_value
  bytes := package.bytes_value
  add := package.add_value
  le := package.le_value
  lt := package.lt_value
  cat := package.cat_value
  len := package.len_value
  slice := package.slice_value
  substring := package.substring_value

/-- The generic compact theorem applies to this concrete Ethane/init target.
Thus direct reference evaluation and checked Ethane lowering state the same
value proposition whenever all slice preconditions hold. -/
theorem lower_agrees (package : InitPackage) {type : Compact.Ty}
    (expression : Compact.Expr type) (bounded : expression.Bounded) :
    (expression.lower package.target).value = expression.eval :=
  expression.lower_sound package.target package.sound bounded

/-- A lowered compact expression is always an ordinarily typed Ethane term. -/
theorem lower_hasType (package : InitPackage) {type : Compact.Ty}
    (expression : Compact.Expr type) :
    Nucleus.Hol.Ethane.HasType (.nil : TyScope [])
      (.nil : TmScope Nucleus.HolE.EmptySig 0)
      (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx Nucleus.HolE.EmptySig [] 0)
      (expression.lower package.target).expression
        (package.types.typeSyntax type) :=
  (expression.lower package.target).hasType

/-! ## Direct/lowered reference examples -/

def naturalExample : Compact.Expr .bool :=
  .le (.add (.nat 20) (.nat 22)) (.nat 42)

@[simp] theorem naturalExample_direct : naturalExample.eval = true := by
  decide

theorem naturalExample_lowered (package : InitPackage) :
    (naturalExample.lower package.target).value = true := by
  rw [package.lower_agrees naturalExample (by simp [naturalExample, Compact.Expr.Bounded]),
    naturalExample_direct]

def bytesExample : Compact.Expr .bool :=
  .substring (.bytes (Nucleus.Bytes.ofList [0x62]))
    (.cat (.bytes (Nucleus.Bytes.ofList [0x61]))
      (.bytes (Nucleus.Bytes.ofList [0x62, 0x63])))

@[simp] theorem bytesExample_direct : bytesExample.eval = true := by
  decide

theorem bytesExample_lowered (package : InitPackage) :
    (bytesExample.lower package.target).value = true := by
  rw [package.lower_agrees bytesExample (by simp [bytesExample, Compact.Expr.Bounded]),
    bytesExample_direct]

end InitPackage

end Nucleus.Hol.Propane.Compact.Ethane
