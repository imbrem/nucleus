import Nucleus.Classical.Tagged.Runtime.SharedRuntime
import Nucleus.Classical.Tagged.Abstract

/-!
# Semantic wire boundary

The public wire contains formulas and sequents, never allocator words, free
rings, or reference counts. Decoding rebuilds private storage through the
constructor interface. The internal whole-arena validator remains an
implementation invariant, not a theorem-producing public capability.
-/

namespace Nucleus.Classical.Tagged.Runtime.SemanticWire

open Nucleus.Classical.Tagged
open Nucleus.Classical.Tagged.Runtime.Shared

/-- The semantic schema is the public tagged syntax itself. -/
abbrev Formula := Tagged.Formula Nat
abbrev Sequent := Tagged.Sequent Nat

def Sequent.decode (sequent : Sequent) : Tagged.Sequent Nat := sequent

def Sequent.encode (sequent : Tagged.Sequent Nat) : Sequent := sequent

@[simp] theorem Sequent.decode_encode (sequent : Tagged.Sequent Nat) :
    (Sequent.encode sequent).decode = sequent := by
  rfl

@[simp] theorem Sequent.encode_decode (sequent : Sequent) :
    Sequent.encode sequent.decode = sequent := by
  rfl

def decode (wire : List Sequent) : List (Tagged.Sequent Nat) :=
  wire.map Sequent.decode

def encode (sequents : List (Tagged.Sequent Nat)) : List Sequent :=
  sequents.map Sequent.encode

@[simp] theorem decode_encode (sequents : List (Tagged.Sequent Nat)) :
    decode (encode sequents) = sequents := by
  induction sequents with
  | nil => rfl
  | cons sequent sequents _ => simp [decode, encode, Function.comp_def]

@[simp] theorem encode_decode (wire : List Sequent) : encode (decode wire) = wire := by
  induction wire with
  | nil => rfl
  | cons sequent wire _ => simp [decode, encode, Function.comp_def]

universe u

/-- Abstract private constructor boundary implemented by the shared arena. -/
structure ConstructorApi (Representation : Type u) where
  construct? : List (Tagged.Sequent Nat) → Option Representation
  represents : Representation → List (Tagged.Sequent Nat) → Prop
  construct_sound : ∀ {sequents representation},
    construct? sequents = some representation → represents representation sequents

variable {Representation : Type u}

def rebuild? (api : ConstructorApi Representation) (wire : List Sequent) :
    Option Representation := api.construct? (decode wire)

theorem rebuild?_sound (api : ConstructorApi Representation) {wire : List Sequent}
    {representation : Representation}
    (rebuilt : rebuild? api wire = some representation) :
    api.represents representation (decode wire) := by
  exact api.construct_sound rebuilt

/-- Representation details cannot affect semantic wire equality. -/
theorem wire_ext {left right : List Sequent} (equal : decode left = decode right) :
    left = right := by
  rw [← encode_decode left, ← encode_decode right, equal]

end Nucleus.Classical.Tagged.Runtime.SemanticWire
