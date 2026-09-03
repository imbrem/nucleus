import Nucleus.Classical.Tagged.Runtime.SemanticWire

/-!
# Classical arena V3 semantic wire

V3 stores each formula as a flat preorder token array. Tokens contain only
constructor, polarity, and atom or arity. Allocator metadata is absent.
-/

namespace Nucleus.Classical.Tagged.Runtime.V3

open Nucleus.Classical.Tagged

def typeName : String := "io.github.imbrem.nucleus.classicalArenaV3"
def maxSequents : Nat := 500000
def maxTokens : Nat := 1000000

inductive Kind where
  | literal | and | or | sat
  deriving DecidableEq, Repr

inductive Payload where
  | atom (value : Nat)
  | arity (value : Nat)
  deriving DecidableEq, Repr

structure Token where
  kind : Kind
  negative : Bool
  payload : Payload
  deriving DecidableEq, Repr

inductive Encodes : Tagged.Formula Nat → List Token → Prop
  | literal (atom : Nat) (negative : Bool) (bound : atom < 2 ^ 32) :
      Encodes (.literal ⟨atom, negative⟩)
        [⟨.literal, negative, .atom atom⟩]
  | and (negative : Bool) (children : List (Tagged.Formula Nat))
      (tokens : List (List Token))
      (childrenEncode : List.Forall₂ Encodes children tokens) :
      Encodes (.and negative children)
        (⟨.and, negative, .arity children.length⟩ :: tokens.flatten)
  | or (negative : Bool) (children : List (Tagged.Formula Nat))
      (tokens : List (List Token))
      (childrenEncode : List.Forall₂ Encodes children tokens) :
      Encodes (.or negative children)
        (⟨.or, negative, .arity children.length⟩ :: tokens.flatten)
  | sat (negative : Bool) (children : List (Tagged.Formula Nat))
      (tokens : List (List Token))
      (childrenEncode : List.Forall₂ Encodes children tokens) :
      Encodes (.sat negative children)
        (⟨.sat, negative, .arity children.length⟩ :: tokens.flatten)

structure Formula where
  tokens : List Token
  tokenBound : tokens.length ≤ maxTokens

structure Sequent where
  premise : Formula
  conclusion : Formula

structure Arena where
  discriminator : String
  sequents : List Sequent
  discriminatorExact : discriminator = typeName
  sequentBound : sequents.length ≤ maxSequents
  tokenBound : (sequents.map fun sequent ↦
    sequent.premise.tokens.length + sequent.conclusion.tokens.length).sum ≤ maxTokens

def Formula.Represents (wire : Formula) (formula : Tagged.Formula Nat) : Prop :=
  Encodes formula wire.tokens

universe u
variable {Representation : Type u}

/-- The flat semantic token relation determines constructor syntax, while
private packing determines only its in-memory representation. -/
theorem constructorCorrespondence
    (api : SemanticWire.ConstructorApi Representation)
    {wire : List SemanticWire.Sequent} {representation : Representation}
    (rebuilt : SemanticWire.rebuild? api wire = some representation) :
    api.represents representation (SemanticWire.decode wire) :=
  SemanticWire.rebuild?_sound api rebuilt

end Nucleus.Classical.Tagged.Runtime.V3
