import Nucleus.HolE.Named.Dense.Representation
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Set.Defs

/-!
# Effectful dense encoders

This layer separates state from the encoder's ambient effect.  Ordinary
failure uses `Option`; other monads may add logging, exceptions, or search.
Finite and unrestricted nondeterminism have direct interfaces below.  A
`Finset` cannot itself implement Lean's unconstrained `Monad` class because
its bind needs decidable equality on the result type, so its interface is
intentionally parallel to, rather than an instance of, `MonadicEncoder`.
-/

namespace Nucleus.HolE.Named.Unsorted.Dense

universe u
set_option relaxedAutoImplicit true

/-- An encoder whose mutable state is supplied by `EncoderStorage` and whose
remaining effect is described by `m`. -/
class MonadicEncoder (E : Type) (m : Type → Type) (Sig : Signature.{u})
    (Name : Type) [Monad m] [EncoderStorage E Sig Name] where
  encodeM : HolE Sig Name →
    StateT (EncoderStorage.State E Sig Name) m Nat

/-- A separately overridable batch-encoding capability. -/
class MonadicListEncoder (E : Type) (m : Type → Type) (Sig : Signature.{u})
    (Name : Type) [Monad m] [EncoderStorage E Sig Name] where
  encodeListM : List (HolE Sig Name) →
    StateT (EncoderStorage.State E Sig Name) m (List Nat)

namespace MonadicEncoder

/-- Run an effectful encoder from the storage's initial state. -/
def run (E : Type) (m : Type → Type) [Monad m]
    [storage : EncoderStorage E Sig Name] [encoder : MonadicEncoder E m Sig Name]
    (tree : HolE Sig Name) (offset : Nat := 0) : m (EncodingResult Sig Name) := do
  let (root, state) ← encoder.encodeM tree (storage.initial offset)
  return ⟨offset, storage.nodes state, root, storage.next state⟩

/-- Regard the original option-valued capability as a state transformer. -/
@[instance_reducible] def ofFallible [EncoderStorage E Sig Name]
    (encoder : FallibleEncoder E Sig Name) : MonadicEncoder E Option Sig Name where
  encodeM := encoder.encode?

/-- Regard a total state-passing encoder as an `Id` state transformer. -/
@[instance_reducible] def ofInfallible [EncoderStorage E Sig Name]
    (encoder : InfallibleEncoder E Sig Name) : MonadicEncoder E Id Sig Name where
  encodeM := encoder.encode

/-- The canonical sequential list implementation induced by a single-value
encoder.  A specialized `MonadicListEncoder` may instead share or batch. -/
def encodeList [Monad m] [EncoderStorage E Sig Name]
    [encoder : MonadicEncoder E m Sig Name] :
    List (HolE Sig Name) → StateT (EncoderStorage.State E Sig Name) m (List Nat)
  | [] => pure []
  | tree :: trees => do
      let root ← encoder.encodeM tree
      let roots ← encodeList trees
      return root :: roots

@[instance_reducible] def listEncoder [Monad m] [EncoderStorage E Sig Name]
    [MonadicEncoder E m Sig Name] : MonadicListEncoder E m Sig Name where
  encodeListM := encodeList

end MonadicEncoder

namespace MonadicListEncoder

def run (E : Type) (m : Type → Type) [Monad m]
    [storage : EncoderStorage E Sig Name]
    [encoder : MonadicListEncoder E m Sig Name]
    (trees : List (HolE Sig Name)) (offset : Nat := 0) :
    m (ListEncodingResult Sig Name) := do
  let (roots, state) ← encoder.encodeListM trees (storage.initial offset)
  return ⟨offset, storage.nodes state, roots, storage.next state⟩

end MonadicListEncoder

/-- A finite-search encoder.  The empty result is failure. -/
class FallibleFinsetEncoder (E : Type) (Sig : Signature.{u}) (Name : Type)
    [EncoderStorage E Sig Name] where
  encodeFinset? : HolE Sig Name → EncoderStorage.State E Sig Name →
    Finset (Nat × EncoderStorage.State E Sig Name)

/-- A finite-search encoder which always has at least one outcome. -/
class InfallibleFinsetEncoder (E : Type) (Sig : Signature.{u}) (Name : Type)
    [EncoderStorage E Sig Name] extends FallibleFinsetEncoder E Sig Name where
  encodeFinset?_nonempty : ∀ tree state, ∃ result, result ∈ encodeFinset? tree state

/-- An unrestricted-search encoder.  The empty set is failure. -/
class FallibleSetEncoder (E : Type) (Sig : Signature.{u}) (Name : Type)
    [EncoderStorage E Sig Name] where
  encodeSet? : HolE Sig Name → EncoderStorage.State E Sig Name →
    Set (Nat × EncoderStorage.State E Sig Name)

/-- An unrestricted-search encoder which always has at least one outcome. -/
class InfallibleSetEncoder (E : Type) (Sig : Signature.{u}) (Name : Type)
    [EncoderStorage E Sig Name] extends FallibleSetEncoder E Sig Name where
  encodeSet?_nonempty : ∀ tree state, (encodeSet? tree state).Nonempty

/-- Every finite-search encoder has the corresponding unrestricted search
semantics. -/
@[instance_reducible] def FallibleFinsetEncoder.toSet [EncoderStorage E Sig Name]
    (encoder : FallibleFinsetEncoder E Sig Name) : FallibleSetEncoder E Sig Name where
  encodeSet? tree state := encoder.encodeFinset? tree state

@[instance_reducible] def InfallibleFinsetEncoder.toSet [EncoderStorage E Sig Name]
    (encoder : InfallibleFinsetEncoder E Sig Name) : InfallibleSetEncoder E Sig Name where
  encodeSet? tree state := encoder.encodeFinset? tree state
  encodeSet?_nonempty tree state := encoder.encodeFinset?_nonempty tree state

/-! The existing postorder implementation is the first concrete inhabitant. -/

instance : MonadicEncoder Encoder.Postorder Id Sig Name :=
  MonadicEncoder.ofInfallible (inferInstance : InfallibleEncoder Encoder.Postorder Sig Name)

instance : MonadicListEncoder Encoder.Postorder Id Sig Name :=
  MonadicEncoder.listEncoder

end Nucleus.HolE.Named.Unsorted.Dense
