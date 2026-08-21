import Nucleus.Hol.Ethane.Arena
import Nucleus.Hol.Ethane.Typing

/-!
# Checked type references for Ethane free variables

`Arena.Valid` proves that row references point backward, but backwardness does
not imply that a referenced row denotes a type.  Consequently the checked
`tmFv` kernel operation cannot honestly be exposed until the kernel state also
retains a checked classification view.

This file fixes the semantic precondition for that operation.  A type reference
must resolve to the erasure of a sorted Ethane type and carry an Ethane
`Kinded` certificate.  The certificate is ghost state in Lean; an implementation
may retain the corresponding checked classification and reconstruct the proof.
No CAS resolution policy is introduced here: `valueAt` is the already agreed
view supplied by the deterministic kernel/CAS boundary.
-/

namespace Nucleus.Hol.Ethane.Kernel

open Nucleus.Hol.Ethane

set_option relaxedAutoImplicit true

/-- A resolved, checked witness that one signed arena reference denotes a
star-kinded Ethane type.  Ethane lowering currently uses natural-number names,
so this first checked-kernel witness fixes `Name := Nat`. -/
structure StarTypeAt {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types)
    (valueAt : Int → Option (Nucleus.Hol.Ethane.Arena.Value Sig Nat))
    (reference : Int) where
  type : Ty Sig
  resolves : valueAt reference = some (.syntax type.erase)
  kinded : Nucleus.Hol.Ethane.Kinded typeScope type

/-- Complete logical precondition for appending a typed free-variable row.
The first conjunct is the wire/arena check; `typeWitness` is the semantic check
which was absent from the day-zero structural arena invariant. -/
structure TmFvReady {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : TyScope types)
    (next : Int)
    (valueAt : Int → Option (Nucleus.Hol.Ethane.Arena.Value Sig Nat))
    (typeReference : Int) where
  backward : typeReference < next
  typeWitness : StarTypeAt typeScope valueAt typeReference

/-- The logical rule required by `tmFv`: once the referenced expression is
certified as a type, a named free variable carrying that type is well typed.
This theorem is independent of arena identity and of CAS lookup policy. -/
theorem tmFv_hasType {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {typeScope : TyScope types} {type : Ty Sig}
    (name : Nat) (typeKinded : Nucleus.Hol.Ethane.Kinded typeScope type) :
    Nucleus.Hol.Ethane.HasType typeScope .nil Nucleus.HolE.emptyBound
      (.tmFv name type) type := by
  obtain ⟨loweredType, loweredClassification, typeLowering,
    classificationLowering, typeDerivation⟩ := typeKinded
  have classificationEq : loweredClassification =
      (Nucleus.HolE.Classification.kind :
        Nucleus.HolE.Classification Sig types (.kind .star)) := by
    simpa [Nucleus.Hol.Ethane.Classification.lower] using
      classificationLowering.symm
  subst loweredClassification
  change Nucleus.HolE.Named.lowerFam typeScope type.toHolE =
    some loweredType at typeLowering
  refine ⟨.fv name loweredType, .tm loweredType, ?_, ?_, .fv name typeDerivation⟩
  · change Nucleus.HolE.Named.lowerTm typeScope .nil
      (.tmFv name type.toHolE) = some (.fv name loweredType)
    rw [Nucleus.HolE.Named.lowerTm]
    simp only [Nucleus.HolE.Named.lookupTm]
    rw [typeLowering]
    rfl
  · change (do
      let lowered ← Nucleus.HolE.Named.lowerFam typeScope type.toHolE
      pure (Nucleus.HolE.Classification.tm lowered)) =
        some (Nucleus.HolE.Classification.tm loweredType)
    rw [typeLowering]
    rfl

/-- A checked arena witness supplies exactly the semantic premise of the
free-variable typing rule.  This is the preservation ingredient a future pure
arena transition must consume after validating its cached classification. -/
theorem TmFvReady.hasType {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {typeScope : TyScope types}
    {next : Int}
    {valueAt : Int → Option (Nucleus.Hol.Ethane.Arena.Value Sig Nat)}
    {typeReference : Int}
    (ready : TmFvReady typeScope next valueAt typeReference) (name : Nat) :
    Nucleus.Hol.Ethane.HasType typeScope .nil Nucleus.HolE.emptyBound
      (.tmFv name ready.typeWitness.type) ready.typeWitness.type :=
  tmFv_hasType name ready.typeWitness.kinded

end Nucleus.Hol.Ethane.Kernel
