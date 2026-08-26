import Nucleus.Hol.Ethane.Subtype
import Nucleus.HolE.ClassicalSemantics

/-!
# Semantics of Ethane's guarded subtype package

This is the semantic content of the single subtype-package axiom.  It is kept
separate from the object-language encoding so the model-theoretic obligation
is small and directly auditable.
-/

namespace Nucleus.Hol.Ethane.Subtype

open Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Representation and abstraction data for one guarded predicate. -/
structure SemanticPackage (carrier : CPointed)
    (predicate : carrier.carrier → Bool) (model : CPointed) where
  rep : model.carrier → carrier.carrier
  abs : carrier.carrier → model.carrier
  absRep : ∀ value, abs (rep value) = value
  repAbs : ∀ value, CGuarded predicate value → rep (abs value) = value
  repGuarded : ∀ value, CGuarded predicate (rep value)

/-- Representation/abstraction data with no package laws attached. -/
structure SemanticDecl (carrier : CPointed)
    (predicate : carrier.carrier → Bool) (model : CPointed) where
  rep : model.carrier → carrier.carrier
  abs : carrier.carrier → model.carrier

/-- Evidence certifying one exact guarded-subtype declaration. -/
structure SemanticProof {carrier : CPointed}
    {predicate : carrier.carrier → Bool} {model : CPointed}
    (D : SemanticDecl carrier predicate model) : Prop where
  absRep : ∀ value, D.abs (D.rep value) = value
  repAbs : ∀ value, CGuarded predicate value → D.rep (D.abs value) = value
  repGuarded : ∀ value, CGuarded predicate (D.rep value)

/-- Forget package evidence while retaining exactly the selected functions. -/
def SemanticPackage.declaration
    {carrier : CPointed} {predicate : carrier.carrier → Bool} {model : CPointed}
    (package : SemanticPackage carrier predicate model) :
    SemanticDecl carrier predicate model where
  rep := package.rep
  abs := package.abs

/-- Project package laws as evidence for the exact declaration. -/
theorem SemanticPackage.proof
    {carrier : CPointed} {predicate : carrier.carrier → Bool} {model : CPointed}
    (package : SemanticPackage carrier predicate model) :
    SemanticProof package.declaration := by
  exact {
    absRep := package.absRep
    repAbs := package.repAbs
    repGuarded := package.repGuarded
  }

/-- A declaration becomes a semantic package only when supplied its laws. -/
def SemanticDecl.certify
    {carrier : CPointed} {predicate : carrier.carrier → Bool} {model : CPointed}
    (D : SemanticDecl carrier predicate model)
    (proof : SemanticProof D) : SemanticPackage carrier predicate model where
  rep := D.rep
  abs := D.abs
  absRep := proof.absRep
  repAbs := proof.repAbs
  repGuarded := proof.repGuarded

@[simp] theorem SemanticPackage.certify_declaration
    {carrier : CPointed} {predicate : carrier.carrier → Bool} {model : CPointed}
    (package : SemanticPackage carrier predicate model) :
    package.declaration.certify package.proof = package := by
  cases package
  rfl

/-- The guarded subtype is a concrete witness for the package predicate. -/
noncomputable def guardedPackage (carrier : CPointed)
    (predicate : carrier.carrier → Bool) :
    SemanticPackage carrier predicate (cGuardedType carrier predicate) where
  rep := Subtype.val
  abs := cGuardedAbs carrier predicate
  absRep := cGuardedAbs_rep carrier predicate
  repAbs := fun value valid => cGuardedAbs_value carrier predicate value valid
  repGuarded := fun value => value.2

/-- A subtype package exists for every predicate, without a nonemptiness
premise. -/
theorem semanticPackage_exists (carrier : CPointed)
    (predicate : carrier.carrier → Bool) :
    ∃ model, Nonempty (SemanticPackage carrier predicate model) :=
  ⟨cGuardedType carrier predicate, ⟨guardedPackage carrier predicate⟩⟩

/-- Classical `Model` choice selects a package whenever its predicate asks
for precisely this structure. -/
theorem chooseModel_hasPackage (carrier : CPointed)
    (predicate : carrier.carrier → Bool) :
    Nonempty (SemanticPackage carrier predicate
      (chooseCModel fun model => Nonempty (SemanticPackage carrier predicate model))) := by
  let satisfies := fun model => Nonempty (SemanticPackage carrier predicate model)
  exact chooseCModel_spec satisfies (cGuardedType carrier predicate)
    ⟨guardedPackage carrier predicate⟩

end Nucleus.Hol.Ethane.Subtype
