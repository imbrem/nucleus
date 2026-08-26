import Nucleus.Hol.Ethane.Arena.OneBased.Layout
import Nucleus.HolE.ClassicalNaturals

/-!
# Semantic certificates for checked natural-number packages

The userspace init language is intentionally absent from this file.  A
certificate names arena references only through checked resolution, gives the
corresponding closed HolE denotations, and identifies the premise-free theorem
rows which prove the Peano laws.  Consequently a parser, elaborator, or name
dictionary can help *construct* a certificate, but none of them is trusted by
the theorem below.
-/

namespace Nucleus.Hol.Ethane.OneBased.Layout

open Nucleus.Hol.Ethane
open Nucleus.Hol.Ethane.ClassicalMatrix
open Nucleus.Hol.Ethane.OneBased
open Nucleus.HolE
open Nucleus.HolE.Infinity
open Nucleus.HolE.Infinity.CNatModel

set_option relaxedAutoImplicit true

/-- One exact premise-free HOL theorem row, together with the proposition
assigned to its checked Boolean reference. -/
structure ProvedProposition (arena : Arena)
    (interpretation : PartialValuation Ref) (proposition : Prop) where
  reference : Ref
  fact : WireSequent
  member : fact ∈ arena.hol.thm
  assertion : fact.semantic = Sequent.assert reference
  interpreted : interpretation reference = some proposition

/-- A premise-free checked theorem row proves its assigned proposition under
the same explicit ambient assumptions as the containing kernel. -/
theorem ProvedProposition.holds {trusted : Arena → Prop} {resolve : Resolver}
    {arena : Arena} {interpretation : PartialValuation Ref}
    {proposition : Prop}
    (proved : ProvedProposition arena interpretation proposition)
    (valid : arena.KernelValid trusted resolve interpretation)
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    proposition := by
  obtain ⟨valuation, completion⟩ := interpretation.exists_completion
  have factHolds := valid.holTheorems ambientValuation admitted
    proved.fact proved.member valuation completion
  rw [proved.assertion, Sequent.assert_holds] at factHolds
  exact (completion proved.reference proposition proved.interpreted).mp factHolds

/-- Source-independent semantics of the exact declaration rows in a checked
natural-number package.  `carrier`, `zero`, and `successor` are related to the
ordinary HolE evaluator, rather than being arbitrary data attached to names.

The law fields deliberately use their decoded semantic propositions.  A
separate, syntax-directed decoder can establish those fields for a concrete
arena without becoming part of the trusted kernel API. -/
structure NaturalPackageCertificate (resolve : Resolver) (arena : Arena)
    (interpretation : PartialValuation Ref) where
  carrierRef : Ref
  zeroRef : Ref
  successorRef : Ref
  carrierSyntax : EmptyTy
  zeroSyntax : EmptyTm
  successorSyntax : EmptyTm
  carrier : Pointed
  zero : carrier.carrier
  successor : carrier.carrier → carrier.carrier
  carrierResolves :
    Resolves (coreResolver resolve) arena.holCore carrierRef
      (.family .star carrierSyntax)
  carrierDenotes :
    Nucleus.Hol.Ethane.DenotesFam (.nil : TyScope []) emptyTypeEnv
      carrierSyntax carrier
  zeroResolves :
    Resolves (coreResolver resolve) arena.holCore zeroRef
      (.term carrierSyntax zeroSyntax)
  zeroEvaluates :
    Nucleus.Hol.Ethane.Eval (.nil : TyScope []) (.nil : TmScope EmptySig 0)
      emptyTypeEnv (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx EmptySig [] 0)
      emptyRawBoundEnv
      zeroSyntax carrierSyntax carrier zero
  successorResolves :
    Resolves (coreResolver resolve) arena.holCore successorRef
      (.term (.arr carrierSyntax carrierSyntax) successorSyntax)
  successorEvaluates :
    Nucleus.Hol.Ethane.Eval (.nil : TyScope []) (.nil : TmScope EmptySig 0)
      emptyTypeEnv (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx EmptySig [] 0)
      emptyRawBoundEnv
      successorSyntax (.arr carrierSyntax carrierSyntax)
      ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩ successor
  successorInjective : ProvedProposition arena interpretation
    (∀ x y, successor x = successor y → x = y)
  zeroNeSuccessor : ProvedProposition arena interpretation
    (∀ x, zero ≠ successor x)
  induction : ProvedProposition arena interpretation
    (∀ P : carrier.carrier → Bool,
      P zero = true →
      (∀ x, P x = true → P (successor x) = true) →
      ∀ x, P x = true)

namespace NaturalPackageCertificate

/-- The declaration denoted by the three checked declaration references. -/
def declaration (certificate : NaturalPackageCertificate resolve arena interpretation) :
    CNatDecl where
  carrier := certificate.carrier.carrier
  zero := certificate.zero
  succ := certificate.successor

/-- Exact checked declaration rows and exact premise-free theorem rows certify
a semantic natural-number model.  The only assumptions are the arena's
existing `KernelValid` invariant and its explicit ambient context. -/
def certify {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (certificate : NaturalPackageCertificate resolve arena interpretation)
    (valid : arena.KernelValid trusted resolve interpretation)
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    CNatModel :=
  certificate.declaration.certify <| CNatDecl.proofOfBoolLaws
    certificate.declaration
    (certificate.successorInjective.holds valid ambientValuation admitted)
    (certificate.zeroNeSuccessor.holds valid ambientValuation admitted)
    (certificate.induction.holds valid ambientValuation admitted)

@[simp] theorem certify_declaration {trusted : Arena → Prop} {resolve : Resolver}
    {arena : Arena} {interpretation : PartialValuation Ref}
    (certificate : NaturalPackageCertificate resolve arena interpretation)
    (valid : arena.KernelValid trusted resolve interpretation)
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    (certificate.certify valid ambientValuation admitted).declaration =
      certificate.declaration := by
  rfl

end NaturalPackageCertificate

/-! ## Primitive recursion -/

/-- Checked denotations and exact theorem rows for one selected primitive
recursor.  The codomain is another checked closed family; the natural carrier
is reused from `naturals`. -/
structure RecursorPackageCertificate (resolve : Resolver) (arena : Arena)
    (interpretation : PartialValuation Ref) where
  naturals : NaturalPackageCertificate resolve arena interpretation
  codomainRef : Ref
  baseRef : Ref
  stepRef : Ref
  selectedRef : Ref
  codomainSyntax : EmptyTy
  baseSyntax : EmptyTm
  stepSyntax : EmptyTm
  selectedSyntax : EmptyTm
  codomain : Pointed
  base : codomain.carrier
  step : naturals.carrier.carrier → codomain.carrier → codomain.carrier
  selected : naturals.carrier.carrier → codomain.carrier
  codomainResolves :
    Resolves (coreResolver resolve) arena.holCore codomainRef
      (.family .star codomainSyntax)
  codomainDenotes :
    Nucleus.Hol.Ethane.DenotesFam (.nil : TyScope []) emptyTypeEnv
      codomainSyntax codomain
  baseResolves :
    Resolves (coreResolver resolve) arena.holCore baseRef
      (.term codomainSyntax baseSyntax)
  baseEvaluates :
    Nucleus.Hol.Ethane.Eval (.nil : TyScope []) (.nil : TmScope EmptySig 0)
      emptyTypeEnv (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx EmptySig [] 0)
      emptyRawBoundEnv baseSyntax codomainSyntax codomain base
  stepResolves :
    Resolves (coreResolver resolve) arena.holCore stepRef
      (.term (.arr naturals.carrierSyntax (.arr codomainSyntax codomainSyntax))
        stepSyntax)
  stepEvaluates :
    Nucleus.Hol.Ethane.Eval (.nil : TyScope []) (.nil : TmScope EmptySig 0)
      emptyTypeEnv (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx EmptySig [] 0)
      emptyRawBoundEnv stepSyntax
      (.arr naturals.carrierSyntax (.arr codomainSyntax codomainSyntax))
      ⟨naturals.carrier.carrier → codomain.carrier → codomain.carrier,
        fun _ _ => codomain.point⟩ step
  selectedResolves :
    Resolves (coreResolver resolve) arena.holCore selectedRef
      (.term (.arr naturals.carrierSyntax codomainSyntax) selectedSyntax)
  selectedEvaluates :
    Nucleus.Hol.Ethane.Eval (.nil : TyScope []) (.nil : TmScope EmptySig 0)
      emptyTypeEnv (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx EmptySig [] 0)
      emptyRawBoundEnv selectedSyntax (.arr naturals.carrierSyntax codomainSyntax)
      ⟨naturals.carrier.carrier → codomain.carrier, fun _ => codomain.point⟩
      selected
  graph : ProvedProposition arena interpretation
    (∀ n, ∀ relation : naturals.carrier.carrier → codomain.carrier → Prop,
      relation naturals.zero base →
      (∀ k z, relation k z →
        relation (naturals.successor k) (step k z)) →
      relation n (selected n))
  atZero : ProvedProposition arena interpretation
    (selected naturals.zero = base)
  atSuccessor : ProvedProposition arena interpretation
    (∀ n, selected (naturals.successor n) = step n (selected n))
  unique : ProvedProposition arena interpretation
    (∀ candidate : naturals.carrier.carrier → codomain.carrier,
      candidate naturals.zero = base →
      (∀ n, candidate (naturals.successor n) = step n (candidate n)) →
      candidate = selected)

namespace RecursorPackageCertificate

/-- The exact selected recursor row interpreted over the natural model and
checked codomain named by the certificate. -/
def declaration {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (certificate : RecursorPackageCertificate resolve arena interpretation)
    (valid : arena.KernelValid trusted resolve interpretation)
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    RecursorDecl (certificate.naturals.certify valid ambientValuation admitted)
      certificate.codomain.carrier where
  base := certificate.base
  step := certificate.step
  selected := certificate.selected

/-- Exact graph, computation, and uniqueness theorem rows certify the exact
selected primitive recursor. -/
theorem proof {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (certificate : RecursorPackageCertificate resolve arena interpretation)
    (valid : arena.KernelValid trusted resolve interpretation)
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    RecursorProof (certificate.declaration valid ambientValuation admitted) := by
  exact {
    graph := certificate.graph.holds valid ambientValuation admitted
    at_zero := certificate.atZero.holds valid ambientValuation admitted
    at_succ := certificate.atSuccessor.holds valid ambientValuation admitted
    unique := certificate.unique.holds valid ambientValuation admitted
  }

end RecursorPackageCertificate

/-! ## First-recursive addition

This second certificate consumes the natural declaration certificate instead
of restating its carrier.  It is therefore impossible for the arithmetic
bridge to silently certify its laws over a different zero or successor. -/

/-- Checked denotation and defining theorems for the init package's
first-argument-recursive addition operation. -/
structure FirstRecursiveAddPackageCertificate (resolve : Resolver) (arena : Arena)
    (interpretation : PartialValuation Ref) where
  naturals : NaturalPackageCertificate resolve arena interpretation
  addRef : Ref
  addSyntax : EmptyTm
  add : naturals.carrier.carrier → naturals.carrier.carrier →
    naturals.carrier.carrier
  addResolves :
    Resolves (coreResolver resolve) arena.holCore addRef
      (.term (.arr naturals.carrierSyntax
        (.arr naturals.carrierSyntax naturals.carrierSyntax)) addSyntax)
  addEvaluates :
    Nucleus.Hol.Ethane.Eval (.nil : TyScope []) (.nil : TmScope EmptySig 0)
      emptyTypeEnv (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx EmptySig [] 0)
      emptyRawBoundEnv addSyntax
      (.arr naturals.carrierSyntax
        (.arr naturals.carrierSyntax naturals.carrierSyntax))
      ⟨naturals.carrier.carrier → naturals.carrier.carrier →
        naturals.carrier.carrier,
        fun _ _ => naturals.carrier.point⟩ add
  atZero : ProvedProposition arena interpretation
    (∀ m, add naturals.zero m = m)
  atSuccessor : ProvedProposition arena interpretation
    (∀ n m, add (naturals.successor n) m =
      naturals.successor (add n m))

namespace FirstRecursiveAddPackageCertificate

/-- The exact checked addition row, interpreted over the already-certified
natural model. -/
def declaration {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (certificate : FirstRecursiveAddPackageCertificate resolve arena interpretation)
    (valid : arena.KernelValid trusted resolve interpretation)
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    FirstRecursiveAddDecl
      (certificate.naturals.certify valid ambientValuation admitted) where
  add := certificate.add

/-- The two exact checked defining equations certify the exact interpreted
addition declaration. -/
theorem proof {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (certificate : FirstRecursiveAddPackageCertificate resolve arena interpretation)
    (valid : arena.KernelValid trusted resolve interpretation)
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    FirstRecursiveAddProof
      (certificate.declaration valid ambientValuation admitted) := by
  exact {
    at_zero := certificate.atZero.holds valid ambientValuation admitted
    at_succ := certificate.atSuccessor.holds valid ambientValuation admitted
  }

/-- Commutativity is then inherited from the source-independent semantic
proof, rather than being another arena-specific decoding obligation. -/
theorem commutative {trusted : Arena → Prop} {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (certificate : FirstRecursiveAddPackageCertificate resolve arena interpretation)
    (valid : arena.KernelValid trusted resolve interpretation)
    (ambientValuation : Valuation Ref)
    (admitted : arena.ambientTheory.Admits (arena.ImportOk trusted resolve)
      (arena.ImportSort resolve) ambientValuation) :
    ∀ m n, certificate.add n m = certificate.add m n :=
  (certificate.proof valid ambientValuation admitted).commutative

end FirstRecursiveAddPackageCertificate

end Nucleus.Hol.Ethane.OneBased.Layout
