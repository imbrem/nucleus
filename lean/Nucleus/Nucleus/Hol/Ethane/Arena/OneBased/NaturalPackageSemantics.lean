import Nucleus.Hol.Ethane.Arena.OneBased.DenseKernelTransport
import Nucleus.HolE.ClassicalNaturals
import Nucleus.HolE.ClassicalRealization

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

abbrev toClassicalTy (family : EmptyTy) : Nucleus.HolE.Named.Ty ClassicalSig :=
  family.toHolE

abbrev toClassicalTm (term : EmptyTm) : Nucleus.HolE.Named.Tm ClassicalSig :=
  term.toHolE

/-- A closed named family denotes one value in the deterministic classical
HolE semantics.  The checking certificate is existential but its denotation
is coherent under the classical conversion model. -/
def ClassicallyDenotesFamily (family : EmptyTy) (semantic : CPointed) : Prop :=
  ∃ lowered, ∃ checking : CChecks
      (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx ClassicalSig [] 0)
      lowered .kind,
    Nucleus.HolE.Named.lowerTy (.nil : TyScope []) (toClassicalTy family) =
      some lowered ∧
    semantic = cSem checking emptyCTypeEnv

/-- A closed named term realizes one value in the deterministic classical
HolE semantics. -/
def ClassicallyEvaluates (term : EmptyTm) (type : EmptyTy) (semantic : CPointed)
    (value : semantic.carrier) : Prop :=
  ∃ loweredTerm loweredType,
    Nucleus.HolE.Named.lowerTm (.nil : TyScope [])
      (.nil : TmScope ClassicalSig 0) (toClassicalTm term) = some loweredTerm ∧
    Nucleus.HolE.Named.lowerTy (.nil : TyScope []) (toClassicalTy type) =
      some loweredType ∧
    CRealizes
      (Γ := (Nucleus.HolE.emptyBound : Nucleus.HolE.BoundCtx ClassicalSig [] 0))
      emptyCTypeEnv emptyCBoundEnv loweredTerm loweredType semantic value

/-- Closed deterministic evaluation has one value, independently of the
proof-relevant conversion certificate hidden by `CRealizes`. -/
theorem ClassicallyEvaluates.value_unique
    {term : EmptyTm} {type : EmptyTy} {semantic : CPointed}
    {left right : semantic.carrier}
    (leftEval : ClassicallyEvaluates term type semantic left)
    (rightEval : ClassicallyEvaluates term type semantic right) :
    left = right := by
  obtain ⟨leftTerm, leftType, leftTermLowered, leftTypeLowered, leftRealizes⟩ :=
    leftEval
  obtain ⟨rightTerm, rightType, rightTermLowered, rightTypeLowered,
    rightRealizes⟩ := rightEval
  have termEqual : leftTerm = rightTerm := by
    exact Option.some.inj (leftTermLowered.symm.trans rightTermLowered)
  have typeEqual : leftType = rightType := by
    exact Option.some.inj (leftTypeLowered.symm.trans rightTypeLowered)
  subst rightTerm
  subst rightType
  exact leftRealizes.value_unique rightRealizes

/-- Truth of one closed, Boolean-valued Ethane expression in the deterministic
classical HolE semantics. -/
def ClosedFormulaHolds (expression : EmptyTm) : Prop :=
  ClassicallyEvaluates expression .boolTy cBool true

@[simp] theorem closedFormulaHolds_true :
    ClosedFormulaHolds (.bool true : EmptyTm) := by
  unfold ClosedFormulaHolds ClassicallyEvaluates
  exact ⟨.bool true, .boolTy,
    by simp [toClassicalTm, Nucleus.Hol.Ethane.Expr.toHolE,
      Nucleus.HolE.Named.lowerTm],
    by simp [toClassicalTy, Nucleus.Hol.Ethane.Expr.toHolE,
      Nucleus.HolE.Named.lowerTy, Nucleus.HolE.Named.lowerFam],
    CRealizes.boolean true _ _⟩

@[simp] theorem not_closedFormulaHolds_false :
    ¬ClosedFormulaHolds (.bool false : EmptyTm) := by
  intro evaluation
  unfold ClosedFormulaHolds ClassicallyEvaluates at evaluation
  obtain ⟨loweredTerm, loweredType, termLowered, typeLowered, evaluated⟩ := evaluation
  simp only [toClassicalTm, Nucleus.Hol.Ethane.Expr.toHolE] at termLowered
  rw [Nucleus.HolE.Named.lowerTm.eq_def] at termLowered
  change some (.bool false) = some loweredTerm at termLowered
  simp only [toClassicalTy, Nucleus.Hol.Ethane.Expr.toHolE] at typeLowered
  rw [Nucleus.HolE.Named.lowerTy, Nucleus.HolE.Named.lowerFam.eq_def] at typeLowered
  change some .boolTy = some loweredType at typeLowered
  injection termLowered with termEqual
  injection typeLowered with typeEqual
  subst loweredTerm
  subst loweredType
  exact Nucleus.HolE.not_realizes_false_as_true _ _ evaluated

/-- The partial Boolean interpretation used by theorem-row soundness agrees
with closed HolE evaluation.  This is the precise semantic bridge missing from
`HolInterpretationSound`, which intentionally talks only about propositions.

Keeping the bridge separate avoids strengthening the kernel TCB.  A model of
the checked arena may establish it once; package-specific formula decoders
then reason solely about `ClosedFormulaHolds`. -/
structure HolEvaluationAgrees (resolve : Resolver) (arena : Arena)
    (interpretation : PartialValuation Ref) : Prop where
  closed : ∀ {reference expression},
    Resolves (coreResolver resolve) arena.holCore reference
      (.term .boolTy expression) →
    interpretation reference = some (ClosedFormulaHolds expression)

/-- Select the unique closed Boolean expression resolved at a reference, when
there is one.  Fuel witnesses are erased; determinism of successful resolution
makes the selected expression canonical. -/
noncomputable def closedFormulaSyntax? (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Option EmptyTm := by
  classical
  exact if found : ∃ expression,
      Resolves (coreResolver resolve) arena.holCore reference
        (.term .boolTy expression) then
    some (Classical.choose found)
  else
    none

theorem closedFormulaSyntax?_eq {resolve : Resolver} {arena : Arena}
    {reference : Ref} {expression : EmptyTm}
    (resolves : Resolves (coreResolver resolve) arena.holCore reference
      (.term .boolTy expression)) :
    closedFormulaSyntax? resolve arena reference = some expression := by
  classical
  unfold closedFormulaSyntax?
  split
  · rename_i found
    have same := Value.Resolves.value_unique (Classical.choose_spec found) resolves
    have expressionEqual : Classical.choose found = expression := by
      simpa using same
    rw [expressionEqual]
  · rename_i absent
    exact False.elim (absent ⟨expression, resolves⟩)

/-- Canonical partial interpretation of checked closed Boolean rows.  Unknown,
ill-sorted, open, or unresolved rows remain indeterminate. -/
noncomputable def closedEvaluationInterpretation (resolve : Resolver)
    (arena : Arena) : PartialValuation Ref := fun reference =>
  (closedFormulaSyntax? resolve arena reference).map ClosedFormulaHolds

/-- The canonical interpretation agrees with closed evaluation by
construction; uniqueness of resolution is the only non-definitional step. -/
theorem closedEvaluationInterpretation_agrees (resolve : Resolver) (arena : Arena) :
    HolEvaluationAgrees resolve arena
      (closedEvaluationInterpretation resolve arena) := by
  constructor
  intro reference expression resolves
  simp [closedEvaluationInterpretation,
    closedFormulaSyntax?_eq resolves]

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

/-- Formula-shape decoding may replace an evaluator-facing proposition by an
equivalent package-facing law without changing the checked theorem row. -/
def ProvedProposition.congr {arena : Arena} {interpretation : PartialValuation Ref}
    {left right : Prop} (proved : ProvedProposition arena interpretation left)
    (equivalent : left ↔ right) : ProvedProposition arena interpretation right := by
  have equal : left = right := propext equivalent
  cases equal
  exact proved

/-- Build evaluator-facing theorem evidence from an exact checked assertion
row.  Package decoders should normally use this constructor and then
`ProvedProposition.congr`, rather than postulating an interpretation entry for
their final high-level law. -/
def ProvedProposition.ofClosedFormula {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref}
    (agreement : HolEvaluationAgrees resolve arena interpretation)
    (reference : Ref) (expression : EmptyTm) (fact : WireSequent)
    (resolves : Resolves (coreResolver resolve) arena.holCore reference
      (.term .boolTy expression))
    (member : fact ∈ arena.hol.thm)
    (assertion : fact.semantic = Sequent.assert reference) :
    ProvedProposition arena interpretation (ClosedFormulaHolds expression) where
  reference := reference
  fact := fact
  member := member
  assertion := assertion
  interpreted := agreement.closed resolves

/-- Complete the standard construction after a package-specific decoder has
identified the exact closed formula's high-level meaning. -/
def ProvedProposition.ofDecodedClosedFormula {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref} {proposition : Prop}
    (agreement : HolEvaluationAgrees resolve arena interpretation)
    (reference : Ref) (expression : EmptyTm) (fact : WireSequent)
    (resolves : Resolves (coreResolver resolve) arena.holCore reference
      (.term .boolTy expression))
    (member : fact ∈ arena.hol.thm)
    (assertion : fact.semantic = Sequent.assert reference)
    (decodes : ClosedFormulaHolds expression ↔ proposition) :
    ProvedProposition arena interpretation proposition :=
  (ProvedProposition.ofClosedFormula agreement reference expression fact
    resolves member assertion).congr decodes

/-- All representation-level evidence needed to decode one exact checked HOL
assertion as a high-level semantic proposition. -/
structure DecodedAssertion (resolve : Resolver) (arena : Arena)
    (proposition : Prop) where
  reference : Ref
  expression : EmptyTm
  fact : WireSequent
  resolves : Resolves (coreResolver resolve) arena.holCore reference
    (.term .boolTy expression)
  member : fact ∈ arena.hol.thm
  assertion : fact.semantic = Sequent.assert reference
  decodes : ClosedFormulaHolds expression ↔ proposition

/-- Base decoder for an exact checked assertion of the Boolean truth literal. -/
def DecodedAssertion.truth {resolve : Resolver} {arena : Arena}
    (reference : Ref) (fact : WireSequent)
    (resolves : Resolves (coreResolver resolve) arena.holCore reference
      (.term .boolTy (.bool true)))
    (member : fact ∈ arena.hol.thm)
    (assertion : fact.semantic = Sequent.assert reference) :
    DecodedAssertion resolve arena True where
  reference := reference
  expression := .bool true
  fact := fact
  resolves := resolves
  member := member
  assertion := assertion
  decodes := by simp

/-- A decoded assertion becomes theorem evidence once the arena's Boolean
interpretation is known to agree with closed HolE evaluation. -/
def DecodedAssertion.proved {resolve : Resolver} {arena : Arena}
    {interpretation : PartialValuation Ref} {proposition : Prop}
    (decoded : DecodedAssertion resolve arena proposition)
    (agreement : HolEvaluationAgrees resolve arena interpretation) :
    ProvedProposition arena interpretation proposition :=
  ProvedProposition.ofDecodedClosedFormula agreement decoded.reference
    decoded.expression decoded.fact decoded.resolves decoded.member
    decoded.assertion decoded.decodes

/-- Source-independent semantics of the exact declaration rows in a checked
natural-number package.  `carrier`, `zero`, and `successor` are related to the
deterministic classical HolE semantics, rather than being arbitrary data
attached to names.

The law fields deliberately use their decoded semantic propositions.  A
separate, syntax-directed decoder can establish those fields for a concrete
arena without becoming part of the trusted kernel API. -/
structure NaturalPackageCertificate (resolve : Resolver) (arena : Arena)
    (interpretation : PartialValuation Ref) where
  agreement : HolEvaluationAgrees resolve arena interpretation
  carrierRef : Ref
  zeroRef : Ref
  successorRef : Ref
  carrierSyntax : EmptyTy
  zeroSyntax : EmptyTm
  successorSyntax : EmptyTm
  carrier : CPointed
  zero : carrier.carrier
  successor : carrier.carrier → carrier.carrier
  carrierResolves :
    Resolves (coreResolver resolve) arena.holCore carrierRef
      (.family .star carrierSyntax)
  carrierDenotes : ClassicallyDenotesFamily carrierSyntax carrier
  zeroResolves :
    Resolves (coreResolver resolve) arena.holCore zeroRef
      (.term carrierSyntax zeroSyntax)
  zeroEvaluates : ClassicallyEvaluates zeroSyntax carrierSyntax carrier zero
  successorResolves :
    Resolves (coreResolver resolve) arena.holCore successorRef
      (.term (.arr carrierSyntax carrierSyntax) successorSyntax)
  successorEvaluates :
    ClassicallyEvaluates successorSyntax (.arr carrierSyntax carrierSyntax)
      ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩ successor
  successorInjective : DecodedAssertion resolve arena
    (∀ x y, successor x = successor y → x = y)
  zeroNeSuccessor : DecodedAssertion resolve arena
    (∀ x, zero ≠ successor x)
  induction : DecodedAssertion resolve arena
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
    ((certificate.successorInjective.proved certificate.agreement).holds
      valid ambientValuation admitted)
    ((certificate.zeroNeSuccessor.proved certificate.agreement).holds
      valid ambientValuation admitted)
    ((certificate.induction.proved certificate.agreement).holds
      valid ambientValuation admitted)

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
  codomain : CPointed
  base : codomain.carrier
  step : naturals.carrier.carrier → codomain.carrier → codomain.carrier
  selected : naturals.carrier.carrier → codomain.carrier
  codomainResolves :
    Resolves (coreResolver resolve) arena.holCore codomainRef
      (.family .star codomainSyntax)
  codomainDenotes : ClassicallyDenotesFamily codomainSyntax codomain
  baseResolves :
    Resolves (coreResolver resolve) arena.holCore baseRef
      (.term codomainSyntax baseSyntax)
  baseEvaluates : ClassicallyEvaluates baseSyntax codomainSyntax codomain base
  stepResolves :
    Resolves (coreResolver resolve) arena.holCore stepRef
      (.term (.arr naturals.carrierSyntax (.arr codomainSyntax codomainSyntax))
        stepSyntax)
  stepEvaluates :
    ClassicallyEvaluates stepSyntax
      (.arr naturals.carrierSyntax (.arr codomainSyntax codomainSyntax))
      ⟨naturals.carrier.carrier → codomain.carrier → codomain.carrier,
        fun _ _ => codomain.point⟩ step
  selectedResolves :
    Resolves (coreResolver resolve) arena.holCore selectedRef
      (.term (.arr naturals.carrierSyntax codomainSyntax) selectedSyntax)
  selectedEvaluates :
    ClassicallyEvaluates selectedSyntax (.arr naturals.carrierSyntax codomainSyntax)
      ⟨naturals.carrier.carrier → codomain.carrier, fun _ => codomain.point⟩
      selected
  graph : DecodedAssertion resolve arena
    (∀ n, ∀ relation : naturals.carrier.carrier → codomain.carrier → Prop,
      relation naturals.zero base →
      (∀ k z, relation k z →
        relation (naturals.successor k) (step k z)) →
      relation n (selected n))
  atZero : DecodedAssertion resolve arena
    (selected naturals.zero = base)
  atSuccessor : DecodedAssertion resolve arena
    (∀ n, selected (naturals.successor n) = step n (selected n))
  unique : DecodedAssertion resolve arena
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
    graph := (certificate.graph.proved certificate.naturals.agreement).holds
      valid ambientValuation admitted
    at_zero := (certificate.atZero.proved certificate.naturals.agreement).holds
      valid ambientValuation admitted
    at_succ := (certificate.atSuccessor.proved certificate.naturals.agreement).holds
      valid ambientValuation admitted
    unique := (certificate.unique.proved certificate.naturals.agreement).holds
      valid ambientValuation admitted
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
    ClassicallyEvaluates addSyntax
      (.arr naturals.carrierSyntax
        (.arr naturals.carrierSyntax naturals.carrierSyntax))
      ⟨naturals.carrier.carrier → naturals.carrier.carrier →
        naturals.carrier.carrier,
        fun _ _ => naturals.carrier.point⟩ add
  atZero : DecodedAssertion resolve arena
    (∀ m, add naturals.zero m = m)
  atSuccessor : DecodedAssertion resolve arena
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
    at_zero := (certificate.atZero.proved certificate.naturals.agreement).holds
      valid ambientValuation admitted
    at_succ := (certificate.atSuccessor.proved certificate.naturals.agreement).holds
      valid ambientValuation admitted
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
