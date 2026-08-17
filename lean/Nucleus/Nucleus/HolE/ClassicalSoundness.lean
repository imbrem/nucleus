import Nucleus.HolE.ClassicalSemantics

/-! # Soundness interface for the deterministic classical HolE semantics

This file is deliberately downstream of `ClassicalSemantics`: it records the
semantic invariants required by the kernel proof without coupling the evaluator
to the syntactic substitution development.
-/

namespace Nucleus.HolE

universe u
set_option relaxedAutoImplicit true

/-- Typing modulo family conversion still determines a well-kinded result
type.  This is useful independently of semantics and lets semantic evaluation
always choose the denotation of the advertised result type. -/
theorem HasTypeDefEq.typeKinded {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (typing : HasTypeDefEq Γ term A) : Kinded A := by
  induction typing with
  | exact raw => exact raw.typeKinded
  | app _ _ ihf _ =>
      cases ihf with
      | arr _ hB => exact hB
  | lam _ hA _ ih => exact .arr hA ih
  | eq | tyExists => exact .boolTy
  | eps hA _ _ | rep hA _ _ _ => exact hA
  | abs hA hp _ _ => exact .sub hA hp
  | conv _ hB _ _ => exact hB

/-- Proof-relevant mirror of typing modulo family equality.  `HasTypeDefEq`
lives in `Prop`, so Lean cannot recurse over it to compute a semantic value;
this mirror is the same standard bridge used by `CChecks` for raw checking. -/
inductive CDefChecks : {types : List Kind} → {depth : Nat} →
    BoundCtx ClassicalSig types depth → Tm ClassicalSig types depth →
    Ty ClassicalSig types → Type 1 where
  | exact : CChecks Γ term (.tm A) → CDefChecks Γ term A
  | app : CDefChecks Γ f (.arr A B) → CDefChecks Γ x A →
      CDefChecks Γ (.app f x) B
  | lam (body : Tm ClassicalSig types (depth + 1)) (hA : CKinded A) :
      CDefChecks (extendBound A Γ) body B →
      CDefChecks Γ (.lam A body) (.arr A B)
  | eq (hA : CKinded A) : CDefChecks Γ x A → CDefChecks Γ y A →
      CDefChecks Γ (.eq A x y) .boolTy
  | eps (hA : CKinded A) : CDefChecks Γ p (.arr A .boolTy) →
      CDefChecks Γ (.eps A p) A
  | abs (hA : CKinded A)
      (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy)) :
      CDefChecks Γ x A → CDefChecks Γ (.abs A p x) (.sub A p)
  | rep (hA : CKinded A)
      (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy)) :
      CDefChecks Γ x (.sub A p) → CDefChecks Γ (.rep A p x) A
  | tyExists : CDefChecks (types := .star :: types) emptyBound p .boolTy →
      CDefChecks (types := types) Γ (.tyExists p) .boolTy
  | conv : CDefChecks Γ term A → CKinded B → FamEq ClassicalSig A B →
      CDefChecks Γ term B

def CDefChecks.typeKinded : CDefChecks Γ term A → CKinded A
  | .exact raw => raw.typeKinded
  | .app function _ => by
      cases function.typeKinded with
      | arr _ hB => exact hB
  | .lam _ hA body => .arr hA body.typeKinded
  | .eq .. | .tyExists _ => .boolTy
  | .eps hA _ | .rep hA _ _ => hA
  | .abs hA hp _ => .sub hA hp
  | .conv _ hB _ => hB

theorem HasTypeDefEq.toC {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (typing : HasTypeDefEq Γ term A) :
    Nonempty (CDefChecks Γ term A) := by
  induction typing with
  | exact raw => exact ⟨.exact raw.certificate⟩
  | app _ _ ihf ihx =>
      obtain ⟨cf⟩ := ihf
      obtain ⟨cx⟩ := ihx
      exact ⟨.app cf cx⟩
  | lam body hA _ ih =>
      obtain ⟨cbody⟩ := ih
      exact ⟨.lam body hA.certificate cbody⟩
  | eq hA _ _ ihx ihy =>
      obtain ⟨cx⟩ := ihx
      obtain ⟨cy⟩ := ihy
      exact ⟨.eq hA.certificate cx cy⟩
  | eps hA _ ih =>
      obtain ⟨cp⟩ := ih
      exact ⟨.eps hA.certificate cp⟩
  | abs hA hp _ ih =>
      obtain ⟨cx⟩ := ih
      exact ⟨.abs hA.certificate hp.certificate cx⟩
  | rep hA hp _ ih =>
      obtain ⟨cx⟩ := ih
      exact ⟨.rep hA.certificate hp.certificate cx⟩
  | tyExists _ ih =>
      obtain ⟨cp⟩ := ih
      exact ⟨.tyExists cp⟩
  | conv _ hB conversion ih =>
      obtain ⟨cterm⟩ := ih
      exact ⟨.conv cterm hB.certificate conversion⟩

noncomputable def HasTypeDefEq.certificate (typing : HasTypeDefEq Γ term A) :
    CDefChecks Γ term A := Classical.choice typing.toC

/-- Deterministic evaluation of typing modulo family conversion.  Conversion
does not alter the term computation: it only changes the expected semantic
carrier.  `famEq_sound` will show that this use of `alignCValue` is always on
equal carriers, never its pointed fallback branch. -/
noncomputable def cDefSem {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (checking : CDefChecks Γ term A) :
    CTypeEnv types → CBoundEnv depth → (expected : CPointed) →
      ULift.{1, 0} expected.carrier := by
  classical
  exact match checking with
  | .exact raw => fun env bound expected => cSem raw env bound expected
  | .app function argument =>
      match function.typeKinded with
      | .arr hA hB => fun env bound expected =>
          let domain := cSem hA env
          let codomain := cSem hB env
          let functionType : CPointed :=
            ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
          ⟨alignCValue codomain expected
            ((cDefSem function env bound functionType).down
              (cDefSem argument env bound domain).down)⟩
  | .lam body hA bodyChecking => fun env bound expected =>
      let domain := cSem hA env
      let codomain := cSem bodyChecking.typeKinded env
      let functionType : CPointed :=
        ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
      let function := fun argument =>
        (cDefSem bodyChecking env
          (extendCBoundEnv domain argument bound) codomain).down
      ⟨alignCValue functionType expected function⟩
  | .eq hA left right => fun env bound expected =>
      let carrier := cSem hA env
      ⟨alignCValue cBool expected
        (decide ((cDefSem left env bound carrier).down =
          (cDefSem right env bound carrier).down))⟩
  | .eps hA predicate => fun env bound expected =>
      let carrier := cSem hA env
      let functionType : CPointed := ⟨carrier.carrier → Bool, fun _ => false⟩
      let pred := (cDefSem predicate env bound functionType).down
      let selected := if witness : ∃ value, pred value = true then
        Classical.choose witness else carrier.point
      ⟨alignCValue carrier expected selected⟩
  | .abs hA hp value => fun env bound expected =>
      let carrier := cSem hA env
      let predicate := fun value =>
        (cSem hp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      let subtype := cGuardedType carrier predicate
      ⟨alignCValue subtype expected
        (cGuardedAbs carrier predicate (cDefSem value env bound carrier).down)⟩
  | .rep hA hp value => fun env bound expected =>
      let carrier := cSem hA env
      let predicate := fun value =>
        (cSem hp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      let subtype := cGuardedType carrier predicate
      ⟨alignCValue carrier expected (cDefSem value env bound subtype).down.1⟩
  | .tyExists predicate => fun env _ expected =>
      ⟨alignCValue cBool expected (decide (∃ candidate : CPointed,
        cDefSem predicate (extendCTypeEnv (kind := .star) candidate env)
          emptyCBoundEnv cBool = ⟨true⟩))⟩
  | .conv source hB conversion => cDefSem source

noncomputable def evalDefEq {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (typing : HasTypeDefEq Γ term A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed) :
    ULift.{1, 0} expected.carrier :=
  cDefSem typing.certificate env bound expected

def CDefTrue {term : Tm ClassicalSig [] 0}
    (typing : HasTypeDefEq (emptyBound : BoundCtx ClassicalSig [] 0) term .boolTy) : Prop :=
  (evalDefEq typing emptyCTypeEnv emptyCBoundEnv cBool).down = true

/-- Both sides of a kernel term equality have its advertised type. -/
theorem EqTm.typing {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {left right : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (equality : EqTm Γ left right A) :
    HasTypeDefEq Γ left A ∧ HasTypeDefEq Γ right A := by
  induction equality with
  | refl typing => exact ⟨typing, typing⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | app _ _ ihf ihx => exact ⟨.app ihf.1 ihx.1, .app ihf.2 ihx.2⟩
  | lam hA _ ih => exact ⟨.lam _ hA ih.1, .lam _ hA ih.2⟩
  | beta body x hA bodyTyping argumentTyping resultTyping =>
      exact ⟨.app (.lam body hA bodyTyping) argumentTyping, resultTyping⟩
  | eta name fresh functionTyping etaTyping => exact ⟨etaTyping, functionTyping⟩

/-- A typed context paired with the polymorphic bound environment consumed by
`cSem`.  At a lookup, the evaluator specializes `bound` to the denotation of
the type certified by `typed`. -/
structure CContextEnv {types : List Kind} {depth : Nat}
    (Γ : BoundCtx ClassicalSig types depth) where
  typed : TypedCtx Γ
  bound : CBoundEnv depth

/-- A term realizes a semantic value when some proof-relevant typing
certificate computes that value.  Existential certificate semantics is enough
for kernel soundness and avoids making consistency wait on proof-irrelevance
of arbitrary `FamEq` certificate paths. -/
def CRealizes {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} (env : CTypeEnv types)
    (bound : CBoundEnv depth) (term : Tm ClassicalSig types depth)
    (A : Ty ClassicalSig types) (expected : CPointed)
    (value : expected.carrier) : Prop :=
  ∃ checking : CDefChecks Γ term A,
    cDefSem checking env bound expected = ⟨value⟩

def CHypsTrue {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} (env : CTypeEnv types)
    (bound : CBoundEnv depth) (hypotheses : List (Tm ClassicalSig types depth)) : Prop :=
  ∀ proposition, proposition ∈ hypotheses →
    CRealizes (Γ := Γ) env bound proposition .boolTy cBool true

def CEntails {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    (hypotheses : List (Tm ClassicalSig types depth))
    (conclusion : Tm ClassicalSig types depth) : Prop :=
  ∀ (env : CTypeEnv types) (bound : CBoundEnv depth),
    CHypsTrue (Γ := Γ) env bound hypotheses →
    CRealizes (Γ := Γ) env bound conclusion .boolTy cBool true

theorem CRealizes.boolean (literal : Bool) (env : CTypeEnv types)
    (bound : CBoundEnv depth) :
    CRealizes (Γ := Γ) env bound (.bool literal) .boolTy cBool literal := by
  refine ⟨.exact (.bool literal), ?_⟩
  change ULift.up (alignCValue cBool cBool literal) = ULift.up literal
  exact congrArg ULift.up (alignCValue_self cBool literal)

theorem cDefSem_false {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} (checking : CDefChecks Γ (.bool false) A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    cDefSem checking env bound cBool = ⟨false⟩ := by
  cases checking with
  | exact raw =>
      cases raw
      change ULift.up (alignCValue cBool cBool false) = ULift.up false
      exact congrArg ULift.up (alignCValue_self cBool false)
  | conv source hB conversion => exact cDefSem_false source env bound
termination_by sizeOf checking

theorem not_realizes_false_as_true (env : CTypeEnv types) (bound : CBoundEnv depth) :
    ¬ CRealizes (Γ := Γ) env bound (.bool false) .boolTy cBool true := by
  rintro ⟨checking, evaluates⟩
  rw [cDefSem_false checking env bound] at evaluates
  exact Bool.noConfusion (congrArg ULift.down evaluates)

/-- Once the rule induction supplies `CEntails`, consistency is immediate and
does not require certificate coherence: literal-false inversion above handles
every possible conversion wrapper. -/
theorem no_closed_false_of_sound
    (sound : ∀ _proof : Proves (emptyBound : BoundCtx ClassicalSig [] 0) []
      (.bool false), CEntails (Γ := (emptyBound : BoundCtx ClassicalSig [] 0))
        [] (.bool false)) :
    Proves (emptyBound : BoundCtx ClassicalSig [] 0) [] (.bool false) → False := by
  intro proof
  have realized := sound proof emptyCTypeEnv emptyCBoundEnv (by
    intro proposition member
    nomatch member)
  exact not_realizes_false_as_true emptyCTypeEnv emptyCBoundEnv realized

/-- Generic one-axiom consistency consequence.  The infinity development only
has to establish realization of its closed axiom by the `Nat` witness. -/
theorem no_closed_false_under_axiom_of_sound
    (axiomTerm : Tm ClassicalSig [] 0)
    (axiomTrue : CRealizes (Γ := (emptyBound : BoundCtx ClassicalSig [] 0))
      emptyCTypeEnv emptyCBoundEnv axiomTerm .boolTy cBool true)
    (sound : ∀ _proof : Proves (emptyBound : BoundCtx ClassicalSig [] 0) [axiomTerm]
      (.bool false), CEntails (Γ := (emptyBound : BoundCtx ClassicalSig [] 0))
        [axiomTerm] (.bool false)) :
    Proves (emptyBound : BoundCtx ClassicalSig [] 0) [axiomTerm] (.bool false) → False := by
  intro proof
  have hypotheses : CHypsTrue (Γ := (emptyBound : BoundCtx ClassicalSig [] 0))
      emptyCTypeEnv emptyCBoundEnv [axiomTerm] := by
    intro proposition member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst proposition
    exact axiomTrue
  exact not_realizes_false_as_true emptyCTypeEnv emptyCBoundEnv
    (sound proof emptyCTypeEnv emptyCBoundEnv hypotheses)

namespace CEntails

theorem hyp (member : proposition ∈ hypotheses) :
    CEntails (Γ := Γ) hypotheses proposition := by
  intro env bound truths
  exact truths proposition member

theorem truth : CEntails (Γ := Γ) hypotheses (.bool true) := by
  intro env bound truths
  exact CRealizes.boolean true env bound

theorem falseElim (premise : CEntails (Γ := Γ) hypotheses (.bool false)) :
    CEntails (Γ := Γ) hypotheses conclusion := by
  intro env bound truths
  exact False.elim (not_realizes_false_as_true env bound (premise env bound truths))

private theorem realizes_eq_false_of_false
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {proposition : Tm ClassicalSig types depth}
    (typing : HasTypeDefEq Γ proposition .boolTy)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (evaluates : cDefSem typing.certificate env bound cBool = ⟨false⟩) :
    CRealizes (Γ := Γ) env bound
      (.eq .boolTy proposition (.bool false)) .boolTy cBool true := by
  let falseChecking : CDefChecks Γ (.bool false) .boolTy := .exact (.bool false)
  refine ⟨.eq .boolTy typing.certificate falseChecking, ?_⟩
  classical
  change ULift.up (alignCValue cBool cBool
    (decide ((cDefSem typing.certificate env bound cBool).down =
      (cDefSem falseChecking env bound cBool).down))) = ULift.up true
  rw [evaluates, cDefSem_false falseChecking env bound]
  simp [cBool, alignCValue]
  apply cast_eq

theorem boolCases (typing : HasTypeDefEq Γ proposition .boolTy)
    (left : CEntails (Γ := Γ) (proposition :: hypotheses) conclusion)
    (right : CEntails (Γ := Γ)
      (.eq .boolTy proposition (.bool false) :: hypotheses) conclusion) :
    CEntails (Γ := Γ) hypotheses conclusion := by
  intro env bound truths
  let evaluated := cDefSem typing.certificate env bound cBool
  generalize valueEq : evaluated.down = value
  have evaluatedEq : evaluated = ULift.up value := by
    have eta : evaluated = ULift.up evaluated.down := by cases evaluated; rfl
    rw [valueEq] at eta
    exact eta
  cases value with
  | true =>
      apply left env bound
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨typing.certificate, ?_⟩
        exact evaluatedEq
      · exact truths candidate member
  | false =>
      apply right env bound
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · apply realizes_eq_false_of_false typing env bound
        exact evaluatedEq
      · exact truths candidate member

theorem eqRefl (hA : Kinded A) (typing : HasTypeDefEq Γ term A) :
    CEntails (Γ := Γ) hypotheses (.eq A term term) := by
  intro env bound truths
  let cA := hA.certificate
  let cterm := typing.certificate
  refine ⟨.eq cA cterm cterm, ?_⟩
  classical
  change ULift.up (alignCValue cBool cBool
    (decide ((cDefSem cterm env bound (cSem cA env)).down =
      (cDefSem cterm env bound (cSem cA env)).down))) = ULift.up true
  have decision : @decide
      ((cDefSem cterm env bound (cSem cA env)).down =
        (cDefSem cterm env bound (cSem cA env)).down)
      (Classical.propDecidable _) = true := by simp
  rw [decision]
  exact congrArg ULift.up (alignCValue_self cBool true)

theorem hypothesisMap
    (subset : ∀ proposition, proposition ∈ source → proposition ∈ target)
    (premise : CEntails (Γ := Γ) source conclusion) :
    CEntails (Γ := Γ) target conclusion := by
  intro env bound targetTrue
  apply premise env bound
  intro proposition member
  exact targetTrue proposition (subset proposition member)

end CEntails

/-- The two fundamental transport facts needed by beta, eta, generalization,
and type quantification.  They are intentionally named here so the kernel
proof and the substitution proof can be developed independently. -/
structure ClassicalTransportLaws where
  famEq_sound : ∀ {types kind} {A B : Fam ClassicalSig types kind}
      (hA : Kinded A) (hB : Kinded B),
    FamEq ClassicalSig A B → ∀ env,
      denoteChecked hA env = denoteChecked hB env

end Nucleus.HolE
