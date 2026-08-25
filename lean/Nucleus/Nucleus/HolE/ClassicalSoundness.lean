import Nucleus.HolE.ClassicalSemantics

/-! # Soundness interface for the deterministic classical HolE semantics

This file is deliberately downstream of `ClassicalSemantics`: it records the
semantic invariants required by the kernel proof without coupling the evaluator
to the syntactic substitution development.
-/

namespace Nucleus.HolE

universe u
set_option relaxedAutoImplicit true

/-- Proof-relevant mirror of typing modulo family equality.  `HasTypeDefEq`
lives in `Prop`, so Lean cannot recurse over it to compute a semantic value;
this mirror is the same standard bridge used by `CChecks` for raw checking. -/
inductive CDefChecks : {types : List Kind} → {depth : Nat} →
    BoundCtx ClassicalSig types depth → Tm ClassicalSig types depth →
    Ty ClassicalSig types → Type 1 where
  | exact : CChecks Γ term (.tm A) → CDefChecks Γ term A
  | app (raw : CChecks Γ (.app f x) (.tm B)) :
      CDefChecks Γ f (.arr A B) → CDefChecks Γ x A →
      CDefChecks Γ (.app f x) B
  | lam (body : Tm ClassicalSig types (depth + 1))
      (raw : CChecks Γ (.lam A body) (.tm (.arr A B))) (hA : CKinded A) :
      CDefChecks (extendBound A Γ) body B →
      CDefChecks Γ (.lam A body) (.arr A B)
  | eq (raw : CChecks Γ (.eq A x y) (.tm .boolTy)) (hA : CKinded A) :
      CDefChecks Γ x A → CDefChecks Γ y A →
      CDefChecks Γ (.eq A x y) .boolTy
  | eps (raw : CChecks Γ (.eps A p) (.tm A)) (hA : CKinded A) :
      CDefChecks Γ p (.arr A .boolTy) →
      CDefChecks Γ (.eps A p) A
  | abs (raw : CChecks Γ (.abs A p x) (.tm (.sub A p))) (hA : CKinded A)
      (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy)) :
      CDefChecks Γ x A → CDefChecks Γ (.abs A p x) (.sub A p)
  | rep (raw : CChecks Γ (.rep A p x) (.tm A)) (hA : CKinded A)
      (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy)) :
      CDefChecks Γ x (.sub A p) → CDefChecks Γ (.rep A p x) A
  | tyExists (raw : CChecks (types := types) Γ (.tyExists p) (.tm .boolTy)) :
      CDefChecks (types := .star :: types) (weakenBoundCtx Γ) p .boolTy →
      CDefChecks (types := types) Γ (.tyExists p) .boolTy
  | tyForall (raw : CChecks (types := types) Γ (.tyForall p) (.tm .boolTy)) :
      CDefChecks (types := .star :: types) (weakenBoundCtx Γ) p .boolTy →
      CDefChecks (types := types) Γ (.tyForall p) .boolTy
  | conv : CDefChecks Γ term A → CKinded B → FamEq ClassicalSig A B →
      CDefChecks Γ term B

/-- Erase a proof-relevant classical checking certificate. -/
theorem CChecks.toChecks : CChecks Γ expression classification →
    Checks Γ expression classification
  | .boolTy => .boolTy
  | .arr hA hB => .arr hA.toChecks hB.toChecks
  | .tyApp hF hA => .tyApp hF.toChecks hA.toChecks
  | .tyLam body => .tyLam body.toChecks
  | .tyBv v => .tyBv v
  | .sub hA hp => .sub hA.toChecks hp.toChecks
  | .model hp => .model hp.toChecks
  | .primFam symbol => nomatch symbol
  | .primTm rule => nomatch rule
  | .bv hA lookup => .bv hA.toChecks lookup
  | .fv name hA => .fv name hA.toChecks
  | .app hA hB function argument => .app function.toChecks argument.toChecks
  | .lam body hA hB bodyChecking => .lam body hA.toChecks bodyChecking.toChecks
  | .bool literal => .bool literal
  | .eq hA left right => .eq hA.toChecks left.toChecks right.toChecks
  | .eps hA predicate => .eps hA.toChecks predicate.toChecks
  | .abs hA hp value => .abs hA.toChecks hp.toChecks value.toChecks
  | .rep hA hp value => .rep hA.toChecks hp.toChecks value.toChecks
  | .tyExists predicate => .tyExists predicate.toChecks
  | .tyForall predicate => .tyForall predicate.toChecks

def CDefChecks.typeKinded : CDefChecks Γ term A → CKinded A
  | .exact raw => raw.typeKinded
  | .app raw .. | .lam _ raw .. | .eq raw .. | .eps raw .. |
      .abs raw .. | .rep raw .. | .tyExists raw _ | .tyForall raw _ => raw.typeKinded
  | .conv _ hB _ => hB

theorem HasTypeDefEq.toC {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (typing : HasTypeDefEq Γ term A) :
    Nonempty (CDefChecks Γ term A) := by
  induction typing with
  | exact raw => exact ⟨.exact raw.certificate⟩
  | app raw _ _ ihf ihx =>
      obtain ⟨cf⟩ := ihf
      obtain ⟨cx⟩ := ihx
      exact ⟨.app raw.certificate cf cx⟩
  | lam body raw hA _ ih =>
      obtain ⟨cbody⟩ := ih
      exact ⟨.lam body raw.certificate hA.certificate cbody⟩
  | eq raw hA _ _ ihx ihy =>
      obtain ⟨cx⟩ := ihx
      obtain ⟨cy⟩ := ihy
      exact ⟨.eq raw.certificate hA.certificate cx cy⟩
  | eps raw hA _ ih =>
      obtain ⟨cp⟩ := ih
      exact ⟨.eps raw.certificate hA.certificate cp⟩
  | abs raw hA hp _ ih =>
      obtain ⟨cx⟩ := ih
      exact ⟨.abs raw.certificate hA.certificate hp.certificate cx⟩
  | rep raw hA hp _ ih =>
      obtain ⟨cx⟩ := ih
      exact ⟨.rep raw.certificate hA.certificate hp.certificate cx⟩
  | tyExists raw _ ih =>
      obtain ⟨cp⟩ := ih
      exact ⟨.tyExists raw.certificate cp⟩
  | tyForall raw _ ih =>
      obtain ⟨cp⟩ := ih
      exact ⟨.tyForall raw.certificate cp⟩
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
  | .app raw .. | .lam _ raw .. | .eq raw .. | .eps raw .. |
      .abs raw .. | .rep raw .. | .tyExists raw _ | .tyForall raw _ =>
      fun env bound expected => cSem raw env bound expected
  | .conv source hB conversion => cDefSem source

/-- A syntax-directed typing certificate underlying definitionally typed
checking.  Structural rules store this certificate for the whole term. -/
structure CDefRawView {types : List Kind} {depth : Nat}
    (Γ : BoundCtx ClassicalSig types depth)
    (term : Tm ClassicalSig types depth) where
  type : Ty ClassicalSig types
  raw : CChecks Γ term (.tm type)

noncomputable def CDefRawView.sem {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    (view : CDefRawView Γ term)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed) :
    ULift expected.carrier := cSem view.raw env bound expected

noncomputable def CDefChecks.rawView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (checking : CDefChecks Γ term A) :
    CDefRawView Γ term :=
  match checking with
  | .exact raw => ⟨_, raw⟩
  | .app raw _ _ => ⟨_, raw⟩
  | .lam _ raw _ _ => ⟨_, raw⟩
  | .eq raw _ _ _ => ⟨_, raw⟩
  | .eps raw _ _ => ⟨_, raw⟩
  | .abs raw _ _ _ => ⟨_, raw⟩
  | .rep raw _ _ _ => ⟨_, raw⟩
  | .tyExists raw _ => ⟨_, raw⟩
  | .tyForall raw _ => ⟨_, raw⟩
  | .conv source _ _ => source.rawView

theorem CDefChecks.rawView_semantics {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (checking : CDefChecks Γ term A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed) :
    cDefSem checking env bound expected = checking.rawView.sem env bound expected := by
  induction checking with
  | conv source hB conversion ih => exact ih env bound
  | exact | app | lam | eq | eps | abs | rep | tyExists | tyForall => rfl

/-- The denotation of a term is independent of both its derivation and its
advertised definitionally equal type. -/
theorem CDefChecks.coherent {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A B : Ty ClassicalSig types} (left : CDefChecks Γ term A)
    (right : CDefChecks Γ term B)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed) :
    cDefSem left env bound expected = cDefSem right env bound expected := by
  rw [left.rawView_semantics, right.rawView_semantics]
  unfold CDefRawView.sem
  cases hl : left.rawView with
  | mk leftType leftRaw =>
    cases hr : right.rawView with
    | mk rightType rightRaw =>
      change cSem leftRaw env bound expected = cSem rightRaw env bound expected
      have typeEqual := leftRaw.type_unique rightRaw
      cases typeEqual
      rw [leftRaw.unique rightRaw]

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
  | app leftRaw rightRaw _ _ _ _ _ _ ihf ihx =>
      exact ⟨.app leftRaw ihf.1 ihx.1, .app rightRaw ihf.2 ihx.2⟩
  | lam leftRaw rightRaw hA _ ih =>
      exact ⟨.lam _ leftRaw hA ih.1, .lam _ rightRaw hA ih.2⟩
  | eq leftRaw rightRaw hA _ _ ihx ihy =>
      exact ⟨.eq leftRaw hA ihx.1 ihy.1, .eq rightRaw hA ihx.2 ihy.2⟩
  | eps leftRaw rightRaw hA _ ih =>
      exact ⟨.eps leftRaw hA ih.1, .eps rightRaw hA ih.2⟩
  | abs leftRaw rightRaw hA hp _ ih =>
      exact ⟨.abs leftRaw hA hp ih.1, .abs rightRaw hA hp ih.2⟩
  | rep leftRaw rightRaw hA hp _ ih =>
      exact ⟨.rep leftRaw hA hp ih.1, .rep rightRaw hA hp ih.2⟩
  | tyExists leftRaw rightRaw _ ih =>
      exact ⟨.tyExists leftRaw ih.1, .tyExists rightRaw ih.2⟩
  | tyForall leftRaw rightRaw _ ih =>
      exact ⟨.tyForall leftRaw ih.1, .tyForall rightRaw ih.2⟩
  | conv leftTyping rightTyping _ _ => exact ⟨leftTyping, rightTyping⟩
  | beta body x hA typedContext applicationRaw bodyTyping argumentTyping resultTyping =>
      cases applicationRaw with
      | app functionRaw argumentRaw =>
          exact ⟨.exact (.app functionRaw argumentRaw), resultTyping⟩
  | eta name fresh typedContext functionTyping etaTyping =>
      exact ⟨etaTyping, functionTyping⟩

/-- The canonical proof that extending a well-kinded bound context preserves
well-kindedness.  Keeping this constructor named is useful because semantic
environment validity below is indexed by the particular context typing
certificate. -/
theorem TypedCtx.extend {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    (hA : Kinded A) (typed : TypedCtx Γ) : TypedCtx (extendBound A Γ) :=
  fun i => Fin.cases hA typed i

/-- A polymorphic bound environment is valid when each entry is represented by
one value at the denotation of its declared type, and every other requested
representation is obtained by `alignCValue` from that value.

This condition is essential: an arbitrary `CBoundEnv` may return unrelated
values when the evaluator asks for definitionally equal types through distinct
typing certificates, which makes beta and eta conversion false. -/
def CBoundValid {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} (typed : TypedCtx Γ)
    (env : CTypeEnv types) (bound : CBoundEnv depth) : Prop :=
  ∀ i expected,
    bound i expected = alignCValue (denoteChecked (typed i) env) expected
      (bound i (denoteChecked (typed i) env))

theorem emptyCBoundEnv_valid (env : CTypeEnv types) :
    CBoundValid (Γ := (emptyBound : BoundCtx ClassicalSig types 0))
      (fun i => Fin.elim0 i) env emptyCBoundEnv := by
  intro i
  exact Fin.elim0 i

private theorem extendCBoundEnv_head_valid (semantic : CPointed)
    (value : semantic.carrier) (bound : CBoundEnv depth) (expected : CPointed) :
    extendCBoundEnv semantic value bound 0 expected =
      alignCValue semantic expected
        (extendCBoundEnv semantic value bound 0 semantic) := by
  by_cases equal : expected = semantic
  · subst expected
    simp [extendCBoundEnv, alignCValue]
  · have reverse : semantic ≠ expected := Ne.symm equal
    simp [extendCBoundEnv, alignCValue, equal, reverse]

theorem extendCBoundEnv_valid {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    (hA : Kinded A) (typed : TypedCtx Γ) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (valid : CBoundValid typed env bound)
    (value : (denoteChecked hA env).carrier) :
    CBoundValid (typed.extend hA) env
      (extendCBoundEnv (denoteChecked hA env) value bound) := by
  intro i expected
  refine Fin.cases ?_ (fun j => ?_) i
  · have proofEq : typed.extend hA (0 : Fin (depth + 1)) = hA :=
      Subsingleton.elim _ _
    rw [proofEq]
    exact extendCBoundEnv_head_valid (denoteChecked hA env) value bound expected
  · change bound j expected = alignCValue
      (denoteChecked (typed j) env) expected
      (bound j (denoteChecked (typed j) env))
    exact valid j expected

/-- A checked context environment packages exactly the data admitted by the
soundness relation. -/
structure CContextEnv {types : List Kind} {depth : Nat}
    (Γ : BoundCtx ClassicalSig types depth) (env : CTypeEnv types) where
  typed : TypedCtx Γ
  bound : CBoundEnv depth
  valid : CBoundValid typed env bound

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
    ∀ (typed : TypedCtx Γ), CBoundValid typed env bound →
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
  have realized := sound proof emptyCTypeEnv emptyCBoundEnv
    (fun i => Fin.elim0 i) (emptyCBoundEnv_valid emptyCTypeEnv) (by
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
    (sound proof emptyCTypeEnv emptyCBoundEnv
      (fun i => Fin.elim0 i) (emptyCBoundEnv_valid emptyCTypeEnv) hypotheses)

namespace CEntails

theorem hyp (member : proposition ∈ hypotheses) :
    CEntails (Γ := Γ) hypotheses proposition := by
  intro env bound typed valid truths
  exact truths proposition member

theorem truth : CEntails (Γ := Γ) hypotheses (.bool true) := by
  intro env bound typed valid truths
  exact CRealizes.boolean true env bound

theorem falseElim (premise : CEntails (Γ := Γ) hypotheses (.bool false)) :
    CEntails (Γ := Γ) hypotheses conclusion := by
  intro env bound typed valid truths
  exact False.elim (not_realizes_false_as_true env bound
    (premise env bound typed valid truths))

private theorem realizes_eq_false_of_false
    {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {proposition : Tm ClassicalSig types depth}
    (typing : HasTypeDefEq Γ proposition .boolTy)
    (equalityTyping : HasTypeDefEq Γ
      (.eq .boolTy proposition (.bool false)) .boolTy)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (evaluates : cDefSem typing.certificate env bound cBool = ⟨false⟩) :
    CRealizes (Γ := Γ) env bound
      (.eq .boolTy proposition (.bool false)) .boolTy cBool true := by
  refine ⟨equalityTyping.certificate, ?_⟩
  classical
  rw [equalityTyping.certificate.rawView_semantics]
  cases viewEq : equalityTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq hA leftChecking rightChecking =>
        have leftEval : cSem leftChecking env bound cBool = ⟨false⟩ := by
          rw [← evaluates]
          exact (typing.certificate.coherent (.exact leftChecking) env bound cBool).symm
        have rightEval : cSem rightChecking env bound cBool = ⟨false⟩ := by
          exact cDefSem_false (.exact rightChecking) env bound
        have hASem : cSem hA env = cBool := cSem_certificate_coherent hA .boolTy env
        change ULift.up (alignCValue cBool cBool
          (decide ((cSem leftChecking env bound (cSem hA env)).down =
            (cSem rightChecking env bound (cSem hA env)).down))) = ULift.up true
        rw [hASem]
        rw [leftEval, rightEval]
        simp [cBool, alignCValue]
        apply cast_eq

theorem boolCases (typing : HasTypeDefEq Γ proposition .boolTy)
    (falseEqualityTyping : HasTypeDefEq Γ
      (.eq .boolTy proposition (.bool false)) .boolTy)
    (left : CEntails (Γ := Γ) (proposition :: hypotheses) conclusion)
    (right : CEntails (Γ := Γ)
      (.eq .boolTy proposition (.bool false) :: hypotheses) conclusion) :
    CEntails (Γ := Γ) hypotheses conclusion := by
  intro env bound typed valid truths
  let evaluated := cDefSem typing.certificate env bound cBool
  generalize valueEq : evaluated.down = value
  have evaluatedEq : evaluated = ULift.up value := by
    have eta : evaluated = ULift.up evaluated.down := by cases evaluated; rfl
    rw [valueEq] at eta
    exact eta
  cases value with
  | true =>
      apply left env bound typed valid
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · refine ⟨typing.certificate, ?_⟩
        exact evaluatedEq
      · exact truths candidate member
  | false =>
      apply right env bound typed valid
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · apply realizes_eq_false_of_false typing falseEqualityTyping env bound
        exact evaluatedEq
      · exact truths candidate member

theorem eqRefl (_hA : Kinded A) (_typing : HasTypeDefEq Γ term A)
    (conclusionTyping : HasTypeDefEq Γ (.eq A term term) .boolTy) :
    CEntails (Γ := Γ) hypotheses (.eq A term term) := by
  intro env bound typed valid truths
  refine ⟨conclusionTyping.certificate, ?_⟩
  classical
  rw [conclusionTyping.certificate.rawView_semantics]
  cases viewEq : conclusionTyping.certificate.rawView with
  | mk rawType raw =>
    simp only [CDefRawView.sem]
    cases raw with
    | eq cA leftChecking rightChecking =>
        have operandsEqual : leftChecking = rightChecking := leftChecking.unique rightChecking
        cases operandsEqual
        change ULift.up (alignCValue cBool cBool
          (decide ((cSem leftChecking env bound (cSem cA env)).down =
            (cSem leftChecking env bound (cSem cA env)).down))) = ULift.up true
        simp
        exact congrArg ULift.up (alignCValue_self cBool true)

theorem hypothesisMap
    (subset : ∀ proposition, proposition ∈ source → proposition ∈ target)
    (premise : CEntails (Γ := Γ) source conclusion) :
    CEntails (Γ := Γ) target conclusion := by
  intro env bound typed valid targetTrue
  apply premise env bound typed valid
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
