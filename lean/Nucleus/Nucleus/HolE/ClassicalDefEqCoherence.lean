import Nucleus.HolE.ClassicalSoundness

/-! # Inversion for typing modulo family conversion

`CDefChecks` deliberately records conversion nodes.  Consequently a direct
case split on an arbitrary certificate first encounters an uninformative
`conv` case.  This file factors every certificate into a syntax-directed root
and one (possibly reflexive) `FamEq` path.  The views below are the useful
inversion interface for semantic coherence proofs: conversions can be handled
once, at the result type, while recursive certificates expose the constructor
of the term being evaluated.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- Evidence that a `CDefChecks` certificate's outermost rule is syntax
directed.  An inductive witness gives dependent inversion substantially better
behavior than a Boolean discriminator. -/
inductive CDefChecks.IsRoot {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} : {A : Ty ClassicalSig types} →
    {term : Tm ClassicalSig types depth} → CDefChecks Γ term A → Type 1 where
  | exact (raw : CChecks Γ term (.tm A)) : IsRoot (.exact raw)
  | app (function : CDefChecks Γ f (.arr A B))
      (argument : CDefChecks Γ x A) : IsRoot (.app function argument)
  | lam (body : Tm ClassicalSig types (depth + 1)) (hA : CKinded A)
      (bodyChecking : CDefChecks (extendBound A Γ) body B) :
      IsRoot (.lam body hA bodyChecking)
  | eq (hA : CKinded A) (left : CDefChecks Γ x A)
      (right : CDefChecks Γ y A) : IsRoot (.eq hA left right)
  | eps (hA : CKinded A) (predicate : CDefChecks Γ p (.arr A .boolTy)) :
      IsRoot (.eps hA predicate)
  | abs (hA : CKinded A)
      (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
      (value : CDefChecks Γ x A) : IsRoot (.abs hA hp value)
  | rep (hA : CKinded A)
      (hp : CChecks (extendBound A emptyBound) p (.tm .boolTy))
      (value : CDefChecks Γ x (.sub A p)) : IsRoot (.rep hA hp value)
  | tyExists (predicate : CDefChecks (types := .star :: types)
      emptyBound p .boolTy) : IsRoot (Γ := Γ) (.tyExists predicate)

/-- The result of stripping all outer conversions from a certificate.  This is
`Type`-valued because both checking and family-equality certificates carry
computational data. -/
structure CDefRootView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (checking : CDefChecks Γ term A) where
  type : Ty ClassicalSig types
  root : CDefChecks Γ term type
  isRoot : root.IsRoot
  conversion : FamEq ClassicalSig type A

private def CDefRootView.self {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (checking : CDefChecks Γ term A)
    (root : checking.IsRoot) : CDefRootView checking :=
  ⟨A, checking, root, .refl⟩

/-- Strip all outer conversion rules, composing their family equalities. -/
noncomputable def CDefChecks.rootView (checking : CDefChecks Γ term A) :
    CDefRootView checking :=
  by
    induction checking with
    | conv source hB conversion ih =>
        exact ⟨ih.type, ih.root, ih.isRoot, .trans ih.conversion conversion⟩
    | exact raw => exact CDefRootView.self (.exact raw) (.exact raw)
    | app function argument _ _ =>
        exact CDefRootView.self (.app function argument) (.app function argument)
    | lam body hA bodyChecking _ =>
        exact CDefRootView.self (.lam body hA bodyChecking)
          (.lam body hA bodyChecking)
    | eq hA left right _ _ =>
        exact CDefRootView.self (.eq hA left right) (.eq hA left right)
    | eps hA predicate _ =>
        exact CDefRootView.self (.eps hA predicate) (.eps hA predicate)
    | abs hA hp value _ =>
        exact CDefRootView.self (.abs hA hp value) (.abs hA hp value)
    | rep hA hp value _ =>
        exact CDefRootView.self (.rep hA hp value) (.rep hA hp value)
    | tyExists predicate _ =>
        exact CDefRootView.self (.tyExists predicate) (.tyExists predicate)

/-- Conversion is definitionally erased by the deterministic evaluator. -/
@[simp] theorem cDefSem_conv_eq {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A B : Ty ClassicalSig types} (source : CDefChecks Γ term A)
    (hB : CKinded B) (conversion : FamEq ClassicalSig A B)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed) :
    cDefSem (.conv source hB conversion) env bound expected =
      cDefSem source env bound expected := rfl

/-- Evaluation agrees with the syntax-directed root obtained by stripping its
outer conversion chain. -/
theorem CDefChecks.rootView_semantics {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (checking : CDefChecks Γ term A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) (expected : CPointed) :
    cDefSem checking env bound expected =
      cDefSem checking.rootView.root env bound expected := by
  induction checking with
  | conv source hB conversion ih =>
      simpa [CDefChecks.rootView] using ih env bound
  | exact | app | lam | eq | eps | abs | rep | tyExists => rfl

/-- Complete application inversion, with every outer conversion composed into
the codomain-to-result path. -/
structure CDefAppView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {function argument : Tm ClassicalSig types depth}
    {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.app function argument) result) where
  domain : Ty ClassicalSig types
  codomain : Ty ClassicalSig types
  functionChecking : CDefChecks Γ function (.arr domain codomain)
  argumentChecking : CDefChecks Γ argument domain
  conversion : FamEq ClassicalSig codomain result

noncomputable def CDefChecks.appView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {function argument : Tm ClassicalSig types depth}
    {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.app function argument) result) :
    CDefAppView checking :=
  match checking with
  | .exact (.app _ _ functionChecking argumentChecking) =>
      ⟨_, _, .exact functionChecking, .exact argumentChecking, .refl⟩
  | .app functionChecking argumentChecking =>
      ⟨_, _, functionChecking, argumentChecking, .refl⟩
  | .conv source _ conversion =>
      let view := source.appView
      ⟨view.domain, view.codomain, view.functionChecking, view.argumentChecking,
        .trans view.conversion conversion⟩

/-- Complete lambda inversion, again exposing only one composed result
conversion. -/
structure CDefLamView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {domain : Ty ClassicalSig types}
    {body : Tm ClassicalSig types (depth + 1)} {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.lam domain body) result) where
  codomain : Ty ClassicalSig types
  domainKinded : CKinded domain
  bodyChecking : CDefChecks (extendBound domain Γ) body codomain
  conversion : FamEq ClassicalSig (.arr domain codomain) result

noncomputable def CDefChecks.lamView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {domain : Ty ClassicalSig types}
    {body : Tm ClassicalSig types (depth + 1)} {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.lam domain body) result) : CDefLamView checking :=
  match checking with
  | .exact (.lam _ hA _ bodyChecking) =>
      ⟨_, hA, .exact bodyChecking, .refl⟩
  | .lam _ hA bodyChecking => ⟨_, hA, bodyChecking, .refl⟩
  | .conv source _ conversion =>
      let view := source.lamView
      ⟨view.codomain, view.domainKinded, view.bodyChecking,
        .trans view.conversion conversion⟩

/-- A Boolean literal has root type `boolTy`; any other advertised type comes
solely from conversion. -/
noncomputable def CDefChecks.boolConversion {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {literal : Bool}
    {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.bool literal) result) :
    FamEq ClassicalSig .boolTy result :=
  match checking with
  | .exact (.bool _) => .refl
  | .conv source _ conversion => .trans source.boolConversion conversion

/-- A type existential has root type `boolTy`. -/
noncomputable def CDefChecks.tyExistsConversion {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    {predicate : Tm ClassicalSig (.star :: types) 0}
    {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.tyExists predicate) result) :
    FamEq ClassicalSig .boolTy result :=
  match checking with
  | .exact (.tyExists predicateChecking) => .refl
  | .tyExists _ => .refl
  | .conv source _ conversion => .trans source.tyExistsConversion conversion

/-- Equality inversion exposes its common operand type and composes any result
conversion from Boolean. -/
structure CDefEqView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {annotated : Ty ClassicalSig types}
    {left right : Tm ClassicalSig types depth} {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.eq annotated left right) result) where
  annotatedKinded : CKinded annotated
  leftChecking : CDefChecks Γ left annotated
  rightChecking : CDefChecks Γ right annotated
  conversion : FamEq ClassicalSig .boolTy result

noncomputable def CDefChecks.eqView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {annotated : Ty ClassicalSig types}
    {left right : Tm ClassicalSig types depth} {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.eq annotated left right) result) :
    CDefEqView checking :=
  match checking with
  | .exact (.eq hA leftChecking rightChecking) =>
      ⟨hA, .exact leftChecking, .exact rightChecking, .refl⟩
  | .eq hA leftChecking rightChecking =>
      ⟨hA, leftChecking, rightChecking, .refl⟩
  | .conv source _ conversion =>
      let view := source.eqView
      ⟨view.annotatedKinded, view.leftChecking, view.rightChecking,
        .trans view.conversion conversion⟩

/-- Choice inversion exposes the predicate certificate and a conversion from
the annotated carrier to the advertised result. -/
structure CDefEpsView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {carrier : Ty ClassicalSig types}
    {predicate : Tm ClassicalSig types depth} {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.eps carrier predicate) result) where
  carrierKinded : CKinded carrier
  predicateChecking : CDefChecks Γ predicate (.arr carrier .boolTy)
  conversion : FamEq ClassicalSig carrier result

noncomputable def CDefChecks.epsView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {carrier : Ty ClassicalSig types}
    {predicate : Tm ClassicalSig types depth} {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.eps carrier predicate) result) :
    CDefEpsView checking :=
  match checking with
  | .exact (.eps hA predicateChecking) =>
      ⟨hA, .exact predicateChecking, .refl⟩
  | .eps hA predicateChecking => ⟨hA, predicateChecking, .refl⟩
  | .conv source _ conversion =>
      let view := source.epsView
      ⟨view.carrierKinded, view.predicateChecking,
        .trans view.conversion conversion⟩

/-- Subtype abstraction inversion. -/
structure CDefAbsView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {carrier : Ty ClassicalSig types}
    {predicate : Tm ClassicalSig types 1} {value : Tm ClassicalSig types depth}
    {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.abs carrier predicate value) result) where
  carrierKinded : CKinded carrier
  predicateChecking : CChecks (extendBound carrier emptyBound) predicate (.tm .boolTy)
  valueChecking : CDefChecks Γ value carrier
  conversion : FamEq ClassicalSig (.sub carrier predicate) result

noncomputable def CDefChecks.absView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {carrier : Ty ClassicalSig types}
    {predicate : Tm ClassicalSig types 1} {value : Tm ClassicalSig types depth}
    {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.abs carrier predicate value) result) :
    CDefAbsView checking :=
  match checking with
  | .exact (.abs hA hp valueChecking) =>
      ⟨hA, hp, .exact valueChecking, .refl⟩
  | .abs hA hp valueChecking => ⟨hA, hp, valueChecking, .refl⟩
  | .conv source _ conversion =>
      let view := source.absView
      ⟨view.carrierKinded, view.predicateChecking, view.valueChecking,
        .trans view.conversion conversion⟩

/-- Subtype representation inversion. -/
structure CDefRepView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {carrier : Ty ClassicalSig types}
    {predicate : Tm ClassicalSig types 1} {value : Tm ClassicalSig types depth}
    {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.rep carrier predicate value) result) where
  carrierKinded : CKinded carrier
  predicateChecking : CChecks (extendBound carrier emptyBound) predicate (.tm .boolTy)
  valueChecking : CDefChecks Γ value (.sub carrier predicate)
  conversion : FamEq ClassicalSig carrier result

noncomputable def CDefChecks.repView {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {carrier : Ty ClassicalSig types}
    {predicate : Tm ClassicalSig types 1} {value : Tm ClassicalSig types depth}
    {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.rep carrier predicate value) result) :
    CDefRepView checking :=
  match checking with
  | .exact (.rep hA hp valueChecking) =>
      ⟨hA, hp, .exact valueChecking, .refl⟩
  | .rep hA hp valueChecking => ⟨hA, hp, valueChecking, .refl⟩
  | .conv source _ conversion =>
      let view := source.repView
      ⟨view.carrierKinded, view.predicateChecking, view.valueChecking,
        .trans view.conversion conversion⟩

/-- Semantic inversion of a true equality.  This deliberately returns the
operand certificates existentially instead of mentioning the noncomputable
view projections, which keeps rewriting robust. -/
theorem cDefSem_eq_true_elim {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {annotated : Ty ClassicalSig types}
    {left right : Tm ClassicalSig types depth} {result : Ty ClassicalSig types}
    (checking : CDefChecks Γ (.eq annotated left right) result)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (truth : cDefSem checking env bound cBool = ⟨true⟩) :
    ∃ (hA : CKinded annotated) (leftChecking : CDefChecks Γ left annotated)
        (rightChecking : CDefChecks Γ right annotated),
      (cDefSem leftChecking env bound (cSem hA env)).down =
        (cDefSem rightChecking env bound (cSem hA env)).down := by
  classical
  cases checking with
  | exact raw =>
      cases raw with
      | eq hA leftChecking rightChecking =>
          refine ⟨hA, .exact leftChecking, .exact rightChecking, ?_⟩
          have decision := congrArg ULift.down truth
          change alignCValue cBool cBool (decide _) = true at decision
          have decision' : decide
              ((cSem leftChecking env bound (cSem hA env)).down =
                (cSem rightChecking env bound (cSem hA env)).down) = true := by
            exact (alignCValue_self cBool _).symm.trans decision
          exact of_decide_eq_true decision'
  | eq hA leftChecking rightChecking =>
      refine ⟨hA, leftChecking, rightChecking, ?_⟩
      have decision := congrArg ULift.down truth
      change alignCValue cBool cBool (decide _) = true at decision
      have decision' : decide
          ((cDefSem leftChecking env bound (cSem hA env)).down =
            (cDefSem rightChecking env bound (cSem hA env)).down) = true := by
        exact (alignCValue_self cBool _).symm.trans decision
      exact of_decide_eq_true decision'
  | conv source hB conversion =>
      exact cDefSem_eq_true_elim source env bound truth

end Nucleus.HolE
