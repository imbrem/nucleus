import Nucleus.HolE.ClassicalEquations

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
  induction checking with
  | exact raw => exact fun env bound expected => cSem raw env bound expected
  | app function argument ihf ihx =>
      cases function.typeKinded with
      | arr hA hB => exact fun env bound expected =>
          let domain := cSem hA env
          let codomain := cSem hB env
          let functionType : CPointed :=
            ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
          ⟨alignCValue codomain expected
            ((ihf env bound functionType).down (ihx env bound domain).down)⟩
  | lam body hA bodyChecking ih => exact fun env bound expected =>
      let domain := cSem hA env
      let codomain := cSem bodyChecking.typeKinded env
      let functionType : CPointed :=
        ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
      let function := fun argument =>
        (ih env (extendCBoundEnv domain argument bound) codomain).down
      ⟨alignCValue functionType expected function⟩
  | eq hA left right ihx ihy => exact fun env bound expected =>
      let carrier := cSem hA env
      ⟨alignCValue cBool expected
        (decide ((ihx env bound carrier).down = (ihy env bound carrier).down))⟩
  | eps hA predicate ih => exact fun env bound expected =>
      let carrier := cSem hA env
      let functionType : CPointed := ⟨carrier.carrier → Bool, fun _ => false⟩
      let pred := (ih env bound functionType).down
      let selected := if witness : ∃ value, pred value = true then
        Classical.choose witness else carrier.point
      ⟨alignCValue carrier expected selected⟩
  | abs hA hp value ih => exact fun env bound expected =>
      let carrier := cSem hA env
      let predicate := fun value =>
        (cSem hp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      let subtype := cGuardedType carrier predicate
      ⟨alignCValue subtype expected
        (cGuardedAbs carrier predicate (ih env bound carrier).down)⟩
  | rep hA hp value ih => exact fun env bound expected =>
      let carrier := cSem hA env
      let predicate := fun value =>
        (cSem hp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      let subtype := cGuardedType carrier predicate
      ⟨alignCValue carrier expected (ih env bound subtype).down.1⟩
  | tyExists predicate ih => exact fun env _ expected =>
      ⟨alignCValue cBool expected (decide (∃ candidate : CPointed,
        ih (extendCTypeEnv (kind := .star) candidate env)
          emptyCBoundEnv cBool = ⟨true⟩))⟩
  | conv source hB conversion ih => exact ih

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

/-- Truth of hypotheses, parameterized by the eventual evaluator for typing
modulo `FamEq`.  Keeping this predicate evaluator-parametric separates the
logical induction from the conversion/substitution proof. -/
def CHypsTrue {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    (eval : ∀ {term A}, HasTypeDefEq Γ term A →
      CTypeEnv types → CBoundEnv depth → CPointed → Bool)
    (typeEnv : CTypeEnv types) (bound : CBoundEnv depth)
    (hypotheses : List (Tm ClassicalSig types depth)) : Prop :=
  ∀ proposition, proposition ∈ hypotheses →
    ∀ typing : HasTypeDefEq Γ proposition .boolTy,
      eval typing typeEnv bound cBool = true

/-- The two fundamental transport facts needed by beta, eta, generalization,
and type quantification.  They are intentionally named here so the kernel
proof and the substitution proof can be developed independently. -/
structure ClassicalTransportLaws where
  famEq_sound : ∀ {types kind} {A B : Fam ClassicalSig types kind}
      (hA : Kinded A) (hB : Kinded B),
    FamEq ClassicalSig A B → ∀ env,
      denoteChecked hA env = denoteChecked hB env

end Nucleus.HolE
