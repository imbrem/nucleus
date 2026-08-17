import Nucleus.HolE.Kernel

/-! # Classical pointed semantics for unrestricted HolE -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

abbrev ClassicalSig : Signature := fun _ => Empty

instance : SigFamilyEquality ClassicalSig where
  Rule := fun _ _ => Empty

instance : SigTyping ClassicalSig where
  HasType symbol := nomatch symbol
  rename _ rule := nomatch rule
  instantiate _ rule := nomatch rule

structure CPointed where
  carrier : Type
  point : carrier

def CDenoteKind : Kind → Type 1
  | .star => CPointed
  | .arr domain codomain => CDenoteKind domain → CDenoteKind codomain

abbrev CTypeEnv (types : List Kind) :=
  (kind : Kind) → TyVar types kind → CDenoteKind kind

def extendCTypeEnv (value : CDenoteKind kind) (environment : CTypeEnv types) :
    CTypeEnv (kind :: types)
  | _, .zero => value
  | kind, .succ v => environment kind v

def emptyCTypeEnv : CTypeEnv ([] : List Kind) := fun _ v => nomatch v

def cBool : CPointed := ⟨Bool, false⟩

abbrev CBoundEnv (depth : Nat) :=
  ∀ (_index : Fin depth) (semantic : CPointed), semantic.carrier

def emptyCBoundEnv : CBoundEnv 0 := fun index => Fin.elim0 index

noncomputable def extendCBoundEnv (semantic : CPointed) (value : semantic.carrier)
    (environment : CBoundEnv depth) : CBoundEnv (depth + 1) := by
  classical
  intro index target
  refine Fin.cases ?_ (fun i => environment i target) index
  exact if equal : target = semantic then cast (by cases equal; rfl) value else target.point

noncomputable def alignCValue (source target : CPointed) (value : source.carrier) :
    target.carrier := by
  classical
  exact if equal : source = target then cast (by cases equal; rfl) value else target.point

@[simp] theorem alignCValue_self (semantic : CPointed) (value : semantic.carrier) :
    alignCValue semantic semantic value = value := by
  simp [alignCValue]

theorem alignCValue_of_eq {source target : CPointed} (equal : source = target)
    (value : source.carrier) :
    alignCValue source target value = cast (congrArg CPointed.carrier equal) value := by
  subst target
  simp

def CGuarded {A : Type} (predicate : A → Bool) (value : A) : Prop :=
  predicate value = true ∨ ¬ ∃ witness, predicate witness = true

noncomputable def cGuardedPoint {A : Type} (point : A) (predicate : A → Bool) :
    {value // CGuarded predicate value} := by
  classical
  by_cases witness : ∃ value, predicate value = true
  · exact ⟨Classical.choose witness, Or.inl (Classical.choose_spec witness)⟩
  · exact ⟨point, Or.inr witness⟩

noncomputable def cGuardedType (carrier : CPointed)
    (predicate : carrier.carrier → Bool) : CPointed :=
  ⟨{value // CGuarded predicate value}, cGuardedPoint carrier.point predicate⟩

noncomputable def cGuardedAbs (carrier : CPointed)
    (predicate : carrier.carrier → Bool) (value : carrier.carrier) :
    (cGuardedType carrier predicate).carrier := by
  classical
  by_cases valid : CGuarded predicate value
  · exact ⟨value, valid⟩
  · exact (cGuardedType carrier predicate).point

theorem cGuardedAbs_value (carrier : CPointed) (predicate : carrier.carrier → Bool)
    (value : carrier.carrier) (valid : CGuarded predicate value) :
    (cGuardedAbs carrier predicate value).1 = value := by
  classical
  simp [cGuardedAbs, valid]

theorem cGuardedAbs_rep (carrier : CPointed) (predicate : carrier.carrier → Bool)
    (value : (cGuardedType carrier predicate).carrier) :
    cGuardedAbs carrier predicate value.1 = value := by
  apply Subtype.ext
  exact cGuardedAbs_value carrier predicate value.1 value.2

theorem cGuarded_rep_abs_of_true (carrier : CPointed)
    (predicate : carrier.carrier → Bool) (value : carrier.carrier)
    (holds : predicate value = true) :
    (cGuardedAbs carrier predicate value).1 = value :=
  cGuardedAbs_value carrier predicate value (Or.inl holds)

theorem cGuarded_rep_pred_of_witness (carrier : CPointed)
    (predicate : carrier.carrier → Bool)
    (witness : carrier.carrier) (witnessHolds : predicate witness = true)
    (value : (cGuardedType carrier predicate).carrier) :
    predicate value.1 = true := by
  rcases value.2 with holds | empty
  · exact holds
  · exact False.elim (empty ⟨witness, witnessHolds⟩)

noncomputable def chooseCModel (satisfies : CPointed → Prop) : CPointed := by
  classical
  exact if witness : ∃ candidate, satisfies candidate then Classical.choose witness else cBool

theorem chooseCModel_spec (satisfies : CPointed → Prop)
    (witness : CPointed) (holds : satisfies witness) :
    satisfies (chooseCModel satisfies) := by
  classical
  simp only [chooseCModel]
  split
  · exact Classical.choose_spec ‹∃ candidate, satisfies candidate›
  · exfalso
    exact ‹¬ ∃ candidate, satisfies candidate› ⟨witness, holds⟩

/-- A proof-relevant mirror of the public, proof-irrelevant checking judgment.
The extra kinding fields on `app` and `lam` make semantic recursion manifestly
structural. -/
inductive CChecks : {types : List Kind} → {sort : HolSort} → {depth : Nat} →
    BoundCtx ClassicalSig types depth → Expr ClassicalSig types sort depth →
    Classification ClassicalSig types sort → Type 1 where
  | boolTy : CChecks emptyBound .boolTy .kind
  | arr : CChecks emptyBound A .kind → CChecks emptyBound B .kind →
      CChecks emptyBound (.arr A B) .kind
  | tyApp : CChecks emptyBound F .kind → CChecks emptyBound A .kind →
      CChecks emptyBound (.tyApp F A) .kind
  | tyLam : CChecks (types := kind :: types) emptyBound body .kind →
      CChecks (types := types) emptyBound (.tyLam body) .kind
  | tyBv (v : TyVar types kind) : CChecks emptyBound (.tyBv v) .kind
  | sub : CChecks emptyBound A .kind →
      CChecks (extendBound A emptyBound) predicate (.tm .boolTy) →
      CChecks emptyBound (.sub A predicate) .kind
  | model : CChecks (types := .star :: types) emptyBound predicate (.tm .boolTy) →
      CChecks (types := types) emptyBound (.model predicate) .kind
  | primFam (symbol : ClassicalSig (.kind kind)) :
      CChecks emptyBound (.primFam symbol) .kind
  | primTm (rule : SigTyping.HasType symbol A) : CChecks Γ (.primTm symbol) (.tm A)
  | bv (hA : CChecks emptyBound A .kind) (lookup : Γ index = A) :
      CChecks Γ (.bv index) (.tm A)
  | fv (name : Nat) (hA : CChecks emptyBound A .kind) :
      CChecks Γ (.fv name A) (.tm A)
  | app (hA : CChecks emptyBound A .kind) (hB : CChecks emptyBound B .kind) :
      CChecks Γ function (.tm (.arr A B)) → CChecks Γ argument (.tm A) →
      CChecks Γ (.app function argument) (.tm B)
  | lam (body : Tm ClassicalSig types (depth + 1))
      (hA : CChecks emptyBound A .kind) (hB : CChecks emptyBound B .kind) :
      CChecks (extendBound A Γ) body (.tm B) →
      CChecks Γ (.lam A body) (.tm (.arr A B))
  | bool (value : Bool) : CChecks Γ (.bool value) (.tm .boolTy)
  | eq (hA : CChecks emptyBound A .kind) : CChecks Γ left (.tm A) →
      CChecks Γ right (.tm A) → CChecks Γ (.eq A left right) (.tm .boolTy)
  | eps (hA : CChecks emptyBound A .kind) :
      CChecks Γ predicate (.tm (.arr A .boolTy)) →
      CChecks Γ (.eps A predicate) (.tm A)
  | abs (hA : CChecks emptyBound A .kind)
      (hp : CChecks (extendBound A emptyBound) predicate (.tm .boolTy)) :
      CChecks Γ value (.tm A) → CChecks Γ (.abs A predicate value) (.tm (.sub A predicate))
  | rep (hA : CChecks emptyBound A .kind)
      (hp : CChecks (extendBound A emptyBound) predicate (.tm .boolTy)) :
      CChecks Γ value (.tm (.sub A predicate)) →
      CChecks Γ (.rep A predicate value) (.tm A)
  | tyExists : CChecks (types := .star :: types) emptyBound predicate (.tm .boolTy) →
      CChecks (types := types) Γ (.tyExists predicate) (.tm .boolTy)

abbrev CKinded (A : Fam ClassicalSig types kind) := CChecks emptyBound A .kind
abbrev CHasType (Γ : BoundCtx ClassicalSig types depth)
    (term : Tm ClassicalSig types depth) (A : Ty ClassicalSig types) :=
  CChecks Γ term (.tm A)

def CChecks.typeKinded : CHasType Γ term A → CKinded A
  | .primTm rule => nomatch rule
  | .bv hA _ | .fv _ hA => hA
  | .app _ hB _ _ => hB
  | .lam _ hA hB _ => .arr hA hB
  | .bool _ | .eq _ _ _ | .tyExists _ => .boolTy
  | .eps hA _ | .rep hA _ _ => hA
  | .abs hA hp _ => .sub hA hp

theorem CChecks.classification_unique {types : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {expression : Expr ClassicalSig types sort depth}
    {leftClass rightClass : Classification ClassicalSig types sort}
    (left : CChecks Γ expression leftClass)
    (right : CChecks Γ expression rightClass) : leftClass = rightClass := by
  induction left <;> cases right <;> simp_all
  case primTm.primTm ruleLeft ruleRight => exact nomatch ruleLeft
  case app.app hA1 hB1 lf lx ihA ihB ihf ihx A2 hA2 rx hB2 rf =>
    have equal := ihB hB2
    injection equal with typeEqual
    injection typeEqual
  case lam.lam hA1 hB1 body1 ihA ihB ihBody B2 hB2 hA2 body2 =>
    have equal := ihBody body2
    injection equal

theorem CChecks.type_unique {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A B : Ty ClassicalSig types} (left : CHasType Γ term A)
    (right : CHasType Γ term B) : A = B := by
  have equal := left.classification_unique right
  cases equal
  rfl

theorem Checks.typeKinded {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} : HasType Γ term A → Kinded A
  | .primTm rule => nomatch rule
  | .bv hA _ | .fv _ hA => hA
  | .app hf _ => by
      cases hf.typeKinded with
      | arr _ hB => exact hB
  | .lam _ hA hb => .arr hA hb.typeKinded
  | .bool _ | .eq _ _ _ | .tyExists _ => .boolTy
  | .eps hA _ | .rep hA _ _ => hA
  | .abs hA hp _ => .sub hA hp

theorem Checks.toC {types : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {expression : Expr ClassicalSig types sort depth}
    {classification : Classification ClassicalSig types sort}
    (checking : Checks Γ expression classification) :
    Nonempty (CChecks Γ expression classification) := by
  induction checking with
  | boolTy => exact ⟨.boolTy⟩
  | arr hA hB ihA ihB =>
      obtain ⟨cA⟩ := ihA
      obtain ⟨cB⟩ := ihB
      exact ⟨.arr cA cB⟩
  | tyApp hF hA ihF ihA =>
      obtain ⟨cF⟩ := ihF
      obtain ⟨cA⟩ := ihA
      exact ⟨.tyApp cF cA⟩
  | tyLam hbody ih =>
      obtain ⟨body⟩ := ih
      exact ⟨.tyLam body⟩
  | tyBv v => exact ⟨.tyBv v⟩
  | sub hA hp ihA ihp =>
      obtain ⟨cA⟩ := ihA
      obtain ⟨cp⟩ := ihp
      exact ⟨.sub cA cp⟩
  | model hp ih =>
      obtain ⟨cp⟩ := ih
      exact ⟨.model cp⟩
  | primFam symbol => exact nomatch symbol
  | primTm rule => exact nomatch rule
  | bv hA lookup ihA =>
      obtain ⟨cA⟩ := ihA
      exact ⟨.bv cA lookup⟩
  | fv name hA ihA =>
      obtain ⟨cA⟩ := ihA
      exact ⟨.fv name cA⟩
  | app hf hx ihf ihx =>
      obtain ⟨cf⟩ := ihf
      obtain ⟨cx⟩ := ihx
      cases cf.typeKinded with
      | arr cA cB => exact ⟨.app cA cB cf cx⟩
  | lam body hA hb ihA ihb =>
      obtain ⟨cA⟩ := ihA
      obtain ⟨cb⟩ := ihb
      exact ⟨.lam body cA cb.typeKinded cb⟩
  | bool literal => exact ⟨.bool literal⟩
  | eq hA hx hy ihA ihx ihy =>
      obtain ⟨cA⟩ := ihA
      obtain ⟨cx⟩ := ihx
      obtain ⟨cy⟩ := ihy
      exact ⟨.eq cA cx cy⟩
  | eps hA hp ihA ihp =>
      obtain ⟨cA⟩ := ihA
      obtain ⟨cp⟩ := ihp
      exact ⟨.eps cA cp⟩
  | abs hA hp hx ihA ihp ihx =>
      obtain ⟨cA⟩ := ihA
      obtain ⟨cp⟩ := ihp
      obtain ⟨cx⟩ := ihx
      exact ⟨.abs cA cp cx⟩
  | rep hA hp hx ihA ihp ihx =>
      obtain ⟨cA⟩ := ihA
      obtain ⟨cp⟩ := ihp
      obtain ⟨cx⟩ := ihx
      exact ⟨.rep cA cp cx⟩
  | tyExists hp ih =>
      obtain ⟨cp⟩ := ih
      exact ⟨.tyExists cp⟩

noncomputable def Checks.certificate {types : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {expression : Expr ClassicalSig types sort depth}
    {classification : Classification ClassicalSig types sort}
    (checking : Checks Γ expression classification) :
    CChecks Γ expression classification :=
  Classical.choice checking.toC

abbrev CResult {types : List Kind} {sort : HolSort} {depth : Nat}
    (classification : Classification ClassicalSig types sort) : Type 1 :=
  match classification with
  | @Classification.kind _ _ kind => CDenoteKind kind
  | .tm _ => CBoundEnv depth → (expected : CPointed) → ULift.{1, 0} expected.carrier

noncomputable def cSem {types : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {expression : Expr ClassicalSig types sort depth}
    {classification : Classification ClassicalSig types sort}
    (checking : CChecks Γ expression classification) :
    CTypeEnv types → CResult (depth := depth) classification := by
  classical
  exact match checking with
  | .boolTy => fun _ => cBool
  | .arr hA hB => fun env =>
      let domain := cSem hA env; let codomain := cSem hB env
      ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
  | .tyApp hF hA => fun env => cSem hF env (cSem hA env)
  | .tyLam body => fun env argument => cSem body (extendCTypeEnv argument env)
  | .tyBv v => fun env => env _ v
  | .sub hA hp => fun env =>
      let carrier := cSem hA env
      let pred := fun value =>
        (cSem hp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      cGuardedType carrier pred
  | .model hp => fun env =>
      let sat := fun candidate : CPointed =>
        cSem hp (extendCTypeEnv (kind := .star) candidate env)
          emptyCBoundEnv cBool = ⟨true⟩
      chooseCModel sat
  | .primFam symbol => nomatch symbol
  | .primTm rule => nomatch rule
  | @CChecks.bv _ _ _ _ index hA lookup =>
      fun _ bound expected => ⟨bound index expected⟩
  | .fv name hA => fun _ _ expected => ⟨expected.point⟩
  | .app hA hB hf hx => fun env bound expected =>
      let domain := cSem hA env; let codomain := cSem hB env
      let functionType : CPointed :=
        ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
      ⟨alignCValue codomain expected
        ((cSem hf env bound functionType).down (cSem hx env bound domain).down)⟩
  | .lam body hA hB hb => fun env bound expected =>
      let domain := cSem hA env; let codomain := cSem hB env
      let functionType : CPointed :=
        ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
      let function := fun argument =>
        (cSem hb env (extendCBoundEnv domain argument bound) codomain).down
      ⟨alignCValue functionType expected function⟩
  | .bool literal => fun _ _ expected => ⟨alignCValue cBool expected literal⟩
  | .eq hA hx hy => fun env bound expected =>
      let carrier := cSem hA env
      ⟨alignCValue cBool expected
        (decide ((cSem hx env bound carrier).down = (cSem hy env bound carrier).down))⟩
  | .eps hA hp => fun env bound expected =>
      let carrier := cSem hA env
      let functionType : CPointed := ⟨carrier.carrier → Bool, fun _ => false⟩
      let predicate := (cSem hp env bound functionType).down
      let selected := if witness : ∃ value, predicate value = true then
        Classical.choose witness else carrier.point
      ⟨alignCValue carrier expected selected⟩
  | .abs hA hp hx => fun env bound expected =>
      let carrier := cSem hA env
      let predicate := fun value =>
        (cSem hp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      let subtype := cGuardedType carrier predicate
      ⟨alignCValue subtype expected
        (cGuardedAbs carrier predicate (cSem hx env bound carrier).down)⟩
  | .rep hA hp hx => fun env bound expected =>
      let carrier := cSem hA env
      let predicate := fun value =>
        (cSem hp env (extendCBoundEnv carrier value emptyCBoundEnv) cBool).down
      let subtype := cGuardedType carrier predicate
      ⟨alignCValue carrier expected (cSem hx env bound subtype).down.1⟩
  | .tyExists hp => fun env _ expected =>
      ⟨alignCValue cBool expected (decide (∃ candidate : CPointed,
        cSem hp (extendCTypeEnv (kind := .star) candidate env)
          emptyCBoundEnv cBool = ⟨true⟩))⟩

noncomputable def cDenoteFam {types : List Kind} {kind : Kind}
    {A : Fam ClassicalSig types kind} (env : CTypeEnv types) (checking : CKinded A) :
    CDenoteKind kind := cSem checking env

noncomputable def cEval {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (env : CTypeEnv types) (bound : CBoundEnv depth)
    (typing : CHasType Γ term A) (expected : CPointed) : ULift.{1, 0} expected.carrier :=
  cSem typing env bound expected

theorem CChecks.unique {types : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {expression : Expr ClassicalSig types sort depth}
    {classification : Classification ClassicalSig types sort}
    (left right : CChecks Γ expression classification) : left = right := by
  induction left <;> cases right
  case app.app hA₁ hB₁ hf₁ hx₁ ihA ihB ihf ihx A₂ hA₂ hx₂ hB₂ hf₂ =>
    have typeEqual := hx₁.type_unique hx₂
    subst A₂
    congr 1 <;> apply_assumption
  all_goals try rfl
  all_goals congr 1 <;> apply_assumption

theorem cSem_certificate_coherent {types : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {expression : Expr ClassicalSig types sort depth}
    {classification : Classification ClassicalSig types sort}
    (left right : CChecks Γ expression classification) (env : CTypeEnv types) :
    cSem left env = cSem right env := by
  rw [left.unique right]

/-- Proof-irrelevant denotation of a well-kinded family.  The public API takes
the ordinary `Prop`-valued checking judgment; `CChecks` remains an internal
recursion device. -/
noncomputable def denoteChecked {types : List Kind} {kind : Kind}
    {family : Fam ClassicalSig types kind} (checking : Kinded family)
    (env : CTypeEnv types) : CDenoteKind kind :=
  cSem checking.certificate env

/-- Evaluation of a syntax-directed typing derivation at its own denoted type. -/
noncomputable def evalChecked {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {term : Tm ClassicalSig types depth}
    {A : Ty ClassicalSig types} (typing : HasType Γ term A)
    (env : CTypeEnv types) (bound : CBoundEnv depth) :
    (denoteChecked typing.typeKinded env).carrier :=
  (cSem typing.certificate env bound (denoteChecked typing.typeKinded env)).down

/-- Closed Boolean truth under the deterministic classical interpretation. -/
def CTrue {term : Tm ClassicalSig [] 0} (typing : HasType emptyBound term .boolTy) : Prop :=
  (cSem typing.certificate emptyCTypeEnv emptyCBoundEnv cBool).down = true

end Nucleus.HolE
