import Mathlib.Tactic.Convert
import Nucleus.HolLN.Kernel

/-!
# Fixed infinite relational interpretation

Base types are interpreted by `Unit`, Booleans by `Bool`, `nat` by Lean's
infinite `Nat`, arrows by functions, and subtypes by their carrier.  The last
choice makes abstraction and representation total identities and validates
both subtype rules.  Evaluation is relational because `HasType` is deliberately
proof-irrelevant `Prop`; existence and uniqueness below recover a canonical
value without eliminating a typing proof into data.
-/

namespace Nucleus.HolLN

universe u

structure Pointed where
  carrier : Type
  point : carrier

def DenoteKind : Kind → Type 1
  | .star => Pointed
  | .arr domain codomain => DenoteKind domain → DenoteKind codomain

def defaultFamily : (kind : Kind) → DenoteKind kind
  | .star => ⟨Unit, ()⟩
  | .arr _ codomain => fun _ => defaultFamily codomain

def DenoteFam {Base : Type u} : {kind : Kind} → Fam Base kind → DenoteKind kind
  | kind, .base _ => defaultFamily kind
  | .star, .boolTy => ⟨Bool, false⟩
  | .star, .natTy => ⟨Nat, 0⟩
  | .star, .arr A B =>
      ⟨(DenoteFam A).carrier → (DenoteFam B).carrier, fun _ => (DenoteFam B).point⟩
  | codomain, .tyApp function argument => DenoteFam function (DenoteFam argument)
  | .star, .sub A _ => DenoteFam A

def DenoteHol {Base : Type u} : {sort : HolSort} → {depth : Nat} →
    Hol Base sort depth → Type
  | _, _, .boolTy => Bool
  | _, _, .natTy => Nat
  | _, _, .arr A B => DenoteHol A → DenoteHol B
  | _, _, .tyApp _ _ => Unit
  | _, _, .sub A _ => DenoteHol A
  | _, _, .base _ => Unit
  | _, _, .bv _ => Unit
  | _, _, .fv _ _ => Unit
  | _, _, .app _ _ => Unit
  | _, _, .lam _ _ => Unit
  | _, _, .bool _ => Unit
  | _, _, .zero => Unit
  | _, _, .succ _ => Unit
  | _, _, .eq _ _ _ => Unit
  | _, _, .eps _ _ => Unit
  | _, _, .abs _ _ _ => Unit
  | _, _, .rep _ _ _ => Unit

abbrev DenoteTy {Base : Type u} (A : Ty Base) : Type := DenoteHol A

@[simp] theorem denoteTy_nat {Base : Type u} :
    DenoteTy (.natTy : Ty Base) = Nat := rfl

def natZero {Base : Type u} : DenoteTy (.natTy : Ty Base) :=
  denoteTy_nat.symm ▸ (0 : Nat)

def natSucc {Base : Type u} (value : DenoteTy (.natTy : Ty Base)) :
    DenoteTy (.natTy : Ty Base) :=
  denoteTy_nat.symm ▸ ((denoteTy_nat ▸ value) + 1)

def defaultValue {Base : Type u} : (A : Ty Base) → DenoteTy A
  | .base _ => ()
  | .boolTy => false
  | .natTy => denoteTy_nat.symm ▸ (0 : Nat)
  | .arr _ B => fun _ => defaultValue B
  | .tyApp _ _ => ()
  | .sub A _ => defaultValue A

abbrev FreeEnv (Base : Type u) :=
  ∀ (_name : Nat) (A : Ty Base), DenoteTy A

abbrev BoundEnv {Base : Type u} {depth : Nat} (Γ : BoundCtx Base depth) :=
  ∀ (i : Fin depth) (A : Ty Base), Γ i = A -> DenoteTy A

def extendBoundEnv {Base : Type u} {depth : Nat} {Γ : BoundCtx Base depth}
    {A : Ty Base} (value : DenoteTy A) (environment : BoundEnv Γ) :
    BoundEnv (extendBound A Γ) :=
  fun i => Fin.cases
    (motive := fun j => ∀ A', extendBound A Γ j = A' -> DenoteTy A')
    (fun _ equality => equality ▸ value)
    (fun j A' equality => environment j A' equality) i

@[simp] theorem extendBoundEnv_zero {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} (value : DenoteTy A)
    (environment : BoundEnv Γ) :
    extendBoundEnv value environment (0 : Fin (depth + 1)) A rfl = value := rfl

@[simp] theorem extendBoundEnv_succ {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base} (value : DenoteTy A)
    (environment : BoundEnv Γ) (i : Fin depth) (lookup : Γ i = B) :
    extendBoundEnv value environment i.succ B lookup = environment i B lookup := rfl

noncomputable def chooseValue {Base : Type u} (A : Ty Base)
    (predicate : DenoteTy A -> Bool) : DenoteTy A := by
  classical
  exact if existsWitness : ∃ x, predicate x = true
    then Classical.choose existsWitness
    else defaultValue A

theorem chooseValue_spec {Base : Type u} {A : Ty Base}
    (predicate : DenoteTy A -> Bool) (witness : DenoteTy A)
    (holds : predicate witness = true) : predicate (chooseValue A predicate) = true := by
  classical
  simp only [chooseValue]
  split
  · exact Classical.choose_spec ‹_›
  · rename_i none
    exact False.elim (none ⟨witness, holds⟩)

theorem natSucc_injective {Base : Type u}
    {x y : DenoteTy (.natTy : Ty Base)} (equality : natSucc x = natSucc y) : x = y := by
  simpa [natSucc] using Nat.succ.inj equality

theorem natZero_ne_natSucc {Base : Type u} (x : DenoteTy (.natTy : Ty Base)) :
    natZero ≠ natSucc x := by
  simp [natZero, natSucc]

/-- The distinguished `ind` interpretation is genuinely infinite: successor
is injective and omits zero. -/
theorem infinite_ind_model {Base : Type u} :
    Function.Injective (@natSucc Base) ∧ ¬ Function.Surjective (@natSucc Base) := by
  constructor
  · intro x y equality
    exact natSucc_injective equality
  · intro surjective
    obtain ⟨x, equality⟩ := surjective (@natZero Base)
    exact natZero_ne_natSucc x equality.symm

inductive Eval {Base : Type u} :
    {depth : Nat} -> (Γ : BoundCtx Base depth) ->
    FreeEnv Base -> BoundEnv Γ ->
    (t : Tm Base depth) -> (A : Ty Base) -> DenoteTy A -> Prop where
  | bv {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base} {i : Fin depth}
      (freeEnv : FreeEnv Base) (boundEnv : BoundEnv Γ) (hA : Kinded A)
      (lookup : Γ i = A) :
      Eval Γ freeEnv boundEnv (.bv i) A (boundEnv i A lookup)
  | fv {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base} (name : Nat)
      (freeEnv : FreeEnv Base) (boundEnv : BoundEnv Γ)
      (hA : Kinded A) :
      Eval Γ freeEnv boundEnv (.fv name A) A (freeEnv name A)
  | app {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} {A B : Ty Base} {f x : Tm Base depth}
      {function : DenoteTy (.arr A B)} {argument : DenoteTy A} :
      Eval Γ freeEnv boundEnv f (.arr A B) function ->
      Eval Γ freeEnv boundEnv x A argument ->
      Eval Γ freeEnv boundEnv (.app f x) B (function argument)
  | lam {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} {A B : Ty Base} {body : Tm Base (depth + 1)}
      {function : DenoteTy (.arr A B)} :
      (hA : Kinded A) -> (∀ argument, Eval (extendBound A Γ) freeEnv
      (extendBoundEnv argument boundEnv) body B (function argument)) ->
      Eval Γ freeEnv boundEnv (.lam A body) (.arr A B) function
  | boolean {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} (literal : Bool) :
      Eval Γ freeEnv boundEnv (.bool literal) .boolTy literal
  | naturalZero {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} :
      Eval Γ freeEnv boundEnv .zero .natTy natZero
  | naturalSucc {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} {x : Tm Base depth}
      {value : DenoteTy (.natTy : Ty Base)} :
      Eval Γ freeEnv boundEnv x .natTy value ->
      Eval Γ freeEnv boundEnv (.succ x) .natTy (natSucc value)
  | eqTrue {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {x y : Tm Base depth}
      {left right : DenoteTy A}
      (hA : Kinded A) (hleft : Eval Γ freeEnv boundEnv x A left)
      (hright : Eval Γ freeEnv boundEnv y A right) (equal : left = right) :
      Eval Γ freeEnv boundEnv (.eq A x y) .boolTy true
  | eqFalse {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {x y : Tm Base depth}
      {left right : DenoteTy A}
      (hA : Kinded A) (hleft : Eval Γ freeEnv boundEnv x A left)
      (hright : Eval Γ freeEnv boundEnv y A right) (notEqual : left ≠ right) :
      Eval Γ freeEnv boundEnv (.eq A x y) .boolTy false
  | eps {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {p : Tm Base depth}
      {predicate : DenoteTy A -> Bool}
      (hA : Kinded A) (hp : Eval Γ freeEnv boundEnv p (.arr A .boolTy) predicate) :
      Eval Γ freeEnv boundEnv (.eps A p) A (chooseValue A predicate)
  | abs {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {p : Tm Base 1} {x : Tm Base depth}
      {value : DenoteTy A} (hA : Kinded A)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : Eval Γ freeEnv boundEnv x A value) :
      Eval Γ freeEnv boundEnv (.abs A p x) (.sub A p) value
  | rep {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {p : Tm Base 1} {x : Tm Base depth}
      {value : DenoteTy A} (hA : Kinded A)
      (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : Eval Γ freeEnv boundEnv x (.sub A p) value) :
      Eval Γ freeEnv boundEnv (.rep A p x) A value

theorem HasType.eval_exists {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base}
    (typing : HasType Γ t A) (freeEnv : FreeEnv Base) (boundEnv : BoundEnv Γ) :
    ∃ value, Eval Γ freeEnv boundEnv t A value := by
  classical
  cases typing with
  | tmBv hA lookup => exact ⟨_, .bv freeEnv boundEnv hA lookup⟩
  | tmFv name hA => exact ⟨_, .fv name freeEnv boundEnv hA⟩
  | tmApp hf hx =>
      obtain ⟨function, hfunction⟩ := HasType.eval_exists hf freeEnv boundEnv
      obtain ⟨argument, hargument⟩ := HasType.eval_exists hx freeEnv boundEnv
      exact ⟨function argument, .app hfunction hargument⟩
  | tmLam body hA bodyTyping =>
      let function := fun argument =>
        Classical.choose (HasType.eval_exists bodyTyping freeEnv
          (extendBoundEnv argument boundEnv))
      refine ⟨function, .lam hA ?_⟩
      intro argument
      exact Classical.choose_spec (HasType.eval_exists bodyTyping freeEnv
        (extendBoundEnv argument boundEnv))
  | tmBool literal => exact ⟨literal, .boolean literal⟩
  | tmZero => exact ⟨_, .naturalZero⟩
  | tmSucc valueTyping =>
      obtain ⟨value, hvalue⟩ := HasType.eval_exists valueTyping freeEnv boundEnv
      exact ⟨natSucc value, .naturalSucc hvalue⟩
  | tmEq hA hx hy =>
      obtain ⟨left, hleft⟩ := HasType.eval_exists hx freeEnv boundEnv
      obtain ⟨right, hright⟩ := HasType.eval_exists hy freeEnv boundEnv
      by_cases equal : left = right
      · exact ⟨true, .eqTrue hA hleft hright equal⟩
      · exact ⟨false, .eqFalse hA hleft hright equal⟩
  | tmEps hA hp =>
      obtain ⟨predicate, hpredicate⟩ := HasType.eval_exists hp freeEnv boundEnv
      exact ⟨chooseValue _ predicate, .eps hA hpredicate⟩
  | tmAbs hA hp hx =>
      obtain ⟨value, hvalue⟩ := HasType.eval_exists hx freeEnv boundEnv
      exact ⟨value, .abs hA hp hvalue⟩
  | tmRep hA hp hx =>
      obtain ⟨value, hvalue⟩ := HasType.eval_exists hx freeEnv boundEnv
      exact ⟨value, .rep hA hp hvalue⟩

noncomputable def HasType.value {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base}
    (typing : HasType Γ t A) (freeEnv : FreeEnv Base) (boundEnv : BoundEnv Γ) :
    DenoteTy A :=
  Classical.choose (HasType.eval_exists typing freeEnv boundEnv)

theorem HasType.value_spec {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base}
    (typing : HasType Γ t A) (freeEnv : FreeEnv Base) (boundEnv : BoundEnv Γ) :
    Eval Γ freeEnv boundEnv t A (typing.value freeEnv boundEnv) :=
  Classical.choose_spec (HasType.eval_exists typing freeEnv boundEnv)

theorem Eval.typing {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base} {boundEnv : BoundEnv Γ}
    {t : Tm Base depth} {A : Ty Base} {value : DenoteTy A}
    (evaluation : Eval Γ freeEnv boundEnv t A value) : HasType Γ t A := by
  induction evaluation with
  | bv _ _ hA lookup => exact .tmBv hA lookup
  | fv name _ _ hA => exact .tmFv name hA
  | app _ _ ihf ihx => exact .tmApp ihf ihx
  | lam hA _ ih => exact .tmLam _ hA (ih (defaultValue _))
  | boolean literal => exact .tmBool literal
  | naturalZero => exact .tmZero
  | naturalSucc _ ih => exact .tmSucc ih
  | eqTrue hA _ _ _ ihx ihy => exact .tmEq hA ihx ihy
  | eqFalse hA _ _ _ ihx ihy => exact .tmEq hA ihx ihy
  | eps hA _ ih => exact .tmEps hA ih
  | abs hA hp _ ih => exact .tmAbs hA hp ih
  | rep hA hp _ ih => exact .tmRep hA hp ih

set_option maxHeartbeats 1000000 in
-- Dependent elimination over two relational evaluations generates a large proof term.
set_option maxRecDepth 2000 in
/-- The relational interpretation is deterministic. -/
theorem Eval.unique {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base} {boundEnv : BoundEnv Γ}
    {t : Tm Base depth} {A : Ty Base} {firstValue secondValue : DenoteTy A}
    (first : Eval Γ freeEnv boundEnv t A firstValue)
    (second : Eval Γ freeEnv boundEnv t A secondValue) :
    firstValue = secondValue := by
  cases first with
  | bv => cases second; rfl
  | fv => cases second; rfl
  | app hfunction hargument =>
      cases second with
      | app hfunction' hargument' =>
          have typeEquality := hfunction.typing.unique hfunction'.typing
          cases typeEquality
          rw [hfunction.unique hfunction', hargument.unique hargument']
  | lam hA hbody =>
      cases second with
      | lam hA' hbody' =>
          funext argument
          exact (hbody argument).unique (hbody' argument)
  | boolean => cases second; rfl
  | naturalZero => cases second; rfl
  | naturalSucc hvalue =>
      cases second with
      | naturalSucc hvalue' => rw [hvalue.unique hvalue']
  | eqTrue hA hleft hright equal =>
      cases second with
      | eqTrue => rfl
      | eqFalse hA' hleft' hright' notEqual =>
          have typeEquality := hleft.typing.unique hleft'.typing
          cases typeEquality
          have hl := hleft.unique hleft'
          have hr := hright.unique hright'
          exact False.elim (notEqual (hl ▸ hr ▸ equal))
  | eqFalse hA hleft hright notEqual =>
      cases second with
      | eqTrue hA' hleft' hright' equal =>
          have typeEquality := hleft.typing.unique hleft'.typing
          cases typeEquality
          have hl := hleft.unique hleft'
          have hr := hright.unique hright'
          exact False.elim (notEqual (hl ▸ hr ▸ equal))
      | eqFalse => rfl
  | eps hA hp =>
      cases second with
      | eps hA' hp' =>
          have typeEquality := hp.typing.unique hp'.typing
          cases typeEquality
          rw [hp.unique hp']
  | abs hA hp hx =>
      cases second with
      | abs _ _ hx' => exact hx.unique hx'
  | rep hA hp hx =>
      cases second with
      | rep _ _ hx' => exact hx.unique hx'

theorem Eval.eq_value {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base} {boundEnv : BoundEnv Γ}
    {t : Tm Base depth} {A : Ty Base} {value : DenoteTy A}
    (evaluation : Eval Γ freeEnv boundEnv t A value)
    (typing : HasType Γ t A) :
    value = typing.value freeEnv boundEnv :=
  evaluation.unique (typing.value_spec freeEnv boundEnv)

theorem Eval.app_inv {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base} {boundEnv : BoundEnv Γ}
    {f x : Tm Base depth} {B : Ty Base} {value : DenoteTy B}
    (evaluation : Eval Γ freeEnv boundEnv (.app f x) B value) :
    ∃ (A : Ty Base) (function : DenoteTy (.arr A B)) (argument : DenoteTy A),
      Eval Γ freeEnv boundEnv f (.arr A B) function ∧
      Eval Γ freeEnv boundEnv x A argument ∧ value = function argument := by
  cases evaluation with
  | app hfunction hargument => exact ⟨_, _, _, hfunction, hargument, rfl⟩

theorem Eval.eq_true_inv {Base : Type u} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Base} {boundEnv : BoundEnv Γ}
    {A : Ty Base} {x y : Tm Base depth}
    (evaluation : Eval Γ freeEnv boundEnv (.eq A x y) .boolTy true) :
    ∃ (left right : DenoteTy A), Eval Γ freeEnv boundEnv x A left ∧
      Eval Γ freeEnv boundEnv y A right ∧ left = right := by
  cases evaluation with
  | eqTrue _ hleft hright equal => exact ⟨_, _, hleft, hright, equal⟩

def EnvRenaming {Base : Type u} {m n : Nat} {Γ : BoundCtx Base m}
    {Γ' : BoundCtx Base n} {ρ : Fin m -> Fin n}
    (relation : ContextRenaming Γ Γ' ρ) (source : BoundEnv Γ)
    (target : BoundEnv Γ') : Prop :=
  ∀ i A (lookup : Γ i = A),
    target (ρ i) A ((relation i).trans lookup) = source i A lookup

theorem liftRen_env {Base : Type u} {m n : Nat} {Γ : BoundCtx Base m}
    {Γ' : BoundCtx Base n} {ρ : Fin m -> Fin n}
    {source : BoundEnv Γ} {target : BoundEnv Γ'}
    (relation : ContextRenaming Γ Γ' ρ) (environments : EnvRenaming relation source target)
    {A : Ty Base} (argument : DenoteTy A) :
    EnvRenaming (liftRen_context relation A)
      (extendBoundEnv argument source) (extendBoundEnv argument target) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro B lookup
    cases lookup
    rfl
  · intro B lookup
    exact environments j B lookup

set_option maxRecDepth 2000 in
theorem Eval.rename {Base : Type u} {m : Nat}
    {Γ : BoundCtx Base m} {freeEnv : FreeEnv Base} {source : BoundEnv Γ}
    {t : Tm Base m} {A : Ty Base} {value : DenoteTy A}
    (evaluation : Eval Γ freeEnv source t A value) :
    ∀ {n : Nat} {Γ' : BoundCtx Base n} {ρ : Fin m -> Fin n}
      {target : BoundEnv Γ'},
      (relation : ContextRenaming Γ Γ' ρ) ->
      EnvRenaming relation source target ->
      Eval Γ' freeEnv target (Nucleus.HolLN.rename ρ t) A value := by
  induction evaluation with
  | bv sourceFree sourceBound hA lookup =>
      intro n Γ' ρ target relation environments
      rename_i i
      let lookup' := (relation i).trans lookup
      have values := environments i _ lookup
      simpa [Nucleus.HolLN.rename, values] using
        Eval.bv sourceFree target hA lookup'
  | fv name sourceFree sourceBound hA =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using Eval.fv name sourceFree target hA
  | app hfunction hargument ihfunction ihargument =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using
        Eval.app (ihfunction relation environments) (ihargument relation environments)
  | lam hA hbody ihbody =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using Eval.lam hA (fun argument =>
        ihbody argument (liftRen_context relation _)
          (liftRen_env relation environments argument))
  | boolean literal =>
      intro n Γ' ρ target relation environments
      simp only [Nucleus.HolLN.rename]
      exact .boolean literal
  | naturalZero =>
      intro n Γ' ρ target relation environments
      simp only [Nucleus.HolLN.rename]
      exact .naturalZero
  | naturalSucc hvalue ih =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using Eval.naturalSucc (ih relation environments)
  | eqTrue hA hleft hright equal ihleft ihright =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using
        Eval.eqTrue hA (ihleft relation environments) (ihright relation environments) equal
  | eqFalse hA hleft hright notEqual ihleft ihright =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using
        Eval.eqFalse hA (ihleft relation environments) (ihright relation environments) notEqual
  | eps hA hp ih =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using Eval.eps hA (ih relation environments)
  | abs hA hp hx ih =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using Eval.abs hA hp (ih relation environments)
  | rep hA hp hx ih =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using Eval.rep hA hp (ih relation environments)

def EnvSubstitution {Base : Type u} {m n : Nat}
    (sourceContext : BoundCtx Base m) (targetContext : BoundCtx Base n)
    (σ : Fin m -> Tm Base n) (freeEnv : FreeEnv Base)
    (sourceEnv : BoundEnv sourceContext) (targetEnv : BoundEnv targetContext) : Prop :=
  ∀ i, Kinded (sourceContext i) ->
    Eval targetContext freeEnv targetEnv (σ i) (sourceContext i)
    (sourceEnv i (sourceContext i) rfl)

theorem liftSub_env {Base : Type u} {m n : Nat}
    {sourceContext : BoundCtx Base m} {targetContext : BoundCtx Base n}
    {σ : Fin m -> Tm Base n} {freeEnv : FreeEnv Base}
    {sourceEnv : BoundEnv sourceContext} {targetEnv : BoundEnv targetContext}
    (environments : EnvSubstitution sourceContext targetContext σ freeEnv sourceEnv targetEnv)
    {A : Ty Base} (hA : Kinded A) (argument : DenoteTy A) :
    EnvSubstitution (extendBound A sourceContext) (extendBound A targetContext)
      (liftSub σ) freeEnv (extendBoundEnv argument sourceEnv)
      (extendBoundEnv argument targetEnv) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hi
    have evaluation := Eval.bv freeEnv
      (extendBoundEnv argument targetEnv) hA
      (show extendBound A targetContext 0 = A from rfl)
    convert evaluation using 1 <;> rfl
  · intro hi
    have renamed := (environments j hi).rename
        (Γ' := extendBound A targetContext) (ρ := Fin.succ)
        (target := extendBoundEnv argument targetEnv)
        (fun _ => rfl) (by
          intro k B lookup
          rfl)
    convert renamed using 1 <;> rfl

set_option maxHeartbeats 1000000 in
-- Substitution traverses typing and evaluation derivations simultaneously.
set_option maxRecDepth 2000 in
theorem HasType.eval_instantiate {Base : Type u} {m : Nat}
    {sourceContext : BoundCtx Base m} {freeEnv : FreeEnv Base}
    {sourceEnv : BoundEnv sourceContext} {t : Tm Base m} {A : Ty Base}
    (typing : HasType sourceContext t A) {value : DenoteTy A}
    (evaluation : Eval sourceContext freeEnv sourceEnv t A value) :
    ∀ {n : Nat} {targetContext : BoundCtx Base n} {σ : Fin m -> Tm Base n}
      {targetEnv : BoundEnv targetContext},
      EnvSubstitution sourceContext targetContext σ freeEnv sourceEnv targetEnv ->
      Eval targetContext freeEnv targetEnv (Nucleus.HolLN.instantiate σ t) A value := by
  cases typing with
  | tmBv hA lookup =>
      intro n targetContext σ targetEnv environments
      rename_i i
      cases evaluation
      have hi : Kinded (sourceContext i) := by rw [lookup]; exact hA
      have result := environments i hi
      cases lookup
      simpa [Nucleus.HolLN.instantiate] using result
  | tmFv name hA =>
      intro n targetContext σ targetEnv environments
      cases evaluation
      simpa [Nucleus.HolLN.instantiate] using
        Eval.fv name freeEnv targetEnv hA
  | tmApp hf hx =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | app hfunction hargument =>
          have typeEquality := HasType.unique hf hfunction.typing
          cases typeEquality
          simpa [Nucleus.HolLN.instantiate] using
          Eval.app (HasType.eval_instantiate hf hfunction environments)
            (HasType.eval_instantiate hx hargument environments)
  | tmLam body hA bodyTyping =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | lam _ hbody =>
          simpa [Nucleus.HolLN.instantiate] using Eval.lam hA (fun argument =>
            HasType.eval_instantiate bodyTyping (hbody argument)
              (liftSub_env environments hA argument))
  | tmBool literal =>
      intro n targetContext σ targetEnv environments
      cases evaluation
      simp only [Nucleus.HolLN.instantiate]
      exact .boolean literal
  | tmZero =>
      intro n targetContext σ targetEnv environments
      cases evaluation
      simp only [Nucleus.HolLN.instantiate]
      exact .naturalZero
  | tmSucc valueTyping =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | naturalSucc hvalue =>
          simp only [Nucleus.HolLN.instantiate]
          exact .naturalSucc (HasType.eval_instantiate valueTyping hvalue environments)
  | tmEq hA hx hy =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | eqTrue _ hleft hright equal =>
          have typeEquality := HasType.unique hx hleft.typing
          cases typeEquality
          simp only [Nucleus.HolLN.instantiate]
          exact .eqTrue hA (HasType.eval_instantiate hx hleft environments)
            (HasType.eval_instantiate hy hright environments) equal
      | eqFalse _ hleft hright notEqual =>
          have typeEquality := HasType.unique hx hleft.typing
          cases typeEquality
          simp only [Nucleus.HolLN.instantiate]
          exact .eqFalse hA (HasType.eval_instantiate hx hleft environments)
            (HasType.eval_instantiate hy hright environments) notEqual
  | tmEps hA hp =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | eps _ hpredicate =>
          have typeEquality := HasType.unique hp hpredicate.typing
          cases typeEquality
          simp only [Nucleus.HolLN.instantiate]
          exact .eps hA (HasType.eval_instantiate hp hpredicate environments)
  | tmAbs hA hp hx =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | abs _ _ hvalue =>
          simp only [Nucleus.HolLN.instantiate]
          exact .abs hA hp (HasType.eval_instantiate hx hvalue environments)
  | tmRep hA hp hx =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | rep _ _ hvalue =>
          simp only [Nucleus.HolLN.instantiate]
          exact .rep hA hp (HasType.eval_instantiate hx hvalue environments)

def defaultFreeEnv {Base : Type u} : FreeEnv Base :=
  fun _ A => defaultValue A

def emptyBoundEnv {Base : Type u} : BoundEnv (emptyBound : BoundCtx Base 0) := by
  intro i A lookup
  exact Fin.elim0 i

end Nucleus.HolLN
