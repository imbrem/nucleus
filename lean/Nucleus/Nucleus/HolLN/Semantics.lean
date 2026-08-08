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

def DenoteHol {Base : Type u} : {sort : HolSort} -> {depth : Nat} ->
    Hol Base sort depth -> Type
  | _, _, .base _ => Unit
  | _, _, .boolTy => Bool
  | _, _, .natTy => Nat
  | _, _, .arr A B => DenoteHol A -> DenoteHol B
  | _, _, .sub A _ => DenoteHol A
  | _, _, .bound _ => Unit
  | _, _, .free _ => Unit
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

def defaultValue {Base : Type u} : (A : Ty Base) -> DenoteTy A
  | .base _ => by change Unit; exact ()
  | .boolTy => by change Bool; exact false
  | .natTy => by change Nat; exact 0
  | .arr _ B => by change DenoteTy _ -> DenoteTy B; exact fun _ => defaultValue B
  | .sub A _ => by change DenoteTy A; exact defaultValue A

abbrev FreeEnv {Base : Type u} (Δ : FreeCtx Base) :=
  ∀ (name : Nat) (A : Ty Base), Δ name = some A -> DenoteTy A

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

inductive Eval {Base : Type u} (Δ : FreeCtx Base) :
    {depth : Nat} -> (Γ : BoundCtx Base depth) ->
    FreeEnv Δ -> BoundEnv Γ ->
    (t : Tm Base depth) -> (A : Ty Base) -> DenoteTy A -> Prop where
  | bound {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base} {i : Fin depth}
      (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ) (hA : Kinded A)
      (lookup : Γ i = A) :
      Eval Δ Γ freeEnv boundEnv (.bound i) A (boundEnv i A lookup)
  | free {depth : Nat} {Γ : BoundCtx Base depth} {A : Ty Base} (name : Nat)
      (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ)
      (hA : Kinded A) (lookup : Δ name = some A) :
      Eval Δ Γ freeEnv boundEnv (.free name) A (freeEnv name A lookup)
  | app {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} {A B : Ty Base} {f x : Tm Base depth}
      {function : DenoteTy (.arr A B)} {argument : DenoteTy A} :
      Eval Δ Γ freeEnv boundEnv f (.arr A B) function ->
      Eval Δ Γ freeEnv boundEnv x A argument ->
      Eval Δ Γ freeEnv boundEnv (.app f x) B (function argument)
  | lam {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} {A B : Ty Base} {body : Tm Base (depth + 1)}
      {function : DenoteTy (.arr A B)} :
      (hA : Kinded A) -> (∀ argument, Eval Δ (extendBound A Γ) freeEnv
      (extendBoundEnv argument boundEnv) body B (function argument)) ->
      Eval Δ Γ freeEnv boundEnv (.lam A body) (.arr A B) function
  | boolean {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} (literal : Bool) :
      Eval Δ Γ freeEnv boundEnv (.bool literal) .boolTy literal
  | naturalZero {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} :
      Eval Δ Γ freeEnv boundEnv .zero .natTy natZero
  | naturalSucc {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} {x : Tm Base depth}
      {value : DenoteTy (.natTy : Ty Base)} :
      Eval Δ Γ freeEnv boundEnv x .natTy value ->
      Eval Δ Γ freeEnv boundEnv (.succ x) .natTy (natSucc value)
  | eqTrue {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {x y : Tm Base depth}
      {left right : DenoteTy A}
      (hA : Kinded A) (hleft : Eval Δ Γ freeEnv boundEnv x A left)
      (hright : Eval Δ Γ freeEnv boundEnv y A right) (equal : left = right) :
      Eval Δ Γ freeEnv boundEnv (.eq A x y) .boolTy true
  | eqFalse {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {x y : Tm Base depth}
      {left right : DenoteTy A}
      (hA : Kinded A) (hleft : Eval Δ Γ freeEnv boundEnv x A left)
      (hright : Eval Δ Γ freeEnv boundEnv y A right) (notEqual : left ≠ right) :
      Eval Δ Γ freeEnv boundEnv (.eq A x y) .boolTy false
  | eps {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {p : Tm Base depth}
      {predicate : DenoteTy A -> Bool}
      (hA : Kinded A) (hp : Eval Δ Γ freeEnv boundEnv p (.arr A .boolTy) predicate) :
      Eval Δ Γ freeEnv boundEnv (.eps A p) A (chooseValue A predicate)
  | abs {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {p : Tm Base 1} {x : Tm Base depth}
      {value : DenoteTy A} (hA : Kinded A)
      (hp : HasType emptyContext (extendBound A emptyBound) p .boolTy)
      (hx : Eval Δ Γ freeEnv boundEnv x A value) :
      Eval Δ Γ freeEnv boundEnv (.abs A p x) (.sub A p) value
  | rep {depth : Nat} {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ}
      {boundEnv : BoundEnv Γ} {A : Ty Base} {p : Tm Base 1} {x : Tm Base depth}
      {value : DenoteTy A} (hA : Kinded A)
      (hp : HasType emptyContext (extendBound A emptyBound) p .boolTy)
      (hx : Eval Δ Γ freeEnv boundEnv x (.sub A p) value) :
      Eval Δ Γ freeEnv boundEnv (.rep A p x) A value

theorem HasType.eval_exists {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base}
    (typing : HasType Δ Γ t A) (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ) :
    ∃ value, Eval Δ Γ freeEnv boundEnv t A value := by
  classical
  cases typing with
  | bound hA lookup => exact ⟨_, .bound freeEnv boundEnv hA lookup⟩
  | free name hA lookup => exact ⟨_, .free name freeEnv boundEnv hA lookup⟩
  | app hf hx =>
      obtain ⟨function, hfunction⟩ := hf.eval_exists freeEnv boundEnv
      obtain ⟨argument, hargument⟩ := hx.eval_exists freeEnv boundEnv
      exact ⟨function argument, .app hfunction hargument⟩
  | lam body hA bodyTyping =>
      let function := fun argument =>
        Classical.choose (bodyTyping.eval_exists freeEnv
          (extendBoundEnv argument boundEnv))
      refine ⟨function, .lam hA ?_⟩
      intro argument
      exact Classical.choose_spec (bodyTyping.eval_exists freeEnv
        (extendBoundEnv argument boundEnv))
  | bool literal => exact ⟨literal, .boolean literal⟩
  | zero => exact ⟨_, .naturalZero⟩
  | succ valueTyping =>
      obtain ⟨value, hvalue⟩ := valueTyping.eval_exists freeEnv boundEnv
      exact ⟨natSucc value, .naturalSucc hvalue⟩
  | eq hA hx hy =>
      obtain ⟨left, hleft⟩ := hx.eval_exists freeEnv boundEnv
      obtain ⟨right, hright⟩ := hy.eval_exists freeEnv boundEnv
      by_cases equal : left = right
      · exact ⟨true, .eqTrue hA hleft hright equal⟩
      · exact ⟨false, .eqFalse hA hleft hright equal⟩
  | eps hA hp =>
      obtain ⟨predicate, hpredicate⟩ := hp.eval_exists freeEnv boundEnv
      exact ⟨chooseValue _ predicate, .eps hA hpredicate⟩
  | abs hA hp hx =>
      obtain ⟨value, hvalue⟩ := hx.eval_exists freeEnv boundEnv
      exact ⟨value, .abs hA hp hvalue⟩
  | rep hA hp hx =>
      obtain ⟨value, hvalue⟩ := hx.eval_exists freeEnv boundEnv
      exact ⟨value, .rep hA hp hvalue⟩

noncomputable def HasType.value {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base}
    (typing : HasType Δ Γ t A) (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ) :
    DenoteTy A :=
  Classical.choose (typing.eval_exists freeEnv boundEnv)

theorem HasType.value_spec {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t : Tm Base depth} {A : Ty Base}
    (typing : HasType Δ Γ t A) (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ) :
    Eval Δ Γ freeEnv boundEnv t A (typing.value freeEnv boundEnv) :=
  Classical.choose_spec (typing.eval_exists freeEnv boundEnv)

theorem Eval.typing {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ} {boundEnv : BoundEnv Γ}
    {t : Tm Base depth} {A : Ty Base} {value : DenoteTy A}
    (evaluation : Eval Δ Γ freeEnv boundEnv t A value) : HasType Δ Γ t A := by
  induction evaluation with
  | bound _ _ hA lookup => exact .bound hA lookup
  | free name _ _ hA lookup => exact .free name hA lookup
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam hA _ ih => exact .lam _ hA (ih (defaultValue _))
  | boolean literal => exact .bool literal
  | naturalZero => exact .zero
  | naturalSucc _ ih => exact .succ ih
  | eqTrue hA _ _ _ ihx ihy => exact .eq hA ihx ihy
  | eqFalse hA _ _ _ ihx ihy => exact .eq hA ihx ihy
  | eps hA _ ih => exact .eps hA ih
  | abs hA hp _ ih => exact .abs hA hp ih
  | rep hA hp _ ih => exact .rep hA hp ih

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
/-- The relational interpretation is deterministic. -/
theorem Eval.unique {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ} {boundEnv : BoundEnv Γ}
    {t : Tm Base depth} {A : Ty Base} {firstValue secondValue : DenoteTy A}
    (first : Eval Δ Γ freeEnv boundEnv t A firstValue)
    (second : Eval Δ Γ freeEnv boundEnv t A secondValue) :
    firstValue = secondValue := by
  cases first with
  | bound => cases second; rfl
  | free => cases second; rfl
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

theorem Eval.eq_value {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ} {boundEnv : BoundEnv Γ}
    {t : Tm Base depth} {A : Ty Base} {value : DenoteTy A}
    (evaluation : Eval Δ Γ freeEnv boundEnv t A value)
    (typing : HasType Δ Γ t A) :
    value = typing.value freeEnv boundEnv :=
  evaluation.unique (typing.value_spec freeEnv boundEnv)

theorem Eval.app_inv {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ} {boundEnv : BoundEnv Γ}
    {f x : Tm Base depth} {B : Ty Base} {value : DenoteTy B}
    (evaluation : Eval Δ Γ freeEnv boundEnv (.app f x) B value) :
    ∃ (A : Ty Base) (function : DenoteTy (.arr A B)) (argument : DenoteTy A),
      Eval Δ Γ freeEnv boundEnv f (.arr A B) function ∧
      Eval Δ Γ freeEnv boundEnv x A argument ∧ value = function argument := by
  cases evaluation with
  | app hfunction hargument => exact ⟨_, _, _, hfunction, hargument, rfl⟩

theorem Eval.eq_true_inv {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {freeEnv : FreeEnv Δ} {boundEnv : BoundEnv Γ}
    {A : Ty Base} {x y : Tm Base depth}
    (evaluation : Eval Δ Γ freeEnv boundEnv (.eq A x y) .boolTy true) :
    ∃ (left right : DenoteTy A), Eval Δ Γ freeEnv boundEnv x A left ∧
      Eval Δ Γ freeEnv boundEnv y A right ∧ left = right := by
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
theorem Eval.rename {Base : Type u} {Δ : FreeCtx Base} {m : Nat}
    {Γ : BoundCtx Base m} {freeEnv : FreeEnv Δ} {source : BoundEnv Γ}
    {t : Tm Base m} {A : Ty Base} {value : DenoteTy A}
    (evaluation : Eval Δ Γ freeEnv source t A value) :
    ∀ {n : Nat} {Γ' : BoundCtx Base n} {ρ : Fin m -> Fin n}
      {target : BoundEnv Γ'},
      (relation : ContextRenaming Γ Γ' ρ) ->
      EnvRenaming relation source target ->
      Eval Δ Γ' freeEnv target (Nucleus.HolLN.rename ρ t) A value := by
  induction evaluation with
  | bound sourceFree sourceBound hA lookup =>
      intro n Γ' ρ target relation environments
      rename_i i
      let lookup' := (relation i).trans lookup
      have values := environments i _ lookup
      simpa [Nucleus.HolLN.rename, values] using
        Eval.bound (Δ := Δ) sourceFree target hA lookup'
  | free name sourceFree sourceBound hA lookup =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.HolLN.rename] using Eval.free name sourceFree target hA lookup
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

def EnvSubstitution {Base : Type u} {Δ : FreeCtx Base} {m n : Nat}
    (sourceContext : BoundCtx Base m) (targetContext : BoundCtx Base n)
    (σ : Fin m -> Tm Base n) (freeEnv : FreeEnv Δ)
    (sourceEnv : BoundEnv sourceContext) (targetEnv : BoundEnv targetContext) : Prop :=
  ∀ i, Kinded (sourceContext i) ->
    Eval Δ targetContext freeEnv targetEnv (σ i) (sourceContext i)
    (sourceEnv i (sourceContext i) rfl)

theorem liftSub_env {Base : Type u} {Δ : FreeCtx Base} {m n : Nat}
    {sourceContext : BoundCtx Base m} {targetContext : BoundCtx Base n}
    {σ : Fin m -> Tm Base n} {freeEnv : FreeEnv Δ}
    {sourceEnv : BoundEnv sourceContext} {targetEnv : BoundEnv targetContext}
    (environments : EnvSubstitution sourceContext targetContext σ freeEnv sourceEnv targetEnv)
    {A : Ty Base} (hA : Kinded A) (argument : DenoteTy A) :
    EnvSubstitution (extendBound A sourceContext) (extendBound A targetContext)
      (liftSub σ) freeEnv (extendBoundEnv argument sourceEnv)
      (extendBoundEnv argument targetEnv) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hi
    have evaluation := Eval.bound (Δ := Δ) freeEnv
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
set_option maxRecDepth 2000 in
theorem HasType.eval_instantiate {Base : Type u} {Δ : FreeCtx Base} {m : Nat}
    {sourceContext : BoundCtx Base m} {freeEnv : FreeEnv Δ}
    {sourceEnv : BoundEnv sourceContext} {t : Tm Base m} {A : Ty Base}
    (typing : HasType Δ sourceContext t A) {value : DenoteTy A}
    (evaluation : Eval Δ sourceContext freeEnv sourceEnv t A value) :
    ∀ {n : Nat} {targetContext : BoundCtx Base n} {σ : Fin m -> Tm Base n}
      {targetEnv : BoundEnv targetContext},
      EnvSubstitution sourceContext targetContext σ freeEnv sourceEnv targetEnv ->
      Eval Δ targetContext freeEnv targetEnv (Nucleus.HolLN.instantiate σ t) A value := by
  cases typing with
  | bound hA lookup =>
      intro n targetContext σ targetEnv environments
      rename_i i
      cases evaluation
      have hi : Kinded (sourceContext i) := by rw [lookup]; exact hA
      have result := environments i hi
      cases lookup
      simpa [Nucleus.HolLN.instantiate] using result
  | free name hA lookup =>
      intro n targetContext σ targetEnv environments
      cases evaluation
      simpa [Nucleus.HolLN.instantiate] using
        Eval.free name freeEnv targetEnv hA lookup
  | app hf hx =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | app hfunction hargument =>
          have typeEquality := hf.unique hfunction.typing
          cases typeEquality
          simpa [Nucleus.HolLN.instantiate] using
          Eval.app (hf.eval_instantiate hfunction environments)
            (hx.eval_instantiate hargument environments)
  | lam body hA bodyTyping =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | lam _ hbody =>
          simpa [Nucleus.HolLN.instantiate] using Eval.lam hA (fun argument =>
            bodyTyping.eval_instantiate (hbody argument)
              (liftSub_env environments hA argument))
  | bool literal =>
      intro n targetContext σ targetEnv environments
      cases evaluation
      simp only [Nucleus.HolLN.instantiate]
      exact .boolean literal
  | zero =>
      intro n targetContext σ targetEnv environments
      cases evaluation
      simp only [Nucleus.HolLN.instantiate]
      exact .naturalZero
  | succ valueTyping =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | naturalSucc hvalue =>
          simp only [Nucleus.HolLN.instantiate]
          exact .naturalSucc (valueTyping.eval_instantiate hvalue environments)
  | eq hA hx hy =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | eqTrue _ hleft hright equal =>
          have typeEquality := hx.unique hleft.typing
          cases typeEquality
          simp only [Nucleus.HolLN.instantiate]
          exact .eqTrue hA (hx.eval_instantiate hleft environments)
            (hy.eval_instantiate hright environments) equal
      | eqFalse _ hleft hright notEqual =>
          have typeEquality := hx.unique hleft.typing
          cases typeEquality
          simp only [Nucleus.HolLN.instantiate]
          exact .eqFalse hA (hx.eval_instantiate hleft environments)
            (hy.eval_instantiate hright environments) notEqual
  | eps hA hp =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | eps _ hpredicate =>
          have typeEquality := hp.unique hpredicate.typing
          cases typeEquality
          simp only [Nucleus.HolLN.instantiate]
          exact .eps hA (hp.eval_instantiate hpredicate environments)
  | abs hA hp hx =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | abs _ _ hvalue =>
          simp only [Nucleus.HolLN.instantiate]
          exact .abs hA hp (hx.eval_instantiate hvalue environments)
  | rep hA hp hx =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | rep _ _ hvalue =>
          simp only [Nucleus.HolLN.instantiate]
          exact .rep hA hp (hx.eval_instantiate hvalue environments)

def emptyFreeEnv {Base : Type u} : FreeEnv (emptyContext : FreeCtx Base) := by
  intro name A impossible
  contradiction

def emptyBoundEnv {Base : Type u} : BoundEnv (emptyBound : BoundCtx Base 0) := by
  intro i A lookup
  exact Fin.elim0 i

end Nucleus.HolLN
