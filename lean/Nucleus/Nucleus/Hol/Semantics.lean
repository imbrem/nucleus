import Nucleus.Hol.Kernel
import Nucleus.Hol.Typing.Unique

/-! # Pointed set semantics for sorted signature HOL -/

namespace Nucleus.Hol

universe u

set_option relaxedAutoImplicit true

structure Pointed where
  carrier : Type
  point : carrier

def DenoteKind : Kind → Type 1
  | .star => Pointed
  | .arr domain codomain => DenoteKind domain → DenoteKind codomain

class FamilyModel (Sig : Signature) where
  denote : ∀ {kind : Kind}, Sig (.kind kind) → DenoteKind kind

@[reducible] def DenoteFam {Sig : Signature} [FamilyModel Sig] : {kind : Kind} →
    Fam Sig kind → DenoteKind kind
  | _, .primFam symbol => FamilyModel.denote symbol
  | .star, .boolTy => ⟨Bool, false⟩
  | .star, .arr A B =>
      ⟨(DenoteFam A).carrier → (DenoteFam B).carrier, fun _ => (DenoteFam B).point⟩
  | _, .tyApp function argument => DenoteFam function (DenoteFam argument)
  | .star, .sub A _ => DenoteFam A

@[reducible] def DenoteExpr {Sig : Signature} [FamilyModel Sig] :
    {sort : HolSort} → {depth : Nat} → Expr Sig sort depth → Type
  | .kind .star, _, .primFam symbol => (FamilyModel.denote symbol).carrier
  | .kind (.arr _ _), _, .primFam _ => Unit
  | _, _, .primTm _ => Unit
  | _, _, .boolTy => Bool
  | _, _, .arr A B => DenoteExpr A → DenoteExpr B
  | .kind .star, _, .tyApp function argument =>
      (DenoteFam (.tyApp function argument)).carrier
  | .kind (.arr _ _), _, .tyApp _ _ => Unit
  | _, _, .sub A _ => DenoteExpr A
  | _, _, .bv _ => Unit
  | _, _, .fv _ _ => Unit
  | _, _, .app _ _ => Unit
  | _, _, .lam _ _ => Unit
  | _, _, .bool _ => Unit
  | _, _, .eq _ _ _ => Unit
  | _, _, .eps _ _ => Unit
  | _, _, .abs _ _ _ => Unit
  | _, _, .rep _ _ _ => Unit

abbrev DenoteTy {Sig : Signature} [FamilyModel Sig] (A : Ty Sig) := DenoteExpr A

def defaultValue {Sig : Signature} [FamilyModel Sig] : (A : Ty Sig) → DenoteTy A
  | .primFam symbol => (FamilyModel.denote symbol).point
  | .boolTy => false
  | .arr _ B => fun _ => defaultValue B
  | .tyApp function argument => (DenoteFam (.tyApp function argument)).point
  | .sub A _ => defaultValue A

def applyValue {Sig : Signature} [FamilyModel Sig] {A B : Ty Sig}
    (function : DenoteTy (.arr A B)) (argument : DenoteTy A) : DenoteTy B :=
  function argument

/-- A model of relational primitive typing supplies a value at every declared
type. Proof irrelevance makes this independent of the particular rule witness. -/
class TermModel (Sig : Signature) [SigTyping Sig] [FamilyModel Sig] where
  denote : ∀ (symbol : Sig .tm) (A : Ty Sig),
    SigTyping.HasType symbol A → DenoteTy A

abbrev FreeEnv (Sig : Signature) [FamilyModel Sig] :=
  ∀ (_name : Nat) (A : Ty Sig), DenoteTy A

abbrev BoundEnv {Sig : Signature} [FamilyModel Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) := ∀ (i : Fin depth) (A : Ty Sig), Γ i = A → DenoteTy A

def extendBoundEnv {Sig : Signature} [FamilyModel Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A : Ty Sig} (value : DenoteTy A) (environment : BoundEnv Γ) :
    BoundEnv (extendBound A Γ) :=
  fun i => Fin.cases
    (motive := fun j => ∀ A', extendBound A Γ j = A' → DenoteTy A')
    (fun _ equality => equality ▸ value)
    (fun j A' equality => environment j A' equality) i

noncomputable def chooseValue {Sig : Signature} [FamilyModel Sig] (A : Ty Sig)
    (predicate : DenoteTy A → Bool) : DenoteTy A := by
  classical
  exact if existsWitness : ∃ x, predicate x = true
    then Classical.choose existsWitness else defaultValue A

theorem chooseValue_spec {Sig : Signature} [FamilyModel Sig] {A : Ty Sig}
    (predicate : DenoteTy A → Bool) (witness : DenoteTy A)
    (holds : predicate witness = true) : predicate (chooseValue A predicate) = true := by
  classical
  simp only [chooseValue]
  split
  · exact Classical.choose_spec ‹_›
  · rename_i none
    exact False.elim (none ⟨witness, holds⟩)

inductive Eval {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig] :
    {depth : Nat} → (Γ : BoundCtx Sig depth) → FreeEnv Sig → BoundEnv Γ →
    (t : Tm Sig depth) → (A : Ty Sig) → DenoteTy A → Prop where
  | prim (rule : SigTyping.HasType symbol A) (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ) :
      Eval Γ freeEnv boundEnv (.primTm symbol) A (TermModel.denote symbol A rule)
  | bv (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ) (hA : Kinded A)
      (lookup : Γ i = A) : Eval Γ freeEnv boundEnv (.bv i) A (boundEnv i A lookup)
  | fv (name : Nat) (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ) (hA : Kinded A) :
      Eval Γ freeEnv boundEnv (.fv name A) A (freeEnv name A)
  | app {function : DenoteTy (.arr A B)} {argument : DenoteTy A} :
      Eval Γ freeEnv boundEnv f (.arr A B) function →
      Eval Γ freeEnv boundEnv x A argument →
      Eval Γ freeEnv boundEnv (.app f x) B (applyValue function argument)
  | lam {function : DenoteTy (.arr A B)} (hA : Kinded A) :
      (∀ argument, Eval (extendBound A Γ) freeEnv (extendBoundEnv argument boundEnv)
        body B (applyValue function argument)) →
      Eval Γ freeEnv boundEnv (.lam A body) (.arr A B) function
  | boolean (literal : Bool) : Eval Γ freeEnv boundEnv (.bool literal) .boolTy literal
  | eqTrue (hA : Kinded A) (hleft : Eval Γ freeEnv boundEnv x A left)
      (hright : Eval Γ freeEnv boundEnv y A right) (equal : left = right) :
      Eval Γ freeEnv boundEnv (.eq A x y) .boolTy true
  | eqFalse (hA : Kinded A) (hleft : Eval Γ freeEnv boundEnv x A left)
      (hright : Eval Γ freeEnv boundEnv y A right) (notEqual : left ≠ right) :
      Eval Γ freeEnv boundEnv (.eq A x y) .boolTy false
  | eps (hA : Kinded A) (hp : Eval Γ freeEnv boundEnv p (.arr A .boolTy) predicate) :
      Eval Γ freeEnv boundEnv (.eps A p) A (chooseValue A predicate)
  | abs (hA : Kinded A) (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : Eval Γ freeEnv boundEnv x A value) :
      Eval Γ freeEnv boundEnv (.abs A p x) (.sub A p) value
  | rep (hA : Kinded A) (hp : HasType (extendBound A emptyBound) p .boolTy)
      (hx : Eval Γ freeEnv boundEnv x (.sub A p) value) :
      Eval Γ freeEnv boundEnv (.rep A p x) A value

theorem HasType.eval_exists {Sig : Signature} [SigTyping Sig] [FamilyModel Sig]
    [TermModel Sig] {depth : Nat} {Γ : BoundCtx Sig depth} {t : Tm Sig depth} {A : Ty Sig}
    (typing : HasType Γ t A) (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ) :
    ∃ value, Eval Γ freeEnv boundEnv t A value := by
  classical
  cases typing with
  | primTm rule => exact ⟨_, .prim rule freeEnv boundEnv⟩
  | bv hA lookup => exact ⟨_, .bv freeEnv boundEnv hA lookup⟩
  | fv name hA => exact ⟨_, .fv name freeEnv boundEnv hA⟩
  | app hf hx =>
      obtain ⟨function, hfunction⟩ := HasType.eval_exists hf freeEnv boundEnv
      obtain ⟨argument, hargument⟩ := HasType.eval_exists hx freeEnv boundEnv
      exact ⟨applyValue function argument, .app hfunction hargument⟩
  | lam body hA bodyTyping =>
      let function := fun argument =>
        Classical.choose (HasType.eval_exists bodyTyping freeEnv
          (extendBoundEnv argument boundEnv))
      refine ⟨function, .lam hA ?_⟩
      intro argument
      exact Classical.choose_spec (HasType.eval_exists bodyTyping freeEnv
        (extendBoundEnv argument boundEnv))
  | bool literal => exact ⟨literal, .boolean literal⟩
  | eq hA hx hy =>
      obtain ⟨left, hleft⟩ := HasType.eval_exists hx freeEnv boundEnv
      obtain ⟨right, hright⟩ := HasType.eval_exists hy freeEnv boundEnv
      by_cases equal : left = right
      · exact ⟨true, .eqTrue hA hleft hright equal⟩
      · exact ⟨false, .eqFalse hA hleft hright equal⟩
  | eps hA hp =>
      obtain ⟨predicate, hpredicate⟩ := HasType.eval_exists hp freeEnv boundEnv
      exact ⟨chooseValue _ predicate, .eps hA hpredicate⟩
  | abs hA hp hx =>
      obtain ⟨value, hvalue⟩ := HasType.eval_exists hx freeEnv boundEnv
      exact ⟨value, .abs hA hp hvalue⟩
  | rep hA hp hx =>
      obtain ⟨value, hvalue⟩ := HasType.eval_exists hx freeEnv boundEnv
      exact ⟨value, .rep hA hp hvalue⟩

theorem Eval.typing {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {depth : Nat} {Γ : BoundCtx Sig depth} {freeEnv : FreeEnv Sig} {boundEnv : BoundEnv Γ}
    {t : Tm Sig depth} {A : Ty Sig} {value : DenoteTy A}
    (evaluation : Eval Γ freeEnv boundEnv t A value) : HasType Γ t A := by
  induction evaluation with
  | prim rule => exact .primTm rule
  | bv _ _ hA lookup => exact .bv hA lookup
  | fv name _ _ hA => exact .fv name hA
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam hA _ ih => exact .lam _ hA (ih (defaultValue _))
  | boolean literal => exact .bool literal
  | eqTrue hA _ _ _ ihx ihy => exact .eq hA ihx ihy
  | eqFalse hA _ _ _ ihx ihy => exact .eq hA ihx ihy
  | eps hA _ ih => exact .eps hA ih
  | abs hA hp _ ih => exact .abs hA hp ih
  | rep hA hp _ ih => exact .rep hA hp ih

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
/-- Evaluation is deterministic for signatures with unique primitive typing. -/
theorem Eval.unique {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    [FamilyModel Sig] [TermModel Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {freeEnv : FreeEnv Sig} {boundEnv : BoundEnv Γ}
    {t : Tm Sig depth} {A : Ty Sig} {firstValue secondValue : DenoteTy A}
    (first : Eval Γ freeEnv boundEnv t A firstValue)
    (second : Eval Γ freeEnv boundEnv t A secondValue) : firstValue = secondValue := by
  cases first with
  | prim => cases second; rfl
  | bv => cases second; rfl
  | fv => cases second; rfl
  | app hfunction hargument =>
      cases second with
      | app hfunction' hargument' =>
          cases hfunction.typing.unique hfunction'.typing
          rw [hfunction.unique hfunction', hargument.unique hargument']
  | lam hA hbody =>
      cases second with
      | lam hA' hbody' =>
          funext argument
          exact (hbody argument).unique (hbody' argument)
  | boolean => cases second; rfl
  | eqTrue hA hleft hright equal =>
      cases second with
      | eqTrue => rfl
      | eqFalse hA' hleft' hright' notEqual =>
          cases hleft.typing.unique hleft'.typing
          have hl := hleft.unique hleft'
          have hr := hright.unique hright'
          exact False.elim (notEqual (hl ▸ hr ▸ equal))
  | eqFalse hA hleft hright notEqual =>
      cases second with
      | eqTrue hA' hleft' hright' equal =>
          cases hleft.typing.unique hleft'.typing
          have hl := hleft.unique hleft'
          have hr := hright.unique hright'
          exact False.elim (notEqual (hl ▸ hr ▸ equal))
      | eqFalse => rfl
  | eps hA hp =>
      cases second with
      | eps hA' hp' =>
          cases hp.typing.unique hp'.typing
          rw [hp.unique hp']
  | abs hA hp hx =>
      cases second with
      | abs _ _ hx' => exact hx.unique hx'
  | rep hA hp hx =>
      cases second with
      | rep _ _ hx' => exact hx.unique hx'

noncomputable def HasType.value {Sig : Signature} [SigTyping Sig] [FamilyModel Sig]
    [TermModel Sig] {depth : Nat} {Γ : BoundCtx Sig depth} {t : Tm Sig depth} {A : Ty Sig}
    (typing : HasType Γ t A) (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ) : DenoteTy A :=
  Classical.choose (typing.eval_exists freeEnv boundEnv)

theorem HasType.value_spec {Sig : Signature} [SigTyping Sig] [FamilyModel Sig]
    [TermModel Sig] {depth : Nat} {Γ : BoundCtx Sig depth} {t : Tm Sig depth} {A : Ty Sig}
    (typing : HasType Γ t A) (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ) :
    Eval Γ freeEnv boundEnv t A (typing.value freeEnv boundEnv) :=
  Classical.choose_spec (typing.eval_exists freeEnv boundEnv)

theorem Eval.eq_value {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    [FamilyModel Sig] [TermModel Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {freeEnv : FreeEnv Sig} {boundEnv : BoundEnv Γ}
    {t : Tm Sig depth} {A : Ty Sig} {value : DenoteTy A}
    (evaluation : Eval Γ freeEnv boundEnv t A value) (typing : HasType Γ t A) :
    value = typing.value freeEnv boundEnv :=
  evaluation.unique (typing.value_spec freeEnv boundEnv)

theorem Eval.app_inv {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {depth : Nat} {Γ : BoundCtx Sig depth} {freeEnv : FreeEnv Sig} {boundEnv : BoundEnv Γ}
    {f x : Tm Sig depth} {B : Ty Sig} {value : DenoteTy B}
    (evaluation : Eval Γ freeEnv boundEnv (.app f x) B value) :
    ∃ (A : Ty Sig) (function : DenoteTy (.arr A B)) (argument : DenoteTy A),
      Eval Γ freeEnv boundEnv f (.arr A B) function ∧
      Eval Γ freeEnv boundEnv x A argument ∧ value = applyValue function argument := by
  cases evaluation with
  | app hfunction hargument => exact ⟨_, _, _, hfunction, hargument, rfl⟩

theorem Eval.eq_true_inv {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {depth : Nat} {Γ : BoundCtx Sig depth} {freeEnv : FreeEnv Sig} {boundEnv : BoundEnv Γ}
    {A : Ty Sig} {x y : Tm Sig depth}
    (evaluation : Eval Γ freeEnv boundEnv (.eq A x y) .boolTy true) :
    ∃ (left right : DenoteTy A), Eval Γ freeEnv boundEnv x A left ∧
      Eval Γ freeEnv boundEnv y A right ∧ left = right := by
  cases evaluation with
  | eqTrue _ hleft hright equal => exact ⟨_, _, hleft, hright, equal⟩

def ContextRenaming {Sig : Signature} {m n : Nat} (Γ : BoundCtx Sig m)
    (Γ' : BoundCtx Sig n) (ρ : Fin m → Fin n) : Prop :=
  ∀ i, Γ' (ρ i) = Γ i

def EnvRenaming {Sig : Signature} [FamilyModel Sig] {m n : Nat}
    {Γ : BoundCtx Sig m} {Γ' : BoundCtx Sig n} {ρ : Fin m → Fin n}
    (relation : ContextRenaming Γ Γ' ρ) (source : BoundEnv Γ)
    (target : BoundEnv Γ') : Prop :=
  ∀ i A (lookup : Γ i = A),
    target (ρ i) A ((relation i).trans lookup) = source i A lookup

theorem liftRen_context {Sig : Signature} {m n : Nat} {Γ : BoundCtx Sig m}
    {Γ' : BoundCtx Sig n} {ρ : Fin m → Fin n}
    (relation : ContextRenaming Γ Γ' ρ) (A : Ty Sig) :
    ContextRenaming (extendBound A Γ) (extendBound A Γ') (liftRen ρ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact relation j

theorem liftRen_env {Sig : Signature} [FamilyModel Sig] {m n : Nat}
    {Γ : BoundCtx Sig m} {Γ' : BoundCtx Sig n} {ρ : Fin m → Fin n}
    {source : BoundEnv Γ} {target : BoundEnv Γ'}
    (relation : ContextRenaming Γ Γ' ρ) (environments : EnvRenaming relation source target)
    {A : Ty Sig} (argument : DenoteTy A) :
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
theorem Eval.rename {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {m : Nat} {Γ : BoundCtx Sig m} {freeEnv : FreeEnv Sig} {source : BoundEnv Γ}
    {t : Tm Sig m} {A : Ty Sig} {value : DenoteTy A}
    (evaluation : Eval Γ freeEnv source t A value) :
    ∀ {n : Nat} {Γ' : BoundCtx Sig n} {ρ : Fin m → Fin n} {target : BoundEnv Γ'},
      (relation : ContextRenaming Γ Γ' ρ) → EnvRenaming relation source target →
      Eval Γ' freeEnv target (Nucleus.Hol.rename ρ t) A value := by
  induction evaluation with
  | prim rule sourceFree sourceBound =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.Hol.rename] using Eval.prim rule sourceFree target
  | bv sourceFree sourceBound hA lookup =>
      intro n Γ' ρ target relation environments
      rename_i i
      let lookup' := (relation i).trans lookup
      have values := environments i _ lookup
      simpa [Nucleus.Hol.rename, values] using Eval.bv sourceFree target hA lookup'
  | fv name sourceFree sourceBound hA =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.Hol.rename] using Eval.fv name sourceFree target hA
  | app hfunction hargument ihfunction ihargument =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.Hol.rename] using
        Eval.app (ihfunction relation environments) (ihargument relation environments)
  | lam hA hbody ihbody =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.Hol.rename] using Eval.lam hA (fun argument =>
        ihbody argument (liftRen_context relation _) (liftRen_env relation environments argument))
  | boolean literal =>
      intro n Γ' ρ target relation environments
      simp only [Nucleus.Hol.rename]
      exact .boolean literal
  | eqTrue hA hleft hright equal ihleft ihright =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.Hol.rename] using
        Eval.eqTrue hA (ihleft relation environments) (ihright relation environments) equal
  | eqFalse hA hleft hright notEqual ihleft ihright =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.Hol.rename] using
        Eval.eqFalse hA (ihleft relation environments) (ihright relation environments) notEqual
  | eps hA hp ih =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.Hol.rename] using Eval.eps hA (ih relation environments)
  | abs hA hp hx ih =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.Hol.rename] using Eval.abs hA hp (ih relation environments)
  | rep hA hp hx ih =>
      intro n Γ' ρ target relation environments
      simpa [Nucleus.Hol.rename] using Eval.rep hA hp (ih relation environments)

def EnvSubstitution {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {m n : Nat} (sourceContext : BoundCtx Sig m) (targetContext : BoundCtx Sig n)
    (σ : Fin m → Tm Sig n) (freeEnv : FreeEnv Sig)
    (sourceEnv : BoundEnv sourceContext) (targetEnv : BoundEnv targetContext) : Prop :=
  ∀ i, Kinded (sourceContext i) → Eval targetContext freeEnv targetEnv (σ i)
    (sourceContext i) (sourceEnv i (sourceContext i) rfl)

theorem liftSub_env {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {m n : Nat} {sourceContext : BoundCtx Sig m} {targetContext : BoundCtx Sig n}
    {σ : Fin m → Tm Sig n} {freeEnv : FreeEnv Sig}
    {sourceEnv : BoundEnv sourceContext} {targetEnv : BoundEnv targetContext}
    (environments : EnvSubstitution sourceContext targetContext σ freeEnv sourceEnv targetEnv)
    {A : Ty Sig} (hA : Kinded A) (argument : DenoteTy A) :
    EnvSubstitution (extendBound A sourceContext) (extendBound A targetContext)
      (liftSub σ) freeEnv (extendBoundEnv argument sourceEnv)
      (extendBoundEnv argument targetEnv) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · intro hi
    have evaluation := Eval.bv freeEnv (extendBoundEnv argument targetEnv) hA
      (show extendBound A targetContext 0 = A from rfl)
    change Eval (extendBound A targetContext) freeEnv (extendBoundEnv argument targetEnv)
      (.bv 0) A argument
    change Eval (extendBound A targetContext) freeEnv (extendBoundEnv argument targetEnv)
      (.bv 0) A argument at evaluation
    exact evaluation
  · intro hi
    have hj : Kinded (sourceContext j) := by simpa [extendBound] using hi
    have renamed := (environments j hj).rename
      (Γ' := extendBound A targetContext) (ρ := Fin.succ)
      (target := extendBoundEnv argument targetEnv)
      (fun _ => rfl) (by intro k B lookup; rfl)
    change Eval (extendBound A targetContext) freeEnv (extendBoundEnv argument targetEnv)
      (weaken (σ j)) (sourceContext j) (sourceEnv j (sourceContext j) rfl)
    simpa [weaken] using renamed

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem HasType.eval_instantiate {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    [FamilyModel Sig] [TermModel Sig] {m : Nat}
    {sourceContext : BoundCtx Sig m} {freeEnv : FreeEnv Sig}
    {sourceEnv : BoundEnv sourceContext} {t : Tm Sig m} {A : Ty Sig}
    (typing : HasType sourceContext t A) {value : DenoteTy A}
    (evaluation : Eval sourceContext freeEnv sourceEnv t A value) :
    ∀ {n : Nat} {targetContext : BoundCtx Sig n} {σ : Fin m → Tm Sig n}
      {targetEnv : BoundEnv targetContext},
      EnvSubstitution sourceContext targetContext σ freeEnv sourceEnv targetEnv →
      Eval targetContext freeEnv targetEnv (Nucleus.Hol.instantiate σ t) A value := by
  cases typing with
  | primTm rule =>
      intro n targetContext σ targetEnv environments
      cases evaluation
      simpa [Nucleus.Hol.instantiate] using Eval.prim rule freeEnv targetEnv
  | bv hA lookup =>
      intro n targetContext σ targetEnv environments
      rename_i i
      cases evaluation
      have hi : Kinded (sourceContext i) := by rw [lookup]; exact hA
      have result := environments i hi
      cases lookup
      simpa [Nucleus.Hol.instantiate] using result
  | fv name hA =>
      intro n targetContext σ targetEnv environments
      cases evaluation
      simpa [Nucleus.Hol.instantiate] using Eval.fv name freeEnv targetEnv hA
  | app hf hx =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | app hfunction hargument =>
          cases HasType.unique hf hfunction.typing
          simpa [Nucleus.Hol.instantiate] using
            Eval.app (HasType.eval_instantiate hf hfunction environments)
              (HasType.eval_instantiate hx hargument environments)
  | lam body hA bodyTyping =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | lam _ hbody =>
          simpa [Nucleus.Hol.instantiate] using Eval.lam hA (fun argument =>
            HasType.eval_instantiate bodyTyping (hbody argument)
              (liftSub_env environments hA argument))
  | bool literal =>
      intro n targetContext σ targetEnv environments
      cases evaluation
      simp only [Nucleus.Hol.instantiate]
      exact .boolean literal
  | eq hA hx hy =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | eqTrue _ hleft hright equal =>
          cases HasType.unique hx hleft.typing
          simp only [Nucleus.Hol.instantiate]
          exact .eqTrue hA (HasType.eval_instantiate hx hleft environments)
            (HasType.eval_instantiate hy hright environments) equal
      | eqFalse _ hleft hright notEqual =>
          cases HasType.unique hx hleft.typing
          simp only [Nucleus.Hol.instantiate]
          exact .eqFalse hA (HasType.eval_instantiate hx hleft environments)
            (HasType.eval_instantiate hy hright environments) notEqual
  | eps hA hp =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | eps _ hpredicate =>
          cases HasType.unique hp hpredicate.typing
          simp only [Nucleus.Hol.instantiate]
          exact .eps hA (HasType.eval_instantiate hp hpredicate environments)
  | abs hA hp hx =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | abs _ _ hvalue =>
          simp only [Nucleus.Hol.instantiate]
          exact .abs hA hp (HasType.eval_instantiate hx hvalue environments)
  | rep hA hp hx =>
      intro n targetContext σ targetEnv environments
      cases evaluation with
      | rep _ _ hvalue =>
          simp only [Nucleus.Hol.instantiate]
          exact .rep hA hp (HasType.eval_instantiate hx hvalue environments)

def defaultFreeEnv {Sig : Signature} [FamilyModel Sig] : FreeEnv Sig :=
  fun _ A => defaultValue A

def emptyBoundEnv {Sig : Signature} [FamilyModel Sig] :
    BoundEnv (emptyBound : BoundCtx Sig 0) := by
  intro i
  exact Fin.elim0 i

end Nucleus.Hol
