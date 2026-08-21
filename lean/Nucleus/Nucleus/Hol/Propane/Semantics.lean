import Nucleus.Hol.Propane.Kernel

/-!
# Semantics and soundness for Propane

The intrinsically typed syntax has a direct set-theoretic interpretation.
Every type is inhabited, so the opaque `junk` term and unsuccessful choice
both have a total interpretation.  No equation for `junk` is assumed by the
proof theory.
-/

namespace Nucleus.Hol.Propane

set_option relaxedAutoImplicit true

noncomputable section

/-- Set-theoretic interpretation of simple types. -/
def Ty.denote : Ty → Type
  | .bool => Bool
  | .arr domain codomain => domain.denote → codomain.denote

noncomputable def Ty.default : (type : Ty) → type.denote
  | .bool => false
  | .arr _ codomain => fun _ => codomain.default

noncomputable instance Ty.denoteInhabited (type : Ty) : Inhabited type.denote :=
  ⟨type.default⟩

/-- A heterogeneous valuation for bound variables. -/
inductive Env : List Ty → Type
  | nil : Env []
  | cons : A.denote → Env Γ → Env (A :: Γ)

def Env.lookup : Env Γ → Var Γ A → A.denote
  | .cons value _, .zero => value
  | .cons _ tail, .succ index => tail.lookup index

/-- Free variables are interpreted independently at every intrinsic type. -/
abbrev Valuation := {A : Ty} → Nat → A.denote

/-- Total Hilbert choice for Boolean predicates. -/
noncomputable def chooseValue {A : Ty} (predicate : A.denote → Bool) : A.denote :=
  by
    classical
    exact if witness : ∃ value, predicate value = true then Classical.choose witness
      else default

theorem chooseValue_spec {A : Ty} (predicate : A.denote → Bool)
    (value : A.denote) (holds : predicate value = true) :
    predicate (chooseValue predicate) = true := by
  classical
  unfold chooseValue
  split
  · rename_i witness
    exact (Classical.choose_spec witness)
  · rename_i noWitness
    exact False.elim (noWitness ⟨value, holds⟩)

/-- Direct interpretation of every intrinsically typed term. -/
noncomputable def Tm.eval {Γ : List Ty} {A : Ty}
    (valuation : Valuation) (env : Env Γ) :
    Tm Γ A → A.denote
  | .bv index => env.lookup index
  | .fv name => valuation name
  | .app function argument => function.eval valuation env (argument.eval valuation env)
  | .lam body => fun value => body.eval valuation (.cons value env)
  | .bool value => value
  | .eq left right =>
      @decide (left.eval valuation env = right.eval valuation env)
        (Classical.propDecidable _)
  | .eps predicate => chooseValue (predicate.eval valuation env)
  | .junk => default

/-- Environments related by a renaming agree on every source variable. -/
def Env.AgreesRen {Γ Δ : List Ty} (rename : Ren Γ Δ)
    (source : Env Γ) (target : Env Δ) : Prop :=
  ∀ {A} (index : Var Γ A), target.lookup (rename index) = source.lookup index

theorem Env.AgreesRen.lift {Γ Δ : List Ty} {rename : Ren Γ Δ}
    {source : Env Γ} {target : Env Δ}
    (agreement : Env.AgreesRen rename source target)
    {A : Ty} (value : A.denote) :
    Env.AgreesRen (liftRen rename) (.cons value source) (.cons value target) := by
  intro type index
  cases index with
  | zero => rfl
  | succ index => exact agreement index

theorem Tm.eval_rename {Γ Δ : List Ty} {A : Ty} {rename : Ren Γ Δ}
    {source : Env Γ} {target : Env Δ} {valuation : Valuation}
    (term : Tm Γ A) (agreement : Env.AgreesRen rename source target) :
    (term.rename rename).eval valuation target = term.eval valuation source := by
  induction term generalizing Δ with
  | bv index => exact agreement index
  | fv => rfl
  | app function argument ihFunction ihArgument =>
      simp only [Tm.rename, Tm.eval, ihFunction agreement, ihArgument agreement]
  | lam body ih =>
      simp only [Tm.rename, Tm.eval]
      funext value
      exact ih (agreement.lift value)
  | bool => rfl
  | eq left right ihLeft ihRight =>
      simp only [Tm.rename, Tm.eval]
      rw [ihLeft agreement, ihRight agreement]
  | eps predicate ih =>
      simp only [Tm.rename, Tm.eval, ih agreement]
  | junk => rfl

theorem Env.weaken_agrees {Γ : List Ty} {A : Ty}
    (env : Env Γ) (value : A.denote) :
    Env.AgreesRen weakenRen env (.cons value env) := by
  intro type index
  rfl

@[simp] theorem Tm.eval_weaken {Γ : List Ty} {A B : Ty}
    {valuation : Valuation} {env : Env Γ}
    (term : Tm Γ A) (value : B.denote) :
    (term.rename weakenRen).eval valuation (.cons value env) = term.eval valuation env :=
  term.eval_rename (Env.weaken_agrees env value)

/-- Environments related by a substitution agree after evaluating every
substituted variable. -/
def Env.AgreesSub {Γ Δ : List Ty} (substitute : Sub Γ Δ)
    (source : Env Γ) (target : Env Δ)
    (valuation : Valuation) : Prop :=
  ∀ {A} (index : Var Γ A),
    (substitute index).eval valuation target = source.lookup index

theorem Env.AgreesSub.lift
    {Γ Δ : List Ty} {substitute : Sub Γ Δ} {source : Env Γ} {target : Env Δ}
    {valuation : Valuation} {A : Ty}
    (agreement : Env.AgreesSub substitute source target valuation)
    (value : A.denote) :
    Env.AgreesSub (liftSub substitute) (.cons value source) (.cons value target)
      valuation := by
  intro type index
  cases index with
  | zero => rfl
  | succ index =>
      simpa only [liftSub, Tm.eval_weaken, Env.lookup] using agreement index

theorem Tm.eval_subst {Γ Δ : List Ty} {A : Ty} {substitute : Sub Γ Δ}
    {source : Env Γ} {target : Env Δ} {valuation : Valuation}
    (term : Tm Γ A)
    (agreement : Env.AgreesSub substitute source target valuation) :
    (term.subst substitute).eval valuation target = term.eval valuation source := by
  induction term generalizing Δ with
  | bv index => exact agreement index
  | fv => rfl
  | app function argument ihFunction ihArgument =>
      simp only [Tm.subst, Tm.eval, ihFunction agreement, ihArgument agreement]
  | lam body ih =>
      simp only [Tm.subst, Tm.eval]
      funext value
      exact ih (agreement.lift value)
  | bool => rfl
  | eq left right ihLeft ihRight =>
      simp only [Tm.subst, Tm.eval]
      rw [ihLeft agreement, ihRight agreement]
  | eps predicate ih =>
      simp only [Tm.subst, Tm.eval, ih agreement]
  | junk => rfl

theorem Env.single_agrees {Γ : List Ty} {A : Ty} {valuation : Valuation}
    (env : Env Γ) (argument : Tm Γ A) :
    Env.AgreesSub (single argument) (.cons (argument.eval valuation env) env) env
      valuation := by
  intro type index
  cases index with
  | zero => rfl
  | succ index => rfl

@[simp] theorem Tm.eval_open {Γ : List Ty} {A B : Ty}
    {valuation : Valuation} {env : Env Γ}
    (body : Tm (A :: Γ) B) (argument : Tm Γ A) :
    (body.open argument).eval valuation env =
      body.eval valuation (.cons (argument.eval valuation env) env) :=
  body.eval_subst (Env.single_agrees env argument)

/-- Semantic equality of typed terms in all environments. -/
def SemEq {Γ : List Ty} {A : Ty} (left right : Tm Γ A) : Prop :=
  ∀ valuation env, left.eval valuation env = right.eval valuation env

theorem EqTm.sound {Γ : List Ty} {A : Ty} {left right : Tm Γ A}
    (equality : EqTm left right) : SemEq left right := by
  induction equality with
  | refl => intro _ _; rfl
  | symm _ ih => intro valuation env; exact (ih valuation env).symm
  | trans _ _ ihLeft ihRight =>
      intro valuation env
      exact (ihLeft valuation env).trans (ihRight valuation env)
  | app _ _ ihFunction ihArgument =>
      intro valuation env
      simp only [Tm.eval, ihFunction valuation env, ihArgument valuation env]
  | lam _ ih =>
      intro valuation env
      simp only [Tm.eval]
      funext value
      exact ih valuation (.cons value env)
  | eq _ _ ihLeft ihRight =>
      intro valuation env
      simp only [Tm.eval]
      rw [ihLeft valuation env, ihRight valuation env]
  | eps _ ih =>
      intro valuation env
      simp only [Tm.eval]
      rw [ih valuation env]
  | beta body argument =>
      intro valuation env
      simp only [Tm.eval, Tm.eval_open]
  | eta function =>
      intro valuation env
      simp only [Tm.eval, Tm.eval_weaken, Env.lookup]
      rfl

/-- Truth of a Boolean term under one interpretation. -/
def Satisfies {Γ : List Ty} (valuation : Valuation) (env : Env Γ)
    (term : Wff Γ) : Prop :=
  term.eval valuation env = true

/-- Semantic consequence. -/
def Entails {Γ : List Ty} (hypotheses : Hyps Γ) (conclusion : Wff Γ) : Prop :=
  ∀ valuation env,
    (∀ proposition, proposition ∈ hypotheses → Satisfies valuation env proposition) →
    Satisfies valuation env conclusion

private theorem bool_eq_of_true_implications {left right : Bool}
    (forward : left = true → right = true)
    (backward : right = true → left = true) : left = right := by
  cases left <;> cases right <;> simp_all

theorem Proves.sound {Γ : List Ty} {hypotheses : Hyps Γ} {conclusion : Wff Γ}
    (proof : Proves hypotheses conclusion) :
    Entails hypotheses conclusion := by
  classical
  induction proof with
  | hyp member =>
      intro valuation env assumptions
      exact assumptions _ member
  | truth =>
      intro valuation env assumptions
      rfl
  | falseElim premise ih =>
      intro valuation env assumptions
      have falseTrue := ih valuation env assumptions
      simp [Satisfies, Tm.eval] at falseTrue
  | boolCases left right ihLeft ihRight =>
      rename_i Γ' proposition hypotheses' conclusion'
      intro valuation env assumptions
      cases value : Tm.eval valuation env proposition with
      | false =>
          apply ihRight valuation env
          intro candidate member
          rcases List.mem_cons.mp member with rfl | member
          · change @decide (Tm.eval valuation env proposition = false)
                (Classical.propDecidable _) = true
            exact decide_eq_true value
          · exact assumptions candidate member
      | true =>
          apply ihLeft valuation env
          intro candidate member
          rcases List.mem_cons.mp member with rfl | member
          · exact value
          · exact assumptions candidate member
  | eqRefl term =>
      intro valuation env assumptions
      simp [Satisfies, Tm.eval]
      rfl
  | eqMp predicate equality premise ihEquality ihPremise =>
      intro valuation env assumptions
      have equalityTrue := ihEquality valuation env assumptions
      have predicateTrue := ihPremise valuation env assumptions
      have valuesEqual : _ = _ :=
        @of_decide_eq_true _ (Classical.propDecidable _) equalityTrue
      simpa only [Satisfies, Tm.eval, valuesEqual] using predicateTrue
  | choice predicate witness premise ih =>
      intro valuation env assumptions
      have witnessTrue := ih valuation env assumptions
      simp only [Satisfies, Tm.eval] at witnessTrue ⊢
      exact chooseValue_spec _ _ witnessTrue
  | generalize body premise ih =>
      intro valuation env assumptions
      have functionsEqual :
          (fun value => Tm.eval valuation (.cons value env) body) =
            (fun _ => true) := by
        funext value
        have bodyTrue := ih valuation (.cons value env) (by
          intro proposition member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          simpa only [Satisfies, Tm.eval_weaken] using
            assumptions original originalMember)
        exact bodyTrue
      change @decide
        ((fun value => Tm.eval valuation (.cons value env) body) = fun _ => true)
        (Classical.propDecidable _) = true
      exact decide_eq_true functionsEqual
  | hypothesisMap subset premise ih =>
      intro valuation env assumptions
      exact ih valuation env fun proposition member =>
        assumptions proposition (subset proposition member)
  | convert equality premise ih =>
      intro valuation env assumptions
      have premiseTrue := ih valuation env assumptions
      unfold Satisfies at premiseTrue ⊢
      rw [← equality.sound valuation env]
      exact premiseTrue
  | eqOfEqTm equality =>
      intro valuation env assumptions
      simp [Satisfies, Tm.eval, equality.sound valuation env]
      rfl
  | antisymm forward backward ihForward ihBackward =>
      intro valuation env assumptions
      have valuesEqual := bool_eq_of_true_implications
        (fun leftTrue => ihForward valuation env (by
          intro proposition member
          rcases List.mem_cons.mp member with rfl | member
          · exact leftTrue
          · exact assumptions proposition member))
        (fun rightTrue => ihBackward valuation env (by
          intro proposition member
          rcases List.mem_cons.mp member with rfl | member
          · exact rightTrue
          · exact assumptions proposition member))
      simp [Satisfies, Tm.eval, valuesEqual]
      rfl

/-- The empty Propane theory is consistent. -/
theorem consistent (proof : Proves ([] : Hyps []) (.bool false)) : False := by
  let valuation : Valuation := fun {_} _ => default
  have valid := proof.sound valuation .nil (by simp)
  simp [Satisfies, Tm.eval] at valid

end

end Nucleus.Hol.Propane
