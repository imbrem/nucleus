import Nucleus.HolLN.Semantics

/-!
# Soundness of every equality and entailment rule

The fixed interpretation is internal: no model or universe argument appears in
the exported results.  This module covers all ordinary HOL rules and the
natural-number infinity extension.
-/

namespace Nucleus.HolLN

universe u

theorem EqTm.typing {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t uterm : Tm Base depth} {A : Ty Base}
    (equality : EqTm Δ Γ t uterm A) :
    HasType Δ Γ t A ∧ HasType Δ Γ uterm A := by
  induction equality with
  | refl typing => exact ⟨typing, typing⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | app _ _ ihf ihx => exact ⟨.app ihf.1 ihx.1, .app ihf.2 ihx.2⟩
  | succ _ ih => exact ⟨.succ ih.1, .succ ih.2⟩
  | lam hA _ ih => exact ⟨.lam _ hA ih.1, .lam _ hA ih.2⟩
  | beta body x hA bodyTyping argumentTyping resultTyping =>
      exact ⟨.app (.lam _ hA bodyTyping) argumentTyping, resultTyping⟩
  | eta name fresh functionTyping etaTyping => exact ⟨etaTyping, functionTyping⟩

set_option maxHeartbeats 1000000 in
-- Soundness eliminates both equality certificates and dependent evaluations.
set_option maxRecDepth 2000 in
theorem EqTm.sound {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {t uterm : Tm Base depth} {A : Ty Base}
    (equality : EqTm Δ Γ t uterm A) (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ)
    {left right : DenoteTy A}
    (leftEval : Eval Δ Γ freeEnv boundEnv t A left)
    (rightEval : Eval Δ Γ freeEnv boundEnv uterm A right) : left = right := by
  induction equality with
  | refl typing => exact leftEval.unique rightEval
  | symm equality ih => exact (ih boundEnv rightEval leftEval).symm
  | trans first second ih₁ ih₂ =>
      obtain ⟨middle, middleEval⟩ := first.typing.2.eval_exists freeEnv boundEnv
      exact (ih₁ boundEnv leftEval middleEval).trans (ih₂ boundEnv middleEval rightEval)
  | app functionEquality argumentEquality ihf ihx =>
      cases leftEval with
      | app leftFunction leftArgument =>
          cases rightEval with
          | app rightFunction rightArgument =>
              have leftType := functionEquality.typing.1.unique leftFunction.typing
              cases leftType
              have rightType := functionEquality.typing.2.unique rightFunction.typing
              cases rightType
              rw [ihf boundEnv leftFunction rightFunction,
                ihx boundEnv leftArgument rightArgument]
  | succ valueEquality ih =>
      cases leftEval with
      | naturalSucc leftValue =>
          cases rightEval with
          | naturalSucc rightValue => rw [ih boundEnv leftValue rightValue]
  | lam hA bodyEquality ih =>
      cases leftEval with
      | lam _ leftBody =>
          cases rightEval with
          | lam _ rightBody =>
              funext argument
              exact ih (extendBoundEnv argument boundEnv)
                (leftBody argument) (rightBody argument)
  | beta body x hA bodyTyping argumentTyping resultTyping =>
      cases leftEval with
      | app functionEval argumentEval =>
          cases functionEval with
          | lam _ bodyEval =>
              let sourceEnv := extendBoundEnv
                (Classical.choose (argumentTyping.eval_exists freeEnv boundEnv)) boundEnv
              have chosenArgument := Classical.choose_spec
                (argumentTyping.eval_exists freeEnv boundEnv)
              have argumentValue := chosenArgument.unique argumentEval
              subst argumentValue
              have substitutions : EnvSubstitution _ _
                  (Fin.cases x .bound) freeEnv sourceEnv boundEnv := by
                intro i
                refine Fin.cases ?_ (fun j => ?_) i
                · intro hi
                  convert argumentEval using 1 <;> rfl
                · intro hi
                  exact .bound freeEnv boundEnv hi rfl
              have opened := bodyTyping.eval_instantiate
                (bodyEval (Classical.choose (argumentTyping.eval_exists freeEnv boundEnv)))
                substitutions
              exact opened.unique rightEval
  | eta name fresh functionTyping etaTyping =>
      cases leftEval with
      | lam _ etaBody =>
          funext argument
          have weakened := rightEval.rename (ρ := Fin.succ)
            (target := extendBoundEnv argument boundEnv) (fun _ => rfl) (by
              intro i B lookup
              rfl)
          have argumentEval := Eval.bound (Δ := Δ) freeEnv
            (i := 0) (extendBoundEnv argument boundEnv)
              (by
                have regular := functionTyping.regularity
                cases regular with
                | arr hA _ => exact hA) rfl
          obtain ⟨domain, bodyFunctionValue, bodyArgumentValue,
              bodyFunction, bodyArgument, output⟩ := (etaBody argument).app_inv
          have domainEquality := weakened.typing.unique bodyFunction.typing
          cases domainEquality
          exact output.trans (congrArg₂ (fun function value => function value)
            (bodyFunction.unique weakened) (bodyArgument.unique argumentEval))

def HypsTrue {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ)
    (hypotheses : List (Tm Base depth)) : Prop :=
  ∀ p, p ∈ hypotheses -> Eval Δ Γ freeEnv boundEnv p .boolTy true

def Entails {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (hypotheses : List (Tm Base depth))
    (conclusion : Tm Base depth) : Prop :=
  ∀ (freeEnv : FreeEnv Δ) (boundEnv : BoundEnv Γ),
    HypsTrue freeEnv boundEnv hypotheses ->
    Eval Δ Γ freeEnv boundEnv conclusion .boolTy true

set_option maxHeartbeats 1000000 in
-- The complete entailment induction carries dependent environments through every rule.
set_option maxRecDepth 2000 in
theorem Proves.sound {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {H : List (Tm Base depth)} {p : Tm Base depth}
    (proof : Proves Δ Γ H p) : Entails (Δ := Δ) (Γ := Γ) H p := by
  intro freeEnv boundEnv hypotheses
  induction proof with
  | hyp typed member => exact hypotheses _ member
  | truth typed => exact .boolean true
  | eqRefl typed hA hx =>
      obtain ⟨value, evaluation⟩ := hx.eval_exists freeEnv boundEnv
      exact .eqTrue hA evaluation evaluation rfl
  | eqMp typed hA hp hx hy equality application ihEquality ihApplication =>
      have equalityTrue := ihEquality hypotheses
      have applicationTrue := ihApplication hypotheses
      obtain ⟨left, right, leftEval, rightEval, equal⟩ := equalityTrue.eq_true_inv
      obtain ⟨domain, function, argument, functionEval, argumentEval, applied⟩ :=
        applicationTrue.app_inv
      have functionType := hp.unique functionEval.typing
      cases functionType
      have argumentType := hx.unique argumentEval.typing
      cases argumentType
      have argumentEqual := argumentEval.unique leftEval
      have output : function right = true := by
        rw [← equal, ← argumentEqual]
        exact applied.symm
      exact output ▸ Eval.app functionEval rightEval
  | choice typed hA hp hx application ih =>
      have applicationTrue := ih hypotheses
      obtain ⟨domain, predicate, witness, predicateEval, witnessEval, holds⟩ :=
        applicationTrue.app_inv
      have predicateType := hp.unique predicateEval.typing
      cases predicateType
      have witnessType := hx.unique witnessEval.typing
      cases witnessType
      have selected : Eval Δ Γ freeEnv boundEnv (.eps _ _) _ (chooseValue _ predicate) :=
        .eps hA predicateEval
      have chosenTrue := chooseValue_spec predicate witness holds.symm
      exact chosenTrue ▸ Eval.app predicateEval selected
  | convert typed equality premise ih =>
      have premiseTrue := ih hypotheses
      obtain ⟨value, targetEval⟩ := equality.typing.2.eval_exists freeEnv boundEnv
      have values := equality.sound freeEnv boundEnv premiseTrue targetEval
      cases values
      exact targetEval
  | eqOfEqTm typed hA equality =>
      obtain ⟨left, leftEval⟩ := equality.typing.1.eval_exists freeEnv boundEnv
      obtain ⟨right, rightEval⟩ := equality.typing.2.eval_exists freeEnv boundEnv
      exact .eqTrue hA leftEval rightEval (equality.sound freeEnv boundEnv leftEval rightEval)
  | antisymm typed hp hq leftTyped rightTyped leftProof rightProof ihLeft ihRight =>
      obtain ⟨left, leftEval⟩ := hp.eval_exists freeEnv boundEnv
      obtain ⟨right, rightEval⟩ := hq.eval_exists freeEnv boundEnv
      have equal : left = right := by
        cases left <;> cases right <;> try rfl
        · have impossible := ihRight (by
            intro r member
            rcases List.mem_cons.mp member with equal | member
            · subst r; exact rightEval
            · exact hypotheses _ member)
          exact False.elim (Bool.noConfusion (impossible.unique leftEval))
        · have impossible := ihLeft (by
            intro r member
            rcases List.mem_cons.mp member with equal | member
            · subst r; exact leftEval
            · exact hypotheses _ member)
          exact False.elim (Bool.noConfusion (impossible.unique rightEval))
      exact .eqTrue .bool leftEval rightEval equal
  | absRep typed hA hp hx =>
      obtain ⟨value, valueEval⟩ := hx.eval_exists freeEnv boundEnv
      exact .eqTrue (.sub hA hp) (.abs hA hp (.rep hA hp valueEval)) valueEval rfl
  | repAbs typed hA hp hx predicateTyping predicateProof ih =>
      obtain ⟨value, valueEval⟩ := hx.eval_exists freeEnv boundEnv
      exact .eqTrue hA (.rep hA hp (.abs hA hp valueEval)) valueEval rfl
  | succInjective typed hx hy premise ih =>
      have premiseTrue := ih hypotheses
      obtain ⟨left, right, leftEval, rightEval, equal⟩ := premiseTrue.eq_true_inv
      cases leftEval with
      | naturalSucc leftValue =>
          cases rightEval with
          | naturalSucc rightValue =>
              exact .eqTrue .nat leftValue rightValue (natSucc_injective equal)
  | zeroNotSucc typed hx =>
      obtain ⟨value, valueEval⟩ := hx.eval_exists freeEnv boundEnv
      have inner : Eval Δ Γ freeEnv boundEnv (.eq .natTy .zero (.succ _))
          .boolTy false :=
        .eqFalse .nat .naturalZero (.naturalSucc valueEval) (natZero_ne_natSucc value)
      exact .eqTrue .bool inner (.boolean false) rfl

end Nucleus.HolLN
