import Nucleus.Hol.Semantics

/-! # Soundness of the complete signature-parametric HOL kernel -/

namespace Nucleus.Hol

universe u
set_option relaxedAutoImplicit true

theorem EqTm.typing {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {t uterm : Tm Sig depth} {A : Ty Sig}
    (equality : EqTm Γ t uterm A) : HasType Γ t A ∧ HasType Γ uterm A := by
  induction equality with
  | refl typing => exact ⟨typing, typing⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | app _ _ ihf ihx => exact ⟨.app ihf.1 ihx.1, .app ihf.2 ihx.2⟩
  | lam hA _ ih => exact ⟨.lam _ hA ih.1, .lam _ hA ih.2⟩
  | beta body x hA bodyTyping argumentTyping resultTyping =>
      exact ⟨.app (.lam _ hA bodyTyping) argumentTyping, resultTyping⟩
  | eta name fresh functionTyping etaTyping => exact ⟨etaTyping, functionTyping⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem EqTm.sound {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    [FamilyModel Sig] [TermModel Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {t uterm : Tm Sig depth} {A : Ty Sig}
    (equality : EqTm Γ t uterm A) (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ)
    {left right : DenoteTy A} (leftEval : Eval Γ freeEnv boundEnv t A left)
    (rightEval : Eval Γ freeEnv boundEnv uterm A right) : left = right := by
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
              cases functionEquality.typing.1.unique leftFunction.typing
              cases functionEquality.typing.2.unique rightFunction.typing
              rw [ihf boundEnv leftFunction rightFunction,
                ihx boundEnv leftArgument rightArgument]
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
              let argument := Classical.choose (argumentTyping.eval_exists freeEnv boundEnv)
              have chosenArgument := Classical.choose_spec
                (argumentTyping.eval_exists freeEnv boundEnv)
              have argumentValue := chosenArgument.unique argumentEval
              subst argumentValue
              let sourceEnv := extendBoundEnv argument boundEnv
              have substitutions : EnvSubstitution _ _ (Fin.cases x .bv)
                  freeEnv sourceEnv boundEnv := by
                intro i
                refine Fin.cases ?_ (fun j => ?_) i
                · intro hi
                  change Eval _ freeEnv boundEnv x _ argument
                  exact argumentEval
                · intro hi
                  exact .bv freeEnv boundEnv hi rfl
              have opened := bodyTyping.eval_instantiate (bodyEval argument) substitutions
              exact opened.unique rightEval
  | eta name fresh functionTyping etaTyping =>
      cases leftEval with
      | lam domainKinded etaBody =>
          funext argument
          have weakened := rightEval.rename (ρ := Fin.succ)
            (target := extendBoundEnv argument boundEnv) (fun _ => rfl) (by
              intro i B lookup
              rfl)
          have argumentEval := Eval.bv freeEnv (i := 0)
            (extendBoundEnv argument boundEnv) domainKinded rfl
          obtain ⟨domain, bodyFunctionValue, bodyArgumentValue,
              bodyFunction, bodyArgument, output⟩ := (etaBody argument).app_inv
          cases weakened.typing.unique bodyFunction.typing
          have hf := bodyFunction.unique weakened
          have ha := bodyArgument.unique argumentEval
          cases hf
          cases ha
          exact output

def HypsTrue {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {depth : Nat} {Γ : BoundCtx Sig depth} (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ)
    (hypotheses : List (Tm Sig depth)) : Prop :=
  ∀ p, p ∈ hypotheses → Eval Γ freeEnv boundEnv p .boolTy true

def Entails {Sig : Signature} [SigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {depth : Nat} {Γ : BoundCtx Sig depth} (hypotheses : List (Tm Sig depth))
    (conclusion : Tm Sig depth) : Prop :=
  ∀ (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ),
    HypsTrue freeEnv boundEnv hypotheses → Eval Γ freeEnv boundEnv conclusion .boolTy true

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem Proves.sound {Sig : Signature} [SigTyping Sig] [UniqueSigTyping Sig]
    [FamilyModel Sig] [TermModel Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {H : List (Tm Sig depth)} {p : Tm Sig depth}
    (proof : Proves Γ H p) : Entails (Γ := Γ) H p := by
  intro freeEnv boundEnv hypotheses
  induction proof with
  | hyp typed member => exact hypotheses _ member
  | truth typed => exact .boolean true
  | falseElim typed hp falseProof ih =>
      have impossible := ih boundEnv hypotheses
      exact False.elim (Bool.noConfusion (impossible.unique (.boolean false)))
  | boolCases typed hp leftTyped rightTyped leftProof rightProof ihLeft ihRight =>
      obtain ⟨value, valueEval⟩ := hp.eval_exists freeEnv boundEnv
      cases value with
      | false =>
          apply ihRight boundEnv
          intro proposition member
          rcases List.mem_cons.mp member with rfl | member
          · exact .eqTrue .boolTy valueEval (.boolean false) rfl
          · exact hypotheses _ member
      | true =>
          apply ihLeft boundEnv
          intro proposition member
          rcases List.mem_cons.mp member with rfl | member
          · exact valueEval
          · exact hypotheses _ member
  | eqRefl typed hA hx =>
      obtain ⟨value, evaluation⟩ := hx.eval_exists freeEnv boundEnv
      exact .eqTrue hA evaluation evaluation rfl
  | eqMp typed hA hp hx hy equality application ihEquality ihApplication =>
      have equalityTrue := ihEquality boundEnv hypotheses
      have applicationTrue := ihApplication boundEnv hypotheses
      obtain ⟨left, right, leftEval, rightEval, equal⟩ := equalityTrue.eq_true_inv
      obtain ⟨domain, function, argument, functionEval, argumentEval, applied⟩ :=
        applicationTrue.app_inv
      cases hp.unique functionEval.typing
      cases hx.unique argumentEval.typing
      have argumentEqual := argumentEval.unique leftEval
      have output : applyValue function right = true := by
        rw [← equal, ← argumentEqual]
        exact applied.symm
      exact output ▸ Eval.app functionEval rightEval
  | choice typed hA hp hx application ih =>
      have applicationTrue := ih boundEnv hypotheses
      obtain ⟨domain, predicate, witness, predicateEval, witnessEval, holds⟩ :=
        applicationTrue.app_inv
      cases hp.unique predicateEval.typing
      cases hx.unique witnessEval.typing
      have selected := Eval.eps hA predicateEval
      have chosenTrue := chooseValue_spec predicate witness holds.symm
      exact chosenTrue ▸ Eval.app predicateEval selected
  | @generalize depth Γ H A body typed hA bodyTyping premise ih =>
      let left : DenoteTy (.arr A .boolTy) := fun argument =>
        Classical.choose (bodyTyping.eval_exists freeEnv (extendBoundEnv argument boundEnv))
      have leftEval : Eval Γ freeEnv boundEnv (.lam A body) (.arr A .boolTy) left :=
        .lam hA fun argument =>
          Classical.choose_spec
            (bodyTyping.eval_exists freeEnv (extendBoundEnv argument boundEnv))
      let right : DenoteTy (.arr A .boolTy) := fun _ => true
      have rightEval : Eval Γ freeEnv boundEnv (.lam A (.bool true))
          (.arr A .boolTy) right := .lam hA fun _ => .boolean true
      have equal : left = right := by
        funext argument
        have lifted : HypsTrue freeEnv (extendBoundEnv argument boundEnv) (H.map weaken) := by
          intro proposition member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact (hypotheses original originalMember).rename (ρ := Fin.succ)
            (target := extendBoundEnv argument boundEnv) (fun _ => rfl) (by
              intro i B lookup
              rfl)
        have bodyTrue := ih (extendBoundEnv argument boundEnv) lifted
        exact (Classical.choose_spec
          (bodyTyping.eval_exists freeEnv (extendBoundEnv argument boundEnv))).unique bodyTrue
      exact .eqTrue (.arr hA .boolTy) leftEval rightEval equal
  | convert typed equality premise ih =>
      have premiseTrue := ih boundEnv hypotheses
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
        · have impossible := ihRight boundEnv (by
            intro r member
            rcases List.mem_cons.mp member with equal | member
            · subst r; exact rightEval
            · exact hypotheses _ member)
          exact False.elim (Bool.noConfusion (impossible.unique leftEval))
        · have impossible := ihLeft boundEnv (by
            intro r member
            rcases List.mem_cons.mp member with equal | member
            · subst r; exact leftEval
            · exact hypotheses _ member)
          exact False.elim (Bool.noConfusion (impossible.unique rightEval))
      exact .eqTrue .boolTy leftEval rightEval equal
  | absRep typed hA hp hx =>
      obtain ⟨value, valueEval⟩ := hx.eval_exists freeEnv boundEnv
      exact .eqTrue (.sub hA hp) (.abs hA hp (.rep hA hp valueEval)) valueEval rfl
  | repAbs typed hA hp hx predicateTyping predicateProof ih =>
      obtain ⟨value, valueEval⟩ := hx.eval_exists freeEnv boundEnv
      exact .eqTrue hA (.rep hA hp (.abs hA hp valueEval)) valueEval rfl

end Nucleus.Hol
