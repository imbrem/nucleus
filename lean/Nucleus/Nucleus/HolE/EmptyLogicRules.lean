import Nucleus.HolE.EmptyLogic
import Nucleus.HolE.Cut

/-!
# Derived proof rules for checked empty-signature HOL

The connectives in `EmptyLogic` are definitions.  This file derives their
ordinary proof rules from the small HOL kernel, keeping the derivations over
intrinsically checked terms.  These rules are reusable by object-language
constructions such as Ethane's subtype package.
-/

namespace Nucleus.HolE.Empty

open Nucleus.HolE

set_option relaxedAutoImplicit true

@[simp] theorem finCasesOne {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 1) → α) : Fin.cases zero succ 1 = succ 0 :=
  Fin.cases_succ 0

@[simp] theorem finCasesTwo {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 2) → α) : Fin.cases zero succ 2 = succ 1 :=
  Fin.cases_succ 1

@[simp] theorem finCasesThree {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 3) → α) : Fin.cases zero succ 3 = succ 2 :=
  Fin.cases_succ 2

@[simp] theorem finCasesFour {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 4) → α) : Fin.cases zero succ 4 = succ 3 :=
  Fin.cases_succ 3

@[simp] theorem finCasesFive {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 5) → α) : Fin.cases zero succ 5 = succ 4 :=
  Fin.cases_succ 4

@[simp] theorem finCasesSix {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 6) → α) : Fin.cases zero succ 6 = succ 5 :=
  Fin.cases_succ 5

@[simp] theorem finCasesSeven {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 7) → α) : Fin.cases zero succ 7 = succ 6 :=
  Fin.cases_succ 6

@[simp] theorem finCasesEight {n : Nat} {α : Sort u}
    (zero : α) (succ : Fin (n + 8) → α) : Fin.cases zero succ 8 = succ 7 :=
  Fin.cases_succ 7

namespace Proof

/-- Add one unused checked proposition to the local context. -/
noncomputable def weakenHyp (proposition : BoolTm Γ)
    (proof : Proof Γ H conclusion) : Proof Γ (proposition :: H) conclusion :=
  proof.hypothesisMap (fun _ member => List.mem_cons_of_mem _ member)

def betaReduce (body : BoolTm (Γ.extend A)) (argument : Term Γ A)
    (premise : Proof Γ H (Term.app (Term.lam A body) argument)) :
    Proof Γ H (body.openBound argument) :=
  premise.convert (TermEq.beta body argument)

def betaExpand (body : BoolTm (Γ.extend A)) (argument : Term Γ A)
    (premise : Proof Γ H (body.openBound argument)) :
    Proof Γ H (Term.app (Term.lam A body) argument) :=
  premise.convert (TermEq.beta body argument).symm

def eqFromLeftBody (left : Term Γ A) : BoolTm (Γ.extend A) :=
  Term.eq A (left.weaken A) (Term.bvAs (Γ.extend A) 0 A (by
    simp [Ctx.extend, extendBound]))

def eqToRightBody (right : Term Γ A) : BoolTm (Γ.extend A) :=
  Term.eq A (Term.bvAs (Γ.extend A) 0 A (by
    simp [Ctx.extend, extendBound])) (right.weaken A)

def boolIdentityBody (Γ : Ctx types depth) : BoolTm (Γ.extend FamK.boolTy) :=
  Term.bvAs (Γ.extend FamK.boolTy) 0 FamK.boolTy (by
    simp [Ctx.extend, extendBound])

@[simp] theorem eqFromLeftBody_open (left argument : Term Γ A) :
    (eqFromLeftBody left).openBound argument = Term.eq A left argument := by
  apply Term.ext_raw
  change HolE.openBound
      (.eq A.raw (HolE.weaken left.raw) (.bv 0)) argument.raw =
    .eq A.raw left.raw argument.raw
  simp [HolE.openBound, HolE.instantiate]

@[simp] theorem eqToRightBody_open (right argument : Term Γ A) :
    (eqToRightBody right).openBound argument = Term.eq A argument right := by
  apply Term.ext_raw
  change HolE.openBound
      (.eq A.raw (.bv 0) (HolE.weaken right.raw)) argument.raw =
    .eq A.raw argument.raw right.raw
  simp [HolE.openBound, HolE.instantiate]

@[simp] theorem boolIdentityBody_open (proposition : BoolTm Γ) :
    (boolIdentityBody Γ).openBound proposition = proposition := by
  apply Term.ext_raw
  change HolE.openBound (.bv 0) proposition.raw = proposition.raw
  simp [HolE.openBound]

/-- Symmetry of object-language equality. -/
noncomputable def eqSymm (left right : Term Γ A)
    (equality : Proof Γ H (Term.eq A left right)) :
    Proof Γ H (Term.eq A right left) := by
  let body := eqToRightBody left
  let predicate := Term.lam A body
  have atLeft : Proof Γ H (body.openBound left) := by
    simpa [body] using (eqRefl (H := H) left)
  have predicateAtLeft : Proof Γ H (Term.app predicate left) :=
    betaExpand body left atLeft
  have predicateAtRight : Proof Γ H (Term.app predicate right) :=
    eqMp predicate left right equality predicateAtLeft
  simpa [body] using betaReduce body right predicateAtRight

/-- Transitivity of object-language equality. -/
noncomputable def eqTrans (left middle right : Term Γ A)
    (first : Proof Γ H (Term.eq A left middle))
    (second : Proof Γ H (Term.eq A middle right)) :
    Proof Γ H (Term.eq A left right) := by
  let body := eqFromLeftBody left
  let predicate := Term.lam A body
  have atMiddle : Proof Γ H (body.openBound middle) := by
    simpa [body] using first
  have predicateAtMiddle : Proof Γ H (Term.app predicate middle) :=
    betaExpand body middle atMiddle
  have predicateAtRight : Proof Γ H (Term.app predicate right) :=
    eqMp predicate middle right second predicateAtMiddle
  simpa [body] using betaReduce body right predicateAtRight

def appFromLeftBody (function : Term Γ (A.arr B)) (argument : Term Γ A) :
    BoolTm (Γ.extend (A.arr B)) :=
  let varied : Term (Γ.extend (A.arr B)) (A.arr B) :=
    Term.bvAs (Γ.extend (A.arr B)) 0 (A.arr B) (by
      simp [Ctx.extend, extendBound])
  Term.eq B (Term.app function argument |>.weaken (A.arr B))
    (Term.app varied (argument.weaken (A.arr B)))

@[simp] theorem appFromLeftBody_open (function varied : Term Γ (A.arr B))
    (argument : Term Γ A) :
    (appFromLeftBody function argument).openBound varied =
      Term.eq B (Term.app function argument) (Term.app varied argument) := by
  apply Term.ext_raw
  change HolE.openBound
      (.eq B.raw (HolE.weaken (.app function.raw argument.raw))
        (.app (.bv 0) (HolE.weaken argument.raw))) varied.raw =
    .eq B.raw (.app function.raw argument.raw) (.app varied.raw argument.raw)
  simp [HolE.openBound, HolE.instantiate]

/-- Equality is a congruence for application in its function position. -/
noncomputable def appCongr (function varied : Term Γ (A.arr B))
    (argument : Term Γ A)
    (equality : Proof Γ H (Term.eq (A.arr B) function varied)) :
    Proof Γ H (Term.eq B (Term.app function argument)
      (Term.app varied argument)) := by
  let body := appFromLeftBody function argument
  let predicate := Term.lam (A.arr B) body
  have atFunction : Proof Γ H (body.openBound function) := by
    simpa [body] using (eqRefl (H := H) (Term.app function argument))
  have predicateAtFunction : Proof Γ H (Term.app predicate function) :=
    betaExpand body function atFunction
  have predicateAtVaried : Proof Γ H (Term.app predicate varied) :=
    eqMp predicate function varied equality predicateAtFunction
  simpa [body] using betaReduce body varied predicateAtVaried

/-- Eliminate Boolean equality by substitution into the identity predicate. -/
noncomputable def ofEqBool (left right : BoolTm Γ)
    (equality : Proof Γ H (Term.eq FamK.boolTy left right))
    (premise : Proof Γ H left) : Proof Γ H right := by
  let body := boolIdentityBody Γ
  let predicate := Term.lam FamK.boolTy body
  have atLeft : Proof Γ H (body.openBound left) := by
    simpa [body] using premise
  have predicateAtLeft : Proof Γ H (Term.app predicate left) :=
    betaExpand body left atLeft
  have predicateAtRight : Proof Γ H (Term.app predicate right) :=
    eqMp predicate left right equality predicateAtLeft
  simpa [body] using betaReduce body right predicateAtRight

/-- A proved Boolean is provably equal to truth. -/
noncomputable def eqTrue (premise : Proof Γ H proposition) :
    Proof Γ H (Term.eq FamK.boolTy proposition (Term.truth Γ)) :=
  antisymm proposition (Term.truth Γ)
    (truth (H := proposition :: H))
    (weakenHyp (Term.truth Γ) premise)

/-- Equality to truth can be eliminated back to the proposition. -/
noncomputable def ofEqTrue
    (equality : Proof Γ H (Term.eq FamK.boolTy proposition (Term.truth Γ))) :
    Proof Γ H proposition :=
  ofEqBool (Term.truth Γ) proposition
    (eqSymm proposition (Term.truth Γ) equality) truth

def andLeftBody (right : BoolTm Γ) : BoolTm (Γ.extend FamK.boolTy) :=
  and (Term.bvAs (Γ.extend FamK.boolTy) 0 FamK.boolTy (by
    simp [Ctx.extend, extendBound])) (right.weaken FamK.boolTy)

def andRightBody (left : BoolTm Γ) : BoolTm (Γ.extend FamK.boolTy) :=
  and (left.weaken FamK.boolTy) (Term.bvAs (Γ.extend FamK.boolTy) 0
    FamK.boolTy (by simp [Ctx.extend, extendBound]))

@[simp] theorem andLeftBody_open (right value : BoolTm Γ) :
    (andLeftBody right).openBound value = and value right := by
  apply Term.ext_raw
  simp only [andLeftBody, and, andLegacy, Term.openBound, Term.eq, Term.lam,
    Term.app, Term.bvAs, Term.bv, Term.weaken, Term.truth, Term.bool,
    HolE.openBound, HolE.instantiate]
  simp [HolE.liftSub]

@[simp] theorem andRightBody_open (left value : BoolTm Γ) :
    (andRightBody left).openBound value = and left value := by
  apply Term.ext_raw
  simp only [andRightBody, and, andLegacy, Term.openBound, Term.eq, Term.lam,
    Term.app, Term.bvAs, Term.bv, Term.weaken, Term.truth, Term.bool,
    HolE.openBound, HolE.instantiate]
  simp [HolE.liftSub]

@[simp] theorem andLhsBody_open (left right : BoolTm Γ)
    (operator : Term Γ andFunctionType) :
    (andLhsBody left right).openBound operator =
      Term.app (Term.app operator left) right := by
  apply Term.ext_raw
  change HolE.openBound
      (.app (.app (.bv 0) (HolE.weaken left.raw))
        (HolE.weaken right.raw)) operator.raw =
    .app (.app operator.raw left.raw) right.raw
  simp [HolE.openBound, HolE.instantiate]

def andLhs_apply (left right : BoolTm Γ) (operator : Term Γ andFunctionType) :
    TermEq Γ (Term.app (andLhs left right) operator)
      (Term.app (Term.app operator left) right) := by
  have reduction := TermEq.beta (andLhsBody left right) operator
  simpa [andLhs] using reduction

def firstBoolAfterFirst (first : BoolTm Γ) :
    Term Γ (FamK.boolTy.arr FamK.boolTy) :=
  Term.lam FamK.boolTy (first.weaken FamK.boolTy)

def firstBoolBody (Γ : Ctx types depth) : Term (Γ.extend FamK.boolTy)
    (FamK.boolTy.arr FamK.boolTy) :=
  firstBoolAfterFirst (Term.bvAs (Γ.extend FamK.boolTy) 0 FamK.boolTy (by
    simp [Ctx.extend, extendBound]))

def firstBool : Term Γ andFunctionType :=
  Term.lam FamK.boolTy (firstBoolBody Γ)

@[simp] theorem firstBoolBody_open (first : BoolTm Γ) :
    (firstBoolBody Γ).openBound first = firstBoolAfterFirst first := by
  apply Term.ext_raw
  simp [firstBoolBody, firstBoolAfterFirst, Term.openBound, Term.lam,
    Term.bvAs, Term.weaken, HolE.openBound, HolE.instantiate, HolE.weaken,
    HolE.liftSub]

@[simp] theorem firstBoolAfterFirst_open (first second : BoolTm Γ) :
    (first.weaken FamK.boolTy).openBound second = first := by
  apply Term.ext_raw
  exact HolE.openBound_weaken first.raw second.raw

def firstBool_apply (first second : BoolTm Γ) :
    TermEq Γ (Term.app (Term.app firstBool first) second) first := by
  have outer := TermEq.beta (firstBoolBody Γ) first
  have applied := TermEq.app outer (TermEq.refl second)
  have inner := TermEq.beta (first.weaken FamK.boolTy) second
  exact applied.trans (by simpa [firstBoolAfterFirst] using inner)

/-- The defining equation for conjunction is reflexive at `true, true`. -/
def andTrueTrue : Proof Γ H (and (Term.truth Γ) (Term.truth Γ)) := by
  rw [and_eq_view]
  simpa [andView, andRhs] using
    (eqRefl (H := H) (andLhs (Term.truth Γ) (Term.truth Γ)))

/-- Conjunction introduction derived from equality substitution. -/
noncomputable def andIntro (left : Proof Γ H p) (right : Proof Γ H q) :
    Proof Γ H (and p q) := by
  let truthValue : BoolTm Γ := Term.truth Γ
  have qTrue := eqTrue right
  have trueQ := eqSymm q truthValue qTrue
  let rightPredicate := Term.lam FamK.boolTy (andRightBody truthValue)
  have atTrue : Proof Γ H (Term.app rightPredicate truthValue) :=
    betaExpand (andRightBody truthValue) truthValue (by
      simpa using (andTrueTrue (Γ := Γ) (H := H)))
  have atQ : Proof Γ H (Term.app rightPredicate q) :=
    eqMp rightPredicate truthValue q trueQ atTrue
  have truthAndQ : Proof Γ H (and truthValue q) := by
    simpa using betaReduce (andRightBody truthValue) q atQ
  have pTrue := eqTrue left
  have trueP := eqSymm p truthValue pTrue
  let leftPredicate := Term.lam FamK.boolTy (andLeftBody q)
  have atTruth : Proof Γ H (Term.app leftPredicate truthValue) :=
    betaExpand (andLeftBody q) truthValue (by simpa using truthAndQ)
  have atP : Proof Γ H (Term.app leftPredicate p) :=
    eqMp leftPredicate truthValue p trueP atTruth
  simpa using betaReduce (andLeftBody q) p atP

/-- Left elimination for equality-defined conjunction. -/
noncomputable def andElimLeft (conjunction : Proof Γ H (and p q)) :
    Proof Γ H p := by
  rw [and_eq_view] at conjunction
  have applied := appCongr (andLhs p q) andRhs firstBool conjunction
  have leftReduction := (andLhs_apply p q firstBool).trans
    (firstBool_apply p q)
  have rightReduction :=
    (andLhs_apply (Term.truth Γ) (Term.truth Γ) firstBool).trans
      (firstBool_apply (Term.truth Γ) (Term.truth Γ))
  have first : Proof Γ H
      (Term.eq FamK.boolTy p (Term.app andRhs firstBool)) :=
    eqTrans p (Term.app (andLhs p q) firstBool)
      (Term.app andRhs firstBool)
      (eqSymm _ _ (eqOfTermEq (H := H) leftReduction)) applied
  have equality : Proof Γ H (Term.eq FamK.boolTy p (Term.truth Γ)) :=
    eqTrans p (Term.app andRhs firstBool) (Term.truth Γ) first
      (eqOfTermEq (H := H) rightReduction)
  exact ofEqTrue equality

def secondBoolBody (Γ : Ctx types depth) : Term (Γ.extend FamK.boolTy)
    (FamK.boolTy.arr FamK.boolTy) :=
  Term.lam FamK.boolTy (Term.bvAs
    ((Γ.extend FamK.boolTy).extend FamK.boolTy) 0 FamK.boolTy (by
      simp [Ctx.extend, extendBound]))

def secondBool : Term Γ andFunctionType :=
  Term.lam FamK.boolTy (secondBoolBody Γ)

@[simp] theorem secondBoolBody_open (first : BoolTm Γ) :
    (secondBoolBody Γ).openBound first =
      Term.lam FamK.boolTy (Term.bvAs (Γ.extend FamK.boolTy) 0 FamK.boolTy (by
        simp [Ctx.extend, extendBound])) := by
  apply Term.ext_raw
  simp [secondBoolBody, Term.openBound, Term.lam, Term.bvAs,
    HolE.openBound, HolE.instantiate, HolE.liftSub]

@[simp] theorem secondBoolInner_open (second : BoolTm Γ) :
    (Term.bvAs (Γ.extend FamK.boolTy) 0 FamK.boolTy (by
      simp [Ctx.extend, extendBound])).openBound second = second := by
  apply Term.ext_raw
  simp [Term.openBound, Term.bvAs, HolE.openBound]

def secondBool_apply (first second : BoolTm Γ) :
    TermEq Γ (Term.app (Term.app secondBool first) second) second := by
  have outer := TermEq.beta (secondBoolBody Γ) first
  have applied := TermEq.app outer (TermEq.refl second)
  let innerBody : BoolTm (Γ.extend FamK.boolTy) :=
    Term.bvAs (Γ.extend FamK.boolTy) 0 FamK.boolTy (by
      simp [Ctx.extend, extendBound])
  have inner := TermEq.beta innerBody second
  exact applied.trans (by simpa [innerBody] using inner)

/-- Right elimination for equality-defined conjunction. -/
noncomputable def andElimRight (conjunction : Proof Γ H (and p q)) :
    Proof Γ H q := by
  rw [and_eq_view] at conjunction
  have applied := appCongr (andLhs p q) andRhs secondBool conjunction
  have leftReduction := (andLhs_apply p q secondBool).trans
    (secondBool_apply p q)
  have rightReduction :=
    (andLhs_apply (Term.truth Γ) (Term.truth Γ) secondBool).trans
      (secondBool_apply (Term.truth Γ) (Term.truth Γ))
  have first : Proof Γ H
      (Term.eq FamK.boolTy q (Term.app andRhs secondBool)) :=
    eqTrans q (Term.app (andLhs p q) secondBool)
      (Term.app andRhs secondBool)
      (eqSymm _ _ (eqOfTermEq (H := H) leftReduction)) applied
  have equality : Proof Γ H (Term.eq FamK.boolTy q (Term.truth Γ)) :=
    eqTrans q (Term.app andRhs secondBool) (Term.truth Γ) first
      (eqOfTermEq (H := H) rightReduction)
  exact ofEqTrue equality

/-- Checked single-hypothesis cut. -/
noncomputable def cutHead (premise : Proof Γ H proposition)
    (derivation : Proof Γ (proposition :: H) conclusion) :
    Proof Γ H conclusion :=
  ⟨Nucleus.HolE.Proves.cutHead Γ.typed proposition.typing premise.raw
    derivation.raw⟩

/-- Negation introduction, with negation represented as equality to false. -/
noncomputable def notIntro (proposition : BoolTm Γ)
    (contradiction : Proof Γ (proposition :: H) (Term.falsehood Γ)) :
    Proof Γ H (not proposition) :=
  antisymm proposition (Term.falsehood Γ) contradiction
    (falseElim proposition (hyp (H := Term.falsehood Γ :: H) (by simp)))

/-- Negation elimination is equality substitution into false. -/
noncomputable def notElim (negated : Proof Γ H (not proposition))
    (premise : Proof Γ H proposition) : Proof Γ H (Term.falsehood Γ) :=
  ofEqBool proposition (Term.falsehood Γ) negated premise

/-- Classical double-negation elimination using Boolean cases. -/
noncomputable def doubleNegElim
    (premise : Proof Γ H (not (not proposition))) : Proof Γ H proposition := by
  apply boolCases proposition proposition
  · exact hyp (by simp)
  · have negated : Proof Γ (not proposition :: H) (not proposition) :=
      hyp (by simp)
    have contradiction := notElim (weakenHyp (not proposition) premise) negated
    exact falseElim proposition contradiction

/-- Left introduction for the De Morgan definition of disjunction. -/
noncomputable def orIntroLeft (premise : Proof Γ H p) : Proof Γ H (or p q) := by
  let denied := and (not p) (not q)
  apply notIntro denied
  have conjunction : Proof Γ (denied :: H) denied := hyp (by simp)
  have deniedP : Proof Γ (denied :: H) (not p) := andElimLeft conjunction
  have pProof : Proof Γ (denied :: H) p := weakenHyp denied premise
  exact notElim deniedP pProof

/-- Right introduction for the De Morgan definition of disjunction. -/
noncomputable def orIntroRight (premise : Proof Γ H q) : Proof Γ H (or p q) := by
  let denied := and (not p) (not q)
  apply notIntro denied
  have conjunction : Proof Γ (denied :: H) denied := hyp (by simp)
  have deniedQ : Proof Γ (denied :: H) (not q) := andElimRight conjunction
  have qProof : Proof Γ (denied :: H) q := weakenHyp denied premise
  exact notElim deniedQ qProof

/-- Introduction for the De Morgan definition `¬(p ∧ ¬q)`. -/
noncomputable def impIntro
    (consequence : Proof Γ (p :: H) q) : Proof Γ H (imp p q) := by
  let denied := and p (not q)
  apply notIntro denied
  have conjunction : Proof Γ (denied :: H) denied := hyp (by simp)
  have pProof : Proof Γ (denied :: H) p := andElimLeft conjunction
  have deniedQ : Proof Γ (denied :: H) (not q) := andElimRight conjunction
  have lifted : Proof Γ (p :: denied :: H) q :=
    consequence.hypothesisMap (by
      intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have qProof : Proof Γ (denied :: H) q := cutHead pProof lifted
  exact notElim deniedQ qProof

/-- Universal introduction is the primitive HOL generalization rule. -/
def forallIntro (body : BoolTm (Γ.extend A))
    (premise : Proof (Γ.extend A) (H.weaken A) body) :
    Proof Γ H (forallTm A body) :=
  generalize A body premise

/-- Existential introduction for the choice-based definition. -/
def existsIntro (body : BoolTm (Γ.extend A)) (witness : Term Γ A)
    (premise : Proof Γ H (body.openBound witness)) :
    Proof Γ H (existsTm A body) := by
  let predicate := Term.lam A body
  have atWitness : Proof Γ H (Term.app predicate witness) :=
    betaExpand body witness premise
  exact choice A predicate witness atWitness

end Proof

end Nucleus.HolE.Empty
