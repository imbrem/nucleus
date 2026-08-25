import Nucleus.Hol.Ethane.Subtype.Checked
import Nucleus.HolE.EmptyLogicRules

/-!
# Syntactic derivation of Ethane's subtype package

The old HolE subtype primitive is applied to the guarded predicate itself.
This is the key proof-theoretic detail: primitive `repAbs` then consumes
exactly the guard used by Ethane, including the empty-predicate fallback.
-/

namespace Nucleus.HolE.Empty.SubtypePackage

open Nucleus.HolE
open Nucleus.HolE.Empty

set_option relaxedAutoImplicit true

/-- Predicate application as a one-bound-variable body. -/
def predicateBody {types} (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    BoolTm (Ctx.empty.extend A) :=
  let extended := Ctx.empty.extend A
  Term.app (predicate.weaken A) (Term.bv extended 0)

@[simp] theorem predicateBody_open {types} (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (value : Term Ctx.empty A) :
    (predicateBody A predicate).openBound value = Term.app predicate value := by
  apply Term.ext_raw
  change HolE.openBound
      (.app (HolE.weaken predicate.raw) (.bv 0)) value.raw =
    .app predicate.raw value.raw
  simp [HolE.openBound, HolE.instantiate]

set_option linter.flexible false in
@[simp] theorem guardBody_open {types depth} {Γ : Ctx types depth}
    (A : Ty types) (predicate : Term Γ (A.arr FamK.boolTy))
    (value : Term Γ A) :
    (guardBody A predicate).openBound value = guard predicate value := by
  apply Term.ext_raw
  simp [guardBody, guard, Empty.existsTm, Empty.or, Empty.not, Empty.and,
    Empty.andLegacy, Term.openBound, Term.eq, Term.lam, Term.app, Term.bv,
    Term.weaken, Term.eps, Term.falsehood, Term.truth, Term.bool,
    HolE.openBound, HolE.instantiate, HolE.liftSub, HolE.weaken, HolE.rename]
  constructor
  · exact HolE.instantiate_lift_head_weaken_weaken predicate.raw value.raw
  · constructor
    · rw [HolE.rename_comp, HolE.rename_comp, HolE.rename_comp]
      apply HolE.instantiate_rename
      intro index
      simp [HolE.liftSub, HolE.liftRen, HolE.weaken]
    · rfl

set_option linter.flexible false in
@[simp] theorem guardPredicate_open {types} (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (value : Term Ctx.empty A) :
    (guardPredicate A predicate).openBound value = guard predicate value := by
  apply Term.ext_raw
  simp [guardPredicate, guardBody, guard, Empty.existsTm, Empty.or,
    Empty.not, Empty.and, Empty.andLegacy, Term.openBound, Term.eq,
    Term.lam, Term.app, Term.bv, Term.weaken, Term.eps, Term.falsehood,
    Term.truth, Term.bool, HolE.openBound, HolE.instantiate, HolE.liftSub,
    HolE.weaken, HolE.rename]
  constructor
  · exact HolE.instantiate_lift_head_weaken_weaken predicate.raw value.raw
  · constructor
    · rw [HolE.rename_comp, HolE.rename_comp]
      rw [HolE.instantiate_rename_closed_default]
      rw [HolE.rename_comp]
      exact HolE.rename_closed_unique predicate.raw _ _
    · rfl

set_option linter.flexible false in
@[simp] theorem guardPredicate_instantiate_weaken {types} (A C : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (value : Term (Ctx.empty.extend C) A) :
    (guardPredicate A predicate).instantiateOne value =
      guard (predicate.weaken C) value := by
  apply Term.ext_raw
  simp [guardPredicate, guardBody, guard, Empty.existsTm, Empty.or, Empty.not,
    Empty.and, Empty.andLegacy, Term.instantiateOne, Term.eq, Term.lam,
    Term.app, Term.bv, Term.weaken, Term.eps, Term.falsehood, Term.truth,
    Term.bool, HolE.instantiateOne, HolE.instantiate, HolE.liftSub,
    HolE.weaken, HolE.rename]
  constructor
  · rw [HolE.rename_comp]
    rw [HolE.instantiate_rename_closed_default]
    exact HolE.rename_closed_unique predicate.raw _ _
  · constructor
    · rw [HolE.rename_comp, HolE.rename_comp]
      rw [HolE.instantiate_rename_closed_default]
      exact HolE.rename_closed_unique predicate.raw _ _
    · rfl

/-- An arbitrary inhabitant of every checked HOL type. -/
def arbitrary {types depth} {Γ : Ctx types depth} (A : Ty types) : Term Γ A :=
  let body : BoolTm (Γ.extend A) := Term.falsehood (Γ.extend A)
  Term.eps A (Term.lam A body)

/-- The guarded predicate is inhabited, constructively at the HOL proof
level after Boolean case analysis on the original predicate's existential. -/
noncomputable def guardExists (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    Proof Ctx.empty [] (existsTm A (guardPredicate A predicate)) := by
  let body := predicateBody A predicate
  let originalExists := existsTm A body
  let guarded := guardPredicate A predicate
  apply Proof.boolCases originalExists (existsTm A guarded)
  · let witness := Term.eps A (Term.lam A body)
    have original : Proof Ctx.empty (originalExists :: []) originalExists :=
      Proof.hyp (by simp)
    have holds : Proof Ctx.empty (originalExists :: []) (body.openBound witness) :=
      Proof.betaReduce body witness original
    have guardedAt : Proof Ctx.empty (originalExists :: [])
        (guarded.openBound witness) := by
      rw [guardPredicate_open]
      apply Proof.orIntroLeft
      simpa [body] using holds
    exact Proof.existsIntro guarded witness guardedAt
  · let witness := arbitrary (Γ := (Ctx.empty : Ctx types 0)) A
    have absent : Proof Ctx.empty (not originalExists :: [])
        (not originalExists) := Proof.hyp (by simp)
    have guardedAt : Proof Ctx.empty (not originalExists :: [])
        (guarded.openBound witness) := by
      rw [guardPredicate_open]
      apply Proof.orIntroRight
      simpa [guard, body, originalExists, predicateBody] using absent
    exact Proof.existsIntro guarded witness guardedAt

theorem primitiveRep_weaken (A C : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    (primitiveRep A predicate).weaken C =
      primitiveRepAt (Ctx.empty.extend C) A predicate := by
  apply Term.ext_raw
  simp [primitiveRep, primitiveRepAt, Term.weaken, Term.lam, Term.rep,
    Term.bv, HolE.weaken, HolE.rename, HolE.liftRen]

theorem primitiveAbs_weaken (A C : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    (primitiveAbs A predicate).weaken C =
      primitiveAbsAt (Ctx.empty.extend C) A predicate := by
  apply Term.ext_raw
  simp [primitiveAbs, primitiveAbsAt, Term.weaken, Term.lam, Term.abs,
    Term.bv, HolE.weaken, HolE.rename, HolE.liftRen]

def primitiveRepAt_apply (Γ : Ctx types depth) (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (value : Term Γ (subViaGuard A predicate)) :
    TermEq Γ (Term.app (primitiveRepAt Γ A predicate) value)
      (Term.rep A (guardPredicate A predicate) value) := by
  let B := subViaGuard A predicate
  let body : Term (Γ.extend B) A :=
    Term.rep A (guardPredicate A predicate) (Term.bv (Γ.extend B) 0)
  have reduction := TermEq.beta body value
  have opened : body.openBound value =
      Term.rep A (guardPredicate A predicate) value := by
    apply Term.ext_raw
    simp [body, Term.openBound, Term.rep, Term.bv, HolE.openBound,
      HolE.instantiate]
  rw [opened] at reduction
  simpa [primitiveRepAt, body, B] using reduction

def primitiveAbsAt_apply (Γ : Ctx types depth) (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) (value : Term Γ A) :
    TermEq Γ (Term.app (primitiveAbsAt Γ A predicate) value)
      (Term.abs A (guardPredicate A predicate) value) := by
  let body : Term (Γ.extend A) (subViaGuard A predicate) :=
    Term.abs A (guardPredicate A predicate) (Term.bv (Γ.extend A) 0)
  have reduction := TermEq.beta body value
  have opened : body.openBound value =
      Term.abs A (guardPredicate A predicate) value := by
    apply Term.ext_raw
    simp [body, Term.openBound, Term.abs, Term.bv, HolE.openBound,
      HolE.instantiate]
  rw [opened] at reduction
  simpa [primitiveAbsAt, body] using reduction

/-- The primitive guarded subtype proves the first package law. -/
noncomputable def absRepAtProof (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    let B := subViaGuard A predicate
    Proof Ctx.empty []
      (absRepAt A B (primitiveRep A predicate) (primitiveAbs A predicate)) := by
  let B := subViaGuard A predicate
  let withB := Ctx.empty.extend B
  let b : Term withB B := Term.bv withB 0
  unfold absRepAt
  apply Proof.forallIntro
  have repReduction : TermEq withB
      (Term.app ((primitiveRep A predicate).weaken B) b)
      (Term.rep A (guardPredicate A predicate) b) := by
    rw [primitiveRep_weaken]
    exact primitiveRepAt_apply withB A predicate b
  have absAfterRep : TermEq withB
      (Term.app ((primitiveAbs A predicate).weaken B)
        (Term.app ((primitiveRep A predicate).weaken B) b))
      (Term.app ((primitiveAbs A predicate).weaken B)
        (Term.rep A (guardPredicate A predicate) b)) :=
    TermEq.app (TermEq.refl _) repReduction
  have absReduction : TermEq withB
      (Term.app ((primitiveAbs A predicate).weaken B)
        (Term.rep A (guardPredicate A predicate) b))
      (Term.abs A (guardPredicate A predicate)
        (Term.rep A (guardPredicate A predicate) b)) := by
    rw [primitiveAbs_weaken]
    exact primitiveAbsAt_apply withB A predicate _
  have composite := absAfterRep.trans absReduction
  have formula := TermEq.eq composite (TermEq.refl b)
  exact (Proof.absRep A (guardPredicate A predicate) b).convert formula.symm

/-- The guarded premise is exactly the primitive subtype predicate, so the
second package law follows from primitive `repAbs`. -/
noncomputable def repAbsAtProof (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    let B := subViaGuard A predicate
    Proof Ctx.empty []
      (repAbsAt A B predicate (primitiveRep A predicate)
        (primitiveAbs A predicate)) := by
  let B := subViaGuard A predicate
  let withA := Ctx.empty.extend A
  let a : Term withA A := Term.bv withA 0
  unfold repAbsAt
  apply Proof.forallIntro
  apply Proof.impIntro
  have guarded : Proof withA
      (guard (predicate.weaken A) a :: []) (guard (predicate.weaken A) a) :=
    Proof.hyp (by simp)
  have instanceEq : (guard (predicate.weaken A) a).raw =
      HolE.instantiateOne (guardPredicate A predicate).raw a.raw := by
    have equality := guardPredicate_instantiate_weaken A A predicate a
    exact congrArg Term.raw equality.symm
  have primitive : Proof withA (guard (predicate.weaken A) a :: [])
      (Term.eq A
        (Term.rep A (guardPredicate A predicate)
          (Term.abs A (guardPredicate A predicate) a)) a) :=
    Proof.repAbs A (guardPredicate A predicate) a
      (guard (predicate.weaken A) a) instanceEq guarded
  have absReduction : TermEq withA
      (Term.app ((primitiveAbs A predicate).weaken A) a)
      (Term.abs A (guardPredicate A predicate) a) := by
    rw [primitiveAbs_weaken]
    exact primitiveAbsAt_apply withA A predicate a
  have repAfterAbs : TermEq withA
      (Term.app ((primitiveRep A predicate).weaken A)
        (Term.app ((primitiveAbs A predicate).weaken A) a))
      (Term.app ((primitiveRep A predicate).weaken A)
        (Term.abs A (guardPredicate A predicate) a)) :=
    TermEq.app (TermEq.refl _) absReduction
  have repReduction : TermEq withA
      (Term.app ((primitiveRep A predicate).weaken A)
        (Term.abs A (guardPredicate A predicate) a))
      (Term.rep A (guardPredicate A predicate)
        (Term.abs A (guardPredicate A predicate) a)) := by
    rw [primitiveRep_weaken]
    exact primitiveRepAt_apply withA A predicate _
  have composite := repAfterAbs.trans repReduction
  have formula := TermEq.eq composite (TermEq.refl a)
  exact primitive.convert formula.symm

/-- Primitive `Sub` applied to the guard proves that every represented value
lies in that same guard. -/
noncomputable def repGuardedAtProof (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    let B := subViaGuard A predicate
    Proof Ctx.empty []
      (repGuardedAt A B predicate (primitiveRep A predicate)) := by
  let B := subViaGuard A predicate
  let withB := Ctx.empty.extend B
  let b : Term withB B := Term.bv withB 0
  let guarded := guardPredicate A predicate
  let witness := Term.eps A (Term.lam A guarded)
  unfold repGuardedAt
  apply Proof.forallIntro
  have witnessClosed : Proof Ctx.empty [] (guarded.openBound witness) := by
    apply Proof.betaReduce guarded witness
    simpa [Empty.existsTm, guarded, witness] using guardExists A predicate
  have witnessProof : Proof withB []
      ((guarded.openBound witness).weaken B) :=
    Proof.weakenBound B witnessClosed
  have witnessEq : ((guarded.openBound witness).weaken B).raw =
      HolE.instantiateOne guarded.raw (witness.weaken B).raw := by
    simp [Term.openBound, Term.weaken]
  have represented : Proof withB []
      (guard (predicate.weaken B)
        (Term.rep A guarded b)) := by
    apply Proof.repPredOfWitness A guarded (witness.weaken B)
      ((guarded.openBound witness).weaken B) witnessEq b
      (guard (predicate.weaken B) (Term.rep A guarded b))
    · exact congrArg Term.raw
        (guardPredicate_instantiate_weaken A B predicate
          (Term.rep A guarded b)).symm
    · exact witnessProof
  have reduction : TermEq withB
      (Term.app ((primitiveRep A predicate).weaken B) b)
      (Term.rep A guarded b) := by
    rw [primitiveRep_weaken]
    exact primitiveRepAt_apply withB A predicate b
  let body := guardBody A (predicate.weaken B)
  let guardFunction := Term.lam A body
  have atRepresentation : Proof withB []
      (Term.app guardFunction (Term.rep A guarded b)) :=
    Proof.betaExpand body (Term.rep A guarded b) (by
      simpa [body, guarded] using represented)
  have atApplication : Proof withB []
      (Term.app guardFunction
        (Term.app ((primitiveRep A predicate).weaken B) b)) :=
    Proof.eqMp guardFunction (Term.rep A guarded b)
      (Term.app ((primitiveRep A predicate).weaken B) b)
      (Proof.eqSymm _ _ (Proof.eqOfTermEq reduction)) atRepresentation
  simpa [body, B, b, PropCtx.weaken] using Proof.betaReduce body
    (Term.app ((primitiveRep A predicate).weaken B) b) atApplication

/-- The guarded primitive representation and abstraction satisfy the complete
three-law package. -/
noncomputable def lawsAtProof (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    let B := subViaGuard A predicate
    Proof Ctx.empty []
      (lawsAt A B predicate (primitiveRep A predicate)
        (primitiveAbs A predicate)) := by
  unfold lawsAt
  exact Proof.andIntro (absRepAtProof A predicate)
    (Proof.andIntro (repAbsAtProof A predicate)
      (repGuardedAtProof A predicate))

def packageAfterRep (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (rep : Term Ctx.empty (B.arr A)) :
    BoolTm (Ctx.empty : Ctx types 0) :=
  let absType := A.arr B
  let withAbs := Ctx.empty.extend absType
  let abs : Term withAbs absType := Term.bv withAbs 0
  existsTm absType (lawsIn A B (predicate.weaken absType)
    (rep.weaken absType) abs)

set_option linter.flexible false in
@[simp] theorem existsLaws_open_rep (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (rep : Term Ctx.empty (B.arr A)) :
    (existsTm (A.arr B) (laws A B predicate)).openBound rep =
      packageAfterRep A B predicate rep := by
  apply Term.ext_raw
  simp [packageAfterRep, lawsIn, absRepIn, repAbsIn, repGuardedIn,
    laws, absRepLaw, repAbsLaw, repGuardedLaw, representation, abstraction,
    LawCtx, guard, Empty.existsTm, Empty.forallTm, Empty.imp, Empty.or,
    Empty.not, Empty.and, Empty.andLegacy, Term.openBound, Term.eq,
    Term.lam, Term.app, Term.bv, Term.weaken, Term.eps, Term.falsehood,
    Term.truth, Term.bool, HolE.openBound, HolE.instantiate, HolE.liftSub,
    HolE.liftRen, HolE.weaken, HolE.rename, HolE.rename_comp,
    Fin.cases_succ, Ctx.extend, extendBound]
  repeat' apply And.intro
  all_goals
    try simp [Fin.cases_succ, Fin.cases_succ', HolE.rename_comp]
    first | rfl | apply HolE.rename_closed_unique

set_option linter.flexible false in
@[simp] theorem lawsIn_open_abs (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (rep : Term Ctx.empty (B.arr A)) (abs : Term Ctx.empty (A.arr B)) :
    let withAbs := Ctx.empty.extend (A.arr B)
    (lawsIn A B (predicate.weaken (A.arr B)) (rep.weaken (A.arr B))
      (Term.bv withAbs 0)).openBound abs =
      lawsAt A B predicate rep abs := by
  apply Term.ext_raw
  simp [lawsIn, absRepIn, repAbsIn, repGuardedIn, lawsAt, absRepAt,
    repAbsAt, repGuardedAt, guard, Empty.existsTm, Empty.forallTm,
    Empty.imp, Empty.or, Empty.not, Empty.and, Empty.andLegacy,
    Term.openBound, Term.eq, Term.lam, Term.app, Term.bv, Term.weaken,
    Term.eps, Term.falsehood, Term.truth, Term.bool, HolE.openBound,
    HolE.instantiate, HolE.liftSub, HolE.liftRen, HolE.weaken, HolE.rename,
    HolE.rename_comp, Fin.cases_succ, Ctx.extend, extendBound]
  repeat' apply And.intro
  all_goals
    try simp [Fin.cases_succ, Fin.cases_succ', HolE.rename_comp]
    first | rfl | apply HolE.rename_closed_unique

/-- The primitive guarded subtype supplies the existential representation and
abstraction package for its carrier. -/
noncomputable def packageAtProof (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    let B := subViaGuard A predicate
    Proof Ctx.empty [] (packageAt A B predicate) := by
  let B := subViaGuard A predicate
  unfold packageAt
  apply Proof.existsIntro _ (primitiveRep A predicate)
  rw [existsLaws_open_rep]
  unfold packageAfterRep
  apply Proof.existsIntro _ (primitiveAbs A predicate)
  rw [lawsIn_open_abs]
  exact lawsAtProof A predicate

@[simp] theorem predicate_openType (A : Ty types)
    (P : Term Ctx.empty (A.arr FamK.boolTy)) (B : Ty types) :
    (Term.openEmpty (predicate A P)).openType B = packageAt A B P := by
  apply Term.ext_raw
  simp [Term.openEmpty_raw, predicate, packageAt, weakenFam, renameFam, weakenClosedTerm,
    renameClosedTerm, FamK.bv, Term.openType, Term.eq, Term.lam, Term.app,
    Term.bv, Term.weaken, Term.eps, Term.falsehood,
    Term.truth, Term.bool, laws, absRepLaw, repAbsLaw, repGuardedLaw,
    representation, abstraction, LawCtx, guard, Empty.existsTm,
    Empty.forallTm, Empty.imp, Empty.or, Empty.not, Empty.and,
    Empty.andLegacy, HolE.openType, HolE.instantiateTypes, HolE.headTySub]

/-- Every checked predicate has an Ethane model package.  This is the exact
sentence used by the native `Model` rule. -/
noncomputable def existsTypeProof (A : Ty types)
    (P : Term Ctx.empty (A.arr FamK.boolTy)) :
    Proof Ctx.empty [] (existsType A P) := by
  unfold existsType
  apply Proof.tyExistsIntro (Term.openEmpty (predicate A P)) (subViaGuard A P)
  rw [predicate_openType]
  exact packageAtProof A P

end Nucleus.HolE.Empty.SubtypePackage
