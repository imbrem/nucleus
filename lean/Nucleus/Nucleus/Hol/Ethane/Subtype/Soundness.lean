import Nucleus.Hol.Ethane.Subtype.Checked
import Nucleus.Hol.Ethane.Subtype.Semantics
import Nucleus.HolE.EmptySemantics
import Nucleus.HolE.ClassicalFamilySoundness

/-!
# Soundness of Ethane's object-language subtype package

The guarded subtype is used only as a semantic witness.  Ethane itself keeps
`Model` as its sole type former beyond ordinary HOL.
-/

namespace Nucleus.HolE.Empty.SubtypePackage

open Nucleus.HolE

set_option relaxedAutoImplicit true

noncomputable section

private abbrev weakRen {types : List Kind} : TyRen types (.star :: types) :=
  fun index => .succ index

private def starValue (candidate : CPointed) : CDenoteKind .star := by
  change CPointed
  exact candidate

private theorem extended_rename_weak
    (candidate : CPointed) (env : CTypeEnv types) :
    (extendCTypeEnv (starValue candidate) env).rename
      (weakRen (types := types)) = env := by
  funext kind index
  rfl

/-- Weakening a checked family past a fresh type variable does not change its
denotation. -/
theorem denote_weakenFam (family : Ty types)
    (candidate : CPointed) (env : CTypeEnv types) :
    (weakenFam (domain := .star) family).denote
      (extendCTypeEnv (starValue candidate) env) = family.denote env := by
  let renamed := family.kinded.certificate.renameTypes
    (weakRen (types := types))
  let clean := (weakenFam (domain := .star) family).kinded.certificate
  have normalized := cSem_kind_normalize (weakRen (types := types)) renamed
    (weakenFam (domain := .star) family).raw (by rfl) clean
    (extendCTypeEnv (starValue candidate) env)
  change (show CPointed from
      cSem renamed (extendCTypeEnv (starValue candidate) env)) =
    cSem clean (extendCTypeEnv (starValue candidate) env) at normalized
  have semantic : cSem renamed (extendCTypeEnv (starValue candidate) env) =
      cSem family.kinded.certificate
        ((extendCTypeEnv (starValue candidate) env).rename
          (weakRen (types := types))) := by
    simpa only [CRenameEq, Classification.rename, CResult] using
      (cSem_renameTypes family.kinded.certificate
        (weakRen (types := types))
        (extendCTypeEnv (starValue candidate) env))
  let middle : CPointed :=
    show CPointed from cSem renamed (extendCTypeEnv (starValue candidate) env)
  have toMiddle : cSem clean (extendCTypeEnv (starValue candidate) env) =
      middle := normalized.symm
  have fromMiddle : middle = cSem family.kinded.certificate
      ((extendCTypeEnv (starValue candidate) env).rename
        (weakRen (types := types))) := semantic
  have finish : cSem family.kinded.certificate
      ((extendCTypeEnv (starValue candidate) env).rename
        (weakRen (types := types))) = cSem family.kinded.certificate env := by
    rw [extended_rename_weak]
  exact toMiddle.trans (fromMiddle.trans finish)

/-- Weakening a closed checked term past a fresh type variable preserves its
value under an extended type environment. -/
theorem Eval.weakenClosedTerm
    (term : Term (Ctx.empty : Ctx types 0) A)
    (candidate : CPointed) (env : CTypeEnv types)
    (expected : CPointed) (value : expected.carrier)
    (evaluation : Eval term env emptyCBoundEnv expected value) :
    Eval (weakenClosedTerm (domain := .star) term)
      (extendCTypeEnv (starValue candidate) env)
      emptyCBoundEnv expected value := by
  unfold Eval Infinity.IEval at evaluation ⊢
  intro checking
  simp only [Ctx.empty, Term.toIntrinsic] at checking ⊢
  let source : CHasType emptyBound term.raw A.raw := by
    simpa [Ctx.empty] using term.typing.certificate
  let renamed := source.renameTypes
    (weakRen (types := types))
  let clean : CHasType emptyBound
      (Nucleus.HolE.Empty.SubtypePackage.weakenClosedTerm
        (domain := .star) term).raw
      (weakenFam (domain := .star) A).raw := by
    simpa [Ctx.empty] using checking
  have normalized := cSem_tm_normalize (weakRen (types := types)) renamed
    emptyBound (renameBoundCtx_empty _) clean
    (extendCTypeEnv (starValue candidate) env)
  let Result := CBoundEnv 0 → (expected : CPointed) →
    ULift.{1, 0} expected.carrier
  change (show Result from
      cSem renamed (extendCTypeEnv (starValue candidate) env)) =
    cSem clean (extendCTypeEnv (starValue candidate) env) at normalized
  have semantic : cSem renamed (extendCTypeEnv (starValue candidate) env) =
      cSem source ((extendCTypeEnv (starValue candidate) env).rename
        (weakRen (types := types))) := by
    simpa only [CRenameEq, Classification.rename, CResult] using
      (cSem_renameTypes source (weakRen (types := types))
        (extendCTypeEnv (starValue candidate) env))
  let middle : Result :=
    show Result from cSem renamed (extendCTypeEnv (starValue candidate) env)
  have combined : cSem clean (extendCTypeEnv (starValue candidate) env) =
      cSem source env := by
    have toMiddle : cSem clean (extendCTypeEnv (starValue candidate) env) =
        middle := normalized.symm
    have fromMiddle : middle = cSem source
        ((extendCTypeEnv (starValue candidate) env).rename
          (weakRen (types := types))) := semantic
    have finish : cSem source
        ((extendCTypeEnv (starValue candidate) env).rename
          (weakRen (types := types))) = cSem source env := by
      rw [extended_rename_weak]
    exact toMiddle.trans (fromMiddle.trans finish)
  have atValue := congrFun (congrFun combined emptyCBoundEnv) expected
  rw [cSem_certificate_coherent checking clean]
  exact atValue.trans (evaluation term.typing.certificate)

/-- Exact Boolean meaning of the object-language guarded predicate. -/
theorem Eval.guard_value {depth : Nat} {Γ : Ctx types depth} {A : Ty types}
    (predicate : Term Γ (A.arr FamK.boolTy)) (value : Term Γ A)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (meaning : (A.denote env).carrier → Bool)
    (actual : (A.denote env).carrier)
    (predicateEval : Eval predicate env bound
      ⟨(A.denote env).carrier → Bool, fun _ => false⟩ meaning)
    (valueEval : Eval value env bound (A.denote env) actual) :
    Eval (guard predicate value) env bound cBool
      (meaning actual || Bool.not (Eval.existsBool meaning)) := by
  classical
  let extended := Γ.extend A
  let witness : Term extended A :=
    Term.bvAs extended 0 A (by simp [extended, Ctx.extend, extendBound])
  let holdsWitness : BoolTm extended :=
    Term.app (predicate.weaken A) witness
  let inhabited : BoolTm Γ := Empty.existsTm A holdsWitness
  have predicateWeakened : ∀ argument : (A.denote env).carrier,
      Eval (predicate.weaken A) env
        (extendCBoundEnv (A.denote env) argument bound)
        ⟨(A.denote env).carrier → Bool, fun _ => false⟩ meaning :=
    fun argument => Eval.weaken predicate A env bound argument
      ⟨(A.denote env).carrier → Bool, fun _ => false⟩ meaning predicateEval
  have witnessEval : ∀ argument : (A.denote env).carrier,
      Eval witness env (extendCBoundEnv (A.denote env) argument bound)
        (A.denote env) argument := by
    intro argument
    apply Eval.bvAs extended 0 A
      (by simp [extended, Ctx.extend, extendBound]) env _ (A.denote env) argument
    exact (extendCBoundEnv_zero (A.denote env) argument bound (A.denote env)).trans
      (alignCValue_self (A.denote env) argument)
  have bodyEval : ∀ argument : (A.denote env).carrier,
      Eval holdsWitness env (extendCBoundEnv (A.denote env) argument bound)
        cBool (meaning argument) := by
    intro argument
    exact Eval.appBool (predicate.weaken A) witness env _ meaning argument
      (predicateWeakened argument) (witnessEval argument)
  have inhabitedEval : Eval inhabited env bound cBool (Eval.existsBool meaning) :=
    Eval.existsTm_value A holdsWitness env bound meaning bodyEval
  have notInhabitedEval : Eval (Empty.not inhabited) env bound cBool
      (!Eval.existsBool meaning) :=
    Eval.not_value inhabited env bound _ inhabitedEval
  have holdsEval : Eval (Term.app predicate value) env bound cBool
      (meaning actual) :=
    Eval.appBool predicate value env bound meaning actual predicateEval valueEval
  have disjunction := Eval.or_value (Term.app predicate value)
    (Empty.not inhabited) env bound (meaning actual) (!Eval.existsBool meaning)
    holdsEval notInhabitedEval
  exact Eval.congr_raw
    (left := Empty.or (Term.app predicate value) (Empty.not inhabited))
    (right := guard predicate value) (by rfl) disjunction

/-- The object-language guard is true on every value admitted by the semantic
guarded predicate. -/
theorem Eval.guard_true {depth : Nat} {Γ : Ctx types depth} {A : Ty types}
    (predicate : Term Γ (A.arr FamK.boolTy)) (value : Term Γ A)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (meaning : (A.denote env).carrier → Bool)
    (actual : (A.denote env).carrier)
    (predicateEval : Eval predicate env bound
      ⟨(A.denote env).carrier → Bool, fun _ => false⟩ meaning)
    (valueEval : Eval value env bound (A.denote env) actual)
    (valid : CGuarded meaning actual) :
    Eval (guard predicate value) env bound cBool true := by
  classical
  have evaluation := guard_value predicate value env bound meaning actual
    predicateEval valueEval
  have result :
      (meaning actual || Bool.not (Eval.existsBool meaning)) = true := by
    rcases valid with holds | empty
    · simp [holds]
    · have noWitness : Eval.existsBool meaning = false := by
        simp [Eval.existsBool, empty]
      simp [noWitness]
  rw [result] at evaluation
  exact evaluation

/-- Failure of the semantic guard is represented by Boolean false. -/
theorem Eval.guard_false {depth : Nat} {Γ : Ctx types depth} {A : Ty types}
    (predicate : Term Γ (A.arr FamK.boolTy)) (value : Term Γ A)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (meaning : (A.denote env).carrier → Bool)
    (actual : (A.denote env).carrier)
    (predicateEval : Eval predicate env bound
      ⟨(A.denote env).carrier → Bool, fun _ => false⟩ meaning)
    (valueEval : Eval value env bound (A.denote env) actual)
    (invalid : ¬CGuarded meaning actual) :
    Eval (guard predicate value) env bound cBool false := by
  classical
  have evaluation := guard_value predicate value env bound meaning actual
    predicateEval valueEval
  have noHold : meaning actual = false := by
    cases holds : meaning actual
    · rfl
    · exact False.elim (invalid (Or.inl holds))
  have hasWitness : ∃ witness, meaning witness = true := by
    exact Classical.byContradiction (fun none => invalid (Or.inr none))
  have existsTrue : Eval.existsBool meaning = true := by
    simp [Eval.existsBool, hasWitness]
  rw [noHold, existsTrue] at evaluation
  simpa using evaluation

/-- Bound environment used to interpret `laws`: representation is index one
and abstraction is index zero. -/
noncomputable abbrev packageRepHead (A B : Ty types) (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env)) :
    ((B.arr A).denote env).carrier :=
  alignCValue (cArrow (B.denote env) (A.denote env))
    ((B.arr A).denote env) package.rep

noncomputable abbrev packageAbsHead (A B : Ty types) (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env)) :
    ((A.arr B).denote env).carrier :=
  alignCValue (cArrow (A.denote env) (B.denote env))
    ((A.arr B).denote env) package.abs

noncomputable def packageBound (A B : Ty types) (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env)) : CBoundEnv 2 :=
  let repType := (B.arr A).denote env
  let absType := (A.arr B).denote env
  extendCBoundEnv absType (packageAbsHead A B env meaning package)
    (extendCBoundEnv repType (packageRepHead A B env meaning package)
      emptyCBoundEnv)

@[simp] theorem packageBound_zero (A B : Ty types) (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env)) :
    packageBound A B env meaning package 0
      (cArrow (A.denote env) (B.denote env)) = package.abs := by
  unfold packageBound
  rw [extendCBoundEnv_zero]
  exact alignCValue_roundtrip (FamK.denote_arr A B env).symm package.abs

@[simp] theorem packageBound_one (A B : Ty types) (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env)) :
    packageBound A B env meaning package 1
      (cArrow (B.denote env) (A.denote env)) = package.rep := by
  change packageBound A B env meaning package (Fin.succ (0 : Fin 1))
    (cArrow (B.denote env) (A.denote env)) = package.rep
  unfold packageBound
  rw [extendCBoundEnv_succ, extendCBoundEnv_zero]
  exact alignCValue_roundtrip (FamK.denote_arr B A env).symm package.rep

theorem Eval.representation (A B : Ty types) (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env)) :
    Eval (SubtypePackage.representation A B) env
      (packageBound A B env meaning package)
      (cArrow (B.denote env) (A.denote env)) package.rep := by
  let boundVar : Term (LawCtx A B) (B.arr A) :=
    Term.bvAs (LawCtx A B) (Fin.succ 0) (B.arr A)
      (by rfl)
  have evaluation := Eval.bvAs (LawCtx A B) (Fin.succ 0) (B.arr A)
    (by rfl) env
    (packageBound A B env meaning package)
    (cArrow (B.denote env) (A.denote env)) package.rep
    (packageBound_one A B env meaning package)
  exact Eval.congr_raw (left := boundVar)
    (right := SubtypePackage.representation A B) (by rfl) evaluation

theorem Eval.abstraction (A B : Ty types) (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env)) :
    Eval (SubtypePackage.abstraction A B) env
      (packageBound A B env meaning package)
      (cArrow (A.denote env) (B.denote env)) package.abs := by
  let boundVar : Term (LawCtx A B) (A.arr B) :=
    Term.bvAs (LawCtx A B) 0 (A.arr B)
      (by simp [LawCtx, Ctx.extend, extendBound])
  have evaluation := Eval.bvAs (LawCtx A B) 0 (A.arr B)
    (by simp [LawCtx, Ctx.extend, extendBound]) env
    (packageBound A B env meaning package)
    (cArrow (A.denote env) (B.denote env)) package.abs
    (packageBound_zero A B env meaning package)
  exact Eval.congr_raw (left := boundVar)
    (right := SubtypePackage.abstraction A B) (by rfl) evaluation

theorem Eval.absRepLaw_true (A B : Ty types) (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env)) :
    Eval (absRepLaw A B) env (packageBound A B env meaning package)
      cBool true := by
  let base := LawCtx A B
  let withB := base.extend B
  let bTm : Term withB B := Term.bvAs withB 0 B (by rfl)
  let repB := Term.app ((SubtypePackage.representation A B).weaken B) bTm
  let absRepB := Term.app ((SubtypePackage.abstraction A B).weaken B) repB
  let body := Term.eq B absRepB bTm
  let quantified := Empty.forallTm B body
  have quantifiedTrue : Eval quantified env (packageBound A B env meaning package)
      cBool true := by
    apply Eval.forallTm B body env (packageBound A B env meaning package)
    intro b
    let extendedBound := extendCBoundEnv (B.denote env) b
      (packageBound A B env meaning package)
    have bEval : Eval bTm env extendedBound (B.denote env) b := by
      apply Eval.bvAs withB 0 B rfl env extendedBound (B.denote env) b
      exact (extendCBoundEnv_zero (B.denote env) b
        (packageBound A B env meaning package) (B.denote env)).trans
        (alignCValue_self (B.denote env) b)
    have repEval := Eval.representation A B env meaning package
    have repWeak : Eval ((SubtypePackage.representation A B).weaken B)
        env extendedBound (cArrow (B.denote env) (A.denote env)) package.rep :=
      Eval.weaken (SubtypePackage.representation A B) B env
        (packageBound A B env meaning package) b
        (cArrow (B.denote env) (A.denote env)) package.rep repEval
    have absEval := Eval.abstraction A B env meaning package
    have absWeak : Eval ((SubtypePackage.abstraction A B).weaken B)
        env extendedBound (cArrow (A.denote env) (B.denote env)) package.abs :=
      Eval.weaken (SubtypePackage.abstraction A B) B env
        (packageBound A B env meaning package) b
        (cArrow (A.denote env) (B.denote env)) package.abs absEval
    have repBEval : Eval repB env extendedBound (A.denote env)
        (package.rep b) :=
      Eval.app ((SubtypePackage.representation A B).weaken B) bTm env
        extendedBound package.rep b repWeak bEval
    have absRepEval : Eval absRepB env extendedBound (B.denote env)
        (package.abs (package.rep b)) :=
      Eval.app ((SubtypePackage.abstraction A B).weaken B) repB env
        extendedBound package.abs (package.rep b) absWeak repBEval
    have equality := Eval.eq B absRepB bTm env extendedBound
      (package.abs (package.rep b)) b absRepEval bEval
    have equalsTrue : Infinity.classicalEqBool (package.abs (package.rep b)) b =
        true := by
      simp [Infinity.classicalEqBool, package.absRep b]
    rw [equalsTrue] at equality
    exact equality
  exact Eval.congr_raw (left := quantified) (right := absRepLaw A B)
    (by rfl) quantifiedTrue

/-- A closed package predicate keeps its meaning after the two law-context
binders are introduced. -/
theorem Eval.predicate_in_lawCtx (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env))
    (predicateEval : Eval predicate env emptyCBoundEnv
      (cArrow (A.denote env) cBool) meaning) :
    Eval (predicate.weaken (B.arr A) |>.weaken (A.arr B)) env
      (packageBound A B env meaning package)
      (cArrow (A.denote env) cBool) meaning := by
  let repType := B.arr A
  let absType := A.arr B
  let repSemantic := cArrow (B.denote env) (A.denote env)
  let absSemantic := cArrow (A.denote env) (B.denote env)
  let repHead : (repType.denote env).carrier :=
    alignCValue repSemantic (repType.denote env) package.rep
  let absHead : (absType.denote env).carrier :=
    alignCValue absSemantic (absType.denote env) package.abs
  have first := Eval.weaken predicate repType env emptyCBoundEnv repHead
    (cArrow (A.denote env) cBool) meaning predicateEval
  have second := Eval.weaken (predicate.weaken repType) absType env
    (extendCBoundEnv (repType.denote env) repHead emptyCBoundEnv) absHead
    (cArrow (A.denote env) cBool) meaning first
  simpa [packageBound, repType, absType, repSemantic, absSemantic,
    repHead, absHead] using second

theorem Eval.repAbsLaw_true (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env))
    (predicateEval : Eval predicate env emptyCBoundEnv
      (cArrow (A.denote env) cBool) meaning) :
    Eval (repAbsLaw A B predicate) env
      (packageBound A B env meaning package) cBool true := by
  classical
  let base := LawCtx A B
  let withA := base.extend A
  let aTm : Term withA A := Term.bvAs withA 0 A (by rfl)
  let absA := Term.app ((SubtypePackage.abstraction A B).weaken A) aTm
  let repAbsA := Term.app ((SubtypePackage.representation A B).weaken A) absA
  let predicateBase := predicate.weaken (B.arr A) |>.weaken (A.arr B)
  let predicateA := predicateBase.weaken A
  let guarded := guard predicateA aTm
  let equality := Term.eq A repAbsA aTm
  let body := Empty.imp guarded equality
  let quantified := Empty.forallTm A body
  have predicateBaseEval := predicate_in_lawCtx A B predicate env meaning package
    predicateEval
  have quantifiedTrue : Eval quantified env
      (packageBound A B env meaning package) cBool true := by
    apply Eval.forallTm A body env (packageBound A B env meaning package)
    intro a
    let extendedBound := extendCBoundEnv (A.denote env) a
      (packageBound A B env meaning package)
    have aEval : Eval aTm env extendedBound (A.denote env) a := by
      apply Eval.bvAs withA 0 A rfl env extendedBound (A.denote env) a
      exact (extendCBoundEnv_zero (A.denote env) a
        (packageBound A B env meaning package) (A.denote env)).trans
        (alignCValue_self (A.denote env) a)
    have absEval := Eval.abstraction A B env meaning package
    have absWeak : Eval ((SubtypePackage.abstraction A B).weaken A)
        env extendedBound (cArrow (A.denote env) (B.denote env)) package.abs :=
      Eval.weaken (SubtypePackage.abstraction A B) A env
        (packageBound A B env meaning package) a
        (cArrow (A.denote env) (B.denote env)) package.abs absEval
    have repEval := Eval.representation A B env meaning package
    have repWeak : Eval ((SubtypePackage.representation A B).weaken A)
        env extendedBound (cArrow (B.denote env) (A.denote env)) package.rep :=
      Eval.weaken (SubtypePackage.representation A B) A env
        (packageBound A B env meaning package) a
        (cArrow (B.denote env) (A.denote env)) package.rep repEval
    have predicateAEval : Eval predicateA env extendedBound
        (cArrow (A.denote env) cBool) meaning :=
      Eval.weaken predicateBase A env
        (packageBound A B env meaning package) a
        (cArrow (A.denote env) cBool) meaning predicateBaseEval
    have absAEval : Eval absA env extendedBound (B.denote env)
        (package.abs a) :=
      Eval.app ((SubtypePackage.abstraction A B).weaken A) aTm env
        extendedBound package.abs a absWeak aEval
    have repAbsEval : Eval repAbsA env extendedBound (A.denote env)
        (package.rep (package.abs a)) :=
      Eval.app ((SubtypePackage.representation A B).weaken A) absA env
        extendedBound package.rep (package.abs a) repWeak absAEval
    have equalityEval := Eval.eq A repAbsA aTm env extendedBound
      (package.rep (package.abs a)) a repAbsEval aEval
    by_cases valid : CGuarded meaning a
    · have guardEval : Eval guarded env extendedBound cBool true :=
        Eval.guard_true predicateA aTm env extendedBound meaning a
          predicateAEval aEval valid
      have eqTrue : Infinity.classicalEqBool (package.rep (package.abs a)) a =
          true := by
        simp [Infinity.classicalEqBool, package.repAbs a valid]
      rw [eqTrue] at equalityEval
      have implication := Eval.imp_value guarded equality env extendedBound
        true true guardEval equalityEval
      simpa using implication
    · have guardEval : Eval guarded env extendedBound cBool false :=
        Eval.guard_false predicateA aTm env extendedBound meaning a
          predicateAEval aEval valid
      have implication := Eval.imp_value guarded equality env extendedBound
        false (Infinity.classicalEqBool (package.rep (package.abs a)) a)
        guardEval equalityEval
      simpa using implication
  exact Eval.congr_raw (left := quantified)
    (right := repAbsLaw A B predicate) (by rfl) quantifiedTrue

theorem Eval.repGuardedLaw_true (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env))
    (predicateEval : Eval predicate env emptyCBoundEnv
      (cArrow (A.denote env) cBool) meaning) :
    Eval (repGuardedLaw A B predicate) env
      (packageBound A B env meaning package) cBool true := by
  let base := LawCtx A B
  let withB := base.extend B
  let bTm : Term withB B := Term.bvAs withB 0 B (by rfl)
  let repB := Term.app ((SubtypePackage.representation A B).weaken B) bTm
  let predicateBase := predicate.weaken (B.arr A) |>.weaken (A.arr B)
  let predicateB := predicateBase.weaken B
  let body := guard predicateB repB
  let quantified := Empty.forallTm B body
  have predicateBaseEval := predicate_in_lawCtx A B predicate env meaning package
    predicateEval
  have quantifiedTrue : Eval quantified env
      (packageBound A B env meaning package) cBool true := by
    apply Eval.forallTm B body env (packageBound A B env meaning package)
    intro b
    let extendedBound := extendCBoundEnv (B.denote env) b
      (packageBound A B env meaning package)
    have bEval : Eval bTm env extendedBound (B.denote env) b := by
      apply Eval.bvAs withB 0 B rfl env extendedBound (B.denote env) b
      exact (extendCBoundEnv_zero (B.denote env) b
        (packageBound A B env meaning package) (B.denote env)).trans
        (alignCValue_self (B.denote env) b)
    have repEval := Eval.representation A B env meaning package
    have repWeak : Eval ((SubtypePackage.representation A B).weaken B)
        env extendedBound (cArrow (B.denote env) (A.denote env)) package.rep :=
      Eval.weaken (SubtypePackage.representation A B) B env
        (packageBound A B env meaning package) b
        (cArrow (B.denote env) (A.denote env)) package.rep repEval
    have predicateBEval : Eval predicateB env extendedBound
        (cArrow (A.denote env) cBool) meaning :=
      Eval.weaken predicateBase B env
        (packageBound A B env meaning package) b
        (cArrow (A.denote env) cBool) meaning predicateBaseEval
    have repBEval : Eval repB env extendedBound (A.denote env)
        (package.rep b) :=
      Eval.app ((SubtypePackage.representation A B).weaken B) bTm env
        extendedBound package.rep b repWeak bEval
    exact Eval.guard_true predicateB repB env extendedBound meaning
      (package.rep b) predicateBEval repBEval (package.repGuarded b)
  exact Eval.congr_raw (left := quantified)
    (right := repGuardedLaw A B predicate) (by rfl) quantifiedTrue

theorem Eval.laws_true (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env))
    (predicateEval : Eval predicate env emptyCBoundEnv
      (cArrow (A.denote env) cBool) meaning) :
    Eval (laws A B predicate) env (packageBound A B env meaning package)
      cBool true := by
  have absRep := Eval.absRepLaw_true A B env meaning package
  have repAbs := Eval.repAbsLaw_true A B predicate env meaning package predicateEval
  have repGuarded := Eval.repGuardedLaw_true A B predicate env meaning package
    predicateEval
  have rest := Eval.and_of_true (repAbsLaw A B predicate)
    (repGuardedLaw A B predicate) env (packageBound A B env meaning package)
    repAbs repGuarded
  exact Eval.and_of_true (absRepLaw A B)
    (Empty.and (repAbsLaw A B predicate) (repGuardedLaw A B predicate))
    env (packageBound A B env meaning package) absRep rest

/-- A semantic package supplies witnesses for the checked existential package
formula. -/
theorem Eval.packageAt_true (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (env : CTypeEnv types)
    (meaning : (A.denote env).carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      (A.denote env) meaning (B.denote env))
    (predicateEval : Eval predicate env emptyCBoundEnv
      (cArrow (A.denote env) cBool) meaning) :
    Eval (packageAt A B predicate) env emptyCBoundEnv cBool true := by
  let repType := B.arr A
  let absType := A.arr B
  let law := laws A B predicate
  let inner := Empty.existsTm absType law
  let outer := Empty.existsTm repType inner
  let repHead := packageRepHead A B env meaning package
  let absHead := packageAbsHead A B env meaning package
  let repBound := extendCBoundEnv (repType.denote env) repHead emptyCBoundEnv
  let absMeaning : (absType.denote env).carrier → Bool := fun candidate =>
    Infinity.iValue law.toIntrinsic env
      (extendCBoundEnv (absType.denote env) candidate repBound) cBool
  have absBodyEval : ∀ candidate : (absType.denote env).carrier,
      Eval law env (extendCBoundEnv (absType.denote env) candidate repBound)
        cBool (absMeaning candidate) := by
    intro candidate
    exact Eval.canonical law env
      (extendCBoundEnv (absType.denote env) candidate repBound) cBool
  have lawTrue := Eval.laws_true A B predicate env meaning package predicateEval
  have lawAtWitness : Eval law env
      (extendCBoundEnv (absType.denote env) absHead repBound) cBool true := by
    simpa [repBound, repHead, absHead, repType, absType, packageBound]
      using lawTrue
  have absHolds : absMeaning absHead = true := by
    exact Eval.value_unique (absBodyEval absHead) lawAtWitness
  have innerTrue : Eval inner env repBound cBool true :=
    Eval.existsTm absType law env repBound absMeaning absBodyEval absHead absHolds
  let repMeaning : (repType.denote env).carrier → Bool := fun candidate =>
    Infinity.iValue inner.toIntrinsic env
      (extendCBoundEnv (repType.denote env) candidate emptyCBoundEnv) cBool
  have repBodyEval : ∀ candidate : (repType.denote env).carrier,
      Eval inner env
        (extendCBoundEnv (repType.denote env) candidate emptyCBoundEnv)
        cBool (repMeaning candidate) := by
    intro candidate
    exact Eval.canonical inner env
      (extendCBoundEnv (repType.denote env) candidate emptyCBoundEnv) cBool
  have repHolds : repMeaning repHead = true := by
    exact Eval.value_unique (repBodyEval repHead) innerTrue
  have outerTrue : Eval outer env emptyCBoundEnv cBool true :=
    Eval.existsTm repType inner env emptyCBoundEnv repMeaning repBodyEval
      repHead repHolds
  exact Eval.congr_raw (left := outer) (right := packageAt A B predicate)
    (by rfl) outerTrue

/-- Version of `packageAt_true` phrased with externally chosen semantic
carrier and model objects. -/
theorem Eval.packageAt_true_of_denote_eq (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (env : CTypeEnv types) (carrier model : CPointed)
    (carrierEq : A.denote env = carrier) (modelEq : B.denote env = model)
    (meaning : carrier.carrier → Bool)
    (package : Nucleus.Hol.Ethane.Subtype.SemanticPackage
      carrier meaning model)
    (predicateEval : Eval predicate env emptyCBoundEnv
      (cArrow carrier cBool) meaning) :
    Eval (packageAt A B predicate) env emptyCBoundEnv cBool true := by
  subst carrier
  subst model
  exact Eval.packageAt_true A B predicate env meaning package predicateEval

/-- The head type variable denotes the head of its semantic environment. -/
theorem denote_head (candidate : CPointed) (env : CTypeEnv types) :
    (FamK.bv (.zero : TyVar (.star :: types) .star)).denote
      (extendCTypeEnv (starValue candidate) env) = candidate := by
  unfold FamK.denote
  rw [cSem_certificate_coherent
    (FamK.bv (.zero : TyVar (.star :: types) .star)).kinded.certificate
    (CChecks.tyBv .zero) (extendCTypeEnv (starValue candidate) env)]
  rfl

/-- The subtype-package predicate has a concrete guarded-subtype witness in
the deterministic classical semantics. -/
theorem Eval.predicate_true {types : List Kind} (A : Ty types)
    (P : Term (Ctx.empty : Ctx types 0) (A.arr FamK.boolTy))
    (env : CTypeEnv types) :
    let carrier := A.denote env
    let meaning := Infinity.iValue P.toIntrinsic env emptyCBoundEnv
      (cArrow carrier cBool)
    let candidate := cGuardedType carrier meaning
    Eval (predicate A P) (extendCTypeEnv (starValue candidate) env)
      emptyCBoundEnv cBool true := by
  let carrier := A.denote env
  let meaning := Infinity.iValue P.toIntrinsic env emptyCBoundEnv
    (cArrow carrier cBool)
  let candidate := cGuardedType carrier meaning
  let extendedEnv := extendCTypeEnv (starValue candidate) env
  let A' := weakenFam (domain := .star) A
  let P' := Nucleus.HolE.Empty.SubtypePackage.weakenClosedTerm
    (domain := .star) P
  let B : Ty (.star :: types) := FamK.bv .zero
  have originalEval : Eval P env emptyCBoundEnv (cArrow carrier cBool) meaning :=
    Eval.canonical P env emptyCBoundEnv (cArrow carrier cBool)
  have weakenedEval : Eval P' extendedEnv emptyCBoundEnv
      (cArrow carrier cBool) meaning :=
    Eval.weakenClosedTerm P candidate env (cArrow carrier cBool) meaning originalEval
  have carrierEq : A'.denote extendedEnv = carrier := by
    exact denote_weakenFam A candidate env
  have modelEq : B.denote extendedEnv = candidate := by
    exact denote_head candidate env
  let package := Nucleus.Hol.Ethane.Subtype.guardedPackage carrier meaning
  have packageTrue := Eval.packageAt_true_of_denote_eq A' B P' extendedEnv
    carrier candidate carrierEq modelEq meaning package weakenedEval
  have result := Eval.congr_raw (left := packageAt A' B P')
    (right := predicate A P) (by rfl) packageTrue
  simpa [carrier, meaning, candidate, extendedEnv, A', P', B] using result

/-- Ethane's single subtype-package sentence is true for every checked
predicate. -/
theorem Eval.existsType_true {types : List Kind} (A : Ty types)
    (P : Term (Ctx.empty : Ctx types 0) (A.arr FamK.boolTy))
    (env : CTypeEnv types) :
    Eval (existsType A P) env emptyCBoundEnv cBool true := by
  let carrier := A.denote env
  let meaning := Infinity.iValue P.toIntrinsic env emptyCBoundEnv
    (cArrow carrier cBool)
  let candidate := cGuardedType carrier meaning
  apply Eval.tyExists Ctx.empty (Term.openEmpty (predicate A P)) env emptyCBoundEnv candidate
  exact (Eval_openEmpty _ _ _ _ _).mpr (Eval.predicate_true A P env)

end

end Nucleus.HolE.Empty.SubtypePackage
