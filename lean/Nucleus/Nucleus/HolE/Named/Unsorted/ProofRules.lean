import Nucleus.HolE.Named.Unsorted.Rulebook

/-!
# Checked proof rules for unsorted named HolE

The public certificates mention only checked named terms.  A few binder rules
also accept an equality describing the expected locally nameless computation;
those equalities disappear once named opening and weakening are exposed as
first-class operations.
-/

namespace Nucleus.HolE.Named.Unsorted

set_option relaxedAutoImplicit true

abbrev BoolTerm {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth) :=
  Term Sig typeScope termScope Γ (Family.boolTy typeScope)

def rawHypotheses {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat} {typeScope : Named.TyScope types}
    {termScope : Named.TmScope Sig depth} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    (hypotheses : List (BoolTerm typeScope termScope Γ)) :
    List (Nucleus.HolE.Tm Sig types depth) :=
  hypotheses.map Term.lowered

theorem rawHypotheses_typed {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {types : List Kind} {depth : Nat} {typeScope : Named.TyScope types}
    {termScope : Named.TmScope Sig depth} {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    (hypotheses : List (BoolTerm typeScope termScope Γ)) :
    Nucleus.HolE.TypedHyps Γ (rawHypotheses hypotheses) := by
  intro proposition member
  obtain ⟨term, _, rfl⟩ := List.mem_map.mp member
  exact .exact (by simpa [Family.boolTy] using term.typing)

/-- Equality between checked named terms. -/
structure TermEq {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth) (type : Family Sig typeScope .star)
    (left right : Term Sig typeScope termScope Γ type) where
  kernel : Nucleus.HolE.EqTm Γ left.lowered right.lowered type.lowered

/-- A proof of a checked named proposition. -/
structure Proof {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth)
    (hypotheses : List (BoolTerm typeScope termScope Γ))
    (conclusion : BoolTerm typeScope termScope Γ) where
  kernel : Nucleus.HolE.Proves Γ (rawHypotheses hypotheses) conclusion.lowered

namespace TermEq

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
  [Nucleus.HolE.SigFamilyEquality Sig]

def refl (term : Term Sig typeScope termScope Γ type) :
    TermEq (Sig := Sig) typeScope termScope Γ type term term :=
  ⟨.refl (.exact term.typing)⟩

def symm (equality : TermEq typeScope termScope Γ type left right) :
    TermEq (Sig := Sig) typeScope termScope Γ type right left :=
  ⟨.symm equality.kernel⟩

def trans (first : TermEq typeScope termScope Γ type left middle)
    (second : TermEq typeScope termScope Γ type middle right) :
    TermEq (Sig := Sig) typeScope termScope Γ type left right :=
  ⟨.trans first.kernel second.kernel⟩

def app (function : TermEq typeScope termScope Γ (Family.arr A B) f g)
    (argument : TermEq typeScope termScope Γ A x y) :
    TermEq (Sig := Sig) typeScope termScope Γ B (Term.app f x) (Term.app g y) :=
  ⟨.app (Term.app f x).typing (Term.app g y).typing f.typing x.typing
    g.typing y.typing function.kernel argument.kernel⟩

def lam (name : Nat) (A B : Family Sig typeScope .star)
    {left right : Term Sig typeScope
      (.cons ⟨name, A.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound A.lowered Γ) B}
    (bodies : TermEq (Sig := Sig) typeScope (.cons ⟨name, A.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound A.lowered Γ) B left right) :
    TermEq (Sig := Sig) typeScope termScope Γ (Family.arr A B)
      (Term.lam name A B left) (Term.lam name A B right) :=
  ⟨.lam (Term.lam name A B left).typing (Term.lam name A B right).typing
    A.kinding bodies.kernel⟩

def beta (name : Nat) (typedContext : Nucleus.HolE.TypedCtx Γ)
    (A B : Family Sig typeScope .star)
    (body : Term Sig typeScope (.cons ⟨name, A.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound A.lowered Γ) B)
    (argument : Term Sig typeScope termScope Γ A)
    (result : Term Sig typeScope termScope Γ B)
    (resultEq : result.lowered = Nucleus.HolE.openBound body.lowered argument.lowered) :
    TermEq (Sig := Sig) typeScope termScope Γ B
      (Term.app (Term.lam name A B body) argument) result := by
  have resultTyping : Nucleus.HolE.HasTypeDefEq Γ
      (Nucleus.HolE.openBound body.lowered argument.lowered) B.lowered :=
    resultEq ▸ (.exact result.typing)
  have certificate := Nucleus.HolE.EqTm.beta body.lowered argument.lowered
    A.kinding typedContext (Term.app (Term.lam name A B body) argument).typing
    (.exact body.typing) (.exact argument.typing) resultTyping
  exact ⟨resultEq.symm ▸ certificate⟩

def eta (name : Nat) (typedContext : Nucleus.HolE.TypedCtx Γ)
    (A B : Family Sig typeScope .star)
    (function : Term Sig typeScope termScope Γ (Family.arr A B))
    (expanded : Term Sig typeScope termScope Γ (Family.arr A B))
    (expandedEq : expanded.lowered = .lam A.lowered
      (.app (Nucleus.HolE.weaken function.lowered) (.bv 0)))
    (fresh : Nucleus.HolE.Fresh name function.lowered) :
    TermEq (Sig := Sig) typeScope termScope Γ (Family.arr A B) expanded function := by
  have expandedTyping : Nucleus.HolE.HasTypeDefEq Γ
      (.lam A.lowered (.app (Nucleus.HolE.weaken function.lowered) (.bv 0)))
      (.arr A.lowered B.lowered) :=
    expandedEq ▸ (.exact expanded.typing)
  have certificate := Nucleus.HolE.EqTm.eta name fresh typedContext
    (.exact function.typing) expandedTyping
  exact ⟨by simpa [Family.arr] using (expandedEq.symm ▸ certificate)⟩

end TermEq

namespace Proof

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
  [Nucleus.HolE.SigFamilyEquality Sig]

def hyp {proposition : BoolTerm typeScope termScope Γ}
    (member : proposition ∈ hypotheses) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses proposition := by
  refine ⟨.hyp (rawHypotheses_typed hypotheses) (.exact ?_) ?_⟩
  · simpa [Family.boolTy] using proposition.typing
  · exact List.mem_map.mpr ⟨proposition, member, rfl⟩

def truth : Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.truth) :=
  ⟨.truth (rawHypotheses_typed hypotheses)
    (.exact (by simpa [Term.truth, Term.bool, Family.boolTy] using (Term.truth (Sig := Sig)
      (typeScope := typeScope) (termScope := termScope) (Γ := Γ)).typing))⟩

def falseElim (conclusion : BoolTerm typeScope termScope Γ)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses Term.falsehood) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses conclusion :=
  ⟨.falseElim (rawHypotheses_typed hypotheses) (.exact (by
      simpa [Family.boolTy] using conclusion.typing)) (.exact (by
      simpa [Family.boolTy] using conclusion.typing)) premise.kernel⟩

def boolCases (proposition conclusion : BoolTerm typeScope termScope Γ)
    (left : Proof (Sig := Sig) typeScope termScope Γ
      (proposition :: hypotheses) conclusion)
    (right : Proof (Sig := Sig) typeScope termScope Γ
      (Term.eq (Family.boolTy typeScope) proposition Term.falsehood :: hypotheses)
      conclusion) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses conclusion :=
  ⟨.boolCases (rawHypotheses_typed hypotheses)
    (.exact (by simpa [Family.boolTy] using proposition.typing))
    (.exact (by simpa [Family.boolTy] using conclusion.typing))
    (rawHypotheses_typed (proposition :: hypotheses))
    (rawHypotheses_typed
      (Term.eq (Family.boolTy typeScope) proposition Term.falsehood :: hypotheses))
    left.kernel right.kernel⟩

def eqRefl (value : Term Sig typeScope termScope Γ A) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.eq A value value) :=
  ⟨.eqRefl (rawHypotheses_typed hypotheses) (.exact (by
      simpa [Term.eq, Family.boolTy] using (Term.eq A value value).typing))
    A.kinding (.exact value.typing)⟩

def eqMp (predicate : Term Sig typeScope termScope Γ (Family.arr A (Family.boolTy typeScope)))
    (left right : Term Sig typeScope termScope Γ A)
    (equality : Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.eq A left right))
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.app predicate left)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.app predicate right) :=
  ⟨.eqMp (rawHypotheses_typed hypotheses) A.kinding (.exact (by
      simpa [Term.app, Family.boolTy] using (Term.app predicate right).typing))
    (.exact (by simpa [Family.arr, Family.boolTy] using predicate.typing))
    (.exact left.typing) (.exact right.typing) equality.kernel premise.kernel⟩

def choice (A : Family Sig typeScope .star)
    (predicate : Term Sig typeScope termScope Γ (Family.arr A (Family.boolTy typeScope)))
    (witness : Term Sig typeScope termScope Γ A)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.app predicate witness)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app predicate (Term.eps A predicate)) :=
  ⟨.choice (rawHypotheses_typed hypotheses) A.kinding (.exact (by
      simpa [Term.app, Term.eps, Family.boolTy] using
        (Term.app predicate (Term.eps A predicate)).typing))
    (.exact (by simpa [Family.arr, Family.boolTy] using predicate.typing))
    (.exact witness.typing) premise.kernel⟩

def generalize (name : Nat) (A : Family Sig typeScope .star)
    (body : BoolTerm typeScope
      (.cons ⟨name, A.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound A.lowered Γ))
    (extendedHypotheses : List (BoolTerm typeScope
      (.cons ⟨name, A.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound A.lowered Γ)))
    (hypothesesEq : rawHypotheses extendedHypotheses =
      (rawHypotheses hypotheses).map Nucleus.HolE.weaken)
    (premise : Proof (Sig := Sig) typeScope
      (.cons ⟨name, A.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound A.lowered Γ) extendedHypotheses body) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.arr A (Family.boolTy typeScope))
        (Term.lam name A (Family.boolTy typeScope) body)
        (Term.lam name A (Family.boolTy typeScope) Term.truth)) := by
  have premiseKernel : Nucleus.HolE.Proves
      (Nucleus.HolE.extendBound A.lowered Γ)
      ((rawHypotheses hypotheses).map Nucleus.HolE.weaken) body.lowered :=
    hypothesesEq ▸ premise.kernel
  exact ⟨.generalize (rawHypotheses_typed hypotheses) A.kinding
    (.exact (by
      simpa [Term.eq, Term.lam, Term.truth, Term.bool, Family.arr, Family.boolTy] using
        (Term.eq (Family.arr A (Family.boolTy typeScope))
          (Term.lam name A (Family.boolTy typeScope) body)
          (Term.lam name A (Family.boolTy typeScope) Term.truth)).typing))
    (.exact (by simpa [Family.boolTy] using body.typing)) premiseKernel⟩

/-- Named weakening with its expected kernel image stated explicitly. -/
def weakenBound (name : Nat) (A : Family Sig typeScope .star)
    (extendedHypotheses : List (BoolTerm typeScope
      (.cons ⟨name, A.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound A.lowered Γ)))
    (hypothesesEq : rawHypotheses extendedHypotheses =
      (rawHypotheses hypotheses).map Nucleus.HolE.weaken)
    (weakened : BoolTerm typeScope
      (.cons ⟨name, A.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound A.lowered Γ))
    (weakenedEq : weakened.lowered = Nucleus.HolE.weaken conclusion.lowered)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses conclusion) :
    Proof (Sig := Sig) typeScope
      (.cons ⟨name, A.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound A.lowered Γ) extendedHypotheses weakened := by
  have certificate := Nucleus.HolE.Proves.weakenBound
    (rawHypotheses_typed hypotheses) A.kinding
    (rawHypotheses_typed extendedHypotheses)
    (.exact (weakenedEq ▸ weakened.typing))
    (fun proposition member => by
      rw [hypothesesEq]
      exact List.mem_map.mpr ⟨proposition, member, rfl⟩)
    premise.kernel
  exact ⟨weakenedEq.symm ▸ certificate⟩

def convert (equality : TermEq (Sig := Sig) typeScope termScope Γ
      (Family.boolTy typeScope) source target)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses source) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses target :=
  ⟨.convert (rawHypotheses_typed hypotheses) (.exact (by
      simpa [Family.boolTy] using target.typing)) equality.kernel premise.kernel⟩

def eqOfTermEq (equality : TermEq (Sig := Sig) typeScope termScope Γ A left right) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.eq A left right) :=
  ⟨.eqOfEqTm (rawHypotheses_typed hypotheses) A.kinding
    (.exact (by simpa [Term.eq, Family.boolTy] using (Term.eq A left right).typing))
    equality.kernel⟩

def hypothesisMap {target : List (BoolTerm typeScope termScope Γ)}
    (subset : ∀ proposition, proposition ∈ hypotheses → proposition ∈ target)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses conclusion) :
    Proof (Sig := Sig) typeScope termScope Γ target conclusion := by
  refine ⟨.hypothesisMap (rawHypotheses_typed target) (.exact (by
    simpa [Family.boolTy] using conclusion.typing)) ?_ premise.kernel⟩
  intro raw member
  obtain ⟨proposition, membership, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨proposition, subset proposition membership, rfl⟩

def antisymm (left right : BoolTerm typeScope termScope Γ)
    (forward : Proof (Sig := Sig) typeScope termScope Γ (left :: hypotheses) right)
    (backward : Proof (Sig := Sig) typeScope termScope Γ (right :: hypotheses) left) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.boolTy typeScope) left right) :=
  ⟨.antisymm (rawHypotheses_typed hypotheses)
    (.exact (by simpa [Family.boolTy] using left.typing))
    (.exact (by simpa [Family.boolTy] using right.typing))
    (rawHypotheses_typed (left :: hypotheses))
    (.exact (by simpa [Term.eq, Family.boolTy] using
      (Term.eq (Family.boolTy typeScope) left right).typing))
    (rawHypotheses_typed (right :: hypotheses)) forward.kernel backward.kernel⟩

def absRep (A : Family Sig typeScope .star) (name : Nat)
    (predicate : BoolTerm typeScope
      (.cons ⟨name, A.expression.sorted⟩ .nil)
      (Nucleus.HolE.extendBound A.lowered Nucleus.HolE.emptyBound))
    (value : Term Sig typeScope termScope Γ (Term.sub A name predicate)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Term.sub A name predicate)
        (Term.abs A name predicate (Term.rep A name predicate value)) value) :=
  ⟨.absRep (rawHypotheses_typed hypotheses) A.kinding
    (.exact (by
      simpa [Term.eq, Term.abs, Term.rep, Term.sub, Family.boolTy] using
        (Term.eq (Term.sub A name predicate)
          (Term.abs A name predicate (Term.rep A name predicate value)) value).typing))
    (by simpa [Family.boolTy] using predicate.typing) (.exact value.typing)⟩

def repAbs (A : Family Sig typeScope .star) (name : Nat)
    (predicate : BoolTerm typeScope
      (.cons ⟨name, A.expression.sorted⟩ .nil)
      (Nucleus.HolE.extendBound A.lowered Nucleus.HolE.emptyBound))
    (value : Term Sig typeScope termScope Γ A)
    (instanceTerm : BoolTerm typeScope termScope Γ)
    (instanceEq : instanceTerm.lowered =
      Nucleus.HolE.instantiateOne predicate.lowered value.lowered)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses instanceTerm) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq A (Term.rep A name predicate (Term.abs A name predicate value)) value) :=
  ⟨.repAbs (rawHypotheses_typed hypotheses) A.kinding
    (.exact (by
      simpa [Term.eq, Term.abs, Term.rep, Term.sub, Family.boolTy] using
        (Term.eq A (Term.rep A name predicate (Term.abs A name predicate value))
          value).typing))
    (by simpa [Family.boolTy] using predicate.typing) value.typing
    (instanceEq ▸ premise.kernel)⟩

def repPredOfWitness (A : Family Sig typeScope .star) (name : Nat)
    (predicate : BoolTerm typeScope
      (.cons ⟨name, A.expression.sorted⟩ .nil)
      (Nucleus.HolE.extendBound A.lowered Nucleus.HolE.emptyBound))
    (witness : Term Sig typeScope termScope Γ A)
    (witnessInstance : BoolTerm typeScope termScope Γ)
    (witnessEq : witnessInstance.lowered =
      Nucleus.HolE.instantiateOne predicate.lowered witness.lowered)
    (value : Term Sig typeScope termScope Γ (Term.sub A name predicate))
    (result : BoolTerm typeScope termScope Γ)
    (resultEq : result.lowered = Nucleus.HolE.instantiateOne predicate.lowered
      (Term.rep A name predicate value).lowered)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses witnessInstance) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses result := by
  have certificate := Nucleus.HolE.Proves.repPredOfWitness
    (rawHypotheses_typed hypotheses) A.kinding
    (.exact (resultEq ▸ result.typing))
    (by simpa [Family.boolTy] using predicate.typing) witness.typing value.typing
    (witnessEq ▸ premise.kernel)
  exact ⟨resultEq.symm ▸ certificate⟩

def tyExistsIntro {types : List Kind} {typeScope : Named.TyScope types}
    {hypotheses : List (BoolTerm typeScope (.nil : Named.TmScope Sig 0)
      Nucleus.HolE.emptyBound)}
    (name : Nat)
    (predicate : BoolTerm (.cons (kind := .star) name typeScope) .nil
      Nucleus.HolE.emptyBound)
    (witness : Family Sig typeScope .star)
    (instanceTerm : BoolTerm typeScope .nil Nucleus.HolE.emptyBound)
    (instanceEq : instanceTerm.lowered =
      Nucleus.HolE.openType predicate.lowered witness.lowered)
    (premise : Proof (Sig := Sig) typeScope .nil Nucleus.HolE.emptyBound
      hypotheses instanceTerm) :
    Proof (Sig := Sig) typeScope .nil Nucleus.HolE.emptyBound hypotheses
      (Term.tyExists name predicate) :=
  ⟨.tyExistsIntro (rawHypotheses_typed hypotheses)
    (.exact (by simpa [Term.tyExists, Family.boolTy] using
      (Term.tyExists (Sig := Sig) (termScope := (.nil : Named.TmScope Sig 0))
        (Γ := Nucleus.HolE.emptyBound) name predicate).typing))
    witness.kinding (.exact (by simpa [Family.boolTy] using predicate.typing))
    (.exact (instanceEq ▸ instanceTerm.typing)) (instanceEq ▸ premise.kernel)⟩

def modelSpec {types : List Kind} {typeScope : Named.TyScope types}
    {hypotheses : List (BoolTerm typeScope (.nil : Named.TmScope Sig 0)
      Nucleus.HolE.emptyBound)}
    (name : Nat)
    (predicate : BoolTerm (.cons (kind := .star) name typeScope) .nil
      Nucleus.HolE.emptyBound)
    (instanceTerm : BoolTerm typeScope .nil Nucleus.HolE.emptyBound)
    (instanceEq : instanceTerm.lowered = Nucleus.HolE.openType predicate.lowered
      (Family.model name predicate).lowered)
    (premise : Proof (Sig := Sig) typeScope .nil Nucleus.HolE.emptyBound
      hypotheses (Term.tyExists name predicate)) :
    Proof (Sig := Sig) typeScope .nil Nucleus.HolE.emptyBound hypotheses instanceTerm := by
  have certificate := Nucleus.HolE.Proves.modelSpec
    (rawHypotheses_typed hypotheses)
    (.exact (instanceEq ▸ instanceTerm.typing))
    (.exact (by simpa [Family.boolTy] using predicate.typing))
    (.exact (instanceEq ▸ instanceTerm.typing)) premise.kernel
  exact ⟨instanceEq.symm ▸ certificate⟩

end Proof

end Nucleus.HolE.Named.Unsorted
