import Nucleus.HolE.EmptySyntax

/-! # Checked proof rules for `HolE Empty`

The wrappers in this file are the intended high-level kernel surface: their
arguments are checked syntax objects and their conclusions are checked
propositions.  Raw contexts and repeated typing premises stay behind the
boundary.
-/

namespace Nucleus.HolE.Empty

open Nucleus.HolE

set_option relaxedAutoImplicit true

/-- A kernel proof over checked empty-signature syntax. -/
structure Proof {types : List Kind} {depth : Nat} (Γ : Ctx types depth)
    (H : PropCtx Γ) (conclusion : BoolTm Γ) where
  raw : Proves Γ.raw H.raw conclusion.raw

/-- A checked kernel equality between two terms. -/
structure TermEq {types : List Kind} {depth : Nat} (Γ : Ctx types depth)
    {A : Ty types} (left right : Term Γ A) where
  raw : EqTm Γ.raw left.raw right.raw A.raw

namespace TermEq

def refl (term : Term Γ A) : TermEq Γ term term :=
  ⟨.refl (.exact term.typing)⟩

def symm (equality : TermEq Γ left right) : TermEq Γ right left :=
  ⟨.symm equality.raw⟩

def trans (first : TermEq Γ left middle) (second : TermEq Γ middle right) :
    TermEq Γ left right :=
  ⟨.trans first.raw second.raw⟩

def app (function : TermEq Γ leftFunction rightFunction)
    (argument : TermEq Γ leftArgument rightArgument) :
    TermEq Γ (Term.app leftFunction leftArgument)
      (Term.app rightFunction rightArgument) :=
  ⟨.app (Term.app leftFunction leftArgument).typing
    (Term.app rightFunction rightArgument).typing
    leftFunction.typing leftArgument.typing
    rightFunction.typing rightArgument.typing function.raw argument.raw⟩

def lam (domain : Ty types) {B : Ty types}
    {leftBody rightBody : Term (Γ.extend domain) B}
    (bodies : TermEq (Γ.extend domain) leftBody rightBody) :
    TermEq Γ (Term.lam domain leftBody) (Term.lam domain rightBody) :=
  ⟨.lam (Term.lam domain leftBody).typing (Term.lam domain rightBody).typing
    domain.kinded bodies.raw⟩

def beta (body : Term (Γ.extend A) B) (argument : Term Γ A) :
    TermEq Γ (Term.app (Term.lam A body) argument) (Term.openBound body argument) :=
  ⟨.beta body.raw argument.raw A.kinded Γ.typed
    (Term.app (Term.lam A body) argument).typing
    (.exact body.typing) (.exact argument.typing)
    (.exact (Term.openBound body argument).typing)⟩

def eta (name : Nat) (function : Term Γ (A.arr B))
    (fresh : Fresh name function.raw) :
    TermEq Γ
      (Term.lam A (Term.app (function.weaken A)
        (Term.bvAs (Γ.extend A) 0 A (by simp [Ctx.extend, extendBound]))))
      function :=
  ⟨.eta name fresh Γ.typed (.exact function.typing)
    (.exact (Term.lam A
      (Term.app (function.weaken A)
        (Term.bvAs (Γ.extend A) 0 A (by simp [Ctx.extend, extendBound])))).typing)⟩

end TermEq

namespace Proof

def hyp {p : BoolTm Γ} (member : p ∈ H) : Proof Γ H p := by
  refine ⟨.hyp H.typed (.exact p.typing) ?_⟩
  exact List.mem_map.mpr ⟨p, member, rfl⟩

def truth : Proof Γ H (Term.truth Γ) :=
  ⟨.truth H.typed (.exact (Term.truth Γ).typing)⟩

def falseElim (conclusion : BoolTm Γ)
    (premise : Proof Γ H (Term.falsehood Γ)) : Proof Γ H conclusion :=
  ⟨.falseElim H.typed (.exact conclusion.typing) (.exact conclusion.typing)
    premise.raw⟩

def boolCases (proposition conclusion : BoolTm Γ)
    (left : Proof Γ (proposition :: H) conclusion)
    (right : Proof Γ
      (Term.eq FamK.boolTy proposition (Term.falsehood Γ) :: H) conclusion) :
    Proof Γ H conclusion :=
  ⟨.boolCases (PropCtx.typed H) (.exact proposition.typing) (.exact conclusion.typing)
    (PropCtx.typed (proposition :: H))
    (PropCtx.typed (Term.eq FamK.boolTy proposition (Term.falsehood Γ) :: H))
    left.raw right.raw⟩

def eqRefl (value : Term Γ A) : Proof Γ H (Term.eq A value value) :=
  ⟨.eqRefl H.typed (.exact (Term.eq A value value).typing)
    A.kinded (.exact value.typing)⟩

def eqMp (predicate : Term Γ (A.arr FamK.boolTy))
    (left right : Term Γ A)
    (equality : Proof Γ H (Term.eq A left right))
    (premise : Proof Γ H (Term.app predicate left)) :
    Proof Γ H (Term.app predicate right) :=
  ⟨.eqMp H.typed A.kinded (.exact (Term.app predicate right).typing)
    (.exact predicate.typing) (.exact left.typing) (.exact right.typing)
    equality.raw premise.raw⟩

def choice (A : Ty types) (predicate : Term Γ (A.arr FamK.boolTy))
    (witness : Term Γ A) (premise : Proof Γ H (Term.app predicate witness)) :
    Proof Γ H (Term.app predicate (Term.eps A predicate)) :=
  ⟨.choice H.typed A.kinded
    (.exact (Term.app predicate (Term.eps A predicate)).typing)
    (.exact predicate.typing) (.exact witness.typing) premise.raw⟩

def generalize (A : Ty types) (body : BoolTm (Γ.extend A))
    (premise : Proof (Γ.extend A) (H.weaken A) body) :
    Proof Γ H (Term.eq (A.arr FamK.boolTy) (Term.lam A body)
      (Term.lam A (Term.truth (Γ.extend A)))) := by
  have rawPremise : Proves (extendBound A.raw Γ.raw) (H.raw.map HolE.weaken)
      body.raw := by
    have proof := premise.raw
    rw [PropCtx.raw_weaken] at proof
    simpa [Ctx.extend] using proof
  exact ⟨.generalize H.typed A.kinded
    (.exact (Term.eq (A.arr FamK.boolTy) (Term.lam A body)
      (Term.lam A (Term.truth (Γ.extend A)))).typing)
    (.exact body.typing) rawPremise⟩

def weakenBound (A : Ty types) (premise : Proof Γ H proposition) :
    Proof (Γ.extend A) (H.weaken A) (proposition.weaken A) := by
  refine ⟨.weakenBound H.typed A.kinded (H.weaken A).typed
    (.exact (proposition.weaken A).typing) ?_ premise.raw⟩
  intro q member
  simpa using List.mem_map.mpr ⟨q, member, rfl⟩

def hypothesisMap {K : PropCtx Γ}
    (subset : ∀ p, p ∈ H → p ∈ K) (premise : Proof Γ H conclusion) :
    Proof Γ K conclusion := by
  refine ⟨.hypothesisMap K.typed (.exact conclusion.typing) ?_ premise.raw⟩
  intro rawTerm member
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨p, subset p hp, rfl⟩

def antisymm (left right : BoolTm Γ)
    (forward : Proof Γ (left :: H) right)
    (backward : Proof Γ (right :: H) left) :
    Proof Γ H (Term.eq FamK.boolTy left right) :=
  ⟨.antisymm (PropCtx.typed H) (.exact left.typing) (.exact right.typing)
    (PropCtx.typed (left :: H)) (.exact (Term.eq FamK.boolTy left right).typing)
    (PropCtx.typed (right :: H)) forward.raw backward.raw⟩

def convert (equality : TermEq Γ source target)
    (premise : Proof Γ H source) : Proof Γ H target :=
  ⟨.convert H.typed (.exact target.typing) equality.raw premise.raw⟩

def eqOfTermEq {A : Ty types} {left right : Term Γ A}
    (equality : TermEq Γ left right) :
    Proof Γ H (Term.eq A left right) :=
  ⟨.eqOfEqTm H.typed A.kinded (.exact (Term.eq A left right).typing)
    equality.raw⟩

def tyExistsIntro {types : List Kind} {H : PropCtx (Ctx.empty : Ctx types 0)}
    (predicate : BoolTm (types := .star :: types) Ctx.empty)
    (witness : Ty types)
    (premise : Proof Ctx.empty H (predicate.openType witness)) :
    Proof Ctx.empty H (Term.tyExists Ctx.empty predicate) :=
  ⟨.tyExistsIntro H.typed (.exact (Term.tyExists Ctx.empty predicate).typing)
    witness.kinded (.exact predicate.typing)
    (.exact (predicate.openType witness).typing) premise.raw⟩

def modelSpec {types : List Kind} {H : PropCtx (Ctx.empty : Ctx types 0)}
    (predicate : BoolTm (types := .star :: types) Ctx.empty)
    (premise : Proof Ctx.empty H (Term.tyExists Ctx.empty predicate)) :
    Proof Ctx.empty H (predicate.openType (Term.model predicate)) :=
  ⟨.modelSpec H.typed (.exact (predicate.openType (Term.model predicate)).typing)
    (.exact predicate.typing)
    (.exact (predicate.openType (Term.model predicate)).typing) premise.raw⟩

def absRep (A : Ty types) (predicate : Term (Ctx.empty.extend A) FamK.boolTy)
    (value : Term Γ (Term.sub A predicate)) :
    Proof Γ H (Term.eq (Term.sub A predicate)
      (Term.abs A predicate (Term.rep A predicate value)) value) :=
  ⟨.absRep H.typed A.kinded
    (.exact (Term.eq (Term.sub A predicate)
      (Term.abs A predicate (Term.rep A predicate value)) value).typing)
    predicate.typing (.exact value.typing)⟩

/-- Representation after abstraction, with the predicate instance supplied as
a checked Boolean term.  This is the direct checked counterpart of the raw
kernel rule. -/
def repAbs (A : Ty types) (predicate : Term (Ctx.empty.extend A) FamK.boolTy)
    (value : Term Γ A) (instanceTerm : BoolTm Γ)
    (instanceEq : instanceTerm.raw = instantiateOne predicate.raw value.raw)
    (premise : Proof Γ H instanceTerm) :
    Proof Γ H (Term.eq A
      (Term.rep A predicate (Term.abs A predicate value)) value) := by
  have instanceProof : Proves Γ.raw H.raw
      (instantiateOne predicate.raw value.raw) := instanceEq ▸ premise.raw
  exact ⟨.repAbs H.typed A.kinded
    (.exact (Term.eq A
      (Term.rep A predicate (Term.abs A predicate value)) value).typing)
    predicate.typing value.typing instanceProof⟩

/-- A concrete witness selects the inhabited branch of a guarded subtype. -/
def repPredOfWitness (A : Ty types)
    (predicate : Term (Ctx.empty.extend A) FamK.boolTy)
    (witness : Term Γ A) (witnessInstance : BoolTm Γ)
    (witnessEq : witnessInstance.raw = instantiateOne predicate.raw witness.raw)
    (value : Term Γ (Term.sub A predicate))
    (result : BoolTm Γ)
    (resultEq : result.raw = instantiateOne predicate.raw
      (Term.rep A predicate value).raw)
    (premise : Proof Γ H witnessInstance) : Proof Γ H result := by
  have witnessProof : Proves Γ.raw H.raw
      (instantiateOne predicate.raw witness.raw) := witnessEq ▸ premise.raw
  have produced := Proves.repPredOfWitness H.typed A.kinded
    (.exact (resultEq ▸ result.typing)) predicate.typing witness.typing value.typing
    witnessProof
  exact ⟨resultEq.symm ▸ produced⟩

end Proof

end Nucleus.HolE.Empty
