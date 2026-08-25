import Nucleus.HolE.Empty

/-! Compile-time examples exercising the checked empty-signature API. -/

namespace Nucleus.HolE.Empty.ApiTest

def Γ : Ctx [] 0 := Ctx.empty

def trueProof : Proof Γ [] (Term.truth Γ) := Proof.truth

def falseReflexive :
    Proof Γ [] (Term.eq FamK.boolTy (Term.falsehood Γ) (Term.falsehood Γ)) :=
  Proof.eqRefl (Term.falsehood Γ)

def identityBody : Term (Γ.extend FamK.boolTy) FamK.boolTy :=
  Term.bvAs _ 0 FamK.boolTy (by simp [Γ, Ctx.extend, extendBound])

def betaIdentity :
    TermEq Γ
      (Term.app (Term.lam FamK.boolTy identityBody) (Term.truth Γ))
      (Term.openBound identityBody (Term.truth Γ)) :=
  TermEq.beta identityBody (Term.truth Γ)

-- The predicate lives in the ambient context seen past the bound type
-- variable.  Here that context is empty, so this is `Ctx.empty` transported.
def typePredicate :
    BoolTm (types := [.star]) ((Ctx.empty : Ctx [] 0).weakenTypes) :=
  Term.truth _

def predicateAtBool : BoolTm (Ctx.empty : Ctx [] 0) :=
  typePredicate.openType FamK.boolTy

def predicateAtBoolProof : Proof Ctx.empty [] predicateAtBool := by
  exact Proof.truth

def someTypeExists :
    Proof Ctx.empty [] (Term.tyExists (Ctx.empty : Ctx [] 0) typePredicate) :=
  Proof.tyExistsIntro typePredicate FamK.boolTy predicateAtBoolProof

end Nucleus.HolE.Empty.ApiTest
