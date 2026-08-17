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

def typePredicate :
    BoolTm (types := [.star]) (Ctx.empty : Ctx [.star] 0) :=
  Term.truth Ctx.empty

def predicateAtBool : BoolTm Γ := typePredicate.openType FamK.boolTy

def predicateAtBoolProof : Proof Γ [] predicateAtBool := by
  exact Proof.truth

def someTypeExists : Proof Γ [] (Term.tyExists Γ typePredicate) :=
  Proof.tyExistsIntro typePredicate FamK.boolTy predicateAtBoolProof

end Nucleus.HolE.Empty.ApiTest
