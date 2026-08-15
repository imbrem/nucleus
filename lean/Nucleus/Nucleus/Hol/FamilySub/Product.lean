import Nucleus.Hol.FamilySub.Intrinsic

/-! # Products from type-family lambda and ordinary subtypes -/

namespace Nucleus.Hol.FamilySub

universe u
set_option relaxedAutoImplicit true

structure Checked (Sig : Signature) [SigTyping Sig] {types : List Kind} {depth : Nat}
    (Γ : BoundCtx Sig types depth) (A : Ty Sig types) where
  tm : Tm Sig types depth
  typing : HasType Γ tm A

namespace Checked

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A B : Ty Sig types}

def bv (hA : Kinded A) (index : Fin depth) (lookup : Γ index = A) : Checked Sig Γ A :=
  ⟨.bv index, .bv hA lookup⟩

def app (function : Checked Sig Γ (.arr A B)) (argument : Checked Sig Γ A) :
    Checked Sig Γ B := ⟨.app function.tm argument.tm, .app function.typing argument.typing⟩

def lam (hA : Kinded A) (body : Checked Sig (extendBound A Γ) B) :
    Checked Sig Γ (.arr A B) := ⟨.lam A body.tm, .lam body.tm hA body.typing⟩

def eq (hA : Kinded A) (left right : Checked Sig Γ A) : Checked Sig Γ .boolTy :=
  ⟨.eq A left.tm right.tm, .eq hA left.typing right.typing⟩

def eps (hA : Kinded A) (predicate : Checked Sig Γ (.arr A .boolTy)) :
    Checked Sig Γ A := ⟨.eps A predicate.tm, .eps hA predicate.typing⟩

def existsTm (hA : Kinded A) (predicate : Checked Sig Γ (.arr A .boolTy)) :
    Checked Sig Γ .boolTy := predicate.app (predicate.eps hA)

def truth : Checked Sig Γ .boolTy := ⟨.bool true, .bool true⟩

def falsehood : Checked Sig Γ .boolTy := ⟨.bool false, .bool false⟩

def weaken {B : Ty Sig types} (value : Checked Sig Γ A) :
    Checked Sig (extendBound B Γ) A :=
  ⟨FamilySub.weaken value.tm, value.typing.weaken⟩

def not (proposition : Checked Sig Γ .boolTy) : Checked Sig Γ .boolTy :=
  eq .boolTy proposition falsehood

/-- Standard HOL conjunction, defined using only equality and lambda. -/
def and (left right : Checked Sig Γ .boolTy) : Checked Sig Γ .boolTy := by
  let functionTy : Ty Sig types := .arr .boolTy (.arr .boolTy .boolTy)
  let hFunction : Kinded functionTy := .arr .boolTy (.arr .boolTy .boolTy)
  let f : Checked Sig (extendBound functionTy Γ) functionTy := Checked.bv hFunction 0 rfl
  let lhsBody := (f.app left.weaken).app right.weaken
  let rhsBody := (f.app (truth (Γ := Γ)).weaken).app (truth (Γ := Γ)).weaken
  let lhs := Checked.lam hFunction lhsBody
  let rhs := Checked.lam hFunction rhsBody
  exact Checked.eq (.arr hFunction .boolTy) lhs rhs

def or (left right : Checked Sig Γ .boolTy) : Checked Sig Γ .boolTy :=
  Checked.not (Checked.and (Checked.not left) (Checked.not right))

def abs (hA : Kinded A) (predicate : Checked Sig (extendBound A emptyBound) .boolTy)
    (value : Checked Sig Γ A) : Checked Sig Γ (.sub A predicate.tm) :=
  ⟨.abs A predicate.tm value.tm, .abs hA predicate.typing value.typing⟩

def rep (hA : Kinded A) (predicate : Checked Sig (extendBound A emptyBound) .boolTy)
    (value : Checked Sig Γ (.sub A predicate.tm)) : Checked Sig Γ A :=
  ⟨.rep A predicate.tm value.tm, .rep hA predicate.typing value.typing⟩

end Checked

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A B : Ty Sig types}

def productCarrier (A B : Ty Sig types) : Ty Sig types :=
  .arr (.arr A (.arr B .boolTy)) .boolTy

theorem productCarrier_kinded (hA : Kinded A) (hB : Kinded B) :
    Kinded (productCarrier A B) :=
  .arr (.arr hA (.arr hB .boolTy)) .boolTy

def pairFunction (hA : Kinded A) (hB : Kinded B) :
    Checked Sig Γ (.arr A (.arr B (productCarrier A B))) := by
  let hF : Kinded (.arr A (.arr B .boolTy)) := .arr hA (.arr hB .boolTy)
  let f : Checked Sig
      (extendBound (.arr A (.arr B .boolTy)) (extendBound B (extendBound A Γ)))
      (.arr A (.arr B .boolTy)) := Checked.bv hF 0 rfl
  let b : Checked Sig
      (extendBound (.arr A (.arr B .boolTy)) (extendBound B (extendBound A Γ))) B :=
    Checked.bv hB 1 rfl
  let a : Checked Sig
      (extendBound (.arr A (.arr B .boolTy)) (extendBound B (extendBound A Γ))) A :=
    Checked.bv hA 2 rfl
  exact Checked.lam hA (Checked.lam hB (Checked.lam hF ((f.app a).app b)))

def pairChurch (hA : Kinded A) (hB : Kinded B)
    (a : Checked Sig Γ A) (b : Checked Sig Γ B) :
    Checked Sig Γ (productCarrier A B) :=
  ((pairFunction (Γ := Γ) hA hB).app a).app b

/-- A Church value is a pair precisely when it has two components. -/
def productPredicate (hA : Kinded A) (hB : Kinded B) :
    Checked Sig (extendBound (productCarrier A B) emptyBound) .boolTy := by
  let carrier := productCarrier A B
  let hCarrier := productCarrier_kinded hA hB
  let Γp : BoundCtx Sig types 1 := extendBound carrier emptyBound
  let Γa : BoundCtx Sig types 2 := extendBound A Γp
  let Γb : BoundCtx Sig types 3 := extendBound B Γa
  let p : Checked Sig Γb carrier := Checked.bv hCarrier 2 rfl
  let a : Checked Sig Γb A := Checked.bv hA 1 rfl
  let b : Checked Sig Γb B := Checked.bv hB 0 rfl
  let equation : Checked Sig Γb .boolTy := Checked.eq hCarrier p (pairChurch hA hB a b)
  let existsB : Checked Sig Γa .boolTy := Checked.existsTm hB (Checked.lam hB equation)
  exact Checked.existsTm hA (Checked.lam hA existsB)

def productTy (hA : Kinded A) (hB : Kinded B) : Ty Sig types :=
  .sub (productCarrier A B) (productPredicate hA hB).tm

theorem productTy_kinded (hA : Kinded A) (hB : Kinded B) :
    Kinded (productTy hA hB) :=
  .sub (productCarrier_kinded hA hB) (productPredicate hA hB).typing

def pair (hA : Kinded A) (hB : Kinded B) (a : Checked Sig Γ A) (b : Checked Sig Γ B) :
    Checked Sig Γ (productTy hA hB) :=
  Checked.abs (productCarrier_kinded hA hB) (productPredicate hA hB)
    (pairChurch hA hB a b)

/-- The predicate selecting a first component from the representation of a
product value.  Choice makes the projection total; subtype membership proves
that the selected pair exists. -/
def firstComponentPredicate (hA : Kinded A) (hB : Kinded B) :
    Checked Sig (extendBound (productTy hA hB) emptyBound) (.arr A .boolTy) := by
  let hCarrier := productCarrier_kinded hA hB
  let hProduct := productTy_kinded hA hB
  let Γx := extendBound (productTy hA hB) (emptyBound : BoundCtx Sig types 0)
  let Γa := extendBound A Γx
  let Γb := extendBound B Γa
  let x : Checked Sig Γb (productTy hA hB) := Checked.bv hProduct 2 rfl
  let a : Checked Sig Γb A := Checked.bv hA 1 rfl
  let b : Checked Sig Γb B := Checked.bv hB 0 rfl
  let represented := Checked.rep hCarrier (productPredicate hA hB) x
  let equation := Checked.eq hCarrier represented (pairChurch hA hB a b)
  let hasSecond : Checked Sig Γa .boolTy :=
    Checked.existsTm hB (Checked.lam hB equation)
  exact Checked.lam hA hasSecond

def fstFunction (hA : Kinded A) (hB : Kinded B) :
    Checked Sig Γ (.arr (productTy hA hB) A) := by
  let hProduct := productTy_kinded hA hB
  let xContext := extendBound (productTy hA hB) Γ
  -- Rebuild the selector under the ambient context so the resulting operation
  -- is usable in open terms as well as closed definitions.
  let Γa := extendBound A xContext
  let Γb := extendBound B Γa
  let x : Checked Sig Γb (productTy hA hB) := Checked.bv hProduct 2 rfl
  let a : Checked Sig Γb A := Checked.bv hA 1 rfl
  let b : Checked Sig Γb B := Checked.bv hB 0 rfl
  let represented := Checked.rep (productCarrier_kinded hA hB) (productPredicate hA hB) x
  let equation := Checked.eq (productCarrier_kinded hA hB) represented
    (pairChurch hA hB a b)
  let hasSecond : Checked Sig Γa .boolTy :=
    Checked.existsTm hB (Checked.lam hB equation)
  let selector : Checked Sig xContext (.arr A .boolTy) := Checked.lam hA hasSecond
  exact Checked.lam hProduct (Checked.eps hA selector)

def sndFunction (hA : Kinded A) (hB : Kinded B) :
    Checked Sig Γ (.arr (productTy hA hB) B) := by
  let hProduct := productTy_kinded hA hB
  let xContext := extendBound (productTy hA hB) Γ
  let Γb := extendBound B xContext
  let Γa := extendBound A Γb
  let x : Checked Sig Γa (productTy hA hB) := Checked.bv hProduct 2 rfl
  let b : Checked Sig Γa B := Checked.bv hB 1 rfl
  let a : Checked Sig Γa A := Checked.bv hA 0 rfl
  let represented := Checked.rep (productCarrier_kinded hA hB) (productPredicate hA hB) x
  let equation := Checked.eq (productCarrier_kinded hA hB) represented
    (pairChurch hA hB a b)
  let hasFirst : Checked Sig Γb .boolTy :=
    Checked.existsTm hA (Checked.lam hA equation)
  let selector : Checked Sig xContext (.arr B .boolTy) := Checked.lam hB hasFirst
  exact Checked.lam hProduct (Checked.eps hB selector)

def fst (hA : Kinded A) (hB : Kinded B) (value : Checked Sig Γ (productTy hA hB)) :
    Checked Sig Γ A := (fstFunction hA hB).app value

def snd (hA : Kinded A) (hB : Kinded B) (value : Checked Sig Γ (productTy hA hB)) :
    Checked Sig Γ B := (sndFunction hA hB).app value

def productFam (Sig : Signature) [SigTyping Sig] :
    Fam Sig [] (.arr .star (.arr .star .star)) :=
  .tyLam (.tyLam (productTy (.tyBv (.succ .zero)) (.tyBv .zero)))

theorem productFam_kinded (Sig : Signature) [SigTyping Sig] : Kinded (productFam Sig) :=
  .tyLam (.tyLam (productTy_kinded (.tyBv (.succ .zero)) (.tyBv .zero)))

def appliedProductFam (Sig : Signature) [SigTyping Sig]
    (A B : Ty Sig []) : Ty Sig [] :=
  .tyApp (.tyApp (productFam Sig) A) B

def appliedProductFam_defeq {A B : Ty Sig []} (hA : Kinded A) (hB : Kinded B) :
    FamEq Sig (appliedProductFam Sig A B) (productTy hA hB) := by
  let body : Fam Sig [.star] (.arr .star .star) :=
    .tyLam (productTy (.tyBv (.succ .zero)) (.tyBv .zero))
  let bodyAfterA : Fam Sig [.star] .star :=
    instantiateTypes (liftTySub (headTySub A))
      (productTy (.tyBv (.succ .zero)) (.tyBv .zero))
  have outer : FamEq Sig (.tyApp (.tyLam body) A) (openType body A) :=
    .beta body A
  have lifted : FamEq Sig (.tyApp (.tyApp (.tyLam body) A) B)
      (.tyApp (openType body A) B) := .app outer .refl
  refine .trans (B := .tyApp (openType body A) B) ?_ ?_
  · simpa [appliedProductFam, productFam, body] using lifted
  · simpa [body, bodyAfterA, openType, headTySub, liftTySub,
      productTy, productPredicate,
      productCarrier, pairChurch, pairFunction, Checked.existsTm,
      Checked.lam, Checked.app, Checked.eps, Checked.eq, Checked.bv] using
      (FamEq.beta (Sig := Sig) bodyAfterA B)

theorem appliedProductFam_kinded {A B : Ty Sig []} (hA : Kinded A) (hB : Kinded B) :
    Kinded (appliedProductFam Sig A B) :=
  .tyApp (.tyApp (productFam_kinded Sig) hA) hB

def pairAtFamily {A B : Ty Sig []} {Γ : BoundCtx Sig [] depth}
    (hA : Kinded A) (hB : Kinded B)
    (a : DefEqChecked Sig Γ A) (b : DefEqChecked Sig Γ B) :
    DefEqChecked Sig Γ (appliedProductFam Sig A B) := by
  let constructor : DefEqChecked Sig Γ (.arr A (.arr B (productCarrier A B))) :=
    .ofRaw (pairFunction hA hB).tm (pairFunction hA hB).typing
  let represented := (constructor.app a).app b
  let value : DefEqChecked Sig Γ (productTy hA hB) :=
    DefEqChecked.abs (productCarrier_kinded hA hB) (productPredicate hA hB).tm
      (productPredicate hA hB).typing represented
  exact value.conv (appliedProductFam_kinded hA hB)
    (.symm (appliedProductFam_defeq hA hB))

def fstAtFamily {A B : Ty Sig []} {Γ : BoundCtx Sig [] depth}
    (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (appliedProductFam Sig A B)) :
    DefEqChecked Sig Γ A := by
  let represented := value.conv (productTy_kinded hA hB)
    (appliedProductFam_defeq hA hB)
  exact (DefEqChecked.ofRaw (fstFunction hA hB).tm (fstFunction hA hB).typing).app
    represented

def sndAtFamily {A B : Ty Sig []} {Γ : BoundCtx Sig [] depth}
    (hA : Kinded A) (hB : Kinded B)
    (value : DefEqChecked Sig Γ (appliedProductFam Sig A B)) :
    DefEqChecked Sig Γ B := by
  let represented := value.conv (productTy_kinded hA hB)
    (appliedProductFam_defeq hA hB)
  exact (DefEqChecked.ofRaw (sndFunction hA hB).tm (sndFunction hA hB).typing).app
    represented

end Nucleus.Hol.FamilySub
