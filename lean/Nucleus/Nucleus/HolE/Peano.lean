import Nucleus.HolE.Infinity

/-!
# Second-order Peano structures

This file constructs the natural-number interface from ordinary HolE syntax.
There are no primitive natural-number constructors: the carrier is selected
with `model`, while zero and successor are selected with Hilbert choice.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

namespace InfinityTm

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth}

/-- Disjunction derived from conjunction and negation by De Morgan. -/
def or (left right : InfinityTm Sig Γ .boolTy) : InfinityTm Sig Γ .boolTy :=
  not (and (not left) (not right))

/-- Material implication derived from disjunction and negation. -/
def imp (antecedent consequent : InfinityTm Sig Γ .boolTy) :
    InfinityTm Sig Γ .boolTy :=
  not (and antecedent (not consequent))

end InfinityTm

namespace Peano

variable {Sig : Signature} [SigTyping Sig] {types : List Kind}

/-- An endomap reflects equality. -/
def reflectsEqualityAt {depth : Nat} {Γ : BoundCtx Sig types depth}
    (A : Ty Sig types) (hA : Kinded A)
    (function : InfinityTm Sig Γ (.arr A A)) : InfinityTm Sig Γ .boolTy := by
  let withX := extendBound A Γ
  let withY := extendBound A withX
  let function : InfinityTm Sig withY (.arr A A) := function.weaken.weaken
  let x : InfinityTm Sig withY A := .bv hA 1 rfl
  let y : InfinityTm Sig withY A := .bv hA 0 rfl
  let reflected := InfinityTm.eq .boolTy
    (InfinityTm.eq hA (function.app x) (function.app y))
    (InfinityTm.eq hA x y)
  exact InfinityTm.forallTm hA (InfinityTm.forallTm hA reflected)

/-- A point is outside the range of an endomap. -/
def missesPointAt {depth : Nat} {Γ : BoundCtx Sig types depth}
    (A : Ty Sig types) (hA : Kinded A)
    (function : InfinityTm Sig Γ (.arr A A)) (zero : InfinityTm Sig Γ A) :
    InfinityTm Sig Γ .boolTy := by
  let withX := extendBound A Γ
  let function : InfinityTm Sig withX (.arr A A) := function.weaken
  let zero : InfinityTm Sig withX A := zero.weaken
  let x : InfinityTm Sig withX A := .bv hA 0 rfl
  exact InfinityTm.forallTm hA
    (InfinityTm.not (InfinityTm.eq hA (function.app x) zero))

/-- Dedekind-infinite structure carried by a chosen endomap and point. -/
def infinityStructureAt {depth : Nat} {Γ : BoundCtx Sig types depth}
    (A : Ty Sig types) (hA : Kinded A)
    (function : InfinityTm Sig Γ (.arr A A)) (zero : InfinityTm Sig Γ A) :
    InfinityTm Sig Γ .boolTy :=
  InfinityTm.and (reflectsEqualityAt A hA function)
    (missesPointAt A hA function zero)

/-- Full second-order Peano structure carried by an endomap and point. -/
def peanoStructureAt {depth : Nat} {Γ : BoundCtx Sig types depth}
    (A : Ty Sig types) (hA : Kinded A)
    (function : InfinityTm Sig Γ (.arr A A)) (zero : InfinityTm Sig Γ A) :
    InfinityTm Sig Γ .boolTy := by
  let predicateTy : Ty Sig types := .arr A .boolTy
  let predicateContext := extendBound predicateTy Γ
  let predicate : InfinityTm Sig predicateContext predicateTy :=
    .bv (.arr hA .boolTy) 0 rfl
  let base := predicate.app zero.weaken

  let stepContext := extendBound A predicateContext
  let predicate : InfinityTm Sig stepContext predicateTy :=
    .bv (.arr hA .boolTy) 1 rfl
  let value : InfinityTm Sig stepContext A := .bv hA 0 rfl
  let stepFunction : InfinityTm Sig stepContext (.arr A A) := function.weaken.weaken
  let step := InfinityTm.imp (predicate.app value)
    (predicate.app (stepFunction.app value))
  let step := InfinityTm.forallTm hA step
  let cases := InfinityTm.and base step

  let allContext := extendBound A predicateContext
  let predicate : InfinityTm Sig allContext predicateTy :=
    .bv (.arr hA .boolTy) 1 rfl
  let value : InfinityTm Sig allContext A := .bv hA 0 rfl
  let all := InfinityTm.forallTm hA (predicate.app value)
  let induction := InfinityTm.imp cases all
  let induction := InfinityTm.forallTm (.arr hA .boolTy) induction
  exact InfinityTm.and (infinityStructureAt A hA function zero) induction

/-- Full second-order Peano structure in context `[z : A, f : A → A]`. -/
def peanoStructure (A : Ty Sig types) (hA : Kinded A) :
    InfinityTm Sig
      (extendBound A (extendBound (.arr A A) emptyBound))
      .boolTy := by
  let context := extendBound A (extendBound (.arr A A) emptyBound)
  let function : InfinityTm Sig context (.arr A A) := .bv (.arr hA hA) 1 rfl
  let zero : InfinityTm Sig context A := .bv hA 0 rfl
  exact peanoStructureAt A hA function zero

/-- Dedekind-infinite structure in context `[z : A, f : A → A]`. -/
def infinityStructure (A : Ty Sig types) (hA : Kinded A) :
    InfinityTm Sig
      (extendBound A (extendBound (.arr A A) emptyBound))
      .boolTy := by
  let context := extendBound A (extendBound (.arr A A) emptyBound)
  let function : InfinityTm Sig context (.arr A A) := .bv (.arr hA hA) 1 rfl
  let zero : InfinityTm Sig context A := .bv hA 0 rfl
  exact infinityStructureAt A hA function zero

/-- Predicate asserting that a carrier admits a Dedekind-infinite structure. -/
def infinityTypePredicate (A : Ty Sig types) (hA : Kinded A) :
    InfinityTm Sig (emptyBound : BoundCtx Sig types 0) .boolTy := by
  let endomap : Ty Sig types := .arr A A
  let withFunction := extendBound endomap (emptyBound : BoundCtx Sig types 0)
  let withZero := extendBound A withFunction
  let body : InfinityTm Sig withZero .boolTy := infinityStructure A hA
  let chooseZero : InfinityTm Sig withFunction .boolTy :=
    InfinityTm.existsTm hA body
  exact InfinityTm.existsTm (.arr hA hA) chooseZero

/-- Predicate asserting that a carrier admits a second-order Peano structure. -/
def typePredicate (A : Ty Sig types) (hA : Kinded A) :
    InfinityTm Sig (emptyBound : BoundCtx Sig types 0) .boolTy := by
  let endomap : Ty Sig types := .arr A A
  let withFunction := extendBound endomap (emptyBound : BoundCtx Sig types 0)
  let withZero := extendBound A withFunction
  let body : InfinityTm Sig withZero .boolTy := peanoStructure A hA
  let chooseZero : InfinityTm Sig withFunction .boolTy :=
    InfinityTm.existsTm hA body
  exact InfinityTm.existsTm (.arr hA hA) chooseZero

abbrev carrier {Sig : Signature} : Ty Sig [.star] := .tyBv .zero

theorem carrier_kinded {Sig : Signature} [SigTyping Sig] :
    Kinded (carrier (Sig := Sig)) := .tyBv .zero

/-- Some type carries a Dedekind-infinite structure. -/
def infinitySentence {Sig : Signature} [SigTyping Sig] : Tm Sig [] 0 :=
  .tyExists (infinityTypePredicate carrier carrier_kinded).tm

theorem infinitySentence_typed {Sig : Signature} [SigTyping Sig] :
    HasType (emptyBound : BoundCtx Sig [] 0) infinitySentence .boolTy :=
  .tyExists (infinityTypePredicate carrier carrier_kinded).typing

/-- Some type carries a second-order Peano structure. -/
def existsSentence {Sig : Signature} [SigTyping Sig] : Tm Sig [] 0 :=
  .tyExists (typePredicate carrier carrier_kinded).tm

theorem existsSentence_typed {Sig : Signature} [SigTyping Sig] :
    HasType (emptyBound : BoundCtx Sig [] 0) existsSentence .boolTy :=
  .tyExists (typePredicate carrier carrier_kinded).typing

/-- The natural-number type is the model selected by the Peano predicate. -/
def natTy {Sig : Signature} [SigTyping Sig] : Ty Sig [] :=
  .model (typePredicate carrier carrier_kinded).tm

theorem natTy_kinded {Sig : Signature} [SigTyping Sig] : Kinded (natTy (Sig := Sig)) :=
  .model (typePredicate carrier carrier_kinded).typing

/-- Successor is a chosen endomap which extends to a Peano structure. -/
def succ {Sig : Signature} [SigTyping Sig] :
    InfinityTm Sig (emptyBound : BoundCtx Sig [] 0) (.arr natTy natTy) := by
  let endomap : Ty Sig [] := .arr natTy natTy
  let withFunction := extendBound endomap (emptyBound : BoundCtx Sig [] 0)
  let withZero := extendBound natTy withFunction
  let body : InfinityTm Sig withZero .boolTy := peanoStructure natTy natTy_kinded
  let chooseZero : InfinityTm Sig withFunction .boolTy :=
    InfinityTm.existsTm natTy_kinded body
  let predicate := InfinityTm.lam (.arr natTy_kinded natTy_kinded) chooseZero
  exact InfinityTm.eps (.arr natTy_kinded natTy_kinded) predicate

/-- Zero is a chosen point completing the selected successor to a structure. -/
def zero {Sig : Signature} [SigTyping Sig] :
    InfinityTm Sig (emptyBound : BoundCtx Sig [] 0) natTy := by
  let withZero := extendBound natTy (emptyBound : BoundCtx Sig [] 0)
  let successor : InfinityTm Sig withZero (.arr natTy natTy) := succ.weaken
  let zeroVar : InfinityTm Sig withZero natTy := .bv natTy_kinded 0 rfl
  let body := peanoStructureAt natTy natTy_kinded successor zeroVar
  let predicate := InfinityTm.lam natTy_kinded body
  exact InfinityTm.eps natTy_kinded predicate

theorem succ_typed {Sig : Signature} [SigTyping Sig] :
    HasType (emptyBound : BoundCtx Sig [] 0) (succ (Sig := Sig)).tm
      (.arr natTy natTy) :=
  succ.typing

theorem zero_typed {Sig : Signature} [SigTyping Sig] :
    HasType (emptyBound : BoundCtx Sig [] 0) (zero (Sig := Sig)).tm natTy :=
  zero.typing

end Peano

end Nucleus.HolE
