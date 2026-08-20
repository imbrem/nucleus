import Nucleus.Hol.Ethane.Logic

/-!
# Guarded subtypes derived from `Model`

This file defines the object-language subtype package without adding syntax.
The package selects a type isomorphic to

```text
{ x : A // P x or not exists y, P y }.
```

All internal binders use the left side of a sum; names in the caller's `A` and
`P` are moved to the right side.  The construction is therefore hygienic
without a freshness oracle.
-/

namespace Nucleus.Hol.Ethane.Subtype

set_option relaxedAutoImplicit true

/-- Private names used by the guarded subtype package. -/
inductive Binder where
  | modelType
  | representation
  | abstraction
  | carrierValue
  | subtypeValue
  | witness
  | conjunction
  deriving DecidableEq

abbrev HygienicName (Name : Type) := Binder ⊕ Name

private def liftTy (A : Ty Sig Name) : Ty Sig (HygienicName Name) :=
  A.mapNames Sum.inr

private def liftTm (term : Tm Sig Name) : Tm Sig (HygienicName Name) :=
  term.mapNames Sum.inr

private def modelType : Ty Sig (HygienicName Name) :=
  .tyFv (.inl .modelType) .star

private def tmVar (name : Binder) (type : Ty Sig (HygienicName Name)) :
    Tm Sig (HygienicName Name) :=
  .tmFv (.inl name) type

private def holds (predicate value : Tm Sig (HygienicName Name)) :
    Tm Sig (HygienicName Name) :=
  .app predicate value

/-- Membership in the guarded predicate. -/
def guardBody (A : Ty Sig (HygienicName Name))
    (predicate value : Tm Sig (HygienicName Name)) :
    Tm Sig (HygienicName Name) :=
  let witness := tmVar (Sig := Sig) .witness A
  let inhabited := Expr.existsTm (.inl .witness) A (holds predicate witness)
  Expr.or (.inl .conjunction) (holds predicate value) (Expr.not inhabited)

/-- The representation and abstraction laws for one candidate model type. -/
def laws (A : Ty Sig (HygienicName Name))
    (predicate representation abstraction : Tm Sig (HygienicName Name)) :
    Tm Sig (HygienicName Name) :=
  let B := modelType (Sig := Sig) (Name := Name)
  let a := tmVar (Sig := Sig) .carrierValue A
  let b := tmVar (Sig := Sig) .subtypeValue B
  let repB := Expr.app representation b
  let absA := Expr.app abstraction a
  let absRep := Expr.forallTm (.inl .subtypeValue) B
    (.eq B (Expr.app abstraction repB) b)
  let repAbs := Expr.forallTm (.inl .carrierValue) A
    (Expr.imp (.inl .conjunction) (guardBody A predicate a)
      (.eq A (Expr.app representation absA) a))
  let repGuarded := Expr.forallTm (.inl .subtypeValue) B
    (guardBody A predicate repB)
  Expr.and (.inl .conjunction) absRep
    (Expr.and (.inl .conjunction) repAbs repGuarded)

/-- Predicate on a candidate type: representation and abstraction witnesses
exist and satisfy the guarded-subtype laws. -/
def predicate (A : Ty Sig Name) (P : Tm Sig Name) :
    Tm Sig (HygienicName Name) :=
  let A' := liftTy A
  let P' := liftTm P
  let B := modelType (Sig := Sig) (Name := Name)
  let repType := Expr.arr B A'
  let absType := Expr.arr A' B
  let representation := tmVar (Sig := Sig) .representation repType
  let abstraction := tmVar (Sig := Sig) .abstraction absType
  Expr.existsTm (.inl .representation) repType
    (Expr.existsTm (.inl .abstraction) absType
      (laws A' P' representation abstraction))

/-- The single polymorphic subtype-existence sentence. -/
def existsType (A : Ty Sig Name) (P : Tm Sig Name) : Tm Sig (HygienicName Name) :=
  .tyExists (.inl .modelType) (predicate A P)

/-- Guarded subtype as the model selected by the package predicate. -/
def sub (A : Ty Sig Name) (P : Tm Sig Name) : Ty Sig (HygienicName Name) :=
  .model (.inl .modelType) (predicate A P)

/-- Representation selected from the model package by Hilbert choice. -/
def rep (A : Ty Sig Name) (P : Tm Sig Name) : Tm Sig (HygienicName Name) :=
  let A' := liftTy A
  let P' := liftTm P
  let B := sub A P
  let repType := Expr.arr B A'
  let absType := Expr.arr A' B
  let representation := tmVar (Sig := Sig) .representation repType
  let abstraction := tmVar (Sig := Sig) .abstraction absType
  let hasAbstraction := Expr.existsTm (.inl .abstraction) absType
    (laws A' P' representation abstraction)
  .eps repType (.lam (.inl .representation) repType hasAbstraction)

/-- Abstraction selected compatibly with `rep` from the same model package. -/
def abs (A : Ty Sig Name) (P : Tm Sig Name) : Tm Sig (HygienicName Name) :=
  let A' := liftTy A
  let P' := liftTm P
  let B := sub A P
  let absType := Expr.arr A' B
  let abstraction := tmVar (Sig := Sig) .abstraction absType
  let compatible := laws A' P' (rep A P) abstraction
  .eps absType (.lam (.inl .abstraction) absType compatible)

end Nucleus.Hol.Ethane.Subtype
