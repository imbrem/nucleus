import Mathlib.Data.Finset.Lattice.Fold
import Nucleus.Hol.Ethane.FV
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

def Binder.code : Binder → Nat
  | .modelType => 0
  | .representation => 1
  | .abstraction => 2
  | .carrierValue => 3
  | .subtypeValue => 4
  | .witness => 5
  | .conjunction => 6

theorem Binder.code_injective : Function.Injective Binder.code := by
  intro left right equality
  cases left <;> cases right <;> simp_all [Binder.code]

abbrev HygienicName (Name : Type) := Binder ⊕ Name

/-- How many names the package reserves. -/
def binderCount : Nat := 7

theorem code_lt_binderCount (binder : Binder) : binder.code < binderCount := by
  cases binder <;> decide

/-- The binder-name assignment: the package's private names occupy
`base`, …, `base + 6`, and the caller's names are left exactly as they are.

Leaving the caller alone is the point.  An assignment that renamed the caller's
names too — as an earlier parity encoding here did, sending private binders to
even numbers and caller names to odd ones — is equally hygienic but builds a
*different* term from the one a kernel constructing the package in place would,
so the two could only ever be compared up to renaming.  This way the Lean
construction and `covalence-logic-hol`'s `Kernel::subtype` build the same
expression, and `base` is the only thing they have to agree on. -/
def assign (base : Nat) : HygienicName Nat → Nat
  | .inl binder => base + binder.code
  | .inr name => name

/-- `base` is fresh for a set of caller names when it clears all of them. -/
def Fresh (base : Nat) (names : Finset Nat) : Prop := ∀ name ∈ names, name < base

/-- A fresh base makes every private binder a name the caller does not use.

This is the hygiene condition in the form the construction actually needs: no
package binder can capture a caller occurrence, because no package binder *is*
a caller name. -/
theorem binder_notMem_of_fresh {base : Nat} {names : Finset Nat}
    (fresh : Fresh base names) (binder : Binder) :
    assign base (.inl binder) ∉ names := by
  intro member
  have : base + binder.code < base := fresh _ member
  omega

/-- With a fresh base the assignment is injective where it is used: on the
private binders, and on the caller names the expression can mention. -/
theorem assign_injOn {base : Nat} {names : Finset Nat} (fresh : Fresh base names) :
    Set.InjOn (assign base) (Set.range Sum.inl ∪ Sum.inr '' (names : Set Nat)) := by
  rintro x memberX y memberY equality
  have caller : ∀ z : HygienicName Nat,
      z ∈ Set.range Sum.inl ∪ Sum.inr '' (names : Set Nat) →
      ∀ n, z = .inr n → n < base := by
    rintro _ (⟨_, rfl⟩ | ⟨n, member, rfl⟩) m equation
    · nomatch equation
    · cases equation
      exact fresh _ (by simpa using member)
  match x, y with
  | .inl left, .inl right =>
      have codes : left.code = right.code := by
        simpa [assign] using equality
      exact congrArg Sum.inl (Binder.code_injective codes)
  | .inr left, .inr right => simpa [assign] using equality
  | .inl left, .inr right =>
      have : right < base := caller _ memberY right rfl
      simp only [assign] at equality
      omega
  | .inr left, .inl right =>
      have : left < base := caller _ memberX left rfl
      simp only [assign] at equality
      omega

/-- Turn a hygienically tagged expression into ordinary `Nat`-named Ethane
syntax without introducing capture. -/
def materialize (base : Nat) (expression : Expr Sig (HygienicName Nat) sort) :
    Expr Sig Nat sort :=
  expression.mapNames (assign base)

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

/-- Every name the caller's carrier and predicate mention. -/
noncomputable def callerNames (A : Ty Sig Nat) (P : Tm Sig Nat) : Finset Nat :=
  A.nameIndices ∪ P.nameIndices

/-- One past the largest name the caller uses — the base a kernel picks when it
has no other source of freshness.

`Finset.sup` of the empty set is `0`, so a carrier and predicate mentioning no
names at all put the package's binders at `0, …, 6`. -/
noncomputable def freshBase (A : Ty Sig Nat) (P : Tm Sig Nat) : Nat :=
  (callerNames A P).sup id + 1

theorem fresh_freshBase (A : Ty Sig Nat) (P : Tm Sig Nat) :
    Fresh (freshBase A P) (callerNames A P) := by
  intro name member
  have bound : name ≤ (callerNames A P).sup id := Finset.le_sup (f := id) member
  simp only [freshBase] at bound ⊢
  omega

/-- Serialization-facing subtype sentence with ordinary natural-number names,
at a caller-chosen base.

The base is explicit because a kernel building this package inside a larger
arena knows a bound the caller's names already respect and should not have to
recompute one; `freshBase` is the choice to make when there is nothing else to
go on, and `fresh_freshBase` discharges its side condition. -/
def existsTypeAt (base : Nat) (A : Ty Sig Nat) (P : Tm Sig Nat) : Tm Sig Nat :=
  materialize base (existsType A P)

/-- Serialization-facing guarded subtype type. -/
def subAt (base : Nat) (A : Ty Sig Nat) (P : Tm Sig Nat) : Ty Sig Nat :=
  materialize base (sub A P)

/-- Serialization-facing representation operation. -/
def repAt (base : Nat) (A : Ty Sig Nat) (P : Tm Sig Nat) : Tm Sig Nat :=
  materialize base (rep A P)

/-- Serialization-facing abstraction operation. -/
def absAt (base : Nat) (A : Ty Sig Nat) (P : Tm Sig Nat) : Tm Sig Nat :=
  materialize base (abs A P)

/-- The package at the base a kernel with no other information would choose. -/
noncomputable def existsTypeNat (A : Ty Sig Nat) (P : Tm Sig Nat) : Tm Sig Nat :=
  existsTypeAt (freshBase A P) A P

noncomputable def subNat (A : Ty Sig Nat) (P : Tm Sig Nat) : Ty Sig Nat :=
  subAt (freshBase A P) A P

noncomputable def repNat (A : Ty Sig Nat) (P : Tm Sig Nat) : Tm Sig Nat :=
  repAt (freshBase A P) A P

noncomputable def absNat (A : Ty Sig Nat) (P : Tm Sig Nat) : Tm Sig Nat :=
  absAt (freshBase A P) A P

/-- No private binder of the package built at `freshBase` is a name the caller
already used — the hygiene guarantee, at the default base. -/
theorem binder_fresh_freshBase (A : Ty Sig Nat) (P : Tm Sig Nat) (binder : Binder) :
    assign (freshBase A P) (.inl binder) ∉ callerNames A P :=
  binder_notMem_of_fresh (fresh_freshBase A P) binder

end Nucleus.Hol.Ethane.Subtype
