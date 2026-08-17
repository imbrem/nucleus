import Nucleus.HolE.EmptyRules
import Nucleus.HolE.Infinity

/-! # Natural numbers and infinity in checked `HolE Empty`

The surface constants in the Rust kernel are definitions, not new trusted
syntax.  This file records their canonical checked expansion.  `nat` is the
model selected for the usual Dedekind-infinity theory; `succ` and `zero` are
Hilbert choices of witnesses for that same theory.
-/

namespace Nucleus.HolE.Empty

open Nucleus.HolE

set_option relaxedAutoImplicit true

namespace Term

/-- HOL universal quantification, defined as equality with the constantly
true predicate. -/
def forallTm {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (A : Ty types) (body : BoolTm (Γ.extend A)) : BoolTm Γ :=
  eq (A.arr FamK.boolTy) (lam A body) (lam A (truth (Γ.extend A)))

/-- HOL existential quantification, defined using choice. -/
def existsTm {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (A : Ty types) (body : BoolTm (Γ.extend A)) : BoolTm Γ :=
  let predicate := lam A body
  app predicate (eps A predicate)

/-- Boolean negation, defined by equality with false. -/
def not {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (proposition : BoolTm Γ) : BoolTm Γ :=
  eq FamK.boolTy proposition (falsehood Γ)

/-- The standard equality-only HOL definition of conjunction. -/
def and {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : BoolTm Γ := by
  let functionTy : Ty types :=
    FamK.boolTy.arr (FamK.boolTy.arr FamK.boolTy)
  let extended := Γ.extend functionTy
  let f : Term extended functionTy :=
    bvAs extended 0 functionTy (by rfl)
  let lhs := lam functionTy
    ((app f (left.weaken functionTy)).app (right.weaken functionTy))
  let rhs := lam functionTy ((app f (truth extended)).app (truth extended))
  exact eq (functionTy.arr FamK.boolTy) lhs rhs

/-- Boolean implication, defined by the absorption equation
`left ∧ right = left`. -/
def imp {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (left right : BoolTm Γ) : BoolTm Γ :=
  eq FamK.boolTy (and left right) left

end Term

namespace Natural

/-- A concrete endomap and missed point form a Dedekind-infinity structure. -/
def structurePred {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (A : Ty types) (next : Term Γ (A.arr A)) (missed : Term Γ A) :
    BoolTm Γ := by
  let withX := Γ.extend A
  let withXY := withX.extend A
  let nextXY := (next.weaken A).weaken A
  let xXY : Term withXY A :=
    Term.bvAs withXY 1 A (by
      change A.raw = A.raw
      rfl)
  let yXY : Term withXY A :=
    Term.bvAs withXY 0 A (by simp [withXY, Ctx.extend, extendBound])
  let reflected := Term.eq FamK.boolTy
    (Term.eq A (Term.app nextXY xXY) (Term.app nextXY yXY))
    (Term.eq A xXY yXY)
  let reflects := Term.forallTm A (Term.forallTm A reflected)

  let nextX := next.weaken A
  let missedX := missed.weaken A
  let xX : Term withX A :=
    Term.bvAs withX 0 A (by simp [withX, Ctx.extend, extendBound])
  let misses := Term.forallTm A
    (Term.not (Term.eq A (Term.app nextX xX) missedX))
  exact Term.and reflects misses

/-- The type-variable-indexed theory used to define natural numbers. -/
def theory : BoolTm (types := [.star]) (Ctx.empty : Ctx [.star] 0) := by
  exact ⟨Infinity.typePredicate.tm, Infinity.typePredicate.typing⟩

/-- `TM_NAT`: the model selected for the Dedekind-infinity theory. -/
def nat : Ty [] := Term.model theory

/-- The predicate used to choose the distinguished successor endomap. -/
def successorPredicate : BoolTm ((Ctx.empty : Ctx [] 0).extend (nat.arr nat)) := by
  let withNext := (Ctx.empty : Ctx [] 0).extend (nat.arr nat)
  let next : Term withNext (nat.arr nat) :=
    Term.bvAs withNext 0 (nat.arr nat)
      (by simp [withNext, Ctx.extend, extendBound])
  let withMissed := withNext.extend nat
  let missed : Term withMissed nat :=
    Term.bvAs withMissed 0 nat
      (by simp [withMissed, Ctx.extend, extendBound])
  exact Term.existsTm nat (structurePred nat (next.weaken nat) missed)

/-- `TM_SUCC`: a chosen equality-reflecting endomap which misses a point. -/
def succ : Term (Ctx.empty : Ctx [] 0) (nat.arr nat) :=
  let predicate := Term.lam (nat.arr nat) successorPredicate
  Term.eps (nat.arr nat) predicate

/-- The predicate used to choose the point missed by `succ`. -/
def zeroPredicate : BoolTm ((Ctx.empty : Ctx [] 0).extend nat) := by
  let withMissed := (Ctx.empty : Ctx [] 0).extend nat
  let missed : Term withMissed nat :=
    Term.bvAs withMissed 0 nat
      (by simp [withMissed, Ctx.extend, extendBound])
  exact structurePred nat (succ.weaken nat) missed

/-- `TM_ZERO`: a chosen point outside the range of `succ`. -/
def zero : Term (Ctx.empty : Ctx [] 0) nat :=
  let predicate := Term.lam nat zeroPredicate
  Term.eps nat predicate

/-- Natural literals lower to repeated successor applications. -/
def numeral : Nat → Term (Ctx.empty : Ctx [] 0) nat
  | 0 => zero
  | n + 1 => Term.app succ (numeral n)

/-- `TM_INF`: the closed axiom asserting that the defining theory has a
model. -/
def inf : BoolTm (Ctx.empty : Ctx [] 0) :=
  Term.tyExists Ctx.empty theory

/-- The checked definition agrees syntactically with the infinity sentence
used by the consistency development. -/
theorem inf_raw_eq : inf.raw = Infinity.infinityAxiom (Sig := ClassicalSig) := by
  rfl

end Natural

end Nucleus.HolE.Empty
