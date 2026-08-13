import Nucleus.HolLN.Kernel
import Nucleus.HolLN.Json

/-!
# Erasures of the intrinsically sorted and scoped HOL syntax

The original `Hol` family records both the syntactic sort and binder depth.
This file gives the other three corners of the erasure square.  Constructor
names intentionally agree at every corner.
-/

namespace Nucleus.HolLN

universe u

set_option linter.style.longLine false

variable {Base : Type u} {sort : HolSort} {depth : Nat}

/-- HOL syntax retaining the type/term sort, but storing unchecked de Bruijn
indices as naturals. -/
inductive NoDepth (Base : Type u) : HolSort → Type u where
  | base (name : Base) : NoDepth Base .ty
  | boolTy : NoDepth Base .ty
  | natTy : NoDepth Base .ty
  | arr (domain codomain : NoDepth Base .ty) : NoDepth Base .ty
  | sub (carrier : NoDepth Base .ty) (predicate : NoDepth Base .tm) : NoDepth Base .ty
  | bound (index : Nat) : NoDepth Base .tm
  | free (name : Nat) : NoDepth Base .tm
  | app (function argument : NoDepth Base .tm) : NoDepth Base .tm
  | lam (domain : NoDepth Base .ty) (body : NoDepth Base .tm) : NoDepth Base .tm
  | bool (value : Bool) : NoDepth Base .tm
  | zero : NoDepth Base .tm
  | succ (value : NoDepth Base .tm) : NoDepth Base .tm
  | eq (type : NoDepth Base .ty) (left right : NoDepth Base .tm) : NoDepth Base .tm
  | eps (type : NoDepth Base .ty) (predicate : NoDepth Base .tm) : NoDepth Base .tm
  | abs (carrier : NoDepth Base .ty) (predicate value : NoDepth Base .tm) : NoDepth Base .tm
  | rep (carrier : NoDepth Base .ty) (predicate value : NoDepth Base .tm) : NoDepth Base .tm
  deriving Repr

/-- HOL syntax retaining binder depth but erasing the type/term sort.  The
depths on annotation and subtype-predicate children retain the original
grammar's scoping invariants. -/
inductive NoSort (Base : Type u) : Nat → Type u where
  | base (name : Base) : NoSort Base 0
  | boolTy : NoSort Base 0
  | natTy : NoSort Base 0
  | arr (domain codomain : NoSort Base 0) : NoSort Base 0
  | sub (carrier : NoSort Base 0) (predicate : NoSort Base 1) : NoSort Base 0
  | bound {d : Nat} (index : Fin d) : NoSort Base d
  | free {d : Nat} (name : Nat) : NoSort Base d
  | app {d : Nat} (function argument : NoSort Base d) : NoSort Base d
  | lam {d : Nat} (domain : NoSort Base 0) (body : NoSort Base (d + 1)) : NoSort Base d
  | bool {d : Nat} (value : Bool) : NoSort Base d
  | zero {d : Nat} : NoSort Base d
  | succ {d : Nat} (value : NoSort Base d) : NoSort Base d
  | eq {d : Nat} (type : NoSort Base 0) (left right : NoSort Base d) : NoSort Base d
  | eps {d : Nat} (type : NoSort Base 0) (predicate : NoSort Base d) : NoSort Base d
  | abs {d : Nat} (carrier : NoSort Base 0) (predicate : NoSort Base 1)
      (value : NoSort Base d) : NoSort Base d
  | rep {d : Nat} (carrier : NoSort Base 0) (predicate : NoSort Base 1)
      (value : NoSort Base d) : NoSort Base d
  deriving Repr

/-- Completely extrinsic HOL syntax. -/
inductive Unindexed (Base : Type u) where
  | base (name : Base) | boolTy | natTy
  | arr (domain codomain : Unindexed Base)
  | sub (carrier predicate : Unindexed Base)
  | bound (index : Nat) | free (name : Nat)
  | app (function argument : Unindexed Base)
  | lam (domain body : Unindexed Base)
  | bool (value : Bool) | zero | succ (value : Unindexed Base)
  | eq (type left right : Unindexed Base)
  | eps (type predicate : Unindexed Base)
  | abs (carrier predicate value : Unindexed Base)
  | rep (carrier predicate value : Unindexed Base)
  | emptyCtx
  | freeCtx (name : Nat) (type tail : Unindexed Base)
  | boundCtx (type tail : Unindexed Base)
  deriving Repr

namespace Erasure

def noDepth : {sort : HolSort} → {depth : Nat} → Hol Base sort depth → NoDepth Base sort
  | _, _, .base n => .base n | _, _, .boolTy => .boolTy | _, _, .natTy => .natTy
  | _, _, .arr a b => .arr (noDepth a) (noDepth b)
  | _, _, .sub a p => .sub (noDepth a) (noDepth p)
  | _, _, .bound i => .bound i | _, _, .free n => .free n
  | _, _, .app f x => .app (noDepth f) (noDepth x)
  | _, _, .lam a b => .lam (noDepth a) (noDepth b)
  | _, _, .bool b => .bool b | _, _, .zero => .zero | _, _, .succ x => .succ (noDepth x)
  | _, _, .eq a x y => .eq (noDepth a) (noDepth x) (noDepth y)
  | _, _, .eps a p => .eps (noDepth a) (noDepth p)
  | _, _, .abs a p x => .abs (noDepth a) (noDepth p) (noDepth x)
  | _, _, .rep a p x => .rep (noDepth a) (noDepth p) (noDepth x)

def noSort : {sort : HolSort} → {depth : Nat} → Hol Base sort depth → NoSort Base depth
  | _, _, .base n => .base n | _, _, .boolTy => .boolTy | _, _, .natTy => .natTy
  | _, _, .arr a b => .arr (noSort a) (noSort b)
  | _, _, .sub a p => .sub (noSort a) (noSort p)
  | _, _, .bound i => .bound i | _, _, .free n => .free n
  | _, _, .app f x => .app (noSort f) (noSort x)
  | _, _, .lam a b => .lam (noSort a) (noSort b)
  | _, _, .bool b => .bool b | _, _, .zero => .zero | _, _, .succ x => .succ (noSort x)
  | _, _, .eq a x y => .eq (noSort a) (noSort x) (noSort y)
  | _, _, .eps a p => .eps (noSort a) (noSort p)
  | _, _, .abs a p x => .abs (noSort a) (noSort p) (noSort x)
  | _, _, .rep a p x => .rep (noSort a) (noSort p) (noSort x)

def noDepthToUnindexed : {sort : HolSort} → NoDepth Base sort → Unindexed Base
  | _, .base n => .base n | _, .boolTy => .boolTy | _, .natTy => .natTy
  | _, .arr a b => .arr (noDepthToUnindexed a) (noDepthToUnindexed b)
  | _, .sub a p => .sub (noDepthToUnindexed a) (noDepthToUnindexed p)
  | _, .bound i => .bound i | _, .free n => .free n
  | _, .app f x => .app (noDepthToUnindexed f) (noDepthToUnindexed x)
  | _, .lam a b => .lam (noDepthToUnindexed a) (noDepthToUnindexed b)
  | _, .bool b => .bool b | _, .zero => .zero | _, .succ x => .succ (noDepthToUnindexed x)
  | _, .eq a x y => .eq (noDepthToUnindexed a) (noDepthToUnindexed x) (noDepthToUnindexed y)
  | _, .eps a p => .eps (noDepthToUnindexed a) (noDepthToUnindexed p)
  | _, .abs a p x => .abs (noDepthToUnindexed a) (noDepthToUnindexed p) (noDepthToUnindexed x)
  | _, .rep a p x => .rep (noDepthToUnindexed a) (noDepthToUnindexed p) (noDepthToUnindexed x)

def noSortToUnindexed : {depth : Nat} → NoSort Base depth → Unindexed Base
  | _, .base n => .base n | _, .boolTy => .boolTy | _, .natTy => .natTy
  | _, .arr a b => .arr (noSortToUnindexed a) (noSortToUnindexed b)
  | _, .sub a p => .sub (noSortToUnindexed a) (noSortToUnindexed p)
  | _, .bound i => .bound i | _, .free n => .free n
  | _, .app f x => .app (noSortToUnindexed f) (noSortToUnindexed x)
  | _, .lam a b => .lam (noSortToUnindexed a) (noSortToUnindexed b)
  | _, .bool b => .bool b | _, .zero => .zero | _, .succ x => .succ (noSortToUnindexed x)
  | _, .eq a x y => .eq (noSortToUnindexed a) (noSortToUnindexed x) (noSortToUnindexed y)
  | _, .eps a p => .eps (noSortToUnindexed a) (noSortToUnindexed p)
  | _, .abs a p x => .abs (noSortToUnindexed a) (noSortToUnindexed p) (noSortToUnindexed x)
  | _, .rep a p x => .rep (noSortToUnindexed a) (noSortToUnindexed p) (noSortToUnindexed x)

def unindexed (x : Hol Base sort depth) : Unindexed Base := noDepthToUnindexed (noDepth x)

@[simp] theorem square (x : Hol Base sort depth) :
    noDepthToUnindexed (noDepth x) = noSortToUnindexed (noSort x) := by
  induction x <;> simp_all [noDepth, noSort, noDepthToUnindexed, noSortToUnindexed]

/-- Computable scope checker: the partial inverse of depth erasure. -/
def checkDepth : (sort : HolSort) → (depth : Nat) → NoDepth Base sort → Option (Hol Base sort depth)
  | .ty, d, .base n => if h : d = 0 then by subst d; exact some (.base n) else none
  | .ty, d, .boolTy => if h : d = 0 then by subst d; exact some .boolTy else none
  | .ty, d, .natTy => if h : d = 0 then by subst d; exact some .natTy else none
  | .ty, d, .arr a b => if h : d = 0 then by
      subst d; exact return .arr (← checkDepth .ty 0 a) (← checkDepth .ty 0 b)
    else none
  | .ty, d, .sub a p => if h : d = 0 then by
      subst d; exact return .sub (← checkDepth .ty 0 a) (← checkDepth .tm 1 p)
    else none
  | .tm, d, .bound i => if h : i < d then some (.bound ⟨i, h⟩) else none
  | .tm, d, .free n => some (.free n)
  | .tm, d, .app f x => return .app (← checkDepth .tm d f) (← checkDepth .tm d x)
  | .tm, d, .lam a b => return .lam (← checkDepth .ty 0 a) (← checkDepth .tm (d+1) b)
  | .tm, d, .bool b => some (.bool b) | .tm, d, .zero => some .zero
  | .tm, d, .succ x => return .succ (← checkDepth .tm d x)
  | .tm, d, .eq a x y => return .eq (← checkDepth .ty 0 a) (← checkDepth .tm d x) (← checkDepth .tm d y)
  | .tm, d, .eps a p => return .eps (← checkDepth .ty 0 a) (← checkDepth .tm d p)
  | .tm, d, .abs a p x => return .abs (← checkDepth .ty 0 a) (← checkDepth .tm 1 p) (← checkDepth .tm d x)
  | .tm, d, .rep a p x => return .rep (← checkDepth .ty 0 a) (← checkDepth .tm 1 p) (← checkDepth .tm d x)

/-- Computable sort checker: the partial inverse of sort erasure. -/
def checkSort : {depth : Nat} → (sort : HolSort) → NoSort Base depth → Option (Hol Base sort depth)
  | _, .ty, .base n => some (.base n)
  | _, .ty, .boolTy => some .boolTy
  | _, .ty, .natTy => some .natTy
  | _, .ty, .arr a b => return .arr (← checkSort .ty a) (← checkSort .ty b)
  | _, .ty, .sub a p => return .sub (← checkSort .ty a) (← checkSort .tm p)
  | _, .tm, .bound i => some (.bound i) | _, .tm, .free n => some (.free n)
  | _, .tm, .app f x => return .app (← checkSort .tm f) (← checkSort .tm x)
  | _, .tm, .lam a b => return .lam (← checkSort .ty a) (← checkSort .tm b)
  | _, .tm, .bool b => some (.bool b) | _, .tm, .zero => some .zero
  | _, .tm, .succ x => return .succ (← checkSort .tm x)
  | _, .tm, .eq a x y => return .eq (← checkSort .ty a) (← checkSort .tm x) (← checkSort .tm y)
  | _, .tm, .eps a p => return .eps (← checkSort .ty a) (← checkSort .tm p)
  | _, .tm, .abs a p x => return .abs (← checkSort .ty a) (← checkSort .tm p) (← checkSort .tm x)
  | _, .tm, .rep a p x => return .rep (← checkSort .ty a) (← checkSort .tm p) (← checkSort .tm x)
  | _, _, _ => none

@[simp] theorem checkDepth_noDepth (x : Hol Base sort depth) : checkDepth sort depth (noDepth x) = some x := by
  induction x <;> simp_all [noDepth, checkDepth]

@[simp] theorem checkSort_noSort (x : Hol Base sort depth) : checkSort sort (noSort x) = some x := by
  induction x <;> simp_all [noSort, checkSort]

theorem noDepth_injective : Function.Injective (noDepth : Hol Base sort depth → NoDepth Base sort) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkDepth_noDepth x, ← checkDepth_noDepth y, h])

theorem noSort_injective : Function.Injective (noSort : Hol Base sort depth → NoSort Base depth) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkSort_noSort x, ← checkSort_noSort y, h])

/-- Computable sort checker for completely unindexed trees. -/
def checkUnindexedSort : (sort : HolSort) → Unindexed Base → Option (NoDepth Base sort)
  | .ty, .base n => some (.base n) | .ty, .boolTy => some .boolTy
  | .ty, .natTy => some .natTy
  | .ty, .arr a b => return .arr (← checkUnindexedSort .ty a) (← checkUnindexedSort .ty b)
  | .ty, .sub a p => return .sub (← checkUnindexedSort .ty a) (← checkUnindexedSort .tm p)
  | .tm, .bound i => some (.bound i) | .tm, .free n => some (.free n)
  | .tm, .app f x => return .app (← checkUnindexedSort .tm f) (← checkUnindexedSort .tm x)
  | .tm, .lam a b => return .lam (← checkUnindexedSort .ty a) (← checkUnindexedSort .tm b)
  | .tm, .bool b => some (.bool b) | .tm, .zero => some .zero
  | .tm, .succ x => return .succ (← checkUnindexedSort .tm x)
  | .tm, .eq a x y => return (NoDepth.eq (← checkUnindexedSort .ty a)
      (← checkUnindexedSort .tm x) (← checkUnindexedSort .tm y))
  | .tm, .eps a p => return .eps (← checkUnindexedSort .ty a) (← checkUnindexedSort .tm p)
  | .tm, .abs a p x => return (NoDepth.abs (← checkUnindexedSort .ty a)
      (← checkUnindexedSort .tm p) (← checkUnindexedSort .tm x))
  | .tm, .rep a p x => return (NoDepth.rep (← checkUnindexedSort .ty a)
      (← checkUnindexedSort .tm p) (← checkUnindexedSort .tm x))
  | _, .emptyCtx | _, .freeCtx .. | _, .boundCtx .. => none
  | _, _ => none

@[simp] theorem checkUnindexedSort_noDepth (x : NoDepth Base sort) :
    checkUnindexedSort sort (noDepthToUnindexed x) = some x := by
  induction x <;> simp_all [noDepthToUnindexed, checkUnindexedSort]

theorem noDepthToUnindexed_injective :
    Function.Injective (noDepthToUnindexed : NoDepth Base sort → Unindexed Base) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkUnindexedSort_noDepth x, ← checkUnindexedSort_noDepth y, h])

/-- The computable partial inverse of simultaneous sort and depth erasure. -/
def checkUnindexed (sort : HolSort) (depth : Nat) (x : Unindexed Base) :
    Option (Hol Base sort depth) := do
  checkDepth sort depth (← checkUnindexedSort sort x)

@[simp] theorem checkUnindexed_unindexed (x : Hol Base sort depth) :
    checkUnindexed sort depth (unindexed x) = some x := by
  unfold checkUnindexed unindexed
  rw [checkUnindexedSort_noDepth]
  exact checkDepth_noDepth x

theorem unindexed_injective :
    Function.Injective (unindexed : Hol Base sort depth → Unindexed Base) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkUnindexed_unindexed x, ← checkUnindexed_unindexed y, h])

/-- Computable partial inverse of the depth-indexed, sort-erased embedding. -/
def checkUnindexedDepth (depth : Nat) (x : Unindexed Base) : Option (NoSort Base depth) :=
  match x with
  | .base n => if h : depth = 0 then by subst depth; exact some (.base n) else none
  | .boolTy => if h : depth = 0 then by subst depth; exact some .boolTy else none
  | .natTy => if h : depth = 0 then by subst depth; exact some .natTy else none
  | .arr a b => if h : depth = 0 then by
      subst depth; exact return .arr (← checkUnindexedDepth 0 a) (← checkUnindexedDepth 0 b)
    else none
  | .sub a p => if h : depth = 0 then by
      subst depth; exact return .sub (← checkUnindexedDepth 0 a) (← checkUnindexedDepth 1 p)
    else none
  | .bound i => if h : i < depth then some (.bound ⟨i, h⟩) else none
  | .free n => some (.free n)
  | .app f x => return .app (← checkUnindexedDepth depth f) (← checkUnindexedDepth depth x)
  | .lam a b => return .lam (← checkUnindexedDepth 0 a) (← checkUnindexedDepth (depth + 1) b)
  | .bool b => some (.bool b) | .zero => some .zero
  | .succ x => return .succ (← checkUnindexedDepth depth x)
  | .eq a x y => return (NoSort.eq (← checkUnindexedDepth 0 a)
      (← checkUnindexedDepth depth x) (← checkUnindexedDepth depth y))
  | .eps a p => return .eps (← checkUnindexedDepth 0 a) (← checkUnindexedDepth depth p)
  | .abs a p x => return (NoSort.abs (← checkUnindexedDepth 0 a)
      (← checkUnindexedDepth 1 p) (← checkUnindexedDepth depth x))
  | .rep a p x => return (NoSort.rep (← checkUnindexedDepth 0 a)
      (← checkUnindexedDepth 1 p) (← checkUnindexedDepth depth x))
  | .emptyCtx | .freeCtx .. | .boundCtx .. => none

@[simp] theorem checkUnindexedDepth_noSort (x : NoSort Base depth) :
    checkUnindexedDepth depth (noSortToUnindexed x) = some x := by
  induction x <;> simp_all [checkUnindexedDepth, noSortToUnindexed]

theorem noSortToUnindexed_injective :
    Function.Injective (noSortToUnindexed : NoSort Base depth → Unindexed Base) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkUnindexedDepth_noSort x, ← checkUnindexedDepth_noSort y, h])

end Erasure

/-! Typing and equality are transported along each injective embedding.  These
definitions expose precisely the same rules while making malformed extrinsic
trees untypable. -/
namespace NoDepth
def Kinded (A : NoDepth Base .ty) : Prop := ∃ a, Nucleus.HolLN.Kinded a ∧ Erasure.noDepth a = A
def HasType (Δ : FreeCtx Base) {depth} (Γ : BoundCtx Base depth)
    (t : NoDepth Base .tm) (A : NoDepth Base .ty) : Prop :=
  ∃ t₀ A₀, Nucleus.HolLN.HasType Δ Γ t₀ A₀ ∧ Erasure.noDepth t₀ = t ∧ Erasure.noDepth A₀ = A
def EqTm (Δ : FreeCtx Base) {depth} (Γ : BoundCtx Base depth)
    (t u : NoDepth Base .tm) (A : NoDepth Base .ty) : Prop :=
  ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ Γ t₀ u₀ A₀) ∧
    Erasure.noDepth t₀ = t ∧ Erasure.noDepth u₀ = u ∧ Erasure.noDepth A₀ = A
end NoDepth

namespace NoSort
def Kinded (A : NoSort Base 0) : Prop := ∃ a, Nucleus.HolLN.Kinded a ∧ Erasure.noSort a = A
def HasType (Δ : FreeCtx Base) {depth} (Γ : BoundCtx Base depth)
    (t : NoSort Base depth) (A : NoSort Base 0) : Prop :=
  ∃ t₀ A₀, Nucleus.HolLN.HasType Δ Γ t₀ A₀ ∧ Erasure.noSort t₀ = t ∧ Erasure.noSort A₀ = A
def EqTm (Δ : FreeCtx Base) {depth} (Γ : BoundCtx Base depth)
    (t u : NoSort Base depth) (A : NoSort Base 0) : Prop :=
  ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ Γ t₀ u₀ A₀) ∧
    Erasure.noSort t₀ = t ∧ Erasure.noSort u₀ = u ∧ Erasure.noSort A₀ = A
end NoSort

namespace Unindexed
def Kinded (A : Unindexed Base) : Prop := ∃ a, Nucleus.HolLN.Kinded a ∧ Erasure.unindexed a = A
def HasType (Δ : FreeCtx Base) {depth} (Γ : BoundCtx Base depth)
    (t A : Unindexed Base) : Prop :=
  ∃ t₀ A₀, Nucleus.HolLN.HasType Δ Γ t₀ A₀ ∧ Erasure.unindexed t₀ = t ∧ Erasure.unindexed A₀ = A
def EqTm (Δ : FreeCtx Base) {depth} (Γ : BoundCtx Base depth)
    (t u A : Unindexed Base) : Prop :=
  ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Δ Γ t₀ u₀ A₀) ∧
    Erasure.unindexed t₀ = t ∧ Erasure.unindexed u₀ = u ∧ Erasure.unindexed A₀ = A
end Unindexed

theorem noDepth_wellTyped_iff_unique {Δ : FreeCtx Base} {Γ : BoundCtx Base depth}
    {t : NoDepth Base .tm} {A : NoDepth Base .ty} :
    NoDepth.HasType Δ Γ t A ↔ ∃! p : Tm Base depth × Ty Base,
      HasType Δ Γ p.1 p.2 ∧ Erasure.noDepth p.1 = t ∧ Erasure.noDepth p.2 = A := by
  constructor
  · rintro ⟨t₀, A₀, ht, rfl, rfl⟩
    refine ⟨⟨t₀, A₀⟩, ⟨ht, rfl, rfl⟩, ?_⟩
    rintro ⟨t₁, A₁⟩ ⟨_, ht₁, hA₁⟩
    exact Prod.ext (Erasure.noDepth_injective ht₁) (Erasure.noDepth_injective hA₁)
  · rintro ⟨⟨t₀, A₀⟩, ⟨ht, et, eA⟩, _⟩; exact ⟨t₀, A₀, ht, et, eA⟩

theorem noSort_wellTyped_iff_unique {Δ : FreeCtx Base} {Γ : BoundCtx Base depth}
    {t : NoSort Base depth} {A : NoSort Base 0} :
    NoSort.HasType Δ Γ t A ↔ ∃! p : Tm Base depth × Ty Base,
      HasType Δ Γ p.1 p.2 ∧ Erasure.noSort p.1 = t ∧ Erasure.noSort p.2 = A := by
  constructor
  · rintro ⟨t₀, A₀, ht, rfl, rfl⟩
    refine ⟨⟨t₀, A₀⟩, ⟨ht, rfl, rfl⟩, ?_⟩
    rintro ⟨t₁, A₁⟩ ⟨_, ht₁, hA₁⟩
    exact Prod.ext (Erasure.noSort_injective ht₁) (Erasure.noSort_injective hA₁)
  · rintro ⟨⟨t₀, A₀⟩, ⟨ht, et, eA⟩, _⟩; exact ⟨t₀, A₀, ht, et, eA⟩

theorem unindexed_wellTyped_iff_unique {Δ : FreeCtx Base} {Γ : BoundCtx Base depth}
    {t A : Unindexed Base} :
    Unindexed.HasType Δ Γ t A ↔ ∃! p : Tm Base depth × Ty Base,
      HasType Δ Γ p.1 p.2 ∧ Erasure.unindexed p.1 = t ∧ Erasure.unindexed p.2 = A := by
  constructor
  · rintro ⟨t₀, A₀, ht, rfl, rfl⟩
    refine ⟨⟨t₀, A₀⟩, ⟨ht, rfl, rfl⟩, ?_⟩
    rintro ⟨t₁, A₁⟩ ⟨_, ht₁, hA₁⟩
    exact Prod.ext (Erasure.unindexed_injective ht₁) (Erasure.unindexed_injective hA₁)
  · rintro ⟨⟨t₀, A₀⟩, ⟨ht, et, eA⟩, _⟩; exact ⟨t₀, A₀, ht, et, eA⟩

/-! All four representations share one JSON image.  Thus changing intrinsic
indices never changes content addressing or wire format. -/
namespace VariantJson

open Nucleus.HolLN.Json

private def scalar (x : Json.Scalar Base) : Json.Tree Base := .scalar x
private def tagged (tag : String) (fields : RawSyn String (Json.Scalar Base) .obj := .objNil) :
    Json.Tree Base := .map (.objCons "tag" (scalar (.string tag)) fields)
private def field (key : String) (value : Json.Tree Base)
    (tail : RawSyn String (Json.Scalar Base) .obj) : RawSyn String (Json.Scalar Base) .obj :=
  .objCons key value tail

/-- Total JSON serialization of the fully extrinsic syntax. -/
def encode : Unindexed Base → Json.Tree Base
  | .base n => tagged "ty.base" (field "name" (scalar (.base n)) .objNil)
  | .boolTy => tagged "ty.bool" | .natTy => tagged "ty.ind"
  | .arr a b => tagged "ty.arr" (field "domain" (encode a) (field "codomain" (encode b) .objNil))
  | .sub a p => tagged "ty.sub" (field "carrier" (encode a) (field "predicate" (encode p) .objNil))
  | .bound i => tagged "tm.bound" (field "index" (scalar (.nat i)) .objNil)
  | .free n => tagged "tm.free" (field "name" (scalar (.nat n)) .objNil)
  | .app f x => tagged "tm.app" (field "function" (encode f) (field "argument" (encode x) .objNil))
  | .lam a b => tagged "tm.lam" (field "domain" (encode a) (field "body" (encode b) .objNil))
  | .bool b => tagged "tm.bool" (field "value" (scalar (.bool b)) .objNil)
  | .zero => tagged "tm.zero"
  | .succ x => tagged "tm.succ" (field "value" (encode x) .objNil)
  | .eq a x y => tagged "tm.eq" (field "type" (encode a)
      (field "left" (encode x) (field "right" (encode y) .objNil)))
  | .eps a p => tagged "tm.eps" (field "type" (encode a) (field "predicate" (encode p) .objNil))
  | .abs a p x => tagged "tm.abs" (field "carrier" (encode a)
      (field "predicate" (encode p) (field "value" (encode x) .objNil)))
  | .rep a p x => tagged "tm.rep" (field "carrier" (encode a)
      (field "predicate" (encode p) (field "value" (encode x) .objNil)))
  | .emptyCtx => tagged "ctx.empty"
  | .freeCtx n a tail => tagged "ctx.free" (field "name" (scalar (.nat n))
      (field "type" (encode a) (field "body" (encode tail) .objNil)))
  | .boundCtx a tail => tagged "ctx.bound"
      (field "type" (encode a) (field "body" (encode tail) .objNil))

def encodeNoDepth (x : NoDepth Base sort) : Json.Tree Base :=
  encode (Erasure.noDepthToUnindexed x)
def encodeNoSort (x : NoSort Base depth) : Json.Tree Base :=
  encode (Erasure.noSortToUnindexed x)

@[simp] theorem encode_embeddings_agree (x : Hol Base sort depth) :
    encodeNoDepth (Erasure.noDepth x) = encodeNoSort (Erasure.noSort x) := by
  simp [encodeNoDepth, encodeNoSort, Erasure.square]

/-- The new encoders reproduce the established HOL-LN JSON codec byte-for-tree. -/
@[simp] theorem encode_unindexed_eq_original (x : Hol Base sort depth) :
    encode (Erasure.unindexed x) = Json.Codec.encode x := by
  induction x <;> simp_all [Erasure.unindexed, Erasure.noDepth,
    Erasure.noDepthToUnindexed, encode, Json.Codec.encode, Json.Codec.encodeWith,
    Json.Schema.v0, tagged, field, scalar] <;> rfl

end VariantJson

end Nucleus.HolLN
