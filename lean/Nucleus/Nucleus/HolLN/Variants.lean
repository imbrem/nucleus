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
inductive Tree.Sorted (Base : Type u) : HolSort → Type u where
  | base (name : Base) : Tree.Sorted Base .ty
  | boolTy : Tree.Sorted Base .ty
  | natTy : Tree.Sorted Base .ty
  | arr (domain codomain : Tree.Sorted Base .ty) : Tree.Sorted Base .ty
  | sub (carrier : Tree.Sorted Base .ty) (predicate : Tree.Sorted Base .tm) : Tree.Sorted Base .ty
  | bound (index : Nat) : Tree.Sorted Base .tm
  | free (name : Nat) (type : Tree.Sorted Base .ty) : Tree.Sorted Base .tm
  | app (function argument : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | lam (domain : Tree.Sorted Base .ty) (body : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | bool (value : Bool) : Tree.Sorted Base .tm
  | zero : Tree.Sorted Base .tm
  | succ (value : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | eq (type : Tree.Sorted Base .ty) (left right : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | eps (type : Tree.Sorted Base .ty) (predicate : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | abs (carrier : Tree.Sorted Base .ty) (predicate value : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | rep (carrier : Tree.Sorted Base .ty) (predicate value : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  deriving Repr

/-- HOL syntax retaining binder depth but erasing the type/term sort.  The
depths on annotation and subtype-predicate children retain the original
grammar's scoping invariants. -/
inductive Tree.Scoped (Base : Type u) : Nat → Type u where
  | base (name : Base) : Tree.Scoped Base 0
  | boolTy : Tree.Scoped Base 0
  | natTy : Tree.Scoped Base 0
  | arr (domain codomain : Tree.Scoped Base 0) : Tree.Scoped Base 0
  | sub (carrier : Tree.Scoped Base 0) (predicate : Tree.Scoped Base 1) : Tree.Scoped Base 0
  | bound {d : Nat} (index : Fin d) : Tree.Scoped Base d
  | free {d : Nat} (name : Nat) (type : Tree.Scoped Base 0) : Tree.Scoped Base d
  | app {d : Nat} (function argument : Tree.Scoped Base d) : Tree.Scoped Base d
  | lam {d : Nat} (domain : Tree.Scoped Base 0) (body : Tree.Scoped Base (d + 1)) : Tree.Scoped Base d
  | bool {d : Nat} (value : Bool) : Tree.Scoped Base d
  | zero {d : Nat} : Tree.Scoped Base d
  | succ {d : Nat} (value : Tree.Scoped Base d) : Tree.Scoped Base d
  | eq {d : Nat} (type : Tree.Scoped Base 0) (left right : Tree.Scoped Base d) : Tree.Scoped Base d
  | eps {d : Nat} (type : Tree.Scoped Base 0) (predicate : Tree.Scoped Base d) : Tree.Scoped Base d
  | abs {d : Nat} (carrier : Tree.Scoped Base 0) (predicate : Tree.Scoped Base 1)
      (value : Tree.Scoped Base d) : Tree.Scoped Base d
  | rep {d : Nat} (carrier : Tree.Scoped Base 0) (predicate : Tree.Scoped Base 1)
      (value : Tree.Scoped Base d) : Tree.Scoped Base d
  deriving Repr

/-- Completely extrinsic HOL syntax. -/
inductive Tree.Raw (Base : Type u) where
  | base (name : Base) | boolTy | natTy
  | arr (domain codomain : Tree.Raw Base)
  | sub (carrier predicate : Tree.Raw Base)
  | bound (index : Nat) | free (name : Nat) (type : Tree.Raw Base)
  | app (function argument : Tree.Raw Base)
  | lam (domain body : Tree.Raw Base)
  | bool (value : Bool) | zero | succ (value : Tree.Raw Base)
  | eq (type left right : Tree.Raw Base)
  | eps (type predicate : Tree.Raw Base)
  | abs (carrier predicate value : Tree.Raw Base)
  | rep (carrier predicate value : Tree.Raw Base)
  | emptyCtx
  | boundCtx (type tail : Tree.Raw Base)
  deriving Repr

namespace Erasure

def toSorted : {sort : HolSort} → {depth : Nat} → Hol Base sort depth → Tree.Sorted Base sort
  | _, _, .base n => .base n | _, _, .boolTy => .boolTy | _, _, .natTy => .natTy
  | _, _, .arr a b => .arr (toSorted a) (toSorted b)
  | _, _, .sub a p => .sub (toSorted a) (toSorted p)
  | _, _, .bound i => .bound i | _, _, .free n A => .free n (toSorted A)
  | _, _, .app f x => .app (toSorted f) (toSorted x)
  | _, _, .lam a b => .lam (toSorted a) (toSorted b)
  | _, _, .bool b => .bool b | _, _, .zero => .zero | _, _, .succ x => .succ (toSorted x)
  | _, _, .eq a x y => .eq (toSorted a) (toSorted x) (toSorted y)
  | _, _, .eps a p => .eps (toSorted a) (toSorted p)
  | _, _, .abs a p x => .abs (toSorted a) (toSorted p) (toSorted x)
  | _, _, .rep a p x => .rep (toSorted a) (toSorted p) (toSorted x)

def toScoped : {sort : HolSort} → {depth : Nat} → Hol Base sort depth → Tree.Scoped Base depth
  | _, _, .base n => .base n | _, _, .boolTy => .boolTy | _, _, .natTy => .natTy
  | _, _, .arr a b => .arr (toScoped a) (toScoped b)
  | _, _, .sub a p => .sub (toScoped a) (toScoped p)
  | _, _, .bound i => .bound i | _, _, .free n A => .free n (toScoped A)
  | _, _, .app f x => .app (toScoped f) (toScoped x)
  | _, _, .lam a b => .lam (toScoped a) (toScoped b)
  | _, _, .bool b => .bool b | _, _, .zero => .zero | _, _, .succ x => .succ (toScoped x)
  | _, _, .eq a x y => .eq (toScoped a) (toScoped x) (toScoped y)
  | _, _, .eps a p => .eps (toScoped a) (toScoped p)
  | _, _, .abs a p x => .abs (toScoped a) (toScoped p) (toScoped x)
  | _, _, .rep a p x => .rep (toScoped a) (toScoped p) (toScoped x)

def sortedToRaw : {sort : HolSort} → Tree.Sorted Base sort → Tree.Raw Base
  | _, .base n => .base n | _, .boolTy => .boolTy | _, .natTy => .natTy
  | _, .arr a b => .arr (sortedToRaw a) (sortedToRaw b)
  | _, .sub a p => .sub (sortedToRaw a) (sortedToRaw p)
  | _, .bound i => .bound i | _, .free n A => .free n (sortedToRaw A)
  | _, .app f x => .app (sortedToRaw f) (sortedToRaw x)
  | _, .lam a b => .lam (sortedToRaw a) (sortedToRaw b)
  | _, .bool b => .bool b | _, .zero => .zero | _, .succ x => .succ (sortedToRaw x)
  | _, .eq a x y => .eq (sortedToRaw a) (sortedToRaw x) (sortedToRaw y)
  | _, .eps a p => .eps (sortedToRaw a) (sortedToRaw p)
  | _, .abs a p x => .abs (sortedToRaw a) (sortedToRaw p) (sortedToRaw x)
  | _, .rep a p x => .rep (sortedToRaw a) (sortedToRaw p) (sortedToRaw x)

def scopedToRaw : {depth : Nat} → Tree.Scoped Base depth → Tree.Raw Base
  | _, .base n => .base n | _, .boolTy => .boolTy | _, .natTy => .natTy
  | _, .arr a b => .arr (scopedToRaw a) (scopedToRaw b)
  | _, .sub a p => .sub (scopedToRaw a) (scopedToRaw p)
  | _, .bound i => .bound i | _, .free n A => .free n (scopedToRaw A)
  | _, .app f x => .app (scopedToRaw f) (scopedToRaw x)
  | _, .lam a b => .lam (scopedToRaw a) (scopedToRaw b)
  | _, .bool b => .bool b | _, .zero => .zero | _, .succ x => .succ (scopedToRaw x)
  | _, .eq a x y => .eq (scopedToRaw a) (scopedToRaw x) (scopedToRaw y)
  | _, .eps a p => .eps (scopedToRaw a) (scopedToRaw p)
  | _, .abs a p x => .abs (scopedToRaw a) (scopedToRaw p) (scopedToRaw x)
  | _, .rep a p x => .rep (scopedToRaw a) (scopedToRaw p) (scopedToRaw x)

def toRaw (x : Hol Base sort depth) : Tree.Raw Base := sortedToRaw (toSorted x)

@[simp] theorem square (x : Hol Base sort depth) :
    sortedToRaw (toSorted x) = scopedToRaw (toScoped x) := by
  induction x <;> simp_all [toSorted, toScoped, sortedToRaw, scopedToRaw]

/-- Computable scope checker: the partial inverse of depth erasure. -/
def checkDepth : (sort : HolSort) → (depth : Nat) → Tree.Sorted Base sort → Option (Hol Base sort depth)
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
  | .tm, d, .free n A => return .free n (← checkDepth .ty 0 A)
  | .tm, d, .app f x => return .app (← checkDepth .tm d f) (← checkDepth .tm d x)
  | .tm, d, .lam a b => return .lam (← checkDepth .ty 0 a) (← checkDepth .tm (d+1) b)
  | .tm, d, .bool b => some (.bool b) | .tm, d, .zero => some .zero
  | .tm, d, .succ x => return .succ (← checkDepth .tm d x)
  | .tm, d, .eq a x y => return .eq (← checkDepth .ty 0 a) (← checkDepth .tm d x) (← checkDepth .tm d y)
  | .tm, d, .eps a p => return .eps (← checkDepth .ty 0 a) (← checkDepth .tm d p)
  | .tm, d, .abs a p x => return .abs (← checkDepth .ty 0 a) (← checkDepth .tm 1 p) (← checkDepth .tm d x)
  | .tm, d, .rep a p x => return .rep (← checkDepth .ty 0 a) (← checkDepth .tm 1 p) (← checkDepth .tm d x)

/-- Computable sort checker: the partial inverse of sort erasure. -/
def checkSort : {depth : Nat} → (sort : HolSort) → Tree.Scoped Base depth → Option (Hol Base sort depth)
  | _, .ty, .base n => some (.base n)
  | _, .ty, .boolTy => some .boolTy
  | _, .ty, .natTy => some .natTy
  | _, .ty, .arr a b => return .arr (← checkSort .ty a) (← checkSort .ty b)
  | _, .ty, .sub a p => return .sub (← checkSort .ty a) (← checkSort .tm p)
  | _, .tm, .bound i => some (.bound i)
  | _, .tm, .free n A => return .free n (← checkSort .ty A)
  | _, .tm, .app f x => return .app (← checkSort .tm f) (← checkSort .tm x)
  | _, .tm, .lam a b => return .lam (← checkSort .ty a) (← checkSort .tm b)
  | _, .tm, .bool b => some (.bool b) | _, .tm, .zero => some .zero
  | _, .tm, .succ x => return .succ (← checkSort .tm x)
  | _, .tm, .eq a x y => return .eq (← checkSort .ty a) (← checkSort .tm x) (← checkSort .tm y)
  | _, .tm, .eps a p => return .eps (← checkSort .ty a) (← checkSort .tm p)
  | _, .tm, .abs a p x => return .abs (← checkSort .ty a) (← checkSort .tm p) (← checkSort .tm x)
  | _, .tm, .rep a p x => return .rep (← checkSort .ty a) (← checkSort .tm p) (← checkSort .tm x)
  | _, _, _ => none

@[simp] theorem checkDepth_toSorted (x : Hol Base sort depth) : checkDepth sort depth (toSorted x) = some x := by
  induction x <;> simp_all [toSorted, checkDepth]

@[simp] theorem checkSort_toScoped (x : Hol Base sort depth) : checkSort sort (toScoped x) = some x := by
  induction x <;> simp_all [toScoped, checkSort]

theorem toSorted_injective : Function.Injective (toSorted : Hol Base sort depth → Tree.Sorted Base sort) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkDepth_toSorted x, ← checkDepth_toSorted y, h])

theorem toScoped_injective : Function.Injective (toScoped : Hol Base sort depth → Tree.Scoped Base depth) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkSort_toScoped x, ← checkSort_toScoped y, h])

/-- Computable sort checker for completely toRaw trees. -/
def checkRawSort : (sort : HolSort) → Tree.Raw Base → Option (Tree.Sorted Base sort)
  | .ty, .base n => some (.base n) | .ty, .boolTy => some .boolTy
  | .ty, .natTy => some .natTy
  | .ty, .arr a b => return .arr (← checkRawSort .ty a) (← checkRawSort .ty b)
  | .ty, .sub a p => return .sub (← checkRawSort .ty a) (← checkRawSort .tm p)
  | .tm, .bound i => some (.bound i)
  | .tm, .free n A => return .free n (← checkRawSort .ty A)
  | .tm, .app f x => return .app (← checkRawSort .tm f) (← checkRawSort .tm x)
  | .tm, .lam a b => return .lam (← checkRawSort .ty a) (← checkRawSort .tm b)
  | .tm, .bool b => some (.bool b) | .tm, .zero => some .zero
  | .tm, .succ x => return .succ (← checkRawSort .tm x)
  | .tm, .eq a x y => return (Tree.Sorted.eq (← checkRawSort .ty a)
      (← checkRawSort .tm x) (← checkRawSort .tm y))
  | .tm, .eps a p => return .eps (← checkRawSort .ty a) (← checkRawSort .tm p)
  | .tm, .abs a p x => return (Tree.Sorted.abs (← checkRawSort .ty a)
      (← checkRawSort .tm p) (← checkRawSort .tm x))
  | .tm, .rep a p x => return (Tree.Sorted.rep (← checkRawSort .ty a)
      (← checkRawSort .tm p) (← checkRawSort .tm x))
  | _, .emptyCtx | _, .boundCtx .. => none
  | _, _ => none

@[simp] theorem checkRawSort_toSorted (x : Tree.Sorted Base sort) :
    checkRawSort sort (sortedToRaw x) = some x := by
  induction x <;> simp_all [sortedToRaw, checkRawSort]

theorem sortedToRaw_injective :
    Function.Injective (sortedToRaw : Tree.Sorted Base sort → Tree.Raw Base) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkRawSort_toSorted x, ← checkRawSort_toSorted y, h])

/-- The computable partial inverse of simultaneous sort and depth erasure. -/
def checkRaw (sort : HolSort) (depth : Nat) (x : Tree.Raw Base) :
    Option (Hol Base sort depth) := do
  checkDepth sort depth (← checkRawSort sort x)

@[simp] theorem checkRaw_toRaw (x : Hol Base sort depth) :
    checkRaw sort depth (toRaw x) = some x := by
  unfold checkRaw toRaw
  rw [checkRawSort_toSorted]
  exact checkDepth_toSorted x

theorem toRaw_injective :
    Function.Injective (toRaw : Hol Base sort depth → Tree.Raw Base) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkRaw_toRaw x, ← checkRaw_toRaw y, h])

/-- Computable partial inverse of the depth-indexed, sort-erased embedding. -/
def checkRawDepth (depth : Nat) (x : Tree.Raw Base) : Option (Tree.Scoped Base depth) :=
  match x with
  | .base n => if h : depth = 0 then by subst depth; exact some (.base n) else none
  | .boolTy => if h : depth = 0 then by subst depth; exact some .boolTy else none
  | .natTy => if h : depth = 0 then by subst depth; exact some .natTy else none
  | .arr a b => if h : depth = 0 then by
      subst depth; exact return .arr (← checkRawDepth 0 a) (← checkRawDepth 0 b)
    else none
  | .sub a p => if h : depth = 0 then by
      subst depth; exact return .sub (← checkRawDepth 0 a) (← checkRawDepth 1 p)
    else none
  | .bound i => if h : i < depth then some (.bound ⟨i, h⟩) else none
  | .free n A => return .free n (← checkRawDepth 0 A)
  | .app f x => return .app (← checkRawDepth depth f) (← checkRawDepth depth x)
  | .lam a b => return .lam (← checkRawDepth 0 a) (← checkRawDepth (depth + 1) b)
  | .bool b => some (.bool b) | .zero => some .zero
  | .succ x => return .succ (← checkRawDepth depth x)
  | .eq a x y => return (Tree.Scoped.eq (← checkRawDepth 0 a)
      (← checkRawDepth depth x) (← checkRawDepth depth y))
  | .eps a p => return .eps (← checkRawDepth 0 a) (← checkRawDepth depth p)
  | .abs a p x => return (Tree.Scoped.abs (← checkRawDepth 0 a)
      (← checkRawDepth 1 p) (← checkRawDepth depth x))
  | .rep a p x => return (Tree.Scoped.rep (← checkRawDepth 0 a)
      (← checkRawDepth 1 p) (← checkRawDepth depth x))
  | .emptyCtx | .boundCtx .. => none

@[simp] theorem checkRawDepth_toScoped (x : Tree.Scoped Base depth) :
    checkRawDepth depth (scopedToRaw x) = some x := by
  induction x <;> simp_all [checkRawDepth, scopedToRaw]

theorem scopedToRaw_injective :
    Function.Injective (scopedToRaw : Tree.Scoped Base depth → Tree.Raw Base) :=
  fun {x y} h => Option.some.inj (by
    rw [← checkRawDepth_toScoped x, ← checkRawDepth_toScoped y, h])

end Erasure

/-! Typing and equality are transported along each injective embedding.  These
definitions expose precisely the same rules while making malformed extrinsic
trees untypable. -/
namespace Tree.Sorted
def Kinded (A : Tree.Sorted Base .ty) : Prop := ∃ a, Nucleus.HolLN.Kinded a ∧ Erasure.toSorted a = A
def HasType {depth} (Γ : BoundCtx Base depth)
    (t : Tree.Sorted Base .tm) (A : Tree.Sorted Base .ty) : Prop :=
  ∃ t₀ A₀, Nucleus.HolLN.HasType Γ t₀ A₀ ∧ Erasure.toSorted t₀ = t ∧ Erasure.toSorted A₀ = A
def EqTm {depth} (Γ : BoundCtx Base depth)
    (t u : Tree.Sorted Base .tm) (A : Tree.Sorted Base .ty) : Prop :=
  ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Γ t₀ u₀ A₀) ∧
    Erasure.toSorted t₀ = t ∧ Erasure.toSorted u₀ = u ∧ Erasure.toSorted A₀ = A
end Tree.Sorted

namespace Tree.Scoped
def Kinded (A : Tree.Scoped Base 0) : Prop := ∃ a, Nucleus.HolLN.Kinded a ∧ Erasure.toScoped a = A
def HasType {depth} (Γ : BoundCtx Base depth)
    (t : Tree.Scoped Base depth) (A : Tree.Scoped Base 0) : Prop :=
  ∃ t₀ A₀, Nucleus.HolLN.HasType Γ t₀ A₀ ∧ Erasure.toScoped t₀ = t ∧ Erasure.toScoped A₀ = A
def EqTm {depth} (Γ : BoundCtx Base depth)
    (t u : Tree.Scoped Base depth) (A : Tree.Scoped Base 0) : Prop :=
  ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Γ t₀ u₀ A₀) ∧
    Erasure.toScoped t₀ = t ∧ Erasure.toScoped u₀ = u ∧ Erasure.toScoped A₀ = A
end Tree.Scoped

namespace Tree.Raw
def Kinded (A : Tree.Raw Base) : Prop := ∃ a, Nucleus.HolLN.Kinded a ∧ Erasure.toRaw a = A
def HasType {depth} (Γ : BoundCtx Base depth)
    (t A : Tree.Raw Base) : Prop :=
  ∃ t₀ A₀, Nucleus.HolLN.HasType Γ t₀ A₀ ∧ Erasure.toRaw t₀ = t ∧ Erasure.toRaw A₀ = A
def EqTm {depth} (Γ : BoundCtx Base depth)
    (t u A : Tree.Raw Base) : Prop :=
  ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Γ t₀ u₀ A₀) ∧
    Erasure.toRaw t₀ = t ∧ Erasure.toRaw u₀ = u ∧ Erasure.toRaw A₀ = A
end Tree.Raw

theorem sorted_wellTyped_iff_unique {Γ : BoundCtx Base depth}
    {t : Tree.Sorted Base .tm} {A : Tree.Sorted Base .ty} :
    Tree.Sorted.HasType Γ t A ↔ ∃! p : Tm Base depth × Ty Base,
      HasType Γ p.1 p.2 ∧ Erasure.toSorted p.1 = t ∧ Erasure.toSorted p.2 = A := by
  constructor
  · rintro ⟨t₀, A₀, ht, rfl, rfl⟩
    refine ⟨⟨t₀, A₀⟩, ⟨ht, rfl, rfl⟩, ?_⟩
    rintro ⟨t₁, A₁⟩ ⟨_, ht₁, hA₁⟩
    exact Prod.ext (Erasure.toSorted_injective ht₁) (Erasure.toSorted_injective hA₁)
  · rintro ⟨⟨t₀, A₀⟩, ⟨ht, et, eA⟩, _⟩; exact ⟨t₀, A₀, ht, et, eA⟩

theorem scoped_wellTyped_iff_unique {Γ : BoundCtx Base depth}
    {t : Tree.Scoped Base depth} {A : Tree.Scoped Base 0} :
    Tree.Scoped.HasType Γ t A ↔ ∃! p : Tm Base depth × Ty Base,
      HasType Γ p.1 p.2 ∧ Erasure.toScoped p.1 = t ∧ Erasure.toScoped p.2 = A := by
  constructor
  · rintro ⟨t₀, A₀, ht, rfl, rfl⟩
    refine ⟨⟨t₀, A₀⟩, ⟨ht, rfl, rfl⟩, ?_⟩
    rintro ⟨t₁, A₁⟩ ⟨_, ht₁, hA₁⟩
    exact Prod.ext (Erasure.toScoped_injective ht₁) (Erasure.toScoped_injective hA₁)
  · rintro ⟨⟨t₀, A₀⟩, ⟨ht, et, eA⟩, _⟩; exact ⟨t₀, A₀, ht, et, eA⟩

theorem raw_wellTyped_iff_unique {Γ : BoundCtx Base depth}
    {t A : Tree.Raw Base} :
    Tree.Raw.HasType Γ t A ↔ ∃! p : Tm Base depth × Ty Base,
      HasType Γ p.1 p.2 ∧ Erasure.toRaw p.1 = t ∧ Erasure.toRaw p.2 = A := by
  constructor
  · rintro ⟨t₀, A₀, ht, rfl, rfl⟩
    refine ⟨⟨t₀, A₀⟩, ⟨ht, rfl, rfl⟩, ?_⟩
    rintro ⟨t₁, A₁⟩ ⟨_, ht₁, hA₁⟩
    exact Prod.ext (Erasure.toRaw_injective ht₁) (Erasure.toRaw_injective hA₁)
  · rintro ⟨⟨t₀, A₀⟩, ⟨ht, et, eA⟩, _⟩; exact ⟨t₀, A₀, ht, et, eA⟩

/-! All four representations share one JSON image.  Thus changing intrinsic
indices never changes content addressing or wire format. -/
namespace Tree.Json

open Nucleus.HolLN.Json

private def scalar (x : Json.Scalar Base) : Json.Tree Base := .scalar x
private def tagged (tag : String) (fields : RawSyn String (Json.Scalar Base) .obj := .objNil) :
    Json.Tree Base := .map (.objCons "tag" (scalar (.string tag)) fields)
private def field (key : String) (value : Json.Tree Base)
    (tail : RawSyn String (Json.Scalar Base) .obj) : RawSyn String (Json.Scalar Base) .obj :=
  .objCons key value tail

/-- Total JSON serialization of the fully extrinsic syntax. -/
def encode : Tree.Raw Base → Json.Tree Base
  | .base n => tagged "ty.base" (field "name" (scalar (.base n)) .objNil)
  | .boolTy => tagged "ty.bool" | .natTy => tagged "ty.ind"
  | .arr a b => tagged "ty.arr" (field "domain" (encode a) (field "codomain" (encode b) .objNil))
  | .sub a p => tagged "ty.sub" (field "carrier" (encode a) (field "predicate" (encode p) .objNil))
  | .bound i => tagged "tm.bound" (field "index" (scalar (.nat i)) .objNil)
  | .free n A => tagged "tm.free" (field "name" (scalar (.nat n))
      (field "type" (encode A) .objNil))
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
  | .boundCtx a tail => tagged "ctx.bound"
      (field "type" (encode a) (field "body" (encode tail) .objNil))

def encodeSorted (x : Tree.Sorted Base sort) : Json.Tree Base :=
  encode (Erasure.sortedToRaw x)
def encodeScoped (x : Tree.Scoped Base depth) : Json.Tree Base :=
  encode (Erasure.scopedToRaw x)

@[simp] theorem encode_embeddings_agree (x : Hol Base sort depth) :
    encodeSorted (Erasure.toSorted x) = encodeScoped (Erasure.toScoped x) := by
  simp [encodeSorted, encodeScoped, Erasure.square]

/-- The new encoders reproduce the established HOL-LN JSON codec byte-for-tree. -/
@[simp] theorem encode_raw_eq_original (x : Hol Base sort depth) :
    encode (Erasure.toRaw x) = Json.Codec.encode x := by
  induction x <;> simp_all [Erasure.toRaw, Erasure.toSorted,
    Erasure.sortedToRaw, encode, Json.Codec.encode, Json.Codec.encodeWith,
    Json.Schema.v0, tagged, field, scalar] <;> rfl

end Tree.Json

end Nucleus.HolLN
