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
  | base {kind : Kind} (name : Base) : Tree.Sorted Base (.kind kind)
  | boolTy : Tree.Sorted Base (.kind .star)
  | natTy : Tree.Sorted Base (.kind .star)
  | arr (domain codomain : Tree.Sorted Base (.kind .star)) : Tree.Sorted Base (.kind .star)
  | tyApp {domain codomain : Kind}
      (function : Tree.Sorted Base (.kind (.arr domain codomain)))
      (argument : Tree.Sorted Base (.kind domain)) : Tree.Sorted Base (.kind codomain)
  | sub (carrier : Tree.Sorted Base (.kind .star))
      (predicate : Tree.Sorted Base .tm) : Tree.Sorted Base (.kind .star)
  | bv (index : Nat) : Tree.Sorted Base .tm
  | fv (name : Nat) (type : Tree.Sorted Base (.kind .star)) : Tree.Sorted Base .tm
  | app (function argument : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | lam (domain : Tree.Sorted Base (.kind .star)) (body : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | bool (value : Bool) : Tree.Sorted Base .tm
  | zero : Tree.Sorted Base .tm
  | succ (value : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | eq (type : Tree.Sorted Base (.kind .star)) (left right : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | eps (type : Tree.Sorted Base (.kind .star)) (predicate : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | abs (carrier : Tree.Sorted Base (.kind .star)) (predicate value : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  | rep (carrier : Tree.Sorted Base (.kind .star)) (predicate value : Tree.Sorted Base .tm) : Tree.Sorted Base .tm
  deriving Repr

/-- HOL syntax retaining binder depth but erasing the type/term sort.  The
depths on annotation and subtype-predicate children retain the original
grammar's scoping invariants. -/
inductive Tree.Scoped (Base : Type u) : Nat → Type u where
  | base (name : Base) (kind : Kind := .star) : Tree.Scoped Base 0
  | boolTy : Tree.Scoped Base 0
  | natTy : Tree.Scoped Base 0
  | arr (domain codomain : Tree.Scoped Base 0) : Tree.Scoped Base 0
  | tyApp (domain codomain : Kind) (function argument : Tree.Scoped Base 0) : Tree.Scoped Base 0
  | sub (carrier : Tree.Scoped Base 0) (predicate : Tree.Scoped Base 1) : Tree.Scoped Base 0
  | bv {d : Nat} (index : Fin d) : Tree.Scoped Base d
  | fv {d : Nat} (name : Nat) (type : Tree.Scoped Base 0) : Tree.Scoped Base d
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
  | base (name : Base) (kind : Kind := .star) | boolTy | natTy
  | arr (domain codomain : Tree.Raw Base)
  | tyApp (domain codomain : Kind) (function argument : Tree.Raw Base)
  | sub (carrier predicate : Tree.Raw Base)
  | bv (index : Nat) | fv (name : Nat) (type : Tree.Raw Base)
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
  | _, _, .tyApp f a => .tyApp (toSorted f) (toSorted a)
  | _, _, .sub a p => .sub (toSorted a) (toSorted p)
  | _, _, .bv i => .bv i | _, _, .fv n A => .fv n (toSorted A)
  | _, _, .app f x => .app (toSorted f) (toSorted x)
  | _, _, .lam a b => .lam (toSorted a) (toSorted b)
  | _, _, .bool b => .bool b | _, _, .zero => .zero | _, _, .succ x => .succ (toSorted x)
  | _, _, .eq a x y => .eq (toSorted a) (toSorted x) (toSorted y)
  | _, _, .eps a p => .eps (toSorted a) (toSorted p)
  | _, _, .abs a p x => .abs (toSorted a) (toSorted p) (toSorted x)
  | _, _, .rep a p x => .rep (toSorted a) (toSorted p) (toSorted x)

def toScoped : {sort : HolSort} → {depth : Nat} → Hol Base sort depth → Tree.Scoped Base depth
  | .kind k, _, .base n => .base n k | _, _, .boolTy => .boolTy | _, _, .natTy => .natTy
  | _, _, .arr a b => .arr (toScoped a) (toScoped b)
  | .kind codomain, _, @Hol.tyApp _ domain _ f a =>
      .tyApp domain codomain (toScoped f) (toScoped a)
  | _, _, .sub a p => .sub (toScoped a) (toScoped p)
  | _, _, .bv i => .bv i | _, _, .fv n A => .fv n (toScoped A)
  | _, _, .app f x => .app (toScoped f) (toScoped x)
  | _, _, .lam a b => .lam (toScoped a) (toScoped b)
  | _, _, .bool b => .bool b | _, _, .zero => .zero | _, _, .succ x => .succ (toScoped x)
  | _, _, .eq a x y => .eq (toScoped a) (toScoped x) (toScoped y)
  | _, _, .eps a p => .eps (toScoped a) (toScoped p)
  | _, _, .abs a p x => .abs (toScoped a) (toScoped p) (toScoped x)
  | _, _, .rep a p x => .rep (toScoped a) (toScoped p) (toScoped x)

def sortedToRaw : {sort : HolSort} → Tree.Sorted Base sort → Tree.Raw Base
  | .kind k, .base n => .base n k | _, .boolTy => .boolTy | _, .natTy => .natTy
  | _, .arr a b => .arr (sortedToRaw a) (sortedToRaw b)
  | .kind codomain, @Tree.Sorted.tyApp _ domain _ f a =>
      .tyApp domain codomain (sortedToRaw f) (sortedToRaw a)
  | _, .sub a p => .sub (sortedToRaw a) (sortedToRaw p)
  | _, .bv i => .bv i | _, .fv n A => .fv n (sortedToRaw A)
  | _, .app f x => .app (sortedToRaw f) (sortedToRaw x)
  | _, .lam a b => .lam (sortedToRaw a) (sortedToRaw b)
  | _, .bool b => .bool b | _, .zero => .zero | _, .succ x => .succ (sortedToRaw x)
  | _, .eq a x y => .eq (sortedToRaw a) (sortedToRaw x) (sortedToRaw y)
  | _, .eps a p => .eps (sortedToRaw a) (sortedToRaw p)
  | _, .abs a p x => .abs (sortedToRaw a) (sortedToRaw p) (sortedToRaw x)
  | _, .rep a p x => .rep (sortedToRaw a) (sortedToRaw p) (sortedToRaw x)

def scopedToRaw : {depth : Nat} → Tree.Scoped Base depth → Tree.Raw Base
  | _, .base n k => .base n k | _, .boolTy => .boolTy | _, .natTy => .natTy
  | _, .arr a b => .arr (scopedToRaw a) (scopedToRaw b)
  | _, .tyApp domain codomain f a => .tyApp domain codomain (scopedToRaw f) (scopedToRaw a)
  | _, .sub a p => .sub (scopedToRaw a) (scopedToRaw p)
  | _, .bv i => .bv i | _, .fv n A => .fv n (scopedToRaw A)
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
  | .kind k, d, .base n => if h : d = 0 then by subst d; exact some (.base n) else none
  | .kind _, d, .boolTy => if h : d = 0 then by subst d; exact some .boolTy else none
  | .kind _, d, .natTy => if h : d = 0 then by subst d; exact some .natTy else none
  | .kind _, d, .arr a b => if h : d = 0 then by
      subst d; exact do
        let A ← checkDepth (.kind .star) 0 a
        let B ← checkDepth (.kind .star) 0 b
        return .arr A B
    else none
  | .kind codomain, d, @Tree.Sorted.tyApp _ domain _ f a => if h : d = 0 then by
      subst d; exact do
        let F ← checkDepth (.kind (.arr domain codomain)) 0 f
        let A ← checkDepth (.kind domain) 0 a
        return .tyApp F A
    else none
  | .kind _, d, .sub a p => if h : d = 0 then by
      subst d; exact return .sub (← checkDepth (.kind .star) 0 a) (← checkDepth .tm 1 p)
    else none
  | .tm, d, .bv i => if h : i < d then some (.bv ⟨i, h⟩) else none
  | .tm, d, .fv n A => return .fv n (← checkDepth (.kind .star) 0 A)
  | .tm, d, .app f x => return .app (← checkDepth .tm d f) (← checkDepth .tm d x)
  | .tm, d, .lam a b => return .lam (← checkDepth (.kind .star) 0 a) (← checkDepth .tm (d+1) b)
  | .tm, d, .bool b => some (.bool b) | .tm, d, .zero => some .zero
  | .tm, d, .succ x => return .succ (← checkDepth .tm d x)
  | .tm, d, .eq a x y => return .eq (← checkDepth (.kind .star) 0 a) (← checkDepth .tm d x) (← checkDepth .tm d y)
  | .tm, d, .eps a p => return .eps (← checkDepth (.kind .star) 0 a) (← checkDepth .tm d p)
  | .tm, d, .abs a p x => return .abs (← checkDepth (.kind .star) 0 a) (← checkDepth .tm 1 p) (← checkDepth .tm d x)
  | .tm, d, .rep a p x => return .rep (← checkDepth (.kind .star) 0 a) (← checkDepth .tm 1 p) (← checkDepth .tm d x)

/-- Computable sort checker: the partial inverse of sort erasure. -/
def checkSort : {depth : Nat} → (sort : HolSort) → Tree.Scoped Base depth → Option (Hol Base sort depth)
  | _, .kind expected, .base n actual => if h : actual = expected then by
      subst actual; exact some (.base n)
    else none
  | _, .kind expected, .boolTy => if h : expected = .star then by subst expected; exact some .boolTy else none
  | _, .kind expected, .natTy => if h : expected = .star then by subst expected; exact some .natTy else none
  | _, .kind expected, .arr a b => if h : expected = .star then by
      subst expected; exact do
        let A ← checkSort (.kind .star) a
        let B ← checkSort (.kind .star) b
        return .arr A B
    else none
  | _, .kind expected, .tyApp domain codomain f a => if h : codomain = expected then by
      subst codomain; exact do
        let F ← checkSort (.kind (.arr domain expected)) f
        let A ← checkSort (.kind domain) a
        return .tyApp F A
    else none
  | _, .kind expected, .sub a p => if h : expected = .star then by
      subst expected; exact return .sub (← checkSort (.kind .star) a) (← checkSort .tm p)
    else none
  | _, .tm, .bv i => some (.bv i)
  | _, .tm, .fv n A => return .fv n (← checkSort (.kind .star) A)
  | _, .tm, .app f x => return .app (← checkSort .tm f) (← checkSort .tm x)
  | _, .tm, .lam a b => return .lam (← checkSort (.kind .star) a) (← checkSort .tm b)
  | _, .tm, .bool b => some (.bool b) | _, .tm, .zero => some .zero
  | _, .tm, .succ x => return .succ (← checkSort .tm x)
  | _, .tm, .eq a x y => return .eq (← checkSort (.kind .star) a) (← checkSort .tm x) (← checkSort .tm y)
  | _, .tm, .eps a p => return .eps (← checkSort (.kind .star) a) (← checkSort .tm p)
  | _, .tm, .abs a p x => return .abs (← checkSort (.kind .star) a) (← checkSort .tm p) (← checkSort .tm x)
  | _, .tm, .rep a p x => return .rep (← checkSort (.kind .star) a) (← checkSort .tm p) (← checkSort .tm x)
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
  | .kind expected, .base n actual => if h : actual = expected then by
      subst actual; exact some (.base n)
    else none
  | .kind expected, .boolTy => if h : expected = .star then by subst expected; exact some .boolTy else none
  | .kind expected, .natTy => if h : expected = .star then by subst expected; exact some .natTy else none
  | .kind expected, .arr a b => if h : expected = .star then by
      subst expected; exact do
        let A ← checkRawSort (.kind .star) a
        let B ← checkRawSort (.kind .star) b
        return .arr A B
    else none
  | .kind expected, .tyApp domain codomain f a => if h : codomain = expected then by
      subst codomain; exact do
        let F ← checkRawSort (.kind (.arr domain expected)) f
        let A ← checkRawSort (.kind domain) a
        return .tyApp F A
    else none
  | .kind expected, .sub a p => if h : expected = .star then by
      subst expected; exact return .sub (← checkRawSort (.kind .star) a) (← checkRawSort .tm p)
    else none
  | .tm, .bv i => some (.bv i)
  | .tm, .fv n A => return .fv n (← checkRawSort (.kind .star) A)
  | .tm, .app f x => return .app (← checkRawSort .tm f) (← checkRawSort .tm x)
  | .tm, .lam a b => return .lam (← checkRawSort (.kind .star) a) (← checkRawSort .tm b)
  | .tm, .bool b => some (.bool b) | .tm, .zero => some .zero
  | .tm, .succ x => return .succ (← checkRawSort .tm x)
  | .tm, .eq a x y => return (Tree.Sorted.eq (← checkRawSort (.kind .star) a)
      (← checkRawSort .tm x) (← checkRawSort .tm y))
  | .tm, .eps a p => return .eps (← checkRawSort (.kind .star) a) (← checkRawSort .tm p)
  | .tm, .abs a p x => return (Tree.Sorted.abs (← checkRawSort (.kind .star) a)
      (← checkRawSort .tm p) (← checkRawSort .tm x))
  | .tm, .rep a p x => return (Tree.Sorted.rep (← checkRawSort (.kind .star) a)
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
  | .base n k => if h : depth = 0 then by subst depth; exact some (.base n k) else none
  | .boolTy => if h : depth = 0 then by subst depth; exact some .boolTy else none
  | .natTy => if h : depth = 0 then by subst depth; exact some .natTy else none
  | .arr a b => if h : depth = 0 then by
      subst depth; exact return .arr (← checkRawDepth 0 a) (← checkRawDepth 0 b)
    else none
  | .tyApp domain codomain f a => if h : depth = 0 then by
      subst depth; exact do
        let F ← checkRawDepth 0 f
        let A ← checkRawDepth 0 a
        return .tyApp domain codomain F A
    else none
  | .sub a p => if h : depth = 0 then by
      subst depth; exact return .sub (← checkRawDepth 0 a) (← checkRawDepth 1 p)
    else none
  | .bv i => if h : i < depth then some (.bv ⟨i, h⟩) else none
  | .fv n A => return .fv n (← checkRawDepth 0 A)
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
def Kinded (A : Tree.Sorted Base (.kind .star)) : Prop := ∃ a, Nucleus.HolLN.Kinded a ∧ Erasure.toSorted a = A
def HasType {depth} (Γ : BoundCtx Base depth)
    (t : Tree.Sorted Base .tm) (A : Tree.Sorted Base (.kind .star)) : Prop :=
  ∃ t₀ A₀, Nucleus.HolLN.HasType Γ t₀ A₀ ∧ Erasure.toSorted t₀ = t ∧ Erasure.toSorted A₀ = A
def EqTm {depth} (Γ : BoundCtx Base depth)
    (t u : Tree.Sorted Base .tm) (A : Tree.Sorted Base (.kind .star)) : Prop :=
  ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Γ t₀ u₀ A₀) ∧
    Erasure.toSorted t₀ = t ∧ Erasure.toSorted u₀ = u ∧ Erasure.toSorted A₀ = A
end Tree.Sorted

namespace Tree.Scoped
def Kinded (A : Tree.Scoped Base 0) : Prop :=
  ∃ a : Ty Base, Nucleus.HolLN.Kinded a ∧ Erasure.toScoped a = A
def HasType {depth} (Γ : BoundCtx Base depth)
    (t : Tree.Scoped Base depth) (A : Tree.Scoped Base 0) : Prop :=
  ∃ t₀ A₀, Nucleus.HolLN.HasType Γ t₀ A₀ ∧ Erasure.toScoped t₀ = t ∧ Erasure.toScoped A₀ = A
def EqTm {depth} (Γ : BoundCtx Base depth)
    (t u : Tree.Scoped Base depth) (A : Tree.Scoped Base 0) : Prop :=
  ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Γ t₀ u₀ A₀) ∧
    Erasure.toScoped t₀ = t ∧ Erasure.toScoped u₀ = u ∧ Erasure.toScoped A₀ = A
end Tree.Scoped

namespace Tree.Raw
def Kinded (A : Tree.Raw Base) : Prop :=
  ∃ a : Ty Base, Nucleus.HolLN.Kinded a ∧ Erasure.toRaw a = A
def HasType {depth} (Γ : BoundCtx Base depth)
    (t A : Tree.Raw Base) : Prop :=
  ∃ t₀ A₀, Nucleus.HolLN.HasType Γ t₀ A₀ ∧ Erasure.toRaw t₀ = t ∧ Erasure.toRaw A₀ = A
def EqTm {depth} (Γ : BoundCtx Base depth)
    (t u A : Tree.Raw Base) : Prop :=
  ∃ t₀ u₀ A₀, Nonempty (Nucleus.HolLN.EqTm Γ t₀ u₀ A₀) ∧
    Erasure.toRaw t₀ = t ∧ Erasure.toRaw u₀ = u ∧ Erasure.toRaw A₀ = A
end Tree.Raw

theorem sorted_wellTyped_iff_unique {Γ : BoundCtx Base depth}
    {t : Tree.Sorted Base .tm} {A : Tree.Sorted Base (.kind .star)} :
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
  | .base n kind => tagged "ty.base" (field "name" (scalar (.base n))
      (field "kind" (scalar (.kind kind)) .objNil))
  | .boolTy => tagged "ty.bool" | .natTy => tagged "ty.ind"
  | .arr a b => tagged "ty.arr" (field "domain" (encode a) (field "codomain" (encode b) .objNil))
  | .tyApp domain _ f a => tagged "ty.app" (field "kind" (scalar (.kind domain))
      (field "function" (encode f) (field "argument" (encode a) .objNil)))
  | .sub a p => tagged "ty.sub" (field "carrier" (encode a) (field "predicate" (encode p) .objNil))
  | .bv i => tagged "tm.bv" (field "index" (scalar (.nat i)) .objNil)
  | .fv n A => tagged "tm.fv" (field "name" (scalar (.nat n))
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
  | .boundCtx a tail => tagged "ctx.bv"
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
