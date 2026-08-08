/-!
# Intrinsically scoped, locally nameless HOL syntax

`Hol` is one dependent family because subtype types contain term predicates.
The term-depth index bounds de Bruijn variables with `Fin`; free variables use
stable natural-number names.  Its constructors are: base, Boolean, individual
(`ind`/natural), arrow and subtype types; bound and free variables;
application, lambda, Boolean and zero literals, successor, equality, choice,
subtype abstraction and subtype representation terms.

A subtype predicate always has depth one.  It consequently has the fixed
one-variable context containing its carrier type and cannot mention ambient
bound term variables.
-/

namespace Nucleus.HolLN

universe u

inductive HolSort where
  | ty
  | tm
  deriving DecidableEq, Repr

inductive Hol (Base : Type u) : HolSort -> Nat -> Type u where
  | base (name : Base) : Hol Base .ty 0
  | boolTy : Hol Base .ty 0
  | natTy : Hol Base .ty 0
  | arr (domain codomain : Hol Base .ty 0) : Hol Base .ty 0
  | sub (carrier : Hol Base .ty 0) (predicate : Hol Base .tm 1) : Hol Base .ty 0
  | bound {depth : Nat} (index : Fin depth) : Hol Base .tm depth
  | free {depth : Nat} (name : Nat) : Hol Base .tm depth
  | app {depth : Nat} (function argument : Hol Base .tm depth) : Hol Base .tm depth
  | lam {depth : Nat} (domain : Hol Base .ty 0)
      (body : Hol Base .tm (depth + 1)) : Hol Base .tm depth
  | bool {depth : Nat} (value : Bool) : Hol Base .tm depth
  | zero {depth : Nat} : Hol Base .tm depth
  | succ {depth : Nat} (value : Hol Base .tm depth) : Hol Base .tm depth
  | eq {depth : Nat} (type : Hol Base .ty 0)
      (left right : Hol Base .tm depth) : Hol Base .tm depth
  | eps {depth : Nat} (type : Hol Base .ty 0)
      (predicate : Hol Base .tm depth) : Hol Base .tm depth
  | abs {depth : Nat} (carrier : Hol Base .ty 0)
      (predicate : Hol Base .tm 1) (value : Hol Base .tm depth) : Hol Base .tm depth
  | rep {depth : Nat} (carrier : Hol Base .ty 0)
      (predicate : Hol Base .tm 1) (value : Hol Base .tm depth) : Hol Base .tm depth
  deriving Repr

abbrev Ty (Base : Type u) := Hol Base .ty 0
abbrev Tm (Base : Type u) (depth : Nat) := Hol Base .tm depth
abbrev ClosedTm (Base : Type u) := Tm Base 0

/-- Traditional HOL name for the distinguished infinite type. -/
abbrev indTy {Base : Type u} : Ty Base := .natTy

/-- Specification-style aliases for the infinity extension. -/
abbrev TY_IND {Base : Type u} : Ty Base := indTy
abbrev TY_NAT {Base : Type u} : Ty Base := .natTy
abbrev TM_ZERO {Base : Type u} {depth : Nat} : Tm Base depth := .zero
abbrev TM_SUCC {Base : Type u} {depth : Nat} (term : Tm Base depth) : Tm Base depth :=
  .succ term

end Nucleus.HolLN
