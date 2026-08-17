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

/-- Kinds of HOL type expressions. `star` classifies ordinary term-level
types; `arr` classifies type constructors. -/
inductive Kind where
  | star
  | arr (domain codomain : Kind)
  deriving DecidableEq, Repr

inductive HolSort where
  | kind (kind : Kind)
  | tm
  deriving DecidableEq, Repr

inductive Hol (Base : Type u) : HolSort -> Nat -> Type u where
  | boolTy : Hol Base (.kind .star) 0
  | natTy : Hol Base (.kind .star) 0
  | arr (domain codomain : Hol Base (.kind .star) 0) : Hol Base (.kind .star) 0
  | tyApp {domain codomain : Kind}
      (function : Hol Base (.kind (.arr domain codomain)) 0)
      (argument : Hol Base (.kind domain) 0) : Hol Base (.kind codomain) 0
  | sub (carrier : Hol Base (.kind .star) 0)
      (predicate : Hol Base .tm 1) : Hol Base (.kind .star) 0
  | base {kind : Kind} (name : Base) : Hol Base (.kind kind) 0
  | bv {depth : Nat} (index : Fin depth) : Hol Base .tm depth
  | fv {depth : Nat} (name : Nat) (type : Hol Base (.kind .star) 0) : Hol Base .tm depth
  | app {depth : Nat} (function argument : Hol Base .tm depth) : Hol Base .tm depth
  | lam {depth : Nat} (domain : Hol Base (.kind .star) 0)
      (body : Hol Base .tm (depth + 1)) : Hol Base .tm depth
  | bool {depth : Nat} (value : Bool) : Hol Base .tm depth
  | zero {depth : Nat} : Hol Base .tm depth
  | succ {depth : Nat} (value : Hol Base .tm depth) : Hol Base .tm depth
  | eq {depth : Nat} (type : Hol Base (.kind .star) 0)
      (left right : Hol Base .tm depth) : Hol Base .tm depth
  | eps {depth : Nat} (type : Hol Base (.kind .star) 0)
      (predicate : Hol Base .tm depth) : Hol Base .tm depth
  | abs {depth : Nat} (carrier : Hol Base (.kind .star) 0)
      (predicate : Hol Base .tm 1) (value : Hol Base .tm depth) : Hol Base .tm depth
  | rep {depth : Nat} (carrier : Hol Base (.kind .star) 0)
      (predicate : Hol Base .tm 1) (value : Hol Base .tm depth) : Hol Base .tm depth
  deriving Repr

abbrev Fam (Base : Type u) (kind : Kind) := Hol Base (.kind kind) 0
abbrev Ty (Base : Type u) := Fam Base .star
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
