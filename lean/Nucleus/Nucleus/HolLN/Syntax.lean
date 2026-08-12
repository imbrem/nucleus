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

universe u v

inductive HolSort where
  | ty
  | tm
  deriving DecidableEq, Repr

inductive HolF (Base : Type u) (Free : Type v) : HolSort -> Nat -> Type (max u v) where
  | base (name : Base) : HolF Base Free .ty 0
  | boolTy : HolF Base Free .ty 0
  | natTy : HolF Base Free .ty 0
  | arr (domain codomain : HolF Base Free .ty 0) : HolF Base Free .ty 0
  | sub (carrier : HolF Base Free .ty 0) (predicate : HolF Base Free .tm 1) :
      HolF Base Free .ty 0
  | bound {depth : Nat} (index : Fin depth) : HolF Base Free .tm depth
  | free {depth : Nat} (name : Free) : HolF Base Free .tm depth
  | app {depth : Nat} (function argument : HolF Base Free .tm depth) :
      HolF Base Free .tm depth
  | lam {depth : Nat} (domain : HolF Base Free .ty 0)
      (body : HolF Base Free .tm (depth + 1)) : HolF Base Free .tm depth
  | bool {depth : Nat} (value : Bool) : HolF Base Free .tm depth
  | zero {depth : Nat} : HolF Base Free .tm depth
  | succ {depth : Nat} (value : HolF Base Free .tm depth) : HolF Base Free .tm depth
  | eq {depth : Nat} (type : HolF Base Free .ty 0)
      (left right : HolF Base Free .tm depth) : HolF Base Free .tm depth
  | eps {depth : Nat} (type : HolF Base Free .ty 0)
      (predicate : HolF Base Free .tm depth) : HolF Base Free .tm depth
  | abs {depth : Nat} (carrier : HolF Base Free .ty 0)
      (predicate : HolF Base Free .tm 1) (value : HolF Base Free .tm depth) :
      HolF Base Free .tm depth
  | rep {depth : Nat} (carrier : HolF Base Free .ty 0)
      (predicate : HolF Base Free .tm 1) (value : HolF Base Free .tm depth) :
      HolF Base Free .tm depth
  deriving Repr

/-- Existing HOL syntax, with natural-number free-variable names. -/
abbrev Hol (Base : Type u) := HolF Base Nat

abbrev TyF (Base : Type u) (Free : Type v) := HolF Base Free .ty 0
abbrev TmF (Base : Type u) (Free : Type v) (depth : Nat) := HolF Base Free .tm depth
abbrev ClosedTmF (Base : Type u) (Free : Type v) := TmF Base Free 0

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
