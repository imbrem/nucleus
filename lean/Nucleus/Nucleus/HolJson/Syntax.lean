/-!
# Raw HOL trees for JSON interchange

`HolJson.Syntax` is the untrusted, untyped tree carried by the JSON wire
format.  It deliberately differs from `HolLN.Hol`: deserializing bytes must be
able to represent ill-scoped and ill-typed input before a checker rejects it.

Base-type names and free-term names are independent parameters.  Bound
variables remain unsigned de Bruijn indices.  The current Rust profile uses
`String` and `UInt64`; linked decoding can instead use `Original ⊕ LinkName`
for free names without adding a special link constructor to HOL.
-/

namespace Nucleus.HolJson

universe u v w x

/-- An untrusted HOL syntax tree, before scope and type checking. -/
inductive Syntax (Base : Type u) (Free : Type v) : Type (max u v) where
  | base (name : Base)
  | boolTy
  | indTy
  | arr (domain codomain : Syntax Base Free)
  | sub (carrier predicate : Syntax Base Free)
  | bound (index : UInt64)
  | free (name : Free)
  | app (function argument : Syntax Base Free)
  | lam (domain body : Syntax Base Free)
  | bool (value : Bool)
  | zero
  | succ (value : Syntax Base Free)
  | eqn (type left right : Syntax Base Free)
  | eps (type predicate : Syntax Base Free)
  | abs (carrier predicate value : Syntax Base Free)
  | rep (carrier predicate value : Syntax Base Free)
  deriving DecidableEq, Repr

/-- The concrete name profile used by the initial Rust JSON tree. -/
abbrev WireSyntax := Syntax String UInt64

namespace Syntax

variable {Base : Type u} {Free : Type v}
variable {Target : Type w}

/-- Rename every free term variable.  Base-type names and bound indices are
unchanged. -/
def mapFree (rename : Free -> Target) : Syntax Base Free -> Syntax Base Target
  | .base name => .base name
  | .boolTy => .boolTy
  | .indTy => .indTy
  | .arr domain codomain => .arr (domain.mapFree rename) (codomain.mapFree rename)
  | .sub carrier predicate => .sub (carrier.mapFree rename) (predicate.mapFree rename)
  | .bound index => .bound index
  | .free name => .free (rename name)
  | .app function argument => .app (function.mapFree rename) (argument.mapFree rename)
  | .lam domain body => .lam (domain.mapFree rename) (body.mapFree rename)
  | .bool value => .bool value
  | .zero => .zero
  | .succ value => .succ (value.mapFree rename)
  | .eqn type left right =>
      .eqn (type.mapFree rename) (left.mapFree rename) (right.mapFree rename)
  | .eps type predicate => .eps (type.mapFree rename) (predicate.mapFree rename)
  | .abs carrier predicate value =>
      .abs (carrier.mapFree rename) (predicate.mapFree rename) (value.mapFree rename)
  | .rep carrier predicate value =>
      .rep (carrier.mapFree rename) (predicate.mapFree rename) (value.mapFree rename)

/-- Partially rename every free term variable.  Failure at any free name
rejects the whole tree. -/
def traverseFree (rename : Free -> Option Target) : Syntax Base Free -> Option (Syntax Base Target)
  | .base name => some (.base name)
  | .boolTy => some .boolTy
  | .indTy => some .indTy
  | .arr domain codomain => do
      let domain' <- domain.traverseFree rename
      let codomain' <- codomain.traverseFree rename
      pure (.arr domain' codomain')
  | .sub carrier predicate => do
      let carrier' <- carrier.traverseFree rename
      let predicate' <- predicate.traverseFree rename
      pure (.sub carrier' predicate')
  | .bound index => some (.bound index)
  | .free name =>
      match rename name with
      | none => none
      | some name' => some (.free name')
  | .app function argument => do
      let function' <- function.traverseFree rename
      let argument' <- argument.traverseFree rename
      pure (.app function' argument')
  | .lam domain body => do
      let domain' <- domain.traverseFree rename
      let body' <- body.traverseFree rename
      pure (.lam domain' body')
  | .bool value => some (.bool value)
  | .zero => some .zero
  | .succ value =>
      match value.traverseFree rename with
      | none => none
      | some value' => some (.succ value')
  | .eqn type left right => do
      let type' <- type.traverseFree rename
      let left' <- left.traverseFree rename
      let right' <- right.traverseFree rename
      pure (.eqn type' left' right')
  | .eps type predicate => do
      let type' <- type.traverseFree rename
      let predicate' <- predicate.traverseFree rename
      pure (.eps type' predicate')
  | .abs carrier predicate value => do
      let carrier' <- carrier.traverseFree rename
      let predicate' <- predicate.traverseFree rename
      let value' <- value.traverseFree rename
      pure (.abs carrier' predicate' value')
  | .rep carrier predicate value => do
      let carrier' <- carrier.traverseFree rename
      let predicate' <- predicate.traverseFree rename
      let value' <- value.traverseFree rename
      pure (.rep carrier' predicate' value')

@[simp] theorem mapFree_id (term : Syntax Base Free) : term.mapFree id = term := by
  induction term <;> simp [mapFree, *]

theorem mapFree_comp {Final : Type x} (first : Free -> Target) (second : Target -> Final)
    (term : Syntax Base Free) :
    (term.mapFree first).mapFree second = term.mapFree (second ∘ first) := by
  induction term <;> simp [mapFree, *, Function.comp_apply]

@[simp] theorem traverseFree_some (rename : Free -> Target) (term : Syntax Base Free) :
    term.traverseFree (some ∘ rename) = some (term.mapFree rename) := by
  induction term <;> simp [traverseFree, mapFree, *, Function.comp_apply]

@[simp] theorem traverseFree_id (term : Syntax Base Free) :
    term.traverseFree some = some term := by
  simpa using traverseFree_some (Base := Base) id term

end Syntax

end Nucleus.HolJson
