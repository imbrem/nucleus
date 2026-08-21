/-!
# Propane: an always-well-typed HOL prototype

Propane is the next experimental hydrocarbon after Ethane.  It deliberately
starts with simple types so the always-well-typed boundary can be studied in
isolation.  Every `Tm Γ A` has type `A` by construction.  Total checked
interfaces return the opaque `junk` term at their requested type on mismatch;
the proof theory gives `junk` no special equations.
-/

namespace Nucleus.Hol.Propane

set_option relaxedAutoImplicit true

/-- Intrinsically well-kinded simple HOL types. -/
inductive Ty where
  | bool
  | arr (domain codomain : Ty)
  deriving DecidableEq, Repr

/-- A typed de Bruijn variable. -/
inductive Var : List Ty → Ty → Type where
  | zero : Var (A :: Γ) A
  | succ : Var Γ A → Var (B :: Γ) A

/-- Every Propane term is intrinsically typed. -/
inductive Tm : (Γ : List Ty) → Ty → Type where
  | bv (index : Var Γ A) : Tm Γ A
  | fv (name : Nat) : Tm Γ A
  | app (function : Tm Γ (.arr A B)) (argument : Tm Γ A) : Tm Γ B
  | lam (body : Tm (A :: Γ) B) : Tm Γ (.arr A B)
  | bool (value : Bool) : Tm Γ .bool
  | eq (left right : Tm Γ A) : Tm Γ .bool
  | eps (predicate : Tm Γ (.arr A .bool)) : Tm Γ A
  /-- Well-typed but intentionally opaque garbage. -/
  | junk : Tm Γ A

abbrev Closed (A : Ty) := Tm [] A
abbrev Wff (Γ : List Ty) := Tm Γ .bool

/-- Type-preserving renamings of bound variables. -/
abbrev Ren (Γ Δ : List Ty) := {A : Ty} → Var Γ A → Var Δ A

def liftRen (rename : Ren Γ Δ) : Ren (A :: Γ) (A :: Δ)
  | _, .zero => .zero
  | _, .succ index => .succ (rename index)

def weakenRen : Ren Γ (A :: Γ) := fun index => .succ index

/-- Rename bound variables. -/
def Tm.rename (rename : Ren Γ Δ) : Tm Γ A → Tm Δ A
  | .bv index => .bv (rename index)
  | .fv name => .fv name
  | .app function argument => .app (function.rename rename) (argument.rename rename)
  | .lam body => .lam (body.rename (liftRen rename))
  | .bool value => .bool value
  | .eq left right => .eq (left.rename rename) (right.rename rename)
  | .eps predicate => .eps (predicate.rename rename)
  | .junk => .junk

/-- Type-preserving simultaneous substitution. -/
abbrev Sub (Γ Δ : List Ty) := {A : Ty} → Var Γ A → Tm Δ A

def liftSub (substitute : Sub Γ Δ) : Sub (A :: Γ) (A :: Δ)
  | _, .zero => .bv .zero
  | _, .succ index => (substitute index).rename weakenRen

/-- Substitute every bound variable. -/
def Tm.subst (substitute : Sub Γ Δ) : Tm Γ A → Tm Δ A
  | .bv index => substitute index
  | .fv name => .fv name
  | .app function argument => .app (function.subst substitute) (argument.subst substitute)
  | .lam body => .lam (body.subst (liftSub substitute))
  | .bool value => .bool value
  | .eq left right => .eq (left.subst substitute) (right.subst substitute)
  | .eps predicate => .eps (predicate.subst substitute)
  | .junk => .junk

def single (argument : Tm Γ A) : Sub (A :: Γ) Γ
  | _, .zero => argument
  | _, .succ index => .bv index

/-- Open the newest lambda binder. -/
def Tm.open (body : Tm (A :: Γ) B) (argument : Tm Γ A) : Tm Γ B :=
  body.subst (single argument)

/-- A total coercion.  It is the identity for syntactically equal types and
opaque garbage at the requested target type otherwise. -/
def Tm.cast (target : Ty) (term : Tm Γ source) : Tm Γ target :=
  if equality : source = target then equality ▸ term else .junk

@[simp] theorem Tm.cast_same (term : Tm Γ A) : term.cast A = term := by
  simp [Tm.cast]

/-- A term carrying its intrinsic type as data. -/
structure AnyTm (Γ : List Ty) where
  type : Ty
  term : Tm Γ type

/-- Total application at a caller-provided function type.  Successful checks
construct ordinary application; either mismatch produces typed garbage. -/
def AnyTm.applyAs (domain codomain : Ty) (function argument : AnyTm Γ) :
    Tm Γ codomain :=
  if functionType : function.type = .arr domain codomain then
    if argumentType : argument.type = domain then
      .app (functionType ▸ function.term) (argumentType ▸ argument.term)
    else .junk
  else .junk

theorem AnyTm.applyAs_exact (function : Tm Γ (.arr A B)) (argument : Tm Γ A) :
    AnyTm.applyAs A B ⟨.arr A B, function⟩ ⟨A, argument⟩ = .app function argument := by
  simp [AnyTm.applyAs]

end Nucleus.Hol.Propane
