import Nucleus.Hol.Propane.Builtin

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
  | word (width : Width)
  | nat
  | int
  | bytes
  | arr (domain codomain : Ty)
  deriving DecidableEq, Repr

@[reducible] def Ty.ofLiteral : LiteralTy → Ty
  | .bool => .bool | .word width => .word width
  | .nat => .nat | .int => .int | .bytes => .bytes

@[reducible] def Ty.denote : Ty → Type
  | .bool => Bool | .word width => BitVec width.bits
  | .nat => Nat | .int => Int | .bytes => List UInt8
  | .arr domain codomain => domain.denote → codomain.denote

def Ty.default : (type : Ty) → type.denote
  | .bool => false | .word _ => 0 | .nat => 0 | .int => 0 | .bytes => []
  | .arr _ codomain => fun _ => codomain.default

@[simp] theorem Ty.denote_ofLiteral (type : LiteralTy) :
    (ofLiteral type).denote = type.denote := by cases type <;> rfl

def Ty.literalValue (type : LiteralTy) (value : type.denote) : (ofLiteral type).denote :=
  (denote_ofLiteral type).symm ▸ value

@[reducible] def Ty.arrows (inputs : List LiteralTy) (output : LiteralTy) : Ty :=
  inputs.foldr (fun input rest => .arr (ofLiteral input) rest) (ofLiteral output)

/-- A heterogeneous list containing exactly the specified literal carriers. -/
inductive LiteralArgs : List LiteralTy → Type where
  | nil : LiteralArgs []
  | cons {type : LiteralTy} {types : List LiteralTy}
      (value : type.denote) (rest : LiteralArgs types) : LiteralArgs (type :: types)

def LiteralArgs.values : {types : List LiteralTy} → LiteralArgs types → List LiteralValue
  | _, .nil => []
  | _, .cons value rest => LiteralValue.ofDenote _ value :: rest.values

/-- A concrete builtin constant has an ordinary curried HOL interpretation.
Undefined applications use the fixed default carrier value. The reduction rule
requires success, so it never exposes this totalization as an execution result. -/
def Builtin.curried (op : Builtin) (output : LiteralTy) :
    (inputs : List LiteralTy) → List LiteralValue → (Ty.arrows inputs output).denote
  | [], supplied =>
      Ty.literalValue output (((op.eval supplied).bind (LiteralValue.as output)).getD
        output.default)
  | input :: inputs, supplied => fun value =>
      op.curried output inputs (supplied ++ [LiteralValue.ofDenote input
        (Ty.denote_ofLiteral input ▸ value)])

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
  | literal (type : LiteralTy) (value : type.denote) : Tm Γ (Ty.ofLiteral type)
  | builtin (op : Builtin) {inputs : List LiteralTy} {output : LiteralTy}
      (signature : op.signature = some (inputs, output)) : Tm Γ (Ty.arrows inputs output)
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
  | .literal type value => .literal type value
  | .builtin op signature => .builtin op signature
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
  | .literal type value => .literal type value
  | .builtin op signature => .builtin op signature
  | .eq left right => .eq (left.subst substitute) (right.subst substitute)
  | .eps predicate => .eps (predicate.subst substitute)
  | .junk => .junk

def single (argument : Tm Γ A) : Sub (A :: Γ) Γ
  | _, .zero => argument
  | _, .succ index => .bv index

/-- Open the newest lambda binder. -/
def Tm.open (body : Tm (A :: Γ) B) (argument : Tm Γ A) : Tm Γ B :=
  body.subst (single argument)

/-- Apply a builtin to typed literal operands without exposing arena storage. -/
def Tm.applyLiterals {Γ : List Ty} {output : LiteralTy} :
    {inputs : List LiteralTy} → Tm Γ (Ty.arrows inputs output) →
      LiteralArgs inputs → Tm Γ (Ty.ofLiteral output)
  | [], term, .nil => term
  | _ :: _, term, .cons value rest =>
      (Tm.app term (.literal _ value)).applyLiterals rest

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
