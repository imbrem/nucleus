import Nucleus.HolE

/-!
# Named HolE syntax

Binders carry names, and occurrences carry the same syntactic sort information
as free variables.  A binder captures only an occurrence with the same name
and the same syntactic sort.  Type conversion is not part of name resolution.
-/

namespace Nucleus.HolE.Named

universe u v
set_option relaxedAutoImplicit true

abbrev Kind := Nucleus.HolE.Kind
abbrev HolSort := Nucleus.HolE.HolSort
abbrev Signature := Nucleus.HolE.Signature

/-- A name paired with the syntactic sort that participates in its identity. -/
structure Decl (S : Type v) (Name : Type := Nat) where
  name : Name
  sort : S
  deriving DecidableEq

/-- Fully named HolE syntax.  There are no de Bruijn occurrences in this type. -/
inductive Expr (Sig : Signature) (Name : Type := Nat) : HolSort → Type (max u 1) where
  | boolTy : Expr Sig Name (.kind .star)
  | arr (domain codomain : Expr Sig Name (.kind .star)) :
      Expr Sig Name (.kind .star)
  | tyApp {domain codomain : Kind}
      (function : Expr Sig Name (.kind (.arr domain codomain)))
      (argument : Expr Sig Name (.kind domain)) : Expr Sig Name (.kind codomain)
  | tyLam {domain codomain : Kind} (name : Name)
      (body : Expr Sig Name (.kind codomain)) :
      Expr Sig Name (.kind (.arr domain codomain))
  | tyFv (name : Name) (kind : Kind) : Expr Sig Name (.kind kind)
  | sub (carrier : Expr Sig Name (.kind .star)) (name : Name)
      (predicate : Expr Sig Name .tm) : Expr Sig Name (.kind .star)
  | tyExists (name : Name) (predicate : Expr Sig Name .tm) : Expr Sig Name .tm
  | tyForall (name : Name) (predicate : Expr Sig Name .tm) : Expr Sig Name .tm
  | model (name : Name) (predicate : Expr Sig Name .tm) :
      Expr Sig Name (.kind .star)
  | primFam {kind : Kind} (symbol : Sig (.kind kind)) : Expr Sig Name (.kind kind)
  | primTm (symbol : Sig .tm) : Expr Sig Name .tm
  | tmFv (name : Name) (type : Expr Sig Name (.kind .star)) : Expr Sig Name .tm
  | app (function argument : Expr Sig Name .tm) : Expr Sig Name .tm
  | lam (name : Name) (domain : Expr Sig Name (.kind .star))
      (body : Expr Sig Name .tm) : Expr Sig Name .tm
  | bool (value : Bool) : Expr Sig Name .tm
  | eq (type : Expr Sig Name (.kind .star))
      (left right : Expr Sig Name .tm) : Expr Sig Name .tm
  | eps (type : Expr Sig Name (.kind .star))
      (predicate : Expr Sig Name .tm) : Expr Sig Name .tm
  | abs (carrier : Expr Sig Name (.kind .star)) (name : Name)
      (predicate value : Expr Sig Name .tm) : Expr Sig Name .tm
  | rep (carrier : Expr Sig Name (.kind .star)) (name : Name)
      (predicate value : Expr Sig Name .tm) : Expr Sig Name .tm

abbrev Fam (Sig : Signature) (kind : Kind) (Name : Type := Nat) :=
  Expr Sig Name (.kind kind)
abbrev Ty (Sig : Signature) (Name : Type := Nat) := Fam Sig .star Name
abbrev Tm (Sig : Signature) (Name : Type := Nat) := Expr Sig Name .tm

abbrev TyDecl (Name : Type := Nat) := Decl Kind Name
abbrev TmDecl (Sig : Signature) (Name : Type := Nat) := Decl (Ty Sig Name) Name

def tyDecl (name : Name) (kind : Kind) : TyDecl Name := ⟨name, kind⟩

def tmDecl (name : Name) (type : Ty Sig Name) : TmDecl Sig Name := ⟨name, type⟩

/-- Core let-binding is lambda application, not a syntax constructor. -/
def letTm (name : Name) (type : Ty Sig Name) (value body : Tm Sig Name) : Tm Sig Name :=
  .app (.lam name type body) value

@[simp] theorem letTm_eq (name : Name) (type : Ty Sig Name) (value body : Tm Sig Name) :
    letTm name type value body = .app (.lam name type body) value := rfl

/-- Rename every binder and variable occurrence uniformly. -/
def mapNames (f : Name → Name') : Expr Sig Name sort → Expr Sig Name' sort
  | .boolTy => .boolTy
  | .arr A B => .arr (mapNames f A) (mapNames f B)
  | .tyApp F A => .tyApp (mapNames f F) (mapNames f A)
  | .tyLam name body => .tyLam (f name) (mapNames f body)
  | .tyFv name kind => .tyFv (f name) kind
  | .sub A name predicate => .sub (mapNames f A) (f name) (mapNames f predicate)
  | .tyExists name predicate => .tyExists (f name) (mapNames f predicate)
  | .tyForall name predicate => .tyForall (f name) (mapNames f predicate)
  | .model name predicate => .model (f name) (mapNames f predicate)
  | .primFam symbol => .primFam symbol
  | .primTm symbol => .primTm symbol
  | .tmFv name A => .tmFv (f name) (mapNames f A)
  | .app function argument => .app (mapNames f function) (mapNames f argument)
  | .lam name A body => .lam (f name) (mapNames f A) (mapNames f body)
  | .bool value => .bool value
  | .eq A left right => .eq (mapNames f A) (mapNames f left) (mapNames f right)
  | .eps A predicate => .eps (mapNames f A) (mapNames f predicate)
  | .abs A name predicate value =>
      .abs (mapNames f A) (f name) (mapNames f predicate) (mapNames f value)
  | .rep A name predicate value =>
      .rep (mapNames f A) (f name) (mapNames f predicate) (mapNames f value)

@[simp] theorem mapNames_id (expression : Expr Sig Name sort) :
    mapNames id expression = expression := by
  induction expression <;> simp_all [mapNames]

theorem mapNames_comp (g : Name' → Name'') (f : Name → Name')
    (expression : Expr Sig Name sort) :
    mapNames g (mapNames f expression) = mapNames (g ∘ f) expression := by
  induction expression <;> simp_all [mapNames, Function.comp_apply]

@[simp] theorem mapNames_letTm (f : Name → Name') (name : Name)
    (A : Ty Sig Name) (value body : Tm Sig Name) :
    mapNames f (letTm name A value body) =
      letTm (f name) (mapNames f A) (mapNames f value) (mapNames f body) := rfl

end Nucleus.HolE.Named
