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
structure Decl (S : Type v) where
  name : Nat
  sort : S
  deriving DecidableEq

/-- Fully named HolE syntax.  There are no de Bruijn occurrences in this type. -/
inductive Expr (Sig : Signature) : HolSort → Type u where
  | boolTy : Expr Sig (.kind .star)
  | arr (domain codomain : Expr Sig (.kind .star)) : Expr Sig (.kind .star)
  | tyApp {domain codomain : Kind}
      (function : Expr Sig (.kind (.arr domain codomain)))
      (argument : Expr Sig (.kind domain)) : Expr Sig (.kind codomain)
  | tyLam {domain codomain : Kind} (name : Nat)
      (body : Expr Sig (.kind codomain)) : Expr Sig (.kind (.arr domain codomain))
  | tyFv (name : Nat) (kind : Kind) : Expr Sig (.kind kind)
  | sub (carrier : Expr Sig (.kind .star)) (name : Nat)
      (predicate : Expr Sig .tm) : Expr Sig (.kind .star)
  | tyExists (name : Nat) (predicate : Expr Sig .tm) : Expr Sig .tm
  | model (name : Nat) (predicate : Expr Sig .tm) : Expr Sig (.kind .star)
  | primFam {kind : Kind} (symbol : Sig (.kind kind)) : Expr Sig (.kind kind)
  | primTm (symbol : Sig .tm) : Expr Sig .tm
  | tmFv (name : Nat) (type : Expr Sig (.kind .star)) : Expr Sig .tm
  | app (function argument : Expr Sig .tm) : Expr Sig .tm
  | lam (name : Nat) (domain : Expr Sig (.kind .star))
      (body : Expr Sig .tm) : Expr Sig .tm
  | bool (value : Bool) : Expr Sig .tm
  | eq (type : Expr Sig (.kind .star))
      (left right : Expr Sig .tm) : Expr Sig .tm
  | eps (type : Expr Sig (.kind .star)) (predicate : Expr Sig .tm) : Expr Sig .tm
  | abs (carrier : Expr Sig (.kind .star)) (name : Nat)
      (predicate value : Expr Sig .tm) : Expr Sig .tm
  | rep (carrier : Expr Sig (.kind .star)) (name : Nat)
      (predicate value : Expr Sig .tm) : Expr Sig .tm

abbrev Fam (Sig : Signature) (kind : Kind) := Expr Sig (.kind kind)
abbrev Ty (Sig : Signature) := Fam Sig .star
abbrev Tm (Sig : Signature) := Expr Sig .tm

abbrev TyDecl := Decl Kind
abbrev TmDecl (Sig : Signature) := Decl (Ty Sig)

def tyDecl (name : Nat) (kind : Kind) : TyDecl := ⟨name, kind⟩

def tmDecl (name : Nat) (type : Ty Sig) : TmDecl Sig := ⟨name, type⟩

/-- Core let-binding is lambda application, not a syntax constructor. -/
def letTm (name : Nat) (type : Ty Sig) (value body : Tm Sig) : Tm Sig :=
  .app (.lam name type body) value

@[simp] theorem letTm_eq (name : Nat) (type : Ty Sig) (value body : Tm Sig) :
    letTm name type value body = .app (.lam name type body) value := rfl

end Nucleus.HolE.Named
