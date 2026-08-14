import Nucleus.Hol.Signature

/-!
# Type-variable-scoped HOL and pointwise subtype families

This is the experimental syntax layer for the question left deliberately out
of the first signature kernel: using ordinary HOL subtypes to construct whole
type families.  Type-variable scope is separate from term-variable scope.
-/

namespace Nucleus.Hol.FamilySub

universe u
set_option relaxedAutoImplicit true

/-- A kind-indexed de Bruijn variable in a heterogeneous type context. -/
inductive TyVar : List Kind → Kind → Type where
  | zero : TyVar (kind :: context) kind
  | succ : TyVar context kind → TyVar (other :: context) kind

abbrev TyRen (source target : List Kind) :=
  {kind : Kind} → TyVar source kind → TyVar target kind

def liftTyRen (ρ : TyRen source target) :
    TyRen (kind :: source) (kind :: target)
  | _, .zero => .zero
  | _, .succ v => .succ (ρ v)

/-- HOL syntax with independent locally nameless scopes for type and term
variables.  `tyLam` is only type-family abstraction; it does not add impredicative
type quantification to the object logic. -/
inductive Expr (Sig : Signature) : List Kind → HolSort → Nat → Type u where
  | boolTy : Expr Sig types (.kind .star) 0
  | arr (domain codomain : Expr Sig types (.kind .star) 0) :
      Expr Sig types (.kind .star) 0
  | tyApp {domain codomain : Kind}
      (function : Expr Sig types (.kind (.arr domain codomain)) 0)
      (argument : Expr Sig types (.kind domain) 0) : Expr Sig types (.kind codomain) 0
  | tyLam {domain codomain : Kind}
      (body : Expr Sig (domain :: types) (.kind codomain) 0) :
      Expr Sig types (.kind (.arr domain codomain)) 0
  | tyBv {kind : Kind} (v : TyVar types kind) : Expr Sig types (.kind kind) 0
  | sub (carrier : Expr Sig types (.kind .star) 0)
      (predicate : Expr Sig types .tm 1) : Expr Sig types (.kind .star) 0
  | primFam {kind : Kind} (symbol : Sig (.kind kind)) : Expr Sig types (.kind kind) 0
  | primTm {depth : Nat} (symbol : Sig .tm) : Expr Sig types .tm depth
  | bv {depth : Nat} (index : Fin depth) : Expr Sig types .tm depth
  | fv {depth : Nat} (name : Nat) (type : Expr Sig types (.kind .star) 0) :
      Expr Sig types .tm depth
  | app {depth : Nat} (function argument : Expr Sig types .tm depth) :
      Expr Sig types .tm depth
  | lam {depth : Nat} (domain : Expr Sig types (.kind .star) 0)
      (body : Expr Sig types .tm (depth + 1)) : Expr Sig types .tm depth
  | bool {depth : Nat} (value : Bool) : Expr Sig types .tm depth
  | eq {depth : Nat} (type : Expr Sig types (.kind .star) 0)
      (left right : Expr Sig types .tm depth) : Expr Sig types .tm depth
  | eps {depth : Nat} (type : Expr Sig types (.kind .star) 0)
      (predicate : Expr Sig types .tm depth) : Expr Sig types .tm depth
  | abs {depth : Nat} (carrier : Expr Sig types (.kind .star) 0)
      (predicate : Expr Sig types .tm 1) (value : Expr Sig types .tm depth) :
      Expr Sig types .tm depth
  | rep {depth : Nat} (carrier : Expr Sig types (.kind .star) 0)
      (predicate : Expr Sig types .tm 1) (value : Expr Sig types .tm depth) :
      Expr Sig types .tm depth

abbrev Fam (Sig : Signature) (types : List Kind) (kind : Kind) :=
  Expr Sig types (.kind kind) 0
abbrev Ty (Sig : Signature) (types : List Kind) := Fam Sig types .star
abbrev Tm (Sig : Signature) (types : List Kind) (depth : Nat) := Expr Sig types .tm depth

def renameTypes (ρ : TyRen source target) :
    Expr Sig source sort depth → Expr Sig target sort depth
  | .boolTy => .boolTy
  | .arr A B => .arr (renameTypes ρ A) (renameTypes ρ B)
  | .tyApp F A => .tyApp (renameTypes ρ F) (renameTypes ρ A)
  | .tyLam body => .tyLam (renameTypes (liftTyRen ρ) body)
  | .tyBv v => .tyBv (ρ v)
  | .sub A p => .sub (renameTypes ρ A) (renameTypes ρ p)
  | .primFam symbol => .primFam symbol
  | .primTm symbol => .primTm symbol
  | .bv index => .bv index
  | .fv name A => .fv name (renameTypes ρ A)
  | .app f x => .app (renameTypes ρ f) (renameTypes ρ x)
  | .lam A body => .lam (renameTypes ρ A) (renameTypes ρ body)
  | .bool value => .bool value
  | .eq A x y => .eq (renameTypes ρ A) (renameTypes ρ x) (renameTypes ρ y)
  | .eps A p => .eps (renameTypes ρ A) (renameTypes ρ p)
  | .abs A p x => .abs (renameTypes ρ A) (renameTypes ρ p) (renameTypes ρ x)
  | .rep A p x => .rep (renameTypes ρ A) (renameTypes ρ p) (renameTypes ρ x)

def weakenTypes (expression : Expr Sig types sort depth) :
    Expr Sig (kind :: types) sort depth :=
  renameTypes (fun v => .succ v) expression

/-- Pointwise subtype-family formation, defined solely from type-family lambda,
application, and ordinary `Sub`.  Its predicate receives one term whose type is
`carrier α`, where `α` is the freshly bound type variable. -/
def subFam {kind : Kind} (carrier : Fam Sig types (.arr kind .star))
    (predicate : Tm Sig (kind :: types) 1) : Fam Sig types (.arr kind .star) :=
  .tyLam (.sub (.tyApp (weakenTypes carrier) (.tyBv .zero)) predicate)

abbrev BoundCtx (Sig : Signature) (types : List Kind) (depth : Nat) :=
  Fin depth → Ty Sig types

def emptyBound : BoundCtx Sig types 0 := Fin.elim0

def extendBound (A : Ty Sig types) (context : BoundCtx Sig types depth) :
    BoundCtx Sig types (depth + 1) := Fin.cases A context

class SigTyping (Sig : Signature) where
  HasType : Sig .tm → Ty Sig [] → Prop

inductive Classification (Sig : Signature) (types : List Kind) : HolSort → Type u where
  | kind {kind : Kind} : Classification Sig types (.kind kind)
  | tm (type : Ty Sig types) : Classification Sig types .tm

def weakenClosed (A : Ty Sig []) : Ty Sig types :=
  renameTypes (source := []) (target := types) (fun {_} v => nomatch v) A

inductive Checks {Sig : Signature} [SigTyping Sig] : {types : List Kind} →
    {sort : HolSort} → {depth : Nat} → BoundCtx Sig types depth →
    Expr Sig types sort depth → Classification Sig types sort → Prop where
  | boolTy : Checks emptyBound .boolTy .kind
  | arr : Checks emptyBound A .kind → Checks emptyBound B .kind →
      Checks emptyBound (.arr A B) .kind
  | tyApp : Checks emptyBound F .kind → Checks emptyBound A .kind →
      Checks emptyBound (.tyApp F A) .kind
  | tyLam : Checks (types := kind :: types) emptyBound body .kind →
      Checks (types := types) emptyBound (.tyLam body) .kind
  | tyBv (v : TyVar types kind) : Checks emptyBound (.tyBv v) .kind
  | sub : Checks emptyBound A .kind →
      Checks (extendBound A emptyBound) p (.tm .boolTy) →
      Checks emptyBound (.sub A p) .kind
  | primFam (symbol : Sig (.kind kind)) : Checks emptyBound (.primFam symbol) .kind
  | primTm (rule : SigTyping.HasType symbol A) :
      Checks Γ (.primTm symbol) (.tm (weakenClosed A))
  | bv (hA : Checks emptyBound A .kind) (lookup : Γ i = A) :
      Checks Γ (.bv i) (.tm A)
  | fv (name : Nat) (hA : Checks emptyBound A .kind) : Checks Γ (.fv name A) (.tm A)
  | app : Checks Γ f (.tm (.arr A B)) → Checks Γ x (.tm A) →
      Checks Γ (.app f x) (.tm B)
  | lam (body : Tm Sig types (depth + 1)) (hA : Checks emptyBound A .kind) :
      Checks (extendBound A Γ) body (.tm B) → Checks Γ (.lam A body) (.tm (.arr A B))
  | bool (value : Bool) : Checks Γ (.bool value) (.tm .boolTy)
  | eq (hA : Checks emptyBound A .kind) : Checks Γ x (.tm A) → Checks Γ y (.tm A) →
      Checks Γ (.eq A x y) (.tm .boolTy)
  | eps (hA : Checks emptyBound A .kind) : Checks Γ p (.tm (.arr A .boolTy)) →
      Checks Γ (.eps A p) (.tm A)
  | abs (hA : Checks emptyBound A .kind)
      (hp : Checks (extendBound A emptyBound) p (.tm .boolTy)) :
      Checks Γ x (.tm A) → Checks Γ (.abs A p x) (.tm (.sub A p))
  | rep (hA : Checks emptyBound A .kind)
      (hp : Checks (extendBound A emptyBound) p (.tm .boolTy)) :
      Checks Γ x (.tm (.sub A p)) → Checks Γ (.rep A p x) (.tm A)

abbrev Kinded {Sig : Signature} [SigTyping Sig] (A : Fam Sig types kind) : Prop :=
  Checks emptyBound A .kind

abbrev HasType {Sig : Signature} [SigTyping Sig] (Γ : BoundCtx Sig types depth)
    (term : Tm Sig types depth) (A : Ty Sig types) : Prop := Checks Γ term (.tm A)

/-- The crucial admissible construction: ordinary subtype formation under a
type-family lambda yields a well-kinded family. -/
theorem subFam_kinded {Sig : Signature} [SigTyping Sig] {kind : Kind}
    {carrier : Fam Sig types (.arr kind .star)}
    {predicate : Tm Sig (kind :: types) 1}
    (_carrierKinded : Kinded carrier)
    (predicateTyped : HasType
      (extendBound (.tyApp (weakenTypes (kind := kind) carrier) (.tyBv .zero)) emptyBound)
      predicate .boolTy)
    (weakenedCarrierKinded : Kinded (weakenTypes (kind := kind) carrier)) :
    Kinded (subFam carrier predicate) := by
  exact .tyLam (.sub (.tyApp weakenedCarrierKinded (.tyBv .zero)) predicateTyped)

/-! ## Embedding of the closed signature kernel -/

def embed : {sort : HolSort} → {depth : Nat} → Nucleus.Hol.Expr Sig sort depth →
    Expr Sig [] sort depth
  | _, _, .boolTy => .boolTy
  | _, _, .arr A B => .arr (embed A) (embed B)
  | _, _, .tyApp F A => .tyApp (embed F) (embed A)
  | _, _, .sub A p => .sub (embed A) (embed p)
  | _, _, .primFam symbol => .primFam symbol
  | _, _, .primTm symbol => .primTm symbol
  | _, _, .bv index => .bv index
  | _, _, .fv name A => .fv name (embed A)
  | _, _, .app f x => .app (embed f) (embed x)
  | _, _, .lam A body => .lam (embed A) (embed body)
  | _, _, .bool value => .bool value
  | _, _, .eq A x y => .eq (embed A) (embed x) (embed y)
  | _, _, .eps A p => .eps (embed A) (embed p)
  | _, _, .abs A p x => .abs (embed A) (embed p) (embed x)
  | _, _, .rep A p x => .rep (embed A) (embed p) (embed x)

def embedBoundCtx (Γ : Nucleus.Hol.BoundCtx Sig depth) : BoundCtx Sig [] depth :=
  fun i => embed (Γ i)

end Nucleus.Hol.FamilySub
