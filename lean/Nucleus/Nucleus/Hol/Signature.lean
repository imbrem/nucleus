import Nucleus.HolLN.Syntax

/-!
# Sorted signatures for HOL

A signature is a family `HolSort → Type`.  Its inhabitants therefore already
belong to one precise syntactic sort: a type-family symbol has a particular
kind, while a term symbol is classified by a syntactic HOL type supplied by
`SigTyping`.
-/

namespace Nucleus.Hol

universe u

abbrev Kind := HolLN.Kind
abbrev HolSort := HolLN.HolSort

/-- A signature has a subtype of primitive symbols at every syntactic sort. -/
abbrev Signature := HolSort → Type u

/-- Sorted, intrinsically scoped, but extrinsically typed HOL syntax. -/
inductive Expr (Sig : Signature) : HolSort → Nat → Type u where
  | boolTy : Expr Sig (.kind .star) 0
  | arr (domain codomain : Expr Sig (.kind .star) 0) : Expr Sig (.kind .star) 0
  | tyApp {domain codomain : Kind}
      (function : Expr Sig (.kind (.arr domain codomain)) 0)
      (argument : Expr Sig (.kind domain) 0) : Expr Sig (.kind codomain) 0
  | sub (carrier : Expr Sig (.kind .star) 0)
      (predicate : Expr Sig .tm 1) : Expr Sig (.kind .star) 0
  | primFam {kind : Kind} (symbol : Sig (.kind kind)) : Expr Sig (.kind kind) 0
  | primTm {depth : Nat} (symbol : Sig .tm) : Expr Sig .tm depth
  | bv {depth : Nat} (index : Fin depth) : Expr Sig .tm depth
  | fv {depth : Nat} (name : Nat)
      (type : Expr Sig (.kind .star) 0) : Expr Sig .tm depth
  | app {depth : Nat} (function argument : Expr Sig .tm depth) : Expr Sig .tm depth
  | lam {depth : Nat} (domain : Expr Sig (.kind .star) 0)
      (body : Expr Sig .tm (depth + 1)) : Expr Sig .tm depth
  | bool {depth : Nat} (value : Bool) : Expr Sig .tm depth
  | eq {depth : Nat} (type : Expr Sig (.kind .star) 0)
      (left right : Expr Sig .tm depth) : Expr Sig .tm depth
  | eps {depth : Nat} (type : Expr Sig (.kind .star) 0)
      (predicate : Expr Sig .tm depth) : Expr Sig .tm depth
  | abs {depth : Nat} (carrier : Expr Sig (.kind .star) 0)
      (predicate : Expr Sig .tm 1) (value : Expr Sig .tm depth) : Expr Sig .tm depth
  | rep {depth : Nat} (carrier : Expr Sig (.kind .star) 0)
      (predicate : Expr Sig .tm 1) (value : Expr Sig .tm depth) : Expr Sig .tm depth

abbrev Fam (Sig : Signature) (kind : Kind) := Expr Sig (.kind kind) 0
abbrev Ty (Sig : Signature) := Fam Sig .star
abbrev Tm (Sig : Signature) (depth : Nat) := Expr Sig .tm depth
abbrev BoundCtx (Sig : Signature) (depth : Nat) := Fin depth → Ty Sig

def emptyBound {Sig : Signature} : BoundCtx Sig 0 := Fin.elim0

def extendBound {Sig : Signature} {depth : Nat} (A : Ty Sig)
    (Γ : BoundCtx Sig depth) : BoundCtx Sig (depth + 1) := Fin.cases A Γ

/-- A signature may assign arbitrary, potentially non-unique types to its term
symbols. Family symbols are already placed at their kind by `Sig`. -/
class SigTyping (Sig : Signature) where
  HasType : Sig .tm → Ty Sig → Prop

/-- Optional stronger structure for signatures whose primitive typing is
computed by a function.  This is not required by syntax or the typing judgment. -/
class FunctionalSigTyping (Sig : Signature) [SigTyping Sig] where
  typeOf : Sig .tm → Ty Sig
  hasType_iff {symbol : Sig .tm} {A : Ty Sig} :
    SigTyping.HasType symbol A ↔ A = typeOf symbol

inductive Classification (Sig : Signature) : HolSort → Type u where
  | kind {kind : Kind} : Classification Sig (.kind kind)
  | tm (type : Ty Sig) : Classification Sig .tm

/-- Unified family formation and term typing. -/
inductive Checks {Sig : Signature} [SigTyping Sig] : {sort : HolSort} →
    {depth : Nat} → BoundCtx Sig depth → Expr Sig sort depth →
    Classification Sig sort → Prop where
  | primFam {kind : Kind} (symbol : Sig (.kind kind)) :
      Checks emptyBound (.primFam symbol) .kind
  | primTm {symbol : Sig .tm} {A : Ty Sig} (rule : SigTyping.HasType symbol A) :
      Checks Γ (.primTm symbol) (.tm A)
  | boolTy : Checks emptyBound .boolTy .kind
  | arr : Checks emptyBound A .kind → Checks emptyBound B .kind →
      Checks emptyBound (.arr A B) .kind
  | tyApp : Checks emptyBound F .kind → Checks emptyBound A .kind →
      Checks emptyBound (.tyApp F A) .kind
  | sub : Checks emptyBound A .kind →
      Checks (extendBound A emptyBound) p (.tm .boolTy) →
      Checks emptyBound (.sub A p) .kind
  | bv (hA : Checks emptyBound A .kind) (lookup : Γ i = A) :
      Checks Γ (.bv i) (.tm A)
  | fv (name : Nat) (hA : Checks emptyBound A .kind) : Checks Γ (.fv name A) (.tm A)
  | app : Checks Γ f (.tm (.arr A B)) → Checks Γ x (.tm A) →
      Checks Γ (.app f x) (.tm B)
  | lam {depth : Nat} {Γ : BoundCtx Sig depth} (body : Tm Sig (depth + 1))
      (hA : Checks emptyBound A .kind) : Checks (extendBound A Γ) body (.tm B) →
      Checks Γ (.lam A body) (.tm (.arr A B))
  | bool (value : Bool) : Checks Γ (.bool value) (.tm .boolTy)
  | eq (hA : Checks emptyBound A .kind) : Checks Γ x (.tm A) →
      Checks Γ y (.tm A) → Checks Γ (.eq A x y) (.tm .boolTy)
  | eps (hA : Checks emptyBound A .kind) : Checks Γ p (.tm (.arr A .boolTy)) →
      Checks Γ (.eps A p) (.tm A)
  | abs (hA : Checks emptyBound A .kind)
      (hp : Checks (extendBound A emptyBound) p (.tm .boolTy)) :
      Checks Γ x (.tm A) → Checks Γ (.abs A p x) (.tm (.sub A p))
  | rep (hA : Checks emptyBound A .kind)
      (hp : Checks (extendBound A emptyBound) p (.tm .boolTy)) :
      Checks Γ x (.tm (.sub A p)) → Checks Γ (.rep A p x) (.tm A)

abbrev Kinded {Sig : Signature} [SigTyping Sig] {kind : Kind} (A : Fam Sig kind) : Prop :=
  Checks emptyBound A .kind

abbrev HasType {Sig : Signature} [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) (tm : Tm Sig depth) (A : Ty Sig) : Prop :=
  Checks Γ tm (.tm A)

structure Checked (Sig : Signature) [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) (A : Ty Sig) where
  tm : Tm Sig depth
  typing : HasType Γ tm A

/-- The empty signature has no extension symbols at any sort. -/
def FiniteSig : HolSort → Type := fun _ => Empty

instance : SigTyping FiniteSig where
  HasType symbol := nomatch symbol

private theorem finite_hasType_iff {symbol : FiniteSig .tm} {A : Ty FiniteSig} :
    SigTyping.HasType symbol A ↔ A = (nomatch symbol : Ty FiniteSig) := nomatch symbol

instance : FunctionalSigTyping FiniteSig where
  typeOf symbol := nomatch symbol
  hasType_iff := finite_hasType_iff

namespace Finite

abbrev Expr := Nucleus.Hol.Expr FiniteSig
abbrev Fam := Nucleus.Hol.Fam FiniteSig
abbrev Ty := Nucleus.Hol.Ty FiniteSig
abbrev Tm := Nucleus.Hol.Tm FiniteSig
abbrev Checks := @Nucleus.Hol.Checks FiniteSig inferInstance
abbrev Checked := @Nucleus.Hol.Checked FiniteSig inferInstance

end Finite

/-- The sorted signature of the existing natural-number extension. -/
inductive NatSig : HolSort → Type where
  | natTy : NatSig (.kind .star)
  | zero : NatSig .tm
  | succ : NatSig .tm
  deriving DecidableEq, Repr

def natTy : Ty NatSig := .primFam .natTy
def zero {depth : Nat} : Tm NatSig depth := .primTm .zero
def succConst {depth : Nat} : Tm NatSig depth := .primTm .succ
def succ {depth : Nat} (value : Tm NatSig depth) : Tm NatSig depth := .app succConst value

instance : SigTyping NatSig where
  HasType
    | .zero, A => A = natTy
    | .succ, A => A = .arr natTy natTy

private theorem nat_hasType_iff {symbol : NatSig .tm} {A : Ty NatSig} :
    SigTyping.HasType symbol A ↔ A = match symbol with
      | .zero => natTy
      | .succ => .arr natTy natTy := by
  cases symbol <;> rfl

instance : FunctionalSigTyping NatSig where
  typeOf
    | .zero => natTy
    | .succ => .arr natTy natTy
  hasType_iff := nat_hasType_iff

theorem natTy_kinded : Kinded natTy := .primFam _
theorem zero_typed {depth : Nat} {Γ : BoundCtx NatSig depth} : HasType Γ zero natTy :=
  .primTm rfl
theorem succ_typed {depth : Nat} {Γ : BoundCtx NatSig depth} {value : Tm NatSig depth}
    (typing : HasType Γ value natTy) : HasType Γ (succ value) natTy :=
  .app (.primTm rfl) typing

end Nucleus.Hol
