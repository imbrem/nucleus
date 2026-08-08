import Nucleus.Hol.Proof

/-!
# Tree-structured Covalence for regular HOL

The object exposed to a store is a tagged row with exactly three optional
children and a one-layer annotation.  The intrinsically indexed `Term` below
is its sound metatheory: each term lowers under every shared named-hole
filling, and carries the typing proof of every such lowering.
-/

universe u

namespace Nucleus.Cov

open Hol

structure HoleName where
  id : Nat
  deriving DecidableEq, Repr

structure Annotation where
  tmDepth : Nat
  deriving DecidableEq, Repr

inductive Tag where
  | variable (index : Nat)
  | application | abstraction | boolean (value : Bool)
  | equality | choice | subtypeAbs | subtypeRep
  | hole (name : HoleName)
  | cast (certificate : Nat)
  | bound (cutoff : Nat)
  deriving DecidableEq, Repr

/-- The store ABI: one tag and exactly three optional recursive coordinates.
Missing required coordinates are interpreted as holes by the future total
elaborator; no variable-size constructor payload is hidden here. -/
structure Row where
  tag : Tag
  left : Option Row := none
  middle : Option Row := none
  right : Option Row := none
  annotation : Annotation
  deriving Repr

structure Typed (Base : Type u) (Γ : Ctx Base) (A : Ty Base) where
  term : Tm Base
  typing : HasType Γ term A

/-- A single filling is shared by every occurrence of a named hole. -/
abbrev Filling (Base : Type u) :=
  ∀ (Γ : Ctx Base) (name : HoleName) (A : Ty Base),
    Kinded A -> Typed Base Γ A

/-- Every formed HOL type has a canonical inhabitant, so filling families are
nonempty.  This fact is essential when deriving exact consistency from a
universal lowering theorem. -/
def canonicalFilling (Base : Type u) : Filling Base := by
  intro Γ name A hA
  exact ⟨.tmEps A (.tmLam A (.tmBool true)),
    .tmEps hA (.tmLam hA .tmBool)⟩

/-- A certificate table may expose CAS aliases and macro expansions, but an
entry is trusted only through this proof-bearing equality.  This first HOL
layer deliberately uses syntactic type equality; `CovOmega` may generalize
the certificate to denotational conversion without changing row lookup. -/
structure TyEqCert {Base : Type u} (A B : Ty Base) where
  eq : A = B

structure TyEqEntry (Base : Type u) where
  left : Ty Base
  right : Ty Base
  certificate : TyEqCert left right

abbrev TyEqTable (Base : Type u) := Nat -> Option (TyEqEntry Base)

/-- The type index is a field, hence available without traversing the row. -/
structure Term (Base : Type u) (Γ : Ctx Base) where
  ty : Ty Base
  formed : Kinded ty
  row : Row
  lower : Filling Base -> Tm Base
  typing : ∀ e, HasType Γ (lower e) ty

namespace Term

variable {Base : Type u} {Γ : Ctx Base}

private def leaf (tag : Tag) (depth : Nat) : Row :=
  { tag := tag, annotation := ⟨depth⟩ }

private def node (tag : Tag) (depth : Nat)
    (left middle right : Option Row := none) : Row :=
  { tag, left, middle, right, annotation := ⟨depth⟩ }

def closed (A : Ty Base) (hA : Kinded A) (t : Tm Base) (ht : HasType Γ t A) :
    Term Base Γ where
  ty := A
  formed := hA
  row := leaf (.bound Γ.length) Γ.length
  lower := fun _ => t
  typing := fun _ => ht

def hole (name : HoleName) (A : Ty Base) (hA : Kinded A) : Term Base Γ where
  ty := A
  formed := hA
  row := node (.hole name) Γ.length
  lower := fun e => (e Γ name A hA).term
  typing := fun e => (e Γ name A hA).typing

def var (n : Nat) (A : Ty Base) (hA : Kinded A) (hn : Γ[n]? = some A) :
    Term Base Γ where
  ty := A
  formed := hA
  row := leaf (.variable n) Γ.length
  lower := fun _ => .tmVar n
  typing := fun _ => .tmVar hn

def bool (b : Bool) : Term Base Γ where
  ty := .tyBool
  formed := .tyBool
  row := leaf (.boolean b) Γ.length
  lower := fun _ => .tmBool b
  typing := fun _ => .tmBool

def app (f x : Term Base Γ) (A B : Ty Base)
    (hf : f.ty = .tyArr A B) (hx : x.ty = A) : Term Base Γ where
  ty := B
  formed := by
    have h := hf ▸ f.formed
    cases h with
    | tyArr _ hB => exact hB
  row := node .application Γ.length (some f.row) (some x.row)
  lower := fun e => .tmApp (f.lower e) (x.lower e)
  typing := fun e => by
    exact .tmApp (hf ▸ f.typing e) (hx ▸ x.typing e)

def lam (A : Ty Base) (hA : Kinded A) (body : Term Base (A :: Γ)) :
    Term Base Γ where
  ty := .tyArr A body.ty
  formed := .tyArr hA body.formed
  row := node .abstraction Γ.length (some body.row)
    (some (leaf (.bound 0) Γ.length))
  lower := fun e => .tmLam A (body.lower e)
  typing := fun e => .tmLam hA (body.typing e)

def equal (A : Ty Base) (hA : Kinded A) (x y : Term Base Γ)
    (hx : x.ty = A) (hy : y.ty = A) : Term Base Γ where
  ty := .tyBool
  formed := .tyBool
  row := node .equality Γ.length (some x.row) (some y.row)
  lower := fun e => .tmEq A (x.lower e) (y.lower e)
  typing := fun e => by
    exact .tmEq hA (hx ▸ x.typing e) (hy ▸ y.typing e)

def choice (A : Ty Base) (hA : Kinded A) (p : Term Base Γ)
    (hp : p.ty = .tyArr A .tyBool) : Term Base Γ where
  ty := A
  formed := hA
  row := node .choice Γ.length (some p.row)
  lower := fun e => .tmEps A (p.lower e)
  typing := fun e => by
    exact .tmEps hA (hp ▸ p.typing e)

/-- Explicit Covalence cast.  Its applicability is a table lookup plus a
certificate check; it never traverses the subject row. -/
def cast (certificateId : Nat) {A B : Ty Base} (c : TyEqCert A B)
    (t : Term Base Γ) (ht : t.ty = A) : Term Base Γ := by
  cases c with
  | mk h =>
    cases h
    cases ht
    exact { t with row := node (.cast certificateId) Γ.length (some t.row) }

/-- An explicit constant-time bound marker.  The sound core takes the already
typed repaired result; the later untyped elaborator computes it lazily and
uses a locally closed hole whenever inspection would cross its budget. -/
def bound (cutoff : Nat) (t : Term Base Γ) : Term Base Γ :=
  { t with row := node (.bound cutoff) Γ.length (some t.row) }

end Term

end Nucleus.Cov
