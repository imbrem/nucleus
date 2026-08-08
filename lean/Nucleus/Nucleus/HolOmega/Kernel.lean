import Mathlib.Logic.Equiv.Defs
import Nucleus.HolOmega.Syntax
import Nucleus.HolOmega.TotalSubtype

/-!
# The semantic kernel: derivations and their soundness

Where `Syntax.lean` gives raw trees and a syntax-directed typing relation, this
layer is *shallow-intrinsic*: a type is a function from a kind environment to a
code, and a term is a function from environments to an element of that code.
Ill-typed terms are therefore not merely underivable, they are unwritable, so
the equality and proof calculi need no typing side conditions.

`Universe` is a Tarskian universe with exactly the closures the kernel uses.
Predicate codes keep syntax stratified: subtype formation does not mention the
term datatype. `Beth.lean` builds one.

## Why ranks

`∀` may only quantify over the codes below a given rank. Without that
restriction the class has no models at all. Take `allCode` over all of `Code`
with every fibre a two-element code: the product is `2 ^ #Code`, and it has to
be some `El c` — instantiate it at `c` itself and you get a surjection from a
set onto its own double powerset.

So ranks are the price of set semantics for `∀`, not an artefact of this
model. Strengthening the cardinal does not buy them off, and impredicative
polymorphism has no set model at all. They are part of Homeier's HOL-omega too.

In this file that means:

* Kind contexts bind `RKind`s — a kind plus the rank its variables range over.
* `Ty.all` takes the binder's rank `r`, a bound `s` on the body's rank, and a
  proof. The side condition is a `Prop`, so proof irrelevance keeps it out of
  every equation.
* `→` and `Sub` do not move rank, so nothing else in the file mentions one.

## The two calculi

* `EqTm` — reflexivity, symmetry, transitivity, application and abstraction
  congruence at both term and type level, and beta/eta at both levels.
  `EqTm.sound` says every rule denotes actual equality.
* `Derives` — assumption, truth, equality reflexivity and substitution, choice,
  conversion, equality introduction, Boolean antisymmetry, and both directions
  of the subtype isomorphism. `Derives.sound` says every rule preserves truth.

Symmetry and transitivity are primitive here rather than derived. With equality
a node former rather than a term constant, the HOL Light derivations of both
from `MK_COMB` do not apply — a point `crates/nucleus/src/hol/semantics.txt`
records for the same reason.
-/

universe u

namespace Nucleus.HolOmega.Kernel

-- `Universe.inhabited` is a class-valued *field*, so its projection is
-- semireducible by construction. That is intentional: the universe supplies
-- inhabitance per code, and `Tm.epsilon` / `Tm.abs` pick it up with `letI` at
-- the specific code they need rather than by instance search.
set_option warn.classDefReducibility false

/-- The codes of rank at most `r`. -/
def CodeLE {Code : Type u} (rank : Code → Nat) (r : Nat) : Type u :=
  {c : Code // rank c ≤ r}

/-- Kind values over the codes of rank at most `r`. This is what `∀` quantifies
over; `Code` itself is too big. -/
def KindVal {Code : Type u} (rank : Code → Nat) (r : Nat) :
    HolOmega.Kind → Type u
  | .star => CodeLE rank r
  | .arr K L => KindVal rank r K → KindVal rank r L

/-- A Tarskian universe with the closures needed by the shallow-intrinsic HOLω
kernel. Predicate codes keep syntax stratified: subtype formation does not
mention the term datatype. -/
class Universe where
  Code : Type u
  El : Code → Type u
  inhabited : ∀ A, Inhabited (El A)
  rank : Code → Nat
  boolCode : Code
  boolEquiv : El boolCode ≃ Bool
  rank_boolCode : rank boolCode = 0
  arr : Code → Code → Code
  arrEquiv : ∀ A B, El (arr A B) ≃ (El A → El B)
  rank_arr : ∀ A B, rank (arr A B) ≤ max (rank A) (rank B)
  subCode : (A : Code) → (El A → Prop) → Code
  subEquiv : ∀ A P, El (subCode A P) ≃ TotalSubtype (El A) P
  rank_subCode : ∀ A P, rank (subCode A P) ≤ rank A
  allCode : (K : HolOmega.Kind) → (r s : Nat) →
    (F : KindVal rank r K → Code) → (∀ X, rank (F X) ≤ s) → Code
  allEquiv : ∀ K r s F h,
    El (allCode K r s F h) ≃ ((X : KindVal rank r K) → El (F X))
  rank_allCode : ∀ K r s F h, rank (allCode K r s F h) ≤ max r s + 2

attribute [instance] Universe.inhabited

/-- A kind, together with the rank its variables range over. -/
structure RKind where
  kind : HolOmega.Kind
  rank : Nat
  deriving DecidableEq, Repr

variable (U : Universe)

abbrev Kind.Val (RK : RKind) : Type u := KindVal U.rank RK.rank RK.kind

def Kind.Env : List RKind → Type u
  | [] => PUnit
  | RK :: Δ => Kind.Val U RK × Kind.Env Δ

/-- Semantic types of kind `⋆`. Contexts and terms only ever need these, so the
rank stays out of their way. -/
abbrev STy (Δ : List RKind) := Kind.Env U Δ → U.Code

/-- Semantic types at an arbitrary kind: the type-level lambda calculus, and
the argument of a type application. -/
abbrev Ty (Δ : List RKind) (RK : RKind) := Kind.Env U Δ → Kind.Val U RK

namespace Ty

def base (A : U.Code) : STy U Δ := fun _ => A
def boolCode : STy U Δ := fun _ => U.boolCode
def arr (A B : STy U Δ) : STy U Δ := fun ρ => U.arr (A ρ) (B ρ)
def lam (A : Ty U (⟨K, r⟩ :: Δ) ⟨L, r⟩) : Ty U Δ ⟨.arr K L, r⟩ :=
  fun ρ X => A (X, ρ)
def app (F : Ty U Δ ⟨.arr K L, r⟩) (A : Ty U Δ ⟨K, r⟩) : Ty U Δ ⟨L, r⟩ :=
  fun ρ => F ρ (A ρ)

/-- Quantification over the types of kind `K` at rank `r`, with the body's rank
bounded by `s`. The one place a rank is visible. -/
def all {Δ : List RKind} {K : HolOmega.Kind} (r s : Nat)
    (A : STy U (⟨K, r⟩ :: Δ)) (h : ∀ ρ, U.rank (A ρ) ≤ s) : STy U Δ :=
  fun ρ => U.allCode K r s (fun X => A (X, ρ)) (fun X => h (X, ρ))

def inst {RK : RKind} (A : STy U (RK :: Δ)) (X : Ty U Δ RK) : STy U Δ :=
  fun ρ => A (X ρ, ρ)

def Pred (A : STy U Δ) := ∀ ρ, U.El (A ρ) → Prop

def sub (A : STy U Δ) (P : Pred U A) : STy U Δ :=
  fun ρ => U.subCode (A ρ) (P ρ)

abbrev Sub (Δ Δ' : List RKind) := Kind.Env U Δ' → Kind.Env U Δ

def subst (A : STy U Δ) (σ : Sub U Δ Δ') : STy U Δ' := fun ρ => A (σ ρ)

@[simp] theorem subst_apply (A : STy U Δ) (σ : Sub U Δ Δ') (ρ) :
    Ty.subst U A σ ρ = A (σ ρ) := rfl

@[simp] theorem subst_id (A : STy U Δ) : Ty.subst U A id = A := rfl

theorem subst_comp (A : STy U Δ) (σ : Sub U Δ Δ') (τ : Sub U Δ' Δ'') :
    Ty.subst U (Ty.subst U A σ) τ = Ty.subst U A (σ ∘ τ) := rfl

theorem subst_arr (A B : STy U Δ) (σ : Sub U Δ Δ') :
    Ty.subst U (arr U A B) σ = arr U (Ty.subst U A σ) (Ty.subst U B σ) := rfl

@[simp] theorem beta (A : Ty U (⟨K, r⟩ :: Δ) ⟨L, r⟩) (X : Ty U Δ ⟨K, r⟩) :
    app U (lam U A) X = fun ρ => A (X ρ, ρ) := rfl

theorem eta (F : Ty U Δ ⟨.arr K L, r⟩) : lam U (fun ρ => F ρ.2 ρ.1) = F := rfl

end Ty

def Ctx (Δ : List RKind) := List (STy U Δ)

def Ctx.El : (Γ : Ctx U Δ) → (ρ : Kind.Env U Δ) → Type u
  | [], _ => PUnit
  | A :: Γ, ρ => U.El (A ρ) × Ctx.El Γ ρ

def Ctx.weaken (RK : RKind) (Γ : Ctx U Δ) : Ctx U (RK :: Δ) :=
  Γ.map fun A ρ => A ρ.2

def Ctx.subst (Γ : Ctx U Δ) (σ : Ty.Sub U Δ Δ') : Ctx U Δ' :=
  Γ.map fun A => Ty.subst U A σ

def Ctx.substEl (σ : Ty.Sub U Δ Δ') :
    (Γ : Ctx U Δ) → Ctx.El U (Ctx.subst U Γ σ) ρ → Ctx.El U Γ (σ ρ)
  | [], _ => PUnit.unit
  | _ :: Γ, γ => (γ.1, Ctx.substEl σ Γ γ.2)

def Ctx.weakenEl {Δ : List RKind} {ρ : Kind.Env U Δ}
    (RK : RKind) (X : Kind.Val U RK) :
    (Γ : Ctx U Δ) → Ctx.El U Γ ρ → Ctx.El U (Ctx.weaken U RK Γ) (X, ρ)
  | [], _ => PUnit.unit
  | _ :: Γ, γ => (γ.1, Ctx.weakenEl RK X Γ γ.2)

def Ctx.strengthenEl {Δ : List RKind} {ρ : Kind.Env U Δ}
    (RK : RKind) (X : Kind.Val U RK) :
    (Γ : Ctx U Δ) → Ctx.El U (Ctx.weaken U RK Γ) (X, ρ) → Ctx.El U Γ ρ
  | [], _ => PUnit.unit
  | _ :: Γ, γ => (γ.1, Ctx.strengthenEl RK X Γ γ.2)

@[simp] theorem Ctx.strengthen_weaken
    {Δ : List RKind} {ρ : Kind.Env U Δ}
    (RK : RKind) (X : Kind.Val U RK)
    (Γ : Ctx U Δ) (γ : Ctx.El U Γ ρ) :
    Ctx.strengthenEl U RK X Γ (Ctx.weakenEl U RK X Γ γ) = γ := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih =>
    rcases γ with ⟨x, γ⟩
    exact congrArg (fun z => (x, z)) (ih γ)

abbrev Tm (Γ : Ctx U Δ) (A : STy U Δ) :=
  ∀ ρ, Ctx.El U Γ ρ → U.El (A ρ)

namespace Tm

def vz : Tm U (A :: Γ) A := fun _ γ => γ.1

def vs (x : Tm U Γ A) : Tm U (B :: Γ) A := fun ρ γ => x ρ γ.2

def app (f : Tm U Γ (Ty.arr U A B)) (x : Tm U Γ A) : Tm U Γ B :=
  fun ρ γ => U.arrEquiv (A ρ) (B ρ) (f ρ γ) (x ρ γ)

def lam (t : Tm U (A :: Γ) B) : Tm U Γ (Ty.arr U A B) :=
  fun ρ γ => (U.arrEquiv (A ρ) (B ρ)).symm (fun x => t ρ (x, γ))

def tyLam {Δ : List RKind} {Γ : Ctx U Δ}
    (K : HolOmega.Kind) (r s : Nat) {A : STy U (⟨K, r⟩ :: Δ)}
    (h : ∀ ρ, U.rank (A ρ) ≤ s) (t : Tm U (Ctx.weaken U ⟨K, r⟩ Γ) A) :
    Tm U Γ (Ty.all U r s A h) :=
  fun ρ γ => (U.allEquiv K r s (fun X => A (X, ρ)) (fun X => h (X, ρ))).symm
    (fun X => t (X, ρ) (Ctx.weakenEl U ⟨K, r⟩ X Γ γ))

def tyApp {Δ : List RKind} {Γ : Ctx U Δ}
    {K : HolOmega.Kind} {r s : Nat} {A : STy U (⟨K, r⟩ :: Δ)}
    {h : ∀ ρ, U.rank (A ρ) ≤ s}
    (f : Tm U Γ (Ty.all U r s A h)) (X : Ty U Δ ⟨K, r⟩) :
    Tm U Γ (Ty.inst U A X) :=
  fun ρ γ =>
    U.allEquiv K r s (fun Y => A (Y, ρ)) (fun Y => h (Y, ρ)) (f ρ γ) (X ρ)

def instantiateBody {Δ : List RKind} {Γ : Ctx U Δ}
    {K : HolOmega.Kind} {r : Nat} {A : STy U (⟨K, r⟩ :: Δ)}
    (t : Tm U (Ctx.weaken U ⟨K, r⟩ Γ) A) (X : Ty U Δ ⟨K, r⟩) :
    Tm U Γ (Ty.inst U A X) :=
  fun ρ γ => t (X ρ, ρ) (Ctx.weakenEl U ⟨K, r⟩ (X ρ) Γ γ)

def weakenTy {Δ : List RKind} {Γ : Ctx U Δ}
    (K : HolOmega.Kind) (r s : Nat) {A : STy U (⟨K, r⟩ :: Δ)}
    {h : ∀ ρ, U.rank (A ρ) ≤ s}
    (f : Tm U Γ (Ty.all U r s A h)) : Tm U (Ctx.weaken U ⟨K, r⟩ Γ) A :=
  fun ρ γ =>
    U.allEquiv K r s (fun X => A (X, ρ.2)) (fun X => h (X, ρ.2))
      (f ρ.2 (Ctx.strengthenEl U ⟨K, r⟩ ρ.1 Γ γ)) ρ.1

def boolCode (b : Bool) : Tm U Γ (Ty.boolCode U) := fun _ _ => U.boolEquiv.symm b

noncomputable def epsilon (p : Tm U Γ (Ty.arr U A (Ty.boolCode U))) :
    Tm U Γ A :=
  fun ρ γ => by
    classical
    letI := U.inhabited (A ρ)
    let q := fun x => U.boolEquiv (U.arrEquiv (A ρ) U.boolCode (p ρ γ) x)
    exact if h : ∃ x, q x = true then Classical.choose h else default

noncomputable def equal (x y : Tm U Γ A) : Tm U Γ (Ty.boolCode U) := by
  classical
  exact fun ρ γ => U.boolEquiv.symm (decide (x ρ γ = y ρ γ))

noncomputable def abs (P : Ty.Pred U A) (x : Tm U Γ A) :
    Tm U Γ (Ty.sub U A P) :=
  fun ρ γ => by
    letI := U.inhabited (A ρ)
    exact (U.subEquiv (A ρ) (P ρ)).symm (TotalSubtype.abs (P ρ) (x ρ γ))

def rep (P : Ty.Pred U A) (x : Tm U Γ (Ty.sub U A P)) : Tm U Γ A :=
  fun ρ γ => TotalSubtype.rep (U.subEquiv (A ρ) (P ρ) (x ρ γ))

theorem abs_rep (P : Ty.Pred U A) (x : Tm U Γ (Ty.sub U A P)) :
    abs U P (rep U P x) = x := by
  funext ρ γ
  letI := U.inhabited (A ρ)
  change (U.subEquiv (A ρ) (P ρ)).symm
    (TotalSubtype.abs (P ρ)
      (TotalSubtype.rep (U.subEquiv (A ρ) (P ρ) (x ρ γ)))) = x ρ γ
  apply (U.subEquiv (A ρ) (P ρ)).injective
  rw [Equiv.apply_symm_apply]
  exact @TotalSubtype.abs_rep (U.El (A ρ))
    (U.inhabited (A ρ)) (P ρ) (U.subEquiv (A ρ) (P ρ) (x ρ γ))

theorem rep_abs (P : Ty.Pred U A) (x : Tm U Γ A)
    (hx : ∀ ρ γ, P ρ (x ρ γ)) : rep U P (abs U P x) = x := by
  funext ρ γ
  letI := U.inhabited (A ρ)
  simp only [rep, abs, Equiv.apply_symm_apply]
  exact TotalSubtype.rep_abs_of (hx ρ γ)

abbrev Sub (Γ Γ' : Ctx U Δ) := ∀ ρ, Ctx.El U Γ' ρ → Ctx.El U Γ ρ

def subst (t : Tm U Γ A) (σ : Sub U Γ Γ') : Tm U Γ' A := fun ρ γ => t ρ (σ ρ γ)

def substTy {Δ Δ' : List RKind} {Γ : Ctx U Δ}
    {A : STy U Δ} (t : Tm U Γ A) (σ : Ty.Sub U Δ Δ') :
    Tm U (Ctx.subst U Γ σ) (Ty.subst U A σ) :=
  fun ρ γ => t (σ ρ) (Ctx.substEl U σ Γ γ)

@[simp] theorem substTy_apply {Δ Δ' : List RKind} {Γ : Ctx U Δ}
    {A : STy U Δ} (t : Tm U Γ A) (σ : Ty.Sub U Δ Δ') ρ γ :
    Tm.substTy U t σ ρ γ = t (σ ρ) (Ctx.substEl U σ Γ γ) := rfl

theorem substTy_app {Δ Δ' : List RKind} {Γ : Ctx U Δ}
    {A B : STy U Δ} (f : Tm U Γ (Ty.arr U A B)) (x : Tm U Γ A)
    (σ : Ty.Sub U Δ Δ') :
    Tm.substTy U (Tm.app U f x) σ =
      Tm.app U (Tm.substTy U f σ) (Tm.substTy U x σ) := rfl

theorem substTy_bool {Δ Δ' : List RKind} {Γ : Ctx U Δ}
    (b : Bool) (σ : Ty.Sub U Δ Δ') :
    Tm.substTy U (Tm.boolCode U (Γ := Γ) b) σ =
      Tm.boolCode U (Γ := Ctx.subst U Γ σ) b := rfl

@[simp] theorem subst_id (t : Tm U Γ A) : Tm.subst U t (fun _ γ => γ) = t := rfl

theorem subst_comp (t : Tm U Γ A) (σ : Sub U Γ Γ') (τ : Sub U Γ' Γ'') :
    Tm.subst U (Tm.subst U t σ) τ = Tm.subst U t (fun ρ γ => σ ρ (τ ρ γ)) := rfl

@[simp] theorem beta (t : Tm U (A :: Γ) B) (x : Tm U Γ A) :
    app U (lam U t) x = fun ρ γ => t ρ (x ρ γ, γ) := by
  funext ρ γ
  change U.arrEquiv (A ρ) (B ρ)
    ((U.arrEquiv (A ρ) (B ρ)).symm (fun y => t ρ (y, γ))) (x ρ γ) = _
  rw [Equiv.apply_symm_apply]

theorem eta (f : Tm U Γ (Ty.arr U A B)) :
    lam U (app U (vs U f) (vz U)) = f := by
  funext ρ γ
  change (U.arrEquiv (A ρ) (B ρ)).symm
    (fun x => U.arrEquiv (A ρ) (B ρ) (f ρ γ) x) = f ρ γ
  rw [show (fun x => U.arrEquiv (A ρ) (B ρ) (f ρ γ) x) =
      U.arrEquiv (A ρ) (B ρ) (f ρ γ) from rfl]
  exact (U.arrEquiv (A ρ) (B ρ)).symm_apply_apply _

@[simp] theorem tyBeta {Δ : List RKind} {K : HolOmega.Kind} {r s : Nat}
    {Γ : Ctx U Δ} {A : STy U (⟨K, r⟩ :: Δ)} {h : ∀ ρ, U.rank (A ρ) ≤ s}
    (t : Tm U (Ctx.weaken U ⟨K, r⟩ Γ) A) (X : Ty U Δ ⟨K, r⟩) :
    tyApp U (h := h) (tyLam U K r s h t) X = instantiateBody U t X := by
  funext ρ γ
  change U.allEquiv K r s (fun Y => A (Y, ρ)) (fun Y => h (Y, ρ))
    ((U.allEquiv K r s (fun Y => A (Y, ρ)) (fun Y => h (Y, ρ))).symm
      (fun Y => t (Y, ρ) (Ctx.weakenEl U ⟨K, r⟩ Y Γ γ))) (X ρ) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem tyEta {Δ : List RKind} {K : HolOmega.Kind} {r s : Nat}
    {Γ : Ctx U Δ} {A : STy U (⟨K, r⟩ :: Δ)} {h : ∀ ρ, U.rank (A ρ) ≤ s}
    (f : Tm U Γ (Ty.all U r s A h)) :
    tyLam U K r s h (weakenTy U K r s f) = f := by
  funext ρ γ
  apply (U.allEquiv K r s (fun X => A (X, ρ)) (fun X => h (X, ρ))).injective
  funext X
  simp [tyLam, weakenTy]

end Tm

/-- The equality calculus is intentionally small: congruence is inherited from
Lean equality, while these constructors expose the HOLω proof rules. -/
inductive EqTm : {Δ : List RKind} →
    (Γ : Ctx U Δ) → {A : STy U Δ} → Tm U Γ A → Tm U Γ A → Prop
  | refl {Δ} {Γ : Ctx U Δ} {A : STy U Δ} (t : Tm U Γ A) : EqTm Γ t t
  | symm : EqTm Γ t u → EqTm Γ u t
  | trans : EqTm Γ t u → EqTm Γ u v → EqTm Γ t v
  | app : EqTm Γ f g → EqTm Γ x y → EqTm Γ (Tm.app U f x) (Tm.app U g y)
  | lam : EqTm (A :: Γ) t u → EqTm Γ (Tm.lam U t) (Tm.lam U u)
  | tyApp {Δ K r s} {Γ : Ctx U Δ} {A : STy U (⟨K, r⟩ :: Δ)}
      {h : ∀ ρ, U.rank (A ρ) ≤ s} {f g : Tm U Γ (Ty.all U r s A h)}
      {X : Ty U Δ ⟨K, r⟩} :
      EqTm Γ f g → EqTm Γ (Tm.tyApp U f X) (Tm.tyApp U g X)
  | tyLam {Δ K r s} {Γ : Ctx U Δ} {A : STy U (⟨K, r⟩ :: Δ)}
      {h : ∀ ρ, U.rank (A ρ) ≤ s} {t u : Tm U (Ctx.weaken U ⟨K, r⟩ Γ) A} :
      EqTm (Ctx.weaken U ⟨K, r⟩ Γ) t u →
      EqTm Γ (Tm.tyLam U K r s h t) (Tm.tyLam U K r s h u)
  | beta (t : Tm U (A :: Γ) B) (x : Tm U Γ A) :
      EqTm Γ (Tm.app U (Tm.lam U t) x) (fun ρ γ => t ρ (x ρ γ, γ))
  | eta (f : Tm U Γ (Ty.arr U A B)) :
      EqTm Γ (Tm.lam U (Tm.app U (Tm.vs U f) (Tm.vz U))) f
  | tyBeta {Δ K r s} {Γ : Ctx U Δ} {A : STy U (⟨K, r⟩ :: Δ)}
      {h : ∀ ρ, U.rank (A ρ) ≤ s} (t : Tm U (Ctx.weaken U ⟨K, r⟩ Γ) A)
      (X : Ty U Δ ⟨K, r⟩) :
      EqTm Γ (Tm.tyApp U (h := h) (Tm.tyLam U K r s h t) X)
        (Tm.instantiateBody U t X)
  | tyEta {Δ K r s} {Γ : Ctx U Δ} {A : STy U (⟨K, r⟩ :: Δ)}
      {h : ∀ ρ, U.rank (A ρ) ≤ s} (f : Tm U Γ (Ty.all U r s A h)) :
      EqTm Γ (Tm.tyLam U K r s h (Tm.weakenTy U K r s f)) f

theorem EqTm.sound {Δ} {Γ : Ctx U Δ} {A : STy U Δ} {t u : Tm U Γ A}
    (h : EqTm U Γ t u) : t = u := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | app _ _ ih₁ ih₂ => simp [ih₁, ih₂]
  | lam _ ih => simp [ih]
  | tyApp _ ih => simp [ih]
  | tyLam _ ih => simp [ih]
  | beta => exact Tm.beta U _ _
  | eta => exact Tm.eta U _
  | tyBeta => exact Tm.tyBeta U _ _
  | tyEta => exact Tm.tyEta U _

def Holds {Δ} {Γ : Ctx U Δ} (p : Tm U Γ (Ty.boolCode U)) : Prop :=
  ∀ ρ γ, U.boolEquiv (p ρ γ) = true

def Entails {Δ} {Γ : Ctx U Δ} (H : List (Tm U Γ (Ty.boolCode U)))
    (p : Tm U Γ (Ty.boolCode U)) : Prop :=
  ∀ ρ γ, (∀ q ∈ H, U.boolEquiv (q ρ γ) = true) → U.boolEquiv (p ρ γ) = true

theorem Tm.equal_true_iff {Δ} {Γ : Ctx U Δ} {A : STy U Δ}
    (x y : Tm U Γ A) (ρ γ) :
    U.boolEquiv (Tm.equal U x y ρ γ) = true ↔ x ρ γ = y ρ γ := by
  classical
  simp [Tm.equal]

theorem Tm.epsilon_spec {Δ} {Γ : Ctx U Δ} {A : STy U Δ}
    (p : Tm U Γ (Ty.arr U A (Ty.boolCode U))) (x : Tm U Γ A) (ρ γ)
    (hx : U.boolEquiv (U.arrEquiv (A ρ) U.boolCode (p ρ γ) (x ρ γ)) = true) :
    U.boolEquiv (U.arrEquiv (A ρ) U.boolCode (p ρ γ)
      (Tm.epsilon U p ρ γ)) = true := by
  classical
  letI := U.inhabited (A ρ)
  simp only [Tm.epsilon]
  split
  · rename_i h
    exact Classical.choose_spec h
  · rename_i h
    exact False.elim (h ⟨x ρ γ, hx⟩)

/-- Natural-deduction fragment for the primitive truth, equality and choice
rules. Each constructor below has a corresponding case in `Derives.sound`. -/
inductive Derives {Δ} {Γ : Ctx U Δ} :
    List (Tm U Γ (Ty.boolCode U)) → Tm U Γ (Ty.boolCode U) → Prop
  | hyp : p ∈ H → Derives H p
  | truth : Derives H (Tm.boolCode U true)
  | eqRefl (x : Tm U Γ A) : Derives H (Tm.equal U x x)
  | eqMp (p : Tm U Γ (Ty.arr U A (Ty.boolCode U))) (x y : Tm U Γ A) :
      Derives H (Tm.equal U x y) → Derives H (Tm.app U p x) →
      Derives H (Tm.app U p y)
  | choice (p : Tm U Γ (Ty.arr U A (Ty.boolCode U))) (x : Tm U Γ A) :
      Derives H (Tm.app U p x) → Derives H (Tm.app U p (Tm.epsilon U p))
  | convert : EqTm U Γ p q → Derives H p → Derives H q
  | eqOfEqTm (x y : Tm U Γ A) : EqTm U Γ x y → Derives H (Tm.equal U x y)
  | antisymm (p q : Tm U Γ (Ty.boolCode U)) :
      Derives (p :: H) q → Derives (q :: H) p → Derives H (Tm.equal U p q)
  | absRep (P : Ty.Pred U A) (x : Tm U Γ (Ty.sub U A P)) :
      Derives H (Tm.equal U (Tm.abs U P (Tm.rep U P x)) x)
  | repAbs (P : Ty.Pred U A) (x : Tm U Γ A) :
      (∀ ρ γ, P ρ (x ρ γ)) →
      Derives H (Tm.equal U (Tm.rep U P (Tm.abs U P x)) x)

theorem Derives.sound {Δ} {Γ : Ctx U Δ} {H : List (Tm U Γ (Ty.boolCode U))}
    {p : Tm U Γ (Ty.boolCode U)} (h : Derives U H p) : Entails U H p := by
  intro ρ γ hH
  induction h with
  | hyp hp => exact hH _ hp
  | truth => simp [Tm.boolCode]
  | eqRefl x => exact (Tm.equal_true_iff U x x ρ γ).2 rfl
  | eqMp p x y hxy hpx ihxy ihpx =>
    have heq := (Tm.equal_true_iff U x y ρ γ).1 (ihxy hH)
    simpa [Tm.app, heq] using ihpx hH
  | choice p x hp ih =>
    exact Tm.epsilon_spec U p x ρ γ (ih hH)
  | convert heq hp ih =>
    have he := congrFun (congrFun (heq.sound U) ρ) γ
    rw [← he]
    exact ih hH
  | eqOfEqTm x y heq =>
    exact (Tm.equal_true_iff U x y ρ γ).2
      (congrFun (congrFun (heq.sound U) ρ) γ)
  | antisymm p q hp hq ihp ihq =>
    apply (Tm.equal_true_iff U p q ρ γ).2
    apply U.boolEquiv.injective
    cases hpv : U.boolEquiv (p ρ γ) <;> cases hqv : U.boolEquiv (q ρ γ) <;>
      try rfl
    · have bad := ihq (by
        intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hqv
        · exact hH _ hr)
      rw [hpv] at bad
      contradiction
    · have bad := ihp (by
        intro r hr
        simp only [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hpv
        · exact hH _ hr)
      rw [hqv] at bad
      contradiction
  | absRep P x =>
    exact (Tm.equal_true_iff U _ _ ρ γ).2
      (congrFun (congrFun (Tm.abs_rep U P x) ρ) γ)
  | repAbs P x hx =>
    exact (Tm.equal_true_iff U _ _ ρ γ).2
      (congrFun (congrFun (Tm.rep_abs U P x hx) ρ) γ)

end Nucleus.HolOmega.Kernel
