import Nucleus.HolE.ClassicalConsistency

/-! # Checked syntax for the empty HolE signature

This is the high-level, serialization-facing syntax API for the finite core
`HolE Empty`.  Every constructor mirrors one raw syntax constructor and returns
its checking certificate at the same time.  Consumers therefore never have to
assemble `Checks` derivations by hand.
-/

namespace Nucleus.HolE.Empty

open Nucleus.HolE

set_option relaxedAutoImplicit true

abbrev Sig : Signature := ClassicalSig

/-- A checked type family at a fixed kind. -/
structure FamK (types : List Kind) (kind : Kind) where
  raw : Fam Sig types kind
  kinded : Kinded raw

/-- A checked ordinary HOL type. -/
abbrev Ty (types : List Kind) := FamK types .star

namespace FamK

abbrev boolTy : Ty types := ⟨.boolTy, .boolTy⟩

abbrev arr (domain codomain : Ty types) : Ty types :=
  ⟨.arr domain.raw codomain.raw, .arr domain.kinded codomain.kinded⟩

def app (function : FamK types (.arr domain codomain))
    (argument : FamK types domain) : FamK types codomain :=
  ⟨.tyApp function.raw argument.raw, .tyApp function.kinded argument.kinded⟩

def lam (body : FamK (domain :: types) codomain) :
    FamK types (.arr domain codomain) :=
  ⟨.tyLam body.raw, .tyLam body.kinded⟩

def bv (v : TyVar types kind) : FamK types kind :=
  ⟨.tyBv v, .tyBv v⟩

end FamK

/-- A raw bound context whose entries have separately checked kinds. -/
structure Ctx (types : List Kind) (depth : Nat) where
  raw : BoundCtx Sig types depth
  typed : TypedCtx raw

namespace Ctx

def empty : Ctx types 0 := ⟨emptyBound, fun i => Fin.elim0 i⟩

def extend (A : Ty types) (Γ : Ctx types depth) : Ctx types (depth + 1) :=
  ⟨extendBound A.raw Γ.raw, fun i => Fin.cases A.kinded Γ.typed i⟩

end Ctx

/-- An intrinsically checked term over the empty signature. -/
structure Term {types : List Kind} {depth : Nat}
    (Γ : Ctx types depth) (A : Ty types) where
  raw : Tm Sig types depth
  typing : HasType Γ.raw raw A.raw

namespace Term

def bv (Γ : Ctx types depth) (index : Fin depth) :
    Term Γ ⟨Γ.raw index, Γ.typed index⟩ :=
  ⟨.bv index, .bv (Γ.typed index) rfl⟩

def bvAs (Γ : Ctx types depth) (index : Fin depth) (A : Ty types)
    (lookup : Γ.raw index = A.raw) : Term Γ A :=
  ⟨.bv index, .bv A.kinded lookup⟩

def fv (Γ : Ctx types depth) (name : Nat) (A : Ty types) : Term Γ A :=
  ⟨.fv name A.raw, .fv name A.kinded⟩

def app (function : Term Γ (domain.arr codomain))
    (argument : Term Γ domain) : Term Γ codomain :=
  ⟨.app function.raw argument.raw, .app function.typing argument.typing⟩

def lam (domain : Ty types) (body : Term (Γ.extend domain) codomain) :
    Term Γ (domain.arr codomain) :=
  ⟨.lam domain.raw body.raw, .lam body.raw domain.kinded body.typing⟩

def bool (Γ : Ctx types depth) (value : Bool) : Term Γ FamK.boolTy :=
  ⟨.bool value, .bool value⟩

def eq (A : Ty types) (left right : Term Γ A) : Term Γ FamK.boolTy :=
  ⟨.eq A.raw left.raw right.raw, .eq A.kinded left.typing right.typing⟩

def eps (A : Ty types) (predicate : Term Γ (A.arr FamK.boolTy)) : Term Γ A :=
  ⟨.eps A.raw predicate.raw, .eps A.kinded predicate.typing⟩

/-- The always-inhabited guarded subtype determined by a closed predicate. -/
def sub (A : Ty types) (predicate : Term (Ctx.empty.extend A) FamK.boolTy) :
    Ty types :=
  ⟨.sub A.raw predicate.raw, .sub A.kinded predicate.typing⟩

def abs (A : Ty types) (predicate : Term (Ctx.empty.extend A) FamK.boolTy)
    (value : Term Γ A) : Term Γ (sub A predicate) :=
  ⟨.abs A.raw predicate.raw value.raw,
    .abs A.kinded predicate.typing value.typing⟩

def rep (A : Ty types) (predicate : Term (Ctx.empty.extend A) FamK.boolTy)
    (value : Term Γ (sub A predicate)) : Term Γ A :=
  ⟨.rep A.raw predicate.raw value.raw,
    .rep A.kinded predicate.typing value.typing⟩

/-- Proposition asserting that some ordinary type satisfies `predicate`. -/
def tyExists (Γ : Ctx types depth)
    (predicate : Term (types := .star :: types) Ctx.empty FamK.boolTy) :
    Term Γ FamK.boolTy :=
  ⟨.tyExists predicate.raw, .tyExists predicate.typing⟩

/-- Guarded choice of a type satisfying `predicate`, with the same total
fallback convention as guarded subtypes. -/
def model (predicate : Term (types := .star :: types) Ctx.empty FamK.boolTy) :
    Ty types :=
  ⟨.model predicate.raw, .model predicate.typing⟩

def truth (Γ : Ctx types depth) : Term Γ FamK.boolTy := bool Γ true

def falsehood (Γ : Ctx types depth) : Term Γ FamK.boolTy := bool Γ false

def weaken {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    {A : Ty types} (term : Term Γ A) (B : Ty types) : Term (Γ.extend B) A :=
  ⟨HolE.weaken term.raw, term.typing.weaken⟩

def openBound (body : Term (Γ.extend A) B) (argument : Term Γ A) : Term Γ B :=
  ⟨HolE.openBound body.raw argument.raw,
    body.typing.openBound Γ.typed argument.typing⟩

def openType (predicate : Term (types := kind :: types) Ctx.empty FamK.boolTy)
    (argument : FamK types kind) :
    Term (types := types) Ctx.empty FamK.boolTy := by
  refine ⟨HolE.openType predicate.raw argument.raw, ?_⟩
  have instantiated := predicate.typing.instantiateTypes
    (wellFormed_headTySub argument.kinded)
  simpa [Ctx.empty, HolE.openType, FamK.boolTy] using instantiated

end Term

/-- Checked propositions are exactly checked Boolean terms. -/
abbrev BoolTm (Γ : Ctx types depth) := Term Γ FamK.boolTy

/-- A checked proposition context. -/
abbrev PropCtx (Γ : Ctx types depth) := List (BoolTm Γ)

namespace PropCtx

def raw {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (H : PropCtx Γ) : List (Tm Sig types depth) := H.map (fun p => p.raw)

theorem typed {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (H : PropCtx Γ) : TypedHyps Γ.raw H.raw := by
  intro proposition member
  obtain ⟨checked, _, rfl⟩ := List.mem_map.mp member
  exact .exact checked.typing

def weaken {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    (H : PropCtx Γ) (A : Ty types) : PropCtx (Γ.extend A) :=
  H.map (fun p => p.weaken A)

@[simp] theorem raw_cons (p : BoolTm Γ) (H : PropCtx Γ) :
    raw (p :: H) = p.raw :: H.raw := rfl

@[simp] theorem raw_weaken {types : List Kind} {depth : Nat}
    {Γ : Ctx types depth} (H : PropCtx Γ) (A : Ty types) :
    (H.weaken A).raw = H.raw.map HolE.weaken := by
  induction H with
  | nil => rfl
  | cons p H ih => simp [weaken, raw, Term.weaken]

end PropCtx

end Nucleus.HolE.Empty
