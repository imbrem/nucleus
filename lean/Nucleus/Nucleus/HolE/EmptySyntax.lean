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

/-- The same term context seen past a fresh type variable.  Term depth is
unchanged, which is what lets a type quantifier stand under term binders. -/
def weakenTypes (Γ : Ctx types depth) : Ctx (kind :: types) depth :=
  ⟨weakenBoundCtx Γ.raw, fun i => (Γ.typed i).weakenTypes⟩

/-- At the closed context, weakening past a type variable changes nothing.
The type quantifiers are open but the *rules* still fire at depth zero, so this
is the bridge every closed statement needs. -/
@[simp] theorem weakenTypes_empty {types : List Kind} {kind : Kind} :
    (Ctx.empty : Ctx types 0).weakenTypes (kind := kind) = Ctx.empty := by
  unfold weakenTypes empty
  congr 1
  exact weakenBoundCtx_empty

end Ctx

/-- An intrinsically checked term over the empty signature. -/
structure Term {types : List Kind} {depth : Nat}
    (Γ : Ctx types depth) (A : Ty types) where
  raw : Tm Sig types depth
  typing : HasType Γ.raw raw A.raw

namespace Term

/-- Checked terms are determined by their raw syntax; typing certificates are
proof-irrelevant. -/
theorem ext_raw {left right : Term Γ A} (equality : left.raw = right.raw) :
    left = right := by
  cases left
  cases right
  cases equality
  rfl

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

/-- Proposition asserting that some ordinary type satisfies `predicate`.  The
predicate may mention the ambient term binders, so it is checked in `Γ` seen
past the new type variable rather than in the empty context. -/
def tyExists (Γ : Ctx types depth)
    (predicate : Term (types := .star :: types) Γ.weakenTypes FamK.boolTy) :
    Term Γ FamK.boolTy :=
  ⟨.tyExists predicate.raw, .tyExists predicate.typing⟩

/-- Proposition asserting that *every* ordinary type satisfies `predicate`. -/
def tyForall (Γ : Ctx types depth)
    (predicate : Term (types := .star :: types) Γ.weakenTypes FamK.boolTy) :
    Term Γ FamK.boolTy :=
  ⟨.tyForall predicate.raw, .tyForall predicate.typing⟩

/-- Reading a closed predicate back at the literal empty context.  Only the
term quantifiers were opened; `ty.model` is still a closed type binder, so a
statement that mixes the two needs this bridge.  The raw syntax is unchanged. -/
def closeEmpty {types : List Kind} {kind : Kind} {A : Ty (kind :: types)}
    (term : Term (types := kind :: types)
      (Ctx.empty : Ctx types 0).weakenTypes A) :
    Term (types := kind :: types) Ctx.empty A :=
  Ctx.weakenTypes_empty ▸ term

/-- Transporting a checked term along an equality of contexts leaves its raw
syntax alone. -/
@[simp] theorem transport_raw {types : List Kind} {depth : Nat}
    {Γ Δ : Ctx types depth} {A : Ty types} (contexts : Γ = Δ) (term : Term Γ A) :
    (contexts ▸ term).raw = term.raw := by
  cases contexts
  rfl

@[simp] theorem closeEmpty_raw {types : List Kind} {kind : Kind}
    {A : Ty (kind :: types)}
    (term : Term (types := kind :: types)
      (Ctx.empty : Ctx types 0).weakenTypes A) :
    (closeEmpty term).raw = term.raw :=
  transport_raw Ctx.weakenTypes_empty term

/-- Guarded choice of a type satisfying `predicate`, with the same total
fallback convention as guarded subtypes.  `ty.model` remains a *closed* type
binder: its meaning is a choice function on the predicate alone. -/
def model (predicate : Term (types := .star :: types)
    (Ctx.empty : Ctx types 0).weakenTypes FamK.boolTy) : Ty types :=
  ⟨.model predicate.raw, .model (weakenBoundCtx_empty ▸ predicate.typing)⟩

def truth (Γ : Ctx types depth) : Term Γ FamK.boolTy := bool Γ true

def falsehood (Γ : Ctx types depth) : Term Γ FamK.boolTy := bool Γ false

def weaken {types : List Kind} {depth : Nat} {Γ : Ctx types depth}
    {A : Ty types} (term : Term Γ A) (B : Ty types) : Term (Γ.extend B) A :=
  ⟨HolE.weaken term.raw, term.typing.weaken⟩

def openBound (body : Term (Γ.extend A) B) (argument : Term Γ A) : Term Γ B :=
  ⟨HolE.openBound body.raw argument.raw,
    body.typing.openBound Γ.typed argument.typing⟩

/-- Instantiate a unary body into an arbitrary checked context. -/
def instantiateOne (body : Term (Ctx.empty.extend A) B)
    (argument : Term Γ A) : Term Γ B :=
  ⟨HolE.instantiateOne body.raw argument.raw,
    body.typing.instantiateOne argument.typing⟩

/-- Open a type quantifier's body at a concrete argument.  The body lives in
the ambient context seen past the bound type variable, and substituting the
variable away restores the ambient context exactly. -/
def openType {Γ : Ctx types depth}
    (predicate : Term (types := kind :: types) Γ.weakenTypes FamK.boolTy)
    (argument : FamK types kind) : Term (types := types) Γ FamK.boolTy := by
  refine ⟨HolE.openType predicate.raw argument.raw, ?_⟩
  have instantiated := predicate.typing.instantiateTypes
    (wellFormed_headTySub argument.kinded)
  simpa [Ctx.weakenTypes, HolE.openType, FamK.boolTy] using instantiated

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
