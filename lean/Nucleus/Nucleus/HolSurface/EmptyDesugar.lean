import Nucleus.HolSurface
import Nucleus.HolE.EmptyNatural

/-! # Canonical HolSurface macro lowering to `HolE Empty`

The primitive HolSurface constructors mirror raw HolE syntax.  The additional
surface tags below are macros, and this file is their normative checked
expansion.  It is intentionally small enough to translate directly into the
Rust checker.
-/

namespace Nucleus.HolSurface.EmptyDesugar

open Nucleus.HolE
open Nucleus.HolE.Empty

set_option relaxedAutoImplicit true

/-- A closed checked type produced by a type-valued surface macro. -/
abbrev ClosedType := Empty.Ty []

/-- A closed checked term of some checked type. -/
abbrev ClosedTerm := Σ A : Empty.Ty [], Empty.Term Empty.Ctx.empty A

/-- Three-way lazy resolution. `opaque` preserves an unavailable link;
`invalid` records that available content failed validation. -/
inductive LinkResolution (Value Error : Type) where
  | resolved (value : Value)
  | opaque
  | invalid (error : Error)

/-- A successful link resolution cannot produce open or unchecked syntax: the
codomain contains both the empty scopes and the checking certificate. -/
structure LinkResolver (Link Error : Type) where
  resolveType : (target : Link) → (kind : Nucleus.HolE.Kind) →
    LinkResolution (Empty.FamK [] kind) Error
  resolveTerm : (target : Link) → (A : Empty.Ty []) →
    LinkResolution (Empty.Term (Empty.Ctx.empty : Empty.Ctx [] 0) A) Error

/-- Lowering preserves unavailable links. Invalid content receives a checked,
fully closed fallback while retaining its diagnostic. -/
inductive LazyLowering (Value Link Error : Type) where
  | resolved (value : Value)
  | opaque (target : Link)
  | invalid (fallback : Value) (error : Error)

/-- A canonical fully closed, well-kinded fallback for an invalid type link.
At kind `*` it is `Model false`; at higher kind it is pointwise lifted through
type lambdas. -/
def invalidFamily : {types : List Nucleus.HolE.Kind} →
    (kind : Nucleus.HolE.Kind) → Empty.FamK types kind
  | _, .star =>
      Empty.Term.model
        (Empty.Term.falsehood (types := .star :: _) Empty.Ctx.empty)
  | _, .arr domain codomain =>
      Empty.FamK.lam (invalidFamily (types := domain :: _) codomain)

/-- A canonical fully closed, well-typed fallback for an invalid term link. -/
def invalidTerm (A : Empty.Ty []) :
    Empty.Term (Empty.Ctx.empty : Empty.Ctx [] 0) A :=
  let predicate := Empty.Term.lam A
    (Empty.Term.falsehood ((Empty.Ctx.empty : Empty.Ctx [] 0).extend A))
  Empty.Term.eps A predicate

/-- Lower a type link without collapsing temporary CAS absence into failure. -/
def lowerTypeLink (resolver : LinkResolver Link Error) (target : Link)
    (kind : Nucleus.HolE.Kind) :
    LazyLowering (Empty.FamK [] kind) Link Error :=
  match resolver.resolveType target kind with
  | .resolved value => .resolved value
  | .opaque => .opaque target
  | .invalid error => .invalid (invalidFamily kind) error

/-- Lower a term link without collapsing temporary CAS absence into failure. -/
def lowerTermLink (resolver : LinkResolver Link Error) (target : Link)
    (A : Empty.Ty []) :
    LazyLowering (Empty.Term (Empty.Ctx.empty : Empty.Ctx [] 0) A) Link Error :=
  match resolver.resolveTerm target A with
  | .resolved value => .resolved value
  | .opaque => .opaque target
  | .invalid error => .invalid (invalidTerm A) error

/-- `TM_NAT` lowers to the selected model of the infinity theory. -/
def nat : ClosedType := Natural.nat

/-- `TM_INF` lowers to the closed type-existential infinity sentence. -/
def inf : Empty.BoolTm (Empty.Ctx.empty : Empty.Ctx [] 0) := Natural.inf

/-- `TM_ZERO` lowers to the epsilon-selected missed point. -/
def zero : Empty.Term (Empty.Ctx.empty : Empty.Ctx [] 0) nat := Natural.zero

/-- `TM_SUCC` lowers to the epsilon-selected successor endomap. -/
def succ : Empty.Term (Empty.Ctx.empty : Empty.Ctx [] 0) (nat.arr nat) :=
  Natural.succ

/-- `TM_LIT_NAT n` lowers to `succ` iterated `n` times over `zero`. -/
def litNat (value : UInt64) :
    Empty.Term (Empty.Ctx.empty : Empty.Ctx [] 0) nat :=
  Natural.numeral value.toNat

/-- `TM_AND` is the native surface operation used to stack contexts. -/
def and (left right : Empty.BoolTm Γ) : Empty.BoolTm Γ :=
  Empty.Term.and left right

/-- `TM_IMP` turns the context proposition into a theorem antecedent. -/
def imp (premises conclusion : Empty.BoolTm Γ) : Empty.BoolTm Γ :=
  Empty.Term.imp premises conclusion

/-- The canonical context operation requested by the Rust theorem API:
`And(TM_INF, rest)`. -/
def withInfinity (rest : Empty.BoolTm (Empty.Ctx.empty : Empty.Ctx [] 0)) :
    Empty.BoolTm (Empty.Ctx.empty : Empty.Ctx [] 0) :=
  and inf rest

/-- Closed nullary macro tags have a total, typed lookup table. -/
def closedMacro : Tag → Option ClosedTerm
  | .tmInf => some ⟨FamK.boolTy, inf⟩
  | .tmZero => some ⟨nat, zero⟩
  | .tmSucc => some ⟨nat.arr nat, succ⟩
  | _ => none

/-- The only closed type-valued macro is `TM_NAT`. -/
def closedTypeMacro : Tag → Option ClosedType
  | .tmNat => some nat
  | _ => none

@[simp] theorem closedMacro_inf :
    closedMacro .tmInf = some ⟨FamK.boolTy, inf⟩ := rfl

@[simp] theorem closedMacro_zero : closedMacro .tmZero = some ⟨nat, zero⟩ := rfl

@[simp] theorem closedMacro_succ :
    closedMacro .tmSucc = some ⟨nat.arr nat, succ⟩ := rfl

@[simp] theorem closedTypeMacro_nat : closedTypeMacro .tmNat = some nat := rfl

theorem inf_is_consistency_axiom :
    inf.raw = Infinity.infinityAxiom (Sig := ClassicalSig) :=
  Natural.inf_raw_eq

end Nucleus.HolSurface.EmptyDesugar
