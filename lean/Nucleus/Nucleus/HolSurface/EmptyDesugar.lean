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

/-- A link resolver cannot produce open or unchecked syntax: the codomain
contains both the empty scopes and the checking certificate. -/
structure LinkResolver (Link : Type) where
  resolveType : (target : Link) → (kind : Nucleus.HolE.Kind) →
    Option (Empty.FamK [] kind)
  resolveTerm : (target : Link) → (A : Empty.Ty []) →
    Option (Empty.Term (Empty.Ctx.empty : Empty.Ctx [] 0) A)

/-- Lower a type link after its surface kind annotation has been checked. -/
def lowerTypeLink (resolver : LinkResolver Link) (target : Link)
    (kind : Nucleus.HolE.Kind) :
    Option (Empty.FamK [] kind) :=
  resolver.resolveType target kind

/-- Lower a term link after its surface type annotation has been checked. -/
def lowerTermLink (resolver : LinkResolver Link) (target : Link) (A : Empty.Ty []) :
    Option (Empty.Term (Empty.Ctx.empty : Empty.Ctx [] 0) A) :=
  resolver.resolveTerm target A

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
