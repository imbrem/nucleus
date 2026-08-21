import Nucleus.Hol.Ethane.Subtype
import Nucleus.HolE.EmptyLogic

/-!
# Intrinsically checked guarded-subtype package

This file reconstructs the Ethane subtype package using the checked empty-
signature HolE API.  It supplies the typing evidence used by the package
axiom; proofs of the encoded laws are kept in the next layer.
-/

namespace Nucleus.HolE.Empty.SubtypePackage

open Nucleus.HolE

set_option relaxedAutoImplicit true

def renameFam (ρ : TyRen source target) (family : FamK source kind) :
    FamK target kind :=
  ⟨HolE.renameTypes ρ family.raw, by
    simpa [renameBoundCtx_empty] using family.kinded.renameTypes ρ⟩

def weakenFam (family : FamK types kind) : FamK (domain :: types) kind :=
  renameFam (fun v => .succ v) family

def renameClosedTerm (ρ : TyRen source target)
    (term : Term (Ctx.empty : Ctx source 0) A) :
    Term (Ctx.empty : Ctx target 0) (renameFam ρ A) :=
  ⟨HolE.renameTypes ρ term.raw, by
    simpa [renameFam, Ctx.empty, renameBoundCtx_empty] using term.typing.renameTypes ρ⟩

def weakenClosedTerm (term : Term (Ctx.empty : Ctx types 0) A) :
    Term (Ctx.empty : Ctx (domain :: types) 0) (weakenFam (domain := domain) A) :=
  renameClosedTerm (fun v => .succ v) term

/-- The predicate strengthened with the empty-predicate fallback. -/
def guard {types depth} {Γ : Ctx types depth} {A : Ty types}
    (predicate : Term Γ (A.arr FamK.boolTy)) (value : Term Γ A) : BoolTm Γ :=
  let extended := Γ.extend A
  let witness := Term.bv extended 0
  let holdsWitness := Term.app (predicate.weaken A) witness
  let inhabited := existsTm A holdsWitness
  or (Term.app predicate value) (not inhabited)

/-- Context containing first `rep : B → A` and then `abs : A → B`. -/
abbrev LawCtx {types} (A B : Ty types) : Ctx types 2 :=
  (Ctx.empty.extend (B.arr A)).extend (A.arr B)

def representation {types} (A B : Ty types) : Term (LawCtx A B) (B.arr A) :=
  Term.bv (LawCtx A B) 1

def abstraction {types} (A B : Ty types) : Term (LawCtx A B) (A.arr B) :=
  Term.bv (LawCtx A B) 0

/-- `abs (rep b) = b`. -/
def absRepLaw {types} (A B : Ty types) : BoolTm (LawCtx A B) :=
  let withB := (LawCtx A B).extend B
  let b : Term withB B := Term.bv withB 0
  let repB := Term.app ((representation A B).weaken B) b
  let absRepB := Term.app ((abstraction A B).weaken B) repB
  forallTm B (Term.eq B absRepB b)

/-- Guarded carrier values round-trip through `abs` and `rep`. -/
def repAbsLaw {types} (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    BoolTm (LawCtx A B) :=
  let withA := (LawCtx A B).extend A
  let a : Term withA A := Term.bv withA 0
  let absA := Term.app ((abstraction A B).weaken A) a
  let repAbsA := Term.app ((representation A B).weaken A) absA
  let predicateA := predicate.weaken (B.arr A) |>.weaken (A.arr B) |>.weaken A
  forallTm A (imp (guard predicateA a) (Term.eq A repAbsA a))

/-- Every represented model value satisfies the guarded predicate. -/
def repGuardedLaw {types} (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    BoolTm (LawCtx A B) :=
  let withB := (LawCtx A B).extend B
  let b : Term withB B := Term.bv withB 0
  let repB := Term.app ((representation A B).weaken B) b
  let predicateB := predicate.weaken (B.arr A) |>.weaken (A.arr B) |>.weaken B
  forallTm B (guard predicateB repB)

/-- The three representation/abstraction laws. -/
def laws {types} (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    BoolTm (LawCtx A B) :=
  and (absRepLaw A B) (and (repAbsLaw A B predicate)
    (repGuardedLaw A B predicate))

/-- Existential package formula for a fixed candidate model type. -/
def packageAt {types} (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    BoolTm (Ctx.empty : Ctx types 0) :=
  let repType := B.arr A
  let absType := A.arr B
  existsTm repType (existsTm absType (laws A B predicate))

/-- Predicate on a candidate type: suitable representation and abstraction
functions exist. -/
def predicate {types} (A : Ty types)
    (P : Term Ctx.empty (A.arr FamK.boolTy)) :
    BoolTm (types := .star :: types) Ctx.empty := by
  let A' := weakenFam (domain := .star) A
  let P' : Term (Ctx.empty : Ctx (.star :: types) 0)
      (A'.arr FamK.boolTy) := weakenClosedTerm (domain := .star) P
  let B : Ty (.star :: types) := FamK.bv .zero
  exact packageAt A' B P'

/-- The subtype-package sentence is well typed by construction. -/
def existsType {types} (A : Ty types)
    (P : Term (Ctx.empty : Ctx types 0) (A.arr FamK.boolTy)) :
    BoolTm (Ctx.empty : Ctx types 0) :=
  Term.tyExists Ctx.empty (predicate A P)

/-- The model selected by the package predicate. -/
def sub {types} (A : Ty types)
    (P : Term (Ctx.empty : Ctx types 0) (A.arr FamK.boolTy)) : Ty types :=
  Term.model (predicate A P)

end Nucleus.HolE.Empty.SubtypePackage
