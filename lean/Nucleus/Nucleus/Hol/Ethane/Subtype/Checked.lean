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

/-- Abstract one value argument of the guarded predicate. -/
def guardBody {types depth} {Γ : Ctx types depth} (A : Ty types)
    (predicate : Term Γ (A.arr FamK.boolTy)) : BoolTm (Γ.extend A) :=
  let extended := Γ.extend A
  guard (predicate.weaken A) (Term.bv extended 0)

/-- The guarded predicate as the unary body expected by primitive `Sub`. -/
def guardPredicate {types} (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    BoolTm (Ctx.empty.extend A) :=
  guardBody A predicate

/-- A proof-friendly realization of the guarded carrier.  Applying primitive
`Sub` to the guard, rather than to the original predicate, makes its existing
`repAbs` rule exactly match the package law. -/
def subViaGuard {types} (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) : Ty types :=
  Term.sub A (guardPredicate A predicate)

def primitiveRepAt {types depth} (Γ : Ctx types depth) (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    Term Γ ((subViaGuard A predicate).arr A) :=
  let B := subViaGuard A predicate
  let extended := Γ.extend B
  Term.lam B (Term.rep A (guardPredicate A predicate) (Term.bv extended 0))

def primitiveRep {types} (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    Term Ctx.empty ((subViaGuard A predicate).arr A) :=
  primitiveRepAt Ctx.empty A predicate

def primitiveAbsAt {types depth} (Γ : Ctx types depth) (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    Term Γ (A.arr (subViaGuard A predicate)) :=
  let extended := Γ.extend A
  Term.lam A (Term.abs A (guardPredicate A predicate) (Term.bv extended 0))

def primitiveAbs {types} (A : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy)) :
    Term Ctx.empty (A.arr (subViaGuard A predicate)) :=
  primitiveAbsAt Ctx.empty A predicate

/-- Context containing first `rep : B → A` and then `abs : A → B`. -/
abbrev LawCtx {types} (A B : Ty types) : Ctx types 2 :=
  (Ctx.empty.extend (B.arr A)).extend (A.arr B)

def representation {types} (A B : Ty types) : Term (LawCtx A B) (B.arr A) :=
  Term.bv (LawCtx A B) 1

def abstraction {types} (A B : Ty types) : Term (LawCtx A B) (A.arr B) :=
  Term.bv (LawCtx A B) 0

/-- The subtype laws with representation and abstraction supplied explicitly. -/
def absRepAt {types} (A B : Ty types)
    (rep : Term Ctx.empty (B.arr A)) (abs : Term Ctx.empty (A.arr B)) :
    BoolTm (Ctx.empty : Ctx types 0) :=
  let withB := Ctx.empty.extend B
  let b : Term withB B := Term.bv withB 0
  forallTm B (Term.eq B
    (Term.app (abs.weaken B) (Term.app (rep.weaken B) b)) b)

def repAbsAt {types} (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (rep : Term Ctx.empty (B.arr A)) (abs : Term Ctx.empty (A.arr B)) :
    BoolTm (Ctx.empty : Ctx types 0) :=
  let withA := Ctx.empty.extend A
  let a : Term withA A := Term.bv withA 0
  let predicateA := predicate.weaken A
  forallTm A (imp (guard predicateA a) (Term.eq A
    (Term.app (rep.weaken A) (Term.app (abs.weaken A) a)) a))

def repGuardedAt {types} (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (rep : Term Ctx.empty (B.arr A)) : BoolTm (Ctx.empty : Ctx types 0) :=
  let withB := Ctx.empty.extend B
  let b : Term withB B := Term.bv withB 0
  let predicateB := predicate.weaken B
  forallTm B (guard predicateB (Term.app (rep.weaken B) b))

def lawsAt {types} (A B : Ty types)
    (predicate : Term Ctx.empty (A.arr FamK.boolTy))
    (rep : Term Ctx.empty (B.arr A)) (abs : Term Ctx.empty (A.arr B)) :
    BoolTm (Ctx.empty : Ctx types 0) :=
  and (absRepAt A B rep abs)
    (and (repAbsAt A B predicate rep abs) (repGuardedAt A B predicate rep))

/-- Context-polymorphic form of the representation/abstraction laws.  The
serialized package uses the closed specialization after its binders open. -/
def absRepIn {types depth} {Γ : Ctx types depth} (A B : Ty types)
    (rep : Term Γ (B.arr A)) (abs : Term Γ (A.arr B)) : BoolTm Γ :=
  let withB := Γ.extend B
  let b : Term withB B := Term.bv withB 0
  forallTm B (Term.eq B
    (Term.app (abs.weaken B) (Term.app (rep.weaken B) b)) b)

def repAbsIn {types depth} {Γ : Ctx types depth} (A B : Ty types)
    (predicate : Term Γ (A.arr FamK.boolTy))
    (rep : Term Γ (B.arr A)) (abs : Term Γ (A.arr B)) : BoolTm Γ :=
  let withA := Γ.extend A
  let a : Term withA A := Term.bv withA 0
  forallTm A (imp (guard (predicate.weaken A) a) (Term.eq A
    (Term.app (rep.weaken A) (Term.app (abs.weaken A) a)) a))

def repGuardedIn {types depth} {Γ : Ctx types depth} (A B : Ty types)
    (predicate : Term Γ (A.arr FamK.boolTy))
    (rep : Term Γ (B.arr A)) : BoolTm Γ :=
  let withB := Γ.extend B
  let b : Term withB B := Term.bv withB 0
  forallTm B (guard (predicate.weaken B) (Term.app (rep.weaken B) b))

def lawsIn {types depth} {Γ : Ctx types depth} (A B : Ty types)
    (predicate : Term Γ (A.arr FamK.boolTy))
    (rep : Term Γ (B.arr A)) (abs : Term Γ (A.arr B)) : BoolTm Γ :=
  and (absRepIn A B rep abs)
    (and (repAbsIn A B predicate rep abs)
      (repGuardedIn A B predicate rep))

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
