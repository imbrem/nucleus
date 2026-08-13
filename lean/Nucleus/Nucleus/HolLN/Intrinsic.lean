import Mathlib.Order.Notation
import Nucleus.HolLN.Consistency

/-!
# Checked HOL propositions, contexts, and derivations

This module gives an intrinsic façade over the reference locally nameless HOL
kernel.  Terms carry their typing derivations, proposition contexts are lists
of checked Boolean terms, and `Intrinsic.Proves` repeats the complete reference
entailment rule inventory without separate `TypedHyps` premises.

The façade remains generic in the bound-variable depth.  `ClosedPropCtx` is the
depth-zero specialization: its terms have no unbound de Bruijn variables, but
may refer to the declared free context `Δ`.

A later context-free presentation can define a map from `PropCtx` to one
`BoolTm` by folding a checked conjunction over the list.  Conjunction is not
made primitive here.
-/

namespace Nucleus.HolLN

universe u

/-- A term intrinsically certified to have Boolean type. -/
abbrev BoolTm {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) := Checked Δ Γ (.boolTy : Ty Base)

/-- Proposition-oriented spelling for APIs that treat Boolean terms logically. -/
abbrev HolProp {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) := BoolTm Δ Γ

/-- A term intrinsically certified to have the distinguished natural type. -/
abbrev NatTm {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) := Checked Δ Γ (.natTy : Ty Base)

/-- A proposition context whose typing invariant is carried by its entries. -/
abbrev PropCtx {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) := List (BoolTm Δ Γ)

/-- A proposition context with no unbound de Bruijn term variables. -/
abbrev ClosedPropCtx {Base : Type u} (Δ : FreeCtx Base) :=
  PropCtx Δ (emptyBound : BoundCtx Base 0)

namespace Checked

@[ext] theorem ext {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} {left right : Checked Δ Γ A}
    (terms : left.term = right.term) : left = right := by
  cases left
  cases right
  cases terms
  rfl

def boolean {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (value : Bool) : BoolTm Δ Γ :=
  ⟨.bool value, .bool value⟩

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : Coe Bool (BoolTm Δ Γ) where
  coe := boolean

/-- Classical quotation of a metatheoretic proposition as a Boolean literal.
This is deliberately noncomputable: it is not an object-language connective. -/
noncomputable def ofProp {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (proposition : Prop) : BoolTm Δ Γ := by
  classical
  exact if proposition then boolean true else boolean false

noncomputable instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : Coe Prop (BoolTm Δ Γ) where
  coe := ofProp

@[simp] theorem ofProp_eq_true {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (proposition : Prop) (holds : proposition) :
    (ofProp proposition : BoolTm Δ Γ) = boolean true := by
  simp [ofProp, holds]

@[simp] theorem ofProp_eq_false {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (proposition : Prop) (fails : ¬ proposition) :
    (ofProp proposition : BoolTm Δ Γ) = boolean false := by
  simp [ofProp, fails]

def app {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base}
    (function : Checked Δ Γ (.arr A B)) (argument : Checked Δ Γ A) :
    Checked Δ Γ B :=
  ⟨.app function.term argument.term, .app function.typing argument.typing⟩

def bound {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} (hA : Kinded A)
    (index : Fin depth) (lookup : Γ index = A) : Checked Δ Γ A :=
  ⟨.bound index, .bound hA lookup⟩

def weaken {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base} (term : Checked Δ Γ A) :
    Checked Δ (extendBound B Γ) A :=
  ⟨Nucleus.HolLN.weaken term.term, term.typing.weakenBound⟩

def lam {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A B : Ty Base} (hA : Kinded A)
    (body : Checked Δ (extendBound A Γ) B) : Checked Δ Γ (.arr A B) :=
  ⟨.lam A body.term, .lam body.term hA body.typing⟩

def eq {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} (hA : Kinded A)
    (left right : Checked Δ Γ A) : BoolTm Δ Γ :=
  ⟨.eq A left.term right.term, .eq hA left.typing right.typing⟩

def eps {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} (hA : Kinded A)
    (predicate : Checked Δ Γ (.arr A .boolTy)) : Checked Δ Γ A :=
  ⟨.eps A predicate.term, .eps hA predicate.typing⟩

def abs {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} (hA : Kinded A)
    (predicate : Checked emptyContext (extendBound A emptyBound) .boolTy)
    (value : Checked Δ Γ A) : Checked Δ Γ (.sub A predicate.term) :=
  ⟨.abs A predicate.term value.term, .abs hA predicate.typing value.typing⟩

def rep {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {A : Ty Base} (hA : Kinded A)
    (predicate : Checked emptyContext (extendBound A emptyBound) .boolTy)
    (value : Checked Δ Γ (.sub A predicate.term)) : Checked Δ Γ A :=
  ⟨.rep A predicate.term value.term, .rep hA predicate.typing value.typing⟩

def succ {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (value : Checked Δ Γ .natTy) : Checked Δ Γ .natTy :=
  ⟨.succ value.term, .succ value.typing⟩

def natural {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : Nat -> NatTm Δ Γ
  | 0 => ⟨.zero, .zero⟩
  | n + 1 => succ (natural n)

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : Coe Nat (NatTm Δ Γ) where
  coe := natural

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (n : Nat) : OfNat (NatTm Δ Γ) n where
  ofNat := natural n

/-- Equality-only HOL definition of conjunction.  Two Boolean arguments are
both true exactly when every binary Boolean function gives them the same value
as it gives `true, true`. -/
def boolAnd {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (left right : BoolTm Δ Γ) : BoolTm Δ Γ :=
  let operatorTy : Ty Base := .arr .boolTy (.arr .boolTy .boolTy)
  let hOperator : Kinded operatorTy := .arr .bool (.arr .bool .bool)
  let operator : Checked Δ (extendBound operatorTy Γ) operatorTy :=
    bound hOperator 0 rfl
  let applied := app (app operator (weaken left)) (weaken right)
  let appliedTrue := app (app operator (boolean true)) (boolean true)
  eq (.arr hOperator .bool) (lam hOperator applied) (lam hOperator appliedTrue)

def boolNot {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (proposition : BoolTm Δ Γ) : BoolTm Δ Γ :=
  eq .bool proposition (boolean false)

def boolOr {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (left right : BoolTm Δ Γ) : BoolTm Δ Γ :=
  boolNot (boolAnd (boolNot left) (boolNot right))

def boolImp {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (left right : BoolTm Δ Γ) : BoolTm Δ Γ :=
  boolOr (boolNot left) right

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : Top (BoolTm Δ Γ) := ⟨boolean true⟩

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : Bot (BoolTm Δ Γ) := ⟨boolean false⟩

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : Min (BoolTm Δ Γ) := ⟨boolAnd⟩

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : Max (BoolTm Δ Γ) := ⟨boolOr⟩

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : HAnd (BoolTm Δ Γ) (BoolTm Δ Γ) (BoolTm Δ Γ) :=
  ⟨boolAnd⟩

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : HOr (BoolTm Δ Γ) (BoolTm Δ Γ) (BoolTm Δ Γ) :=
  ⟨boolOr⟩

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : Compl (BoolTm Δ Γ) := ⟨boolNot⟩

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : HNot (BoolTm Δ Γ) := ⟨boolNot⟩

instance {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} : HImp (BoolTm Δ Γ) := ⟨boolImp⟩

end Checked

namespace PropCtx

def terms {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (context : PropCtx Δ Γ) : List (Tm Base depth) :=
  context.map Checked.term

theorem typed {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (context : PropCtx Δ Γ) :
    TypedHyps Δ Γ context.terms := by
  intro p member
  obtain ⟨checked, _, rfl⟩ := List.mem_map.mp member
  exact checked.typing

def ofTyped {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (hypotheses : List (Tm Base depth))
    (typed : TypedHyps Δ Γ hypotheses) : PropCtx Δ Γ :=
  hypotheses.attach.map fun member => ⟨member.1, typed member.1 member.2⟩

@[simp] theorem terms_ofTyped {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} (hypotheses : List (Tm Base depth))
    (typed : TypedHyps Δ Γ hypotheses) :
    (ofTyped hypotheses typed).terms = hypotheses := by
  simp [ofTyped, terms]

/-- Reserved interface for context internalization.  A later module providing
checked conjunction will define the corresponding fold `PropCtx -> BoolTm`. -/
class HasConjoin {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) where
  conjoin : PropCtx Δ Γ -> BoolTm Δ Γ

end PropCtx

namespace Intrinsic

/-- Checked term equality.  The endpoints carry typing evidence; the
proof-relevant equality certificate remains the reference kernel certificate. -/
structure EqTm {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) {A : Ty Base}
    (left right : Checked Δ Γ A) : Type u where
  proof : Nucleus.HolLN.EqTm Δ Γ left.term right.term A

/-- Checked HOL entailment. Context and conclusion carry the typing invariant;
the proof field remains an inspectable reference-kernel certificate. -/
structure Proves {Base : Type u} (Δ : FreeCtx Base) {depth : Nat}
    (Γ : BoundCtx Base depth) (H : PropCtx Δ Γ) (p : BoolTm Δ Γ) : Type u where
  proof : Nucleus.HolLN.Proves Δ Γ H.terms p.term

namespace Proves

def hyp {p : BoolTm Δ Γ} (member : p ∈ H) : Proves Δ Γ H p :=
  ⟨.hyp (PropCtx.typed H) (List.mem_map_of_mem member)⟩

def truth : Proves Δ Γ H (Checked.boolean true) := ⟨.truth (PropCtx.typed H)⟩

def eqRefl (hA : Kinded A) (x : Checked Δ Γ A) :
    Proves Δ Γ H (Checked.eq hA x x) := ⟨.eqRefl (PropCtx.typed H) hA x.typing⟩

def eqMp (hA : Kinded A) (predicate : Checked Δ Γ (.arr A .boolTy))
    (x y : Checked Δ Γ A) (equality : Proves Δ Γ H (Checked.eq hA x y))
    (application : Proves Δ Γ H (Checked.app predicate x)) :
    Proves Δ Γ H (Checked.app predicate y) :=
  ⟨.eqMp (PropCtx.typed H) hA predicate.typing x.typing y.typing
    equality.proof application.proof⟩

def choice (hA : Kinded A) (predicate : Checked Δ Γ (.arr A .boolTy))
    (x : Checked Δ Γ A) (premise : Proves Δ Γ H (Checked.app predicate x)) :
    Proves Δ Γ H (Checked.app predicate (Checked.eps hA predicate)) :=
  ⟨.choice (PropCtx.typed H) hA predicate.typing x.typing premise.proof⟩

def convert {p q : BoolTm Δ Γ} (equality : EqTm Δ Γ p q)
    (premise : Proves Δ Γ H p) : Proves Δ Γ H q :=
  ⟨.convert (PropCtx.typed H) equality.proof premise.proof⟩

def eqOfEqTm (hA : Kinded A) {x y : Checked Δ Γ A} (equality : EqTm Δ Γ x y) :
    Proves Δ Γ H (Checked.eq hA x y) :=
  ⟨.eqOfEqTm (PropCtx.typed H) hA equality.proof⟩

def antisymm (p q : BoolTm Δ Γ) (left : Proves Δ Γ (p :: H) q)
    (right : Proves Δ Γ (q :: H) p) : Proves Δ Γ H (Checked.eq .bool p q) :=
  ⟨.antisymm (PropCtx.typed H) p.typing q.typing (PropCtx.typed (p :: H))
    (PropCtx.typed (q :: H)) left.proof right.proof⟩

def absRep (hA : Kinded A)
    (predicate : Checked emptyContext (extendBound A emptyBound) .boolTy)
    (x : Checked Δ Γ (.sub A predicate.term)) :
    Proves Δ Γ H (Checked.eq (.sub hA predicate.typing)
      (Checked.abs hA predicate (Checked.rep hA predicate x)) x) :=
  ⟨.absRep (PropCtx.typed H) hA predicate.typing x.typing⟩

def repAbs (hA : Kinded A)
    (predicate : Checked emptyContext (extendBound A emptyBound) .boolTy)
    (x : Checked Δ Γ A) (instantiated : BoolTm Δ Γ)
    (term_eq : instantiated.term = instantiateOne predicate.term x.term)
    (premise : Proves Δ Γ H instantiated) :
    Proves Δ Γ H (Checked.eq hA
      (Checked.rep hA predicate (Checked.abs hA predicate x)) x) := by
  refine ⟨.repAbs (PropCtx.typed H) hA predicate.typing x.typing ?_ ?_⟩
  · exact term_eq ▸ instantiated.typing
  · exact term_eq ▸ premise.proof

def succInjective (x y : NatTm Δ Γ)
    (premise : Proves Δ Γ H (Checked.eq .nat (Checked.succ x) (Checked.succ y))) :
    Proves Δ Γ H (Checked.eq .nat x y) :=
  ⟨.succInjective (PropCtx.typed H) x.typing y.typing premise.proof⟩

def zeroNotSucc (x : NatTm Δ Γ) :
    Proves Δ Γ H (Checked.eq .bool
      (Checked.eq .nat ⟨.zero, .zero⟩ (Checked.succ x)) (Checked.boolean false)) :=
  ⟨.zeroNotSucc (PropCtx.typed H) x.typing⟩

def toKernel {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {H : PropCtx Δ Γ} {p : BoolTm Δ Γ}
    (proof : Proves Δ Γ H p) : Nucleus.HolLN.Proves Δ Γ H.terms p.term :=
  proof.proof

def ofKernel (proof : Nucleus.HolLN.Proves Δ Γ H.terms p.term) : Proves Δ Γ H p :=
  ⟨proof⟩

end Proves

theorem proves_iff_kernel {Base : Type u} {Δ : FreeCtx Base} {depth : Nat}
    {Γ : BoundCtx Base depth} {H : PropCtx Δ Γ} {p : BoolTm Δ Γ} :
    Nonempty (Proves Δ Γ H p) ↔
      Nonempty (Nucleus.HolLN.Proves Δ Γ H.terms p.term) := by
  constructor <;> rintro ⟨proof⟩
  · exact ⟨proof.proof⟩
  · exact ⟨⟨proof⟩⟩

theorem nonemptyProvesOfProp {Base : Type u} (proposition : Prop)
    (holds : proposition) :
    Nonempty (Proves (emptyContext : FreeCtx Base) (emptyBound : BoundCtx Base 0) []
      (Checked.ofProp proposition)) := by
  constructor
  rw [Checked.ofProp_eq_true proposition holds]
  exact .truth

noncomputable def provesOfProp {Base : Type u} (proposition : Prop)
    (holds : proposition) :
    Proves (emptyContext : FreeCtx Base) (emptyBound : BoundCtx Base 0) []
      (Checked.ofProp proposition) :=
  Classical.choice (nonemptyProvesOfProp proposition holds)

theorem propOfProves {Base : Type u} (proposition : Prop)
    (proof : Proves (emptyContext : FreeCtx Base) (emptyBound : BoundCtx Base 0) []
      (Checked.ofProp proposition)) : proposition := by
  classical
  by_cases holds : proposition
  · exact holds
  · have equality := Checked.ofProp_eq_false (Base := Base)
      (Δ := emptyContext) (Γ := emptyBound) proposition holds
    have falseProof : Proves (emptyContext : FreeCtx Base)
        (emptyBound : BoundCtx Base 0) [] (Checked.boolean false) :=
      equality ▸ proof
    exact False.elim (empty_not_proves_false ⟨falseProof.toKernel⟩)

theorem provesOfProp_iff {Base : Type u} (proposition : Prop) :
    Nonempty (Proves (emptyContext : FreeCtx Base) (emptyBound : BoundCtx Base 0) []
      (Checked.ofProp proposition)) ↔ proposition := by
  constructor
  · rintro ⟨proof⟩
    exact propOfProves proposition proof
  · exact nonemptyProvesOfProp proposition

end Intrinsic

end Nucleus.HolLN
