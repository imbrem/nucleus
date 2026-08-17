import Nucleus.HolE.ClassicalSemantics

/-! # A type-existential axiom of infinity

This file gives a closed HolE sentence asserting the existence of a type with
an injective, non-surjective endomap.  It is deliberately expressed using only
the primitive equality, lambda, application, choice, and type-existential
syntax.  `Nat`, with successor and zero, is the intended classical witness.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- A small intrinsically checked view used to construct the infinity
sentence.  Unlike the eventual generic intrinsic API, this wrapper is local to
the experiment and does not add syntax or proof rules. -/
structure InfinityTm (Sig : Signature) [SigTyping Sig] {types : List Kind}
    {depth : Nat} (Γ : BoundCtx Sig types depth) (A : Ty Sig types) where
  tm : Tm Sig types depth
  typing : HasType Γ tm A

namespace InfinityTm

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A B : Ty Sig types}

def bv (hA : Kinded A) (index : Fin depth) (lookup : Γ index = A) :
    InfinityTm Sig Γ A :=
  ⟨.bv index, .bv hA lookup⟩

def boolean (value : Bool) : InfinityTm Sig Γ .boolTy :=
  ⟨.bool value, .bool value⟩

def weaken {C : Ty Sig types} (term : InfinityTm Sig Γ A) :
    InfinityTm Sig (extendBound C Γ) A :=
  ⟨HolE.weaken term.tm, term.typing.weaken⟩

def app (function : InfinityTm Sig Γ (.arr A B))
    (argument : InfinityTm Sig Γ A) : InfinityTm Sig Γ B :=
  ⟨.app function.tm argument.tm, .app function.typing argument.typing⟩

def lam (hA : Kinded A) (body : InfinityTm Sig (extendBound A Γ) B) :
    InfinityTm Sig Γ (.arr A B) :=
  ⟨.lam A body.tm, .lam body.tm hA body.typing⟩

def eq (hA : Kinded A) (left right : InfinityTm Sig Γ A) :
    InfinityTm Sig Γ .boolTy :=
  ⟨.eq A left.tm right.tm, .eq hA left.typing right.typing⟩

def eps (hA : Kinded A) (predicate : InfinityTm Sig Γ (.arr A .boolTy)) :
    InfinityTm Sig Γ A :=
  ⟨.eps A predicate.tm, .eps hA predicate.typing⟩

def truth : InfinityTm Sig Γ .boolTy := boolean true
def falsehood : InfinityTm Sig Γ .boolTy := boolean false

/-- HOL universal quantification, represented by equality of the predicate
with the constantly-true function. -/
def forallTm (hA : Kinded A) (body : InfinityTm Sig (extendBound A Γ) .boolTy) :
    InfinityTm Sig Γ .boolTy :=
  eq (.arr hA .boolTy) (lam hA body) (lam hA truth)

/-- Choice-based existential quantification. -/
def existsTm (hA : Kinded A) (body : InfinityTm Sig (extendBound A Γ) .boolTy) :
    InfinityTm Sig Γ .boolTy :=
  let predicate := lam hA body
  predicate.app (predicate.eps hA)

def not (proposition : InfinityTm Sig Γ .boolTy) : InfinityTm Sig Γ .boolTy :=
  eq .boolTy proposition falsehood

/-- The standard equality-only HOL definition of conjunction. -/
def and (left right : InfinityTm Sig Γ .boolTy) : InfinityTm Sig Γ .boolTy := by
  let functionTy : Ty Sig types := .arr .boolTy (.arr .boolTy .boolTy)
  let hFunction : Kinded functionTy := .arr .boolTy (.arr .boolTy .boolTy)
  let f : InfinityTm Sig (extendBound functionTy Γ) functionTy := bv hFunction 0 rfl
  let lhsBody := (f.app left.weaken).app right.weaken
  let lhs := lam hFunction lhsBody
  let trueInExtended : InfinityTm Sig (extendBound functionTy Γ) .boolTy := truth
  let rhsBody := (f.app trueInExtended).app trueInExtended
  let rhs := lam hFunction rhsBody
  exact eq (.arr hFunction .boolTy) lhs rhs

end InfinityTm

namespace Infinity

abbrev A {Sig : Signature} : Ty Sig [.star] := .tyBv .zero

theorem hA {Sig : Signature} [SigTyping Sig] : Kinded (A (Sig := Sig)) := .tyBv .zero

/-- In the context `f, z`, successor-like `f` reflects equality.  Equality
reflection is stronger than injectivity, but equivalent for every injective
function and especially convenient in equality-only HOL. -/
def reflectsEquality {Sig : Signature} [SigTyping Sig] :
    InfinityTm Sig
      (extendBound (A (Sig := Sig))
        (extendBound (.arr A A) (emptyBound : BoundCtx Sig [.star] 0)))
      .boolTy := by
  let Γfz := extendBound (A (Sig := Sig))
    (extendBound (.arr A A) (emptyBound : BoundCtx Sig [.star] 0))
  let xBodyCtx := extendBound A Γfz
  let yBodyCtx := extendBound A xBodyCtx
  let f : InfinityTm Sig yBodyCtx (.arr A A) :=
    .bv (.arr hA hA) 3 rfl
  let x : InfinityTm Sig yBodyCtx A := .bv hA 1 rfl
  let y : InfinityTm Sig yBodyCtx A := .bv hA 0 rfl
  let reflected := InfinityTm.eq .boolTy
    (InfinityTm.eq hA (f.app x) (f.app y))
    (InfinityTm.eq hA x y)
  exact InfinityTm.forallTm hA (InfinityTm.forallTm hA reflected)

/-- In the context `f, z`, `z` is outside the range of `f`. -/
def missesPoint {Sig : Signature} [SigTyping Sig] :
    InfinityTm Sig
      (extendBound (A (Sig := Sig))
        (extendBound (.arr A A) (emptyBound : BoundCtx Sig [.star] 0)))
      .boolTy := by
  let Γfz := extendBound (A (Sig := Sig))
    (extendBound (.arr A A) (emptyBound : BoundCtx Sig [.star] 0))
  let bodyCtx := extendBound A Γfz
  let f : InfinityTm Sig bodyCtx (.arr A A) := .bv (.arr hA hA) 2 rfl
  let z : InfinityTm Sig bodyCtx A := .bv hA 1 rfl
  let x : InfinityTm Sig bodyCtx A := .bv hA 0 rfl
  exact InfinityTm.forallTm hA (InfinityTm.not (InfinityTm.eq hA (f.app x) z))

/-- Predicate on a type: it carries an equality-reflecting endomap which
misses a point, hence is Dedekind-infinite. -/
def typePredicate {Sig : Signature} [SigTyping Sig] :
    InfinityTm Sig (emptyBound : BoundCtx Sig [.star] 0) .boolTy := by
  let endomap : Ty Sig [.star] := .arr A A
  let withF := extendBound endomap (emptyBound : BoundCtx Sig [.star] 0)
  let withZ := extendBound A withF
  let body : InfinityTm Sig withZ .boolTy :=
    InfinityTm.and reflectsEquality missesPoint
  let chooseZ : InfinityTm Sig withF .boolTy := InfinityTm.existsTm hA body
  exact InfinityTm.existsTm (.arr hA hA) chooseZ

/-- The closed HolE axiom of infinity: some type satisfies `typePredicate`. -/
def infinityAxiom {Sig : Signature} [SigTyping Sig] : Tm Sig [] 0 :=
  .tyExists (typePredicate (Sig := Sig)).tm

theorem axiom_typed {Sig : Signature} [SigTyping Sig] :
    HasType (emptyBound : BoundCtx Sig [] 0) (infinityAxiom (Sig := Sig)) .boolTy :=
  .tyExists (typePredicate (Sig := Sig)).typing

/-- The pointed carrier used for the semantic witness. -/
def natPointed : CPointed := ⟨Nat, 0⟩

/-- The direct classical meaning of the object-language infinity predicate.
Keeping this record explicit makes the `Nat` witness independent of the
still-developing proof that semantic evaluation commutes with all syntactic
opening and substitution operations. -/
structure CInfinityStructure (carrier : CPointed) where
  next : carrier.carrier → carrier.carrier
  missed : carrier.carrier
  reflectsEquality : ∀ x y, next x = next y ↔ x = y
  misses : ∀ x, next x ≠ missed

theorem nat_succ_reflects_equality (x y : Nat) :
    (Nat.succ x = Nat.succ y) = (x = y) := by
  simp

theorem nat_succ_misses_zero (x : Nat) : Nat.succ x ≠ 0 := Nat.succ_ne_zero x

def natInfinity : CInfinityStructure natPointed := by
  change CInfinityStructure ⟨Nat, 0⟩
  exact {
    next := Nat.succ
    missed := 0
    reflectsEquality := by simp
    misses := Nat.succ_ne_zero
  }

theorem classical_infinity_has_witness :
    Nonempty (Σ carrier : CPointed, CInfinityStructure carrier) :=
  ⟨⟨natPointed, natInfinity⟩⟩

end Infinity

end Nucleus.HolE
