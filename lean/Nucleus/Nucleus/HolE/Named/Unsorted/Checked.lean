import Nucleus.HolE.Named.Unsorted.Kernel
import Nucleus.HolE.Named.Unsorted.WellSorted

/-!
# Intrinsically checked named HolE

The structures here retain both the review-friendly named surface expression
and its locally nameless kernel image.  This makes construction syntax-directed
without moving lowering or typing into the trusted boundary.
-/

namespace Nucleus.HolE.Named.Unsorted

set_option relaxedAutoImplicit true

/-- Primitive term symbols have a unique raw type.  The core deliberately
permits relational primitive typing, so implementations opt into this stronger
property when they want type inference and projection injectivity. -/
class UniqueSigTyping (Sig : Signature) [rules : Nucleus.HolE.SigTyping Sig] : Prop where
  unique {types : List Kind} {symbol : Sig .tm}
    {left right : Nucleus.HolE.Ty Sig types} :
    rules.HasType symbol left → rules.HasType symbol right → left = right

/-- A well-kinded named type family. -/
structure Family (Sig : Signature) [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} (typeScope : Named.TyScope types) (kind : Kind) where
  expression : WellSorted Sig (.kind kind)
  lowered : Nucleus.HolE.Fam Sig types kind
  lowering : Named.lowerFam typeScope expression.sorted = some lowered
  kinding : Nucleus.HolE.Kinded lowered

/-- A well-typed named term at one intrinsic type. -/
structure Term (Sig : Signature) [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat}
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth)
    (type : Family Sig typeScope .star) where
  expression : WellSorted Sig .tm
  lowered : Nucleus.HolE.Tm Sig types depth
  lowering : Named.lowerTm typeScope termScope expression.sorted = some lowered
  typing : Nucleus.HolE.HasType Γ lowered type.lowered

namespace Family

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]

def raw (family : Family Sig typeScope kind) : Expr Sig Nat := family.expression.raw

theorem toKinded (family : Family Sig typeScope kind) :
    Kinded typeScope family.raw kind := by
  exact Checks.complete (check_erase family.expression.sorted) rfl
    (Named.Checks.complete family.lowering rfl family.kinding)

@[ext] theorem ext {left right : Family Sig typeScope kind}
    (expression : left.expression = right.expression)
    (lowered : left.lowered = right.lowered) : left = right := by
  cases left
  cases right
  cases expression
  cases lowered
  rfl

end Family

namespace Term

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]

def raw (term : Term Sig typeScope termScope Γ type) : Expr Sig Nat := term.expression.raw

def rawType (_term : Term Sig typeScope termScope Γ type) : Expr Sig Nat := type.raw

theorem toHasType (term : Term Sig typeScope termScope Γ type) :
    HasType typeScope termScope Γ term.raw term.rawType := by
  exact Checks.complete (check_erase term.expression.sorted)
    (by
      change checkClassification (.tm type.raw) = some (.tm type.expression.sorted)
      simp [checkClassification, Family.raw, WellSorted.raw])
    (Named.Checks.complete term.lowering
      (by
        simp [Named.lowerClassification, Named.lowerTy, type.lowering]) term.typing)

/-- Partial injection into one requested intrinsic type.  It is noncomputable
for a relational signature; an implementation with decidable typing can use
the same interface executably. -/
noncomputable def ofRaw (type : Family Sig typeScope .star)
    (expression : Expr Sig Nat) : Option (Term Sig typeScope termScope Γ type) := by
  classical
  if present : ∃ term : Term Sig typeScope termScope Γ type,
      term.raw = expression then
    exact some present.choose
  else
    exact none

theorem ofRaw_sound {type : Family Sig typeScope .star} {expression : Expr Sig Nat}
    {result : Term Sig typeScope termScope Γ type}
    (checked : ofRaw type expression = some result) : result.raw = expression := by
  classical
  unfold ofRaw at checked
  split at checked
  next present =>
    simp only [Option.some.injEq] at checked
    subst result
    exact present.choose_spec
  next absent => simp at checked

theorem ofRaw_complete (term : Term Sig typeScope termScope Γ type) :
    ∃ result : Term Sig typeScope termScope Γ type,
      ofRaw type term.raw = some result ∧ result.raw = term.raw := by
  classical
  unfold ofRaw
  split
  next present => exact ⟨present.choose, rfl, present.choose_spec⟩
  next absent => exact False.elim (absent ⟨term, rfl⟩)

end Term

/-- A kinded family or typed term with its classification stored explicitly. -/
inductive SomeTyped (Sig : Signature) [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat}
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth) where
  | family {kind : Kind} (value : Family Sig typeScope kind)
  | term (type : Family Sig typeScope .star)
      (value : Term Sig typeScope termScope Γ type)

namespace SomeTyped

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]

def sort : SomeTyped Sig typeScope termScope Γ → HolSort
  | .family (kind := kind) _ => .kind kind
  | .term .. => .tm

def raw : SomeTyped Sig typeScope termScope Γ → Expr Sig Nat
  | .family value => value.raw
  | .term _ value => value.raw

/-- Extract the object-language type of a term.  Families have no term type. -/
def type? : (value : SomeTyped Sig typeScope termScope Γ) →
    Option (Family Sig typeScope .star)
  | .family _ => none
  | .term type _ => some type

/-- Classify raw syntax noncomputably using the existing sound and complete
typing relation.  This is partial because well-sorted syntax can be ill-typed.
Concrete kernels may replace it with an executable checker. -/
noncomputable def ofRaw (expression : Expr Sig Nat) :
    Option (SomeTyped Sig typeScope termScope Γ) := by
  classical
  if familyPresent :
      ∃ (kind : Kind) (family : Family Sig typeScope kind), family.raw = expression then
    let kind := familyPresent.choose
    let family := familyPresent.choose_spec.choose
    exact some (.family family)
  else if termPresent :
      ∃ (type : Family Sig typeScope .star)
        (term : Term Sig typeScope termScope Γ type), term.raw = expression then
    let type := termPresent.choose
    let term := termPresent.choose_spec.choose
    exact some (.term type term)
  else
    exact none

theorem ofRaw_sound {expression : Expr Sig Nat}
    {result : SomeTyped Sig typeScope termScope Γ}
    (checked : ofRaw expression = some result) : result.raw = expression := by
  classical
  unfold ofRaw at checked
  split at checked
  next familyPresent =>
    simp only [Option.some.injEq] at checked
    subst result
    exact familyPresent.choose_spec.choose_spec
  next noFamily =>
    split at checked
    next termPresent =>
      simp only [Option.some.injEq] at checked
      subst result
      exact termPresent.choose_spec.choose_spec
    next noTerm => simp at checked

/-- Every checked value makes raw classification succeed.  Without uniqueness
the returned witness need not be definitionally the supplied one. -/
theorem ofRaw_complete (value : SomeTyped Sig typeScope termScope Γ) :
    ∃ result : SomeTyped Sig typeScope termScope Γ,
      ofRaw (typeScope := typeScope) (termScope := termScope) (Γ := Γ) value.raw =
        some result ∧
      raw result = raw value := by
  classical
  cases value with
  | family value =>
      unfold ofRaw
      split
      next familyPresent =>
        refine ⟨.family familyPresent.choose_spec.choose, rfl, ?_⟩
        exact familyPresent.choose_spec.choose_spec
      next noFamily =>
        exact False.elim (noFamily ⟨_, value, rfl⟩)
  | term type value =>
      unfold ofRaw
      split
      next familyPresent =>
        refine ⟨.family familyPresent.choose_spec.choose, rfl, ?_⟩
        exact familyPresent.choose_spec.choose_spec
      next noFamily =>
        split
        next termPresent =>
          refine ⟨.term termPresent.choose termPresent.choose_spec.choose, rfl, ?_⟩
          exact termPresent.choose_spec.choose_spec
        next noTerm =>
          exact False.elim (noTerm ⟨type, value, rfl⟩)

/-- Uniqueness of the intrinsic classification exposed by this façade.  It is
not automatic for arbitrary signatures: primitive typing is relational. -/
def UniqueClassification {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    {types : List Kind} {depth : Nat}
    (typeScope : Named.TyScope types) (termScope : Named.TmScope Sig depth)
    (Γ : Nucleus.HolE.BoundCtx Sig types depth) : Prop :=
  ∀ left right : SomeTyped Sig typeScope termScope Γ,
    left.raw = right.raw → left = right

theorem raw_injective (unique : UniqueClassification (Sig := Sig)
    (typeScope := typeScope) (termScope := termScope) (Γ := Γ)) :
    Function.Injective (raw (Sig := Sig) (typeScope := typeScope)
      (termScope := termScope) (Γ := Γ)) :=
  unique

end SomeTyped

end Nucleus.HolE.Named.Unsorted
