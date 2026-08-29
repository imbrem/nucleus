/-!
# Total and partial Boolean assignments

This module supplies the valuation theory shared by the alternative classical
prover designs.  A partial assignment denotes all of its total completions;
unknown atoms are never assigned a default truth value.  Consequently the
everywhere-unknown assignment is the least informative assignment, and a
claim valid there is a syllogism: it holds under every total assignment.
-/

namespace Nucleus.Classical

universe u

variable {Atom : Type u}

/-- A total Boolean assignment to uninterpreted atoms. -/
abbrev Assignment (Atom : Type u) := Atom → Bool

/-- A partial assignment. `none` means that the atom remains unconstrained. -/
abbrev PartialAssignment (Atom : Type u) := Atom → Option Bool

/-- A signed occurrence of an atom. `negative = true` complements its value. -/
structure Literal (Atom : Type u) where
  atom : Atom
  negative : Bool
  deriving DecidableEq, Repr

namespace Literal

/-- Evaluate a signed literal under a total assignment. -/
def eval (assignment : Assignment Atom) (literal : Literal Atom) : Bool :=
  if literal.negative then !assignment literal.atom else assignment literal.atom

/-- Complement a literal without inspecting or interpreting its atom. -/
def neg (literal : Literal Atom) : Literal Atom :=
  { literal with negative := !literal.negative }

@[simp] theorem neg_negative (literal : Literal Atom) :
    literal.neg.negative = !literal.negative := rfl

@[simp] theorem neg_atom (literal : Literal Atom) : literal.neg.atom = literal.atom := rfl

@[simp] theorem neg_neg (literal : Literal Atom) : literal.neg.neg = literal := by
  cases literal
  simp [neg]

@[simp] theorem eval_neg (assignment : Assignment Atom) (literal : Literal Atom) :
    literal.neg.eval assignment = !literal.eval assignment := by
  cases literal with
  | mk atom negative => cases negative <;> simp [neg, eval]

end Literal

/-- `total` completes `partial` when it agrees with every assigned atom. -/
def Completes (total : Assignment Atom) (known : PartialAssignment Atom) : Prop :=
  ∀ atom value, known atom = some value → total atom = value

/-- The information order on partial assignments. -/
def Refines (less more : PartialAssignment Atom) : Prop :=
  ∀ atom value, less atom = some value → more atom = some value

/-- The least informative partial assignment. -/
def bottom : PartialAssignment Atom := fun _ ↦ none

/-- Regard a total assignment as a maximally informative partial assignment. -/
def Assignment.toPartial (assignment : Assignment Atom) : PartialAssignment Atom :=
  fun atom ↦ some (assignment atom)

/-- Fill every unknown atom from a caller-selected fallback assignment. -/
def PartialAssignment.complete (known : PartialAssignment Atom)
    (fallback : Assignment Atom) : Assignment Atom := fun atom ↦
  (known atom).getD (fallback atom)

/-- A valuation-indexed claim holds under a partial assignment when it holds
under every total completion. -/
def Under (known : PartialAssignment Atom) (claim : Assignment Atom → Prop) : Prop :=
  ∀ total, Completes total known → claim total

/-- A syllogism is a claim valid without assigning any atom. -/
def Syllogism (claim : Assignment Atom → Prop) : Prop :=
  Under bottom claim

@[simp] theorem completes_bottom (total : Assignment Atom) :
    Completes total (bottom : PartialAssignment Atom) := by
  intro atom value known
  simp [bottom] at known

theorem refines_refl (known : PartialAssignment Atom) : Refines known known := by
  intro atom value
  exact id

theorem Refines.trans {first second third : PartialAssignment Atom}
    (firstSecond : Refines first second) (secondThird : Refines second third) :
    Refines first third := by
  intro atom value known
  exact secondThird atom value (firstSecond atom value known)

theorem bottom_refines (known : PartialAssignment Atom) :
    Refines (bottom : PartialAssignment Atom) known := by
  intro atom value known
  simp [bottom] at known

theorem Completes.of_refines {less more : PartialAssignment Atom}
    {total : Assignment Atom} (refines : Refines less more)
    (completes : Completes total more) : Completes total less := by
  intro atom value known
  exact completes atom value (refines atom value known)

/-- Adding assignments can only reduce the set of completions. -/
theorem Under.mono {less more : PartialAssignment Atom}
    {claim : Assignment Atom → Prop} (holds : Under less claim)
    (refines : Refines less more) : Under more claim := by
  intro total completes
  exact holds total (Completes.of_refines refines completes)

@[simp] theorem under_bottom_iff (claim : Assignment Atom → Prop) :
    Under (bottom : PartialAssignment Atom) claim ↔ ∀ total, claim total := by
  constructor
  · intro holds total
    exact holds total (completes_bottom total)
  · intro holds total _
    exact holds total

@[simp] theorem syllogism_iff (claim : Assignment Atom → Prop) :
    Syllogism claim ↔ ∀ total, claim total :=
  under_bottom_iff claim

theorem PartialAssignment.complete_completes (known : PartialAssignment Atom)
    (fallback : Assignment Atom) : Completes (known.complete fallback) known := by
  intro atom value known
  simp [PartialAssignment.complete, known]

theorem PartialAssignment.exists_completion (known : PartialAssignment Atom) :
    ∃ total, Completes total known :=
  ⟨known.complete (fun _ ↦ false), known.complete_completes _⟩

theorem completes_total_iff (candidate original : Assignment Atom) :
    Completes candidate original.toPartial ↔ candidate = original := by
  constructor
  · intro completes
    funext atom
    exact completes atom (original atom) rfl
  · rintro rfl
    intro atom value known
    simpa [Assignment.toPartial] using Option.some.inj known

@[simp] theorem under_total_iff (assignment : Assignment Atom)
    (claim : Assignment Atom → Prop) :
    Under assignment.toPartial claim ↔ claim assignment := by
  constructor
  · intro holds
    exact holds assignment ((completes_total_iff assignment assignment).2 rfl)
  · intro holds candidate completes
    rw [(completes_total_iff candidate assignment).1 completes]
    exact holds

end Nucleus.Classical
