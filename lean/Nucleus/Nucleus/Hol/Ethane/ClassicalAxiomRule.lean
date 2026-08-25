import Nucleus.Hol.Ethane.ClassicalMatrix

/-!
# What a premise-free axiom rule owes

`Kernel.push_axiom` — the hook `sub_exists` mints its conclusion through —
records the sequent `⊢ φ` for a Boolean term `φ` it has just built.  Nothing in
the classical layer checks that `φ` deserves it, and nothing can: the rule is
an *axiom*, so its warrant is semantic and comes from outside.

This file says exactly what that warrant is, so the obligation is a theorem
rather than a comment.  Two facts, and the pair is the point:

* `axiomSequent_not_sound` — the sequent is **not** universally sound.  A rule
  that minted it unconditionally would be wrong, which is why `push_axiom` is
  reachable only from a rule that has built `φ` itself and only in an arena
  that has declared the capability.
* `axiomSequent_holds_of_interpretation` — it holds under exactly those
  completions of a HOL interpretation that make `φ` true.

So the entire burden sits on "the sentence denotes true", which for the guarded
subtype package is `Nucleus.HolE.Empty.SubtypePackage.Eval.existsType_true`
together with the lowering that carries it to the named construction
(`Nucleus.Hol.Ethane.Subtype.Lower`, which does not yet reach that far).

## Why this is stated about a sequent and not about an arena

Theorems are kernel-local in Ethane: `Kernel` holds `thm` and `syl` alongside
its `Arena`, and neither is part of the arena's wire encoding or its address.
So `Arena.CoreKernelValid` is not neglecting them — they are not arena state,
and a conclusion does not survive serialization at all.  What *does* survive is
the capability in `axs` and the sentence row itself, which is what lets an
auditor see that an arena rested on the subtype axiom.

A serialized representation for derived conclusions is the `amb.thm` half of
the ambient-logic work, and a kernel-level soundness invariant belongs with it.
-/

namespace Nucleus.Hol.Ethane.ClassicalMatrix

set_option relaxedAutoImplicit true

variable {Atom : Type}

/-- The sequent a premise-free axiom rule mints: nothing on the left, one
single-literal cube on the right. -/
def axiomSequent (atom : Atom) : Sequent Atom :=
  ⟨⟨[]⟩, ⟨[⟨[(atom, false)]⟩]⟩⟩

/-- It holds under a valuation exactly when the concluded atom does. -/
@[simp] theorem axiomSequent_holds_iff (atom : Atom) (valuation : Valuation Atom) :
    (axiomSequent atom).Holds valuation ↔ valuation atom := by
  simp [axiomSequent, Sequent.Holds, Cnf.Holds, Dnf.Holds, Cube.Holds, Lit.Holds]

/-- It is therefore not universally sound, and could not be: an axiom rule's
warrant is semantic, so no structural check can supply it. -/
theorem axiomSequent_not_sound (atom : Atom) : ¬ (axiomSequent atom).Sound := by
  intro sound
  have holds := sound (fun _ => False)
  simp at holds

/-- The obligation in the form a HOL consumer discharges it.

If the interpretation knows the concluded atom to mean `proposition`, and
`proposition` is true, the minted sequent holds under *every* completion — the
unknown atoms are irrelevant, exactly as `Sound.holds_of_completion` arranges
for universally sound syllogisms. -/
theorem axiomSequent_holds_of_interpretation (atom : Atom)
    (interpretation : PartialValuation Atom) (proposition : Prop)
    (known : interpretation atom = some proposition) (truth : proposition)
    (valuation : Valuation Atom) (completion : valuation.Completes interpretation) :
    (axiomSequent atom).Holds valuation := by
  have agrees : valuation atom ↔ proposition := completion atom proposition known
  simpa using agrees.mpr truth

/-- Conversely, a false conclusion makes the sequent fail, so the rule cannot
be discharged by anything weaker than the truth of what it concludes. -/
theorem axiomSequent_fails_of_false (atom : Atom) (valuation : Valuation Atom)
    (falsity : ¬ valuation atom) : ¬ (axiomSequent atom).Holds valuation := by
  simpa using falsity

end Nucleus.Hol.Ethane.ClassicalMatrix
