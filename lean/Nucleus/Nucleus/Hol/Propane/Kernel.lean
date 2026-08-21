import Nucleus.Hol.Propane.Syntax

/-!
# Propane proof theory

The judgments mention only intrinsically typed terms.  Consequently there are
no typing premises to forget, serialize, or accidentally trust.  Beta and eta
are ordinary typed constructors, while `junk` has no distinguished proof rule.
-/

namespace Nucleus.Hol.Propane

universe u
set_option relaxedAutoImplicit true

/-- Typed term equality. -/
inductive EqTm : {Γ : List Ty} → {A : Ty} → Tm Γ A → Tm Γ A → Type where
  | refl (term : Tm Γ A) : EqTm term term
  | symm : EqTm left right → EqTm right left
  | trans : EqTm left middle → EqTm middle right → EqTm left right
  | app : EqTm function function' → EqTm argument argument' →
      EqTm (.app function argument) (.app function' argument')
  | lam : EqTm body body' → EqTm (.lam body) (.lam body')
  | eq : EqTm left left' → EqTm right right' →
      EqTm (.eq left right) (.eq left' right')
  | eps : EqTm predicate predicate' → EqTm (.eps predicate) (.eps predicate')
  | beta (body : Tm (A :: Γ) B) (argument : Tm Γ A) :
      EqTm (.app (.lam body) argument) (body.open argument)
  | eta (function : Tm Γ (.arr A B)) :
      EqTm (.lam (.app (function.rename weakenRen) (.bv .zero))) function

abbrev Hyps (Γ : List Ty) := List (Wff Γ)

/-- A small LCF-style HOL proof system over intrinsically typed syntax. -/
inductive Proves : {Γ : List Ty} → Hyps Γ → Wff Γ → Type where
  | hyp (member : proposition ∈ hypotheses) : Proves hypotheses proposition
  | truth : Proves hypotheses (.bool true)
  | falseElim : Proves hypotheses (.bool false) → Proves hypotheses proposition
  | boolCases : Proves (proposition :: hypotheses) conclusion →
      Proves (.eq proposition (.bool false) :: hypotheses) conclusion →
      Proves hypotheses conclusion
  | eqRefl (term : Tm Γ A) : Proves hypotheses (.eq term term)
  | eqMp (predicate : Tm Γ (.arr A .bool)) :
      Proves hypotheses (.eq left right) → Proves hypotheses (.app predicate left) →
      Proves hypotheses (.app predicate right)
  | choice (predicate : Tm Γ (.arr A .bool)) (witness : Tm Γ A) :
      Proves hypotheses (.app predicate witness) →
      Proves hypotheses (.app predicate (.eps predicate))
  | generalize (body : Tm (A :: Γ) .bool) :
      Proves (hypotheses.map (Tm.rename weakenRen)) body →
      Proves hypotheses (.eq (.lam body) (.lam (.bool true)))
  | hypothesisMap (subset : ∀ proposition, proposition ∈ source → proposition ∈ target) :
      Proves source conclusion → Proves target conclusion
  | convert : EqTm left right → Proves hypotheses left → Proves hypotheses right
  | eqOfEqTm : EqTm left right → Proves hypotheses (.eq left right)
  | antisymm : Proves (left :: hypotheses) right → Proves (right :: hypotheses) left →
      Proves hypotheses (.eq left right)

namespace Proves

/-- Adding an unused, already typed proposition is admissible without a
separate typing side condition. -/
def weaken {Γ : List Ty} {hypotheses : Hyps Γ} {conclusion proposition : Wff Γ}
    (proof : Proves hypotheses conclusion) :
    Proves (proposition :: hypotheses) conclusion :=
  .hypothesisMap (fun _ member => List.mem_cons_of_mem _ member) proof

/-- Every conclusion is Boolean by the index of `Proves`; this is the entire
typing-preservation theorem for the proof system. -/
theorem conclusion_is_typed {Γ : List Ty} {hypotheses : Hyps Γ}
    {conclusion : Wff Γ} (_proof : Proves hypotheses conclusion) :
    ∃ term : Tm Γ .bool, term = conclusion :=
  ⟨conclusion, rfl⟩

end Proves

end Nucleus.Hol.Propane
