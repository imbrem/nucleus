import Mathlib.Logic.Basic

/-!
# Total subtypes

`{x : α // P x ∨ ¬∃ y, P y}` — the subtype of `P`, made inhabited by falling
back to all of `α` when `P` is empty. This is what lets `abs` be a total
function while `rep ∘ abs` is still the identity *on* the subtype, which is
exactly the pair of laws the `ABS_REP`/`REP_ABS` rules need.

This is what the `ABS_REP` and `REP_ABS` rules need: `abs` must be total, so
it has to do something when the predicate is empty, and falling back to all of
`α` is the choice that keeps `rep ∘ abs` the identity *on* the subtype.
-/

universe u

namespace Nucleus.HolOmega

def TotalSubtype (α : Type u) (P : α → Prop) :=
  {x : α // P x ∨ ¬∃ y, P y}

namespace TotalSubtype

def rep {α : Type u} {P : α → Prop} : TotalSubtype α P → α :=
  Subtype.val

noncomputable def abs {α : Type u} [Inhabited α] (P : α → Prop) :
    α → TotalSubtype α P := by
  classical
  intro x
  exact if hx : P x then ⟨x, Or.inl hx⟩
    else if hP : ∃ y, P y then
      ⟨Classical.choose hP, Or.inl (Classical.choose_spec hP)⟩
    else ⟨x, Or.inr hP⟩

noncomputable instance {α : Type u} [Inhabited α] (P : α → Prop) :
    Inhabited (TotalSubtype α P) where
  default := abs P default

@[simp]
theorem rep_abs_of {α : Type u} [Inhabited α] {P : α → Prop}
    {x : α} (hx : P x) : rep (abs P x) = x := by
  classical
  simp [abs, hx, rep]

@[simp]
theorem abs_rep {α : Type u} [Inhabited α] {P : α → Prop}
    (x : TotalSubtype α P) : abs P (rep x) = x := by
  classical
  apply Subtype.ext
  rcases x.property with hx | hP
  · simp [abs, rep, hx]
  · have hx : ¬P x.val := fun hp => hP ⟨x.val, hp⟩
    simp [abs, rep, hx, hP]

theorem nonempty {α : Type u} [Inhabited α] (P : α → Prop) :
    Nonempty (TotalSubtype α P) :=
  ⟨abs P default⟩

end TotalSubtype

end Nucleus.HolOmega
