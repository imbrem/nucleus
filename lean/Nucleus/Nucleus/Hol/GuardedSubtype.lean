import Mathlib.Logic.Equiv.Defs

/-! # Always-inhabited guarded subtype semantics -/

namespace Nucleus.Hol

/-- The low-level HOL subtype used by the kernel.  If `predicate` has a
witness this is the ordinary subtype; if it is empty, every carrier value is
admitted. -/
def GuardedSubtype (carrier : Type u) (predicate : carrier → Prop) :=
  {value : carrier // predicate value ∨ ¬ ∃ witness, predicate witness}

namespace GuardedSubtype

variable {carrier : Type u} {predicate : carrier → Prop}

def rep (value : GuardedSubtype carrier predicate) : carrier := value.1

/-- Total abstraction.  A value outside a nonempty predicate is sent to an
arbitrary witness; in the empty case it represents itself. -/
noncomputable def abs (value : carrier) : GuardedSubtype carrier predicate := by
  classical
  by_cases satisfies : predicate value
  · exact ⟨value, .inl satisfies⟩
  · by_cases inhabited : ∃ witness, predicate witness
    · exact ⟨Classical.choose inhabited, .inl (Classical.choose_spec inhabited)⟩
    · exact ⟨value, .inr inhabited⟩

theorem abs_rep (value : GuardedSubtype carrier predicate) :
    abs (rep value) = value := by
  apply Subtype.ext
  classical
  by_cases satisfies : predicate value.1
  · simp [abs, rep, satisfies]
  · have empty : ¬ ∃ witness, predicate witness := by
      intro inhabited
      exact value.2.elim satisfies (fun notInhabited => notInhabited inhabited)
    simp [abs, rep, satisfies, empty]

theorem rep_abs_of (value : carrier) (satisfies : predicate value) :
    rep (predicate := predicate) (abs (predicate := predicate) value) = value := by
  classical
  simp [abs, rep, satisfies]

theorem predicate_rep_of_witness (value : GuardedSubtype carrier predicate)
    {witness : carrier} (witnessSatisfies : predicate witness) :
    predicate (rep value) := by
  exact value.2.elim id fun empty => False.elim (empty ⟨witness, witnessSatisfies⟩)

instance [Nonempty carrier] : Nonempty (GuardedSubtype carrier predicate) :=
  ⟨abs (predicate := predicate) (Classical.choice (inferInstance : Nonempty carrier))⟩

/-- Once a witness is known, the guarded carrier is equivalent to the ordinary
subtype. -/
noncomputable def equivSubtype (witness : carrier) (witnessSatisfies : predicate witness) :
    GuardedSubtype carrier predicate ≃ {value : carrier // predicate value} where
  toFun value := ⟨rep value, predicate_rep_of_witness value witnessSatisfies⟩
  invFun value := ⟨value.1, .inl value.2⟩
  left_inv value := by apply Subtype.ext; rfl
  right_inv value := by apply Subtype.ext; rfl

/-- If the predicate is empty, the guard makes the subtype equivalent to its
entire carrier. -/
noncomputable def equivCarrier (empty : ¬ ∃ witness, predicate witness) :
    GuardedSubtype carrier predicate ≃ carrier where
  toFun := rep
  invFun value := ⟨value, .inr empty⟩
  left_inv value := by apply Subtype.ext; rfl
  right_inv _ := rfl

end GuardedSubtype

end Nucleus.Hol
