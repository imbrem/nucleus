import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Nucleus.Hol.Intrinsic

/-! # Genuinely finite semantics for the empty HOL signature -/

namespace Nucleus.Hol.Finite

instance : FamilyModel FiniteSig where
  denote symbol := nomatch symbol

instance : TermModel FiniteSig where
  denote symbol := nomatch symbol

/-- With no signature symbols and no type-level lambda, there is no closed
family expression of higher kind. -/
theorem noHigherFamily : {kind : Kind} → Fam kind → kind ≠ .star → False
  | _, .primFam symbol, _ => nomatch symbol
  | _, .tyApp function argument, notStar =>
      noHigherFamily function (by simp)

/-- Every semantic carrier denoted by an empty-signature HOL type can be
enumerated. -/
noncomputable def fintypeDenote : (A : Ty) → Fintype (DenoteTy A)
  | .primFam symbol => nomatch symbol
  | .boolTy => inferInstance
  | .arr A B => by
      letI := fintypeDenote A
      letI := fintypeDenote B
      letI := Classical.decEq (DenoteTy A)
      change Fintype (DenoteTy A → DenoteTy B)
      infer_instance
  | .tyApp function argument => False.elim (noHigherFamily function (by simp))
  | .sub A _ => fintypeDenote A

noncomputable instance (A : Ty) : Fintype (DenoteTy A) := fintypeDenote A

/-- In particular, every empty-signature semantic carrier is finite. -/
theorem finiteDenote (A : Ty) : _root_.Finite (DenoteTy A) := inferInstance

/-- The semantic universe of each well-formed empty-signature type is a finite,
inhabited type. -/
def finitePointed (A : Ty) : Pointed where
  carrier := DenoteTy A
  point := defaultValue A

theorem false_unprovable :
    ¬ Nonempty (Nucleus.Hol.Proves (emptyBound : BoundCtx FiniteSig 0) [] (.bool false)) := by
  rintro ⟨proof⟩
  have evaluation := proof.sound defaultFreeEnv emptyBoundEnv (by
    intro proposition member
    simp at member)
  cases evaluation

/-- Kernel consistency follows immediately from the finite model. -/
theorem consistency :
    ¬ Nonempty (Intrinsic.Proves (emptyBound : BoundCtx FiniteSig 0) []
      (Checked.boolean false)) := by
  intro proof
  exact false_unprovable (Intrinsic.proves_iff_kernel.mp proof)

end Nucleus.Hol.Finite
