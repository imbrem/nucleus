import Nucleus.Hol.Ethane.Typing
import Nucleus.HolE.Named.Semantics

/-!
# Ethane semantics

Ethane borrows the established HolE semantics through its constructor-preserving
embedding.  The unsorted semantics remains partial: rejected or ill-typed syntax
has no denotation.
-/

namespace Nucleus.Hol.Ethane

set_option relaxedAutoImplicit true

abbrev EmptySig := Nucleus.HolE.EmptySig
abbrev TypeEnv := Nucleus.HolE.TypeEnv
abbrev DenoteKind := Nucleus.HolE.DenoteKind
abbrev Pointed := Nucleus.HolE.Pointed
abbrev RawBoundEnv := Nucleus.HolE.RawBoundEnv

/-- A sorted Ethane family denotes through the named HolE embedding. -/
def DenotesFam (typeScope : TyScope types) (typeEnv : TypeEnv types)
    (family : Fam EmptySig kind) (semantic : DenoteKind kind) : Prop :=
  Kinded typeScope family ∧
    Nucleus.HolE.Named.DenotesFam typeScope typeEnv family.toHolE semantic

/-- A sorted Ethane term evaluates through the named HolE embedding. -/
def Eval (typeScope : TyScope types) (termScope : TmScope EmptySig depth)
    (typeEnv : TypeEnv types) (Γ : BoundCtx EmptySig types depth)
    (boundEnv : RawBoundEnv depth) (term : Tm EmptySig) (type : Ty EmptySig)
    (semantic : Pointed) (value : semantic.carrier) : Prop :=
  HasType typeScope termScope Γ term type ∧
    Nucleus.HolE.Named.Eval typeScope termScope typeEnv Γ boundEnv
      term.toHolE type.toHolE semantic value

theorem DenotesFam.kinded
    (denotation : DenotesFam typeScope typeEnv family semantic) :
    Kinded typeScope family :=
  denotation.1

theorem Eval.hasType (evaluation :
    Eval typeScope termScope typeEnv Γ boundEnv term type semantic value) :
    HasType typeScope termScope Γ term type :=
  evaluation.1

namespace Syn

/-- Unsorted family denotation checks the requested kind before evaluation. -/
def DenotesFam (typeScope : TyScope types) (typeEnv : TypeEnv types)
    (family : Syn EmptySig) (kind : Kind) (semantic : DenoteKind kind) : Prop :=
  ∃ sortedFamily,
    family.check (.kind kind) = some sortedFamily ∧
    Nucleus.Hol.Ethane.DenotesFam typeScope typeEnv sortedFamily semantic

/-- Unsorted term evaluation checks the term and its type before evaluation. -/
def Eval (typeScope : TyScope types) (termScope : TmScope EmptySig depth)
    (typeEnv : TypeEnv types) (Γ : BoundCtx EmptySig types depth)
    (boundEnv : RawBoundEnv depth) (term type : Syn EmptySig)
    (semantic : Pointed) (value : semantic.carrier) : Prop :=
  ∃ sortedTerm sortedType,
    term.check .tm = some sortedTerm ∧
    type.check (.kind .star) = some sortedType ∧
    Nucleus.Hol.Ethane.Eval typeScope termScope typeEnv Γ boundEnv
      sortedTerm sortedType semantic value

theorem DenotesFam.kinded
    (denotation : DenotesFam typeScope typeEnv family kind semantic) :
    Syn.Kinded typeScope family kind := by
  obtain ⟨sortedFamily, checked, denotation⟩ := denotation
  exact ⟨sortedFamily, .kind, checked, rfl, denotation.kinded⟩

theorem Eval.hasType
    (evaluation : Eval typeScope termScope typeEnv Γ boundEnv
      term type semantic value) :
    Syn.HasType typeScope termScope Γ term type := by
  obtain ⟨sortedTerm, sortedType, termCheck, typeCheck, evaluation⟩ := evaluation
  exact ⟨sortedTerm, .tm sortedType, termCheck,
    by simp [Syn.Classification.check, typeCheck], evaluation.hasType⟩

theorem not_denotesFam_of_check_eq_none
    (rejected : family.check (.kind kind) = none) :
    ¬DenotesFam typeScope typeEnv family kind semantic := by
  rintro ⟨_, checked, _⟩
  rw [rejected] at checked
  contradiction

theorem not_eval_of_term_check_eq_none
    (rejected : term.check .tm = none) :
    ¬Eval typeScope termScope typeEnv Γ boundEnv term type semantic value := by
  rintro ⟨_, _, checked, _⟩
  rw [rejected] at checked
  contradiction

theorem not_eval_of_type_check_eq_none
    (rejected : type.check (.kind .star) = none) :
    ¬Eval typeScope termScope typeEnv Γ boundEnv term type semantic value := by
  rintro ⟨_, _, _, checked, _⟩
  rw [rejected] at checked
  contradiction

end Syn

end Nucleus.Hol.Ethane
