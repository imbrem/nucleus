import Nucleus.HolE.Named.Semantics
import Nucleus.HolE.Named.Unsorted.Typing

/-!
# Semantics of unsorted named HolE

The semantics is the exact pullback of named HolE semantics through the sort
checker. An expression denotes only when its requested sort checks, so malformed
and ill-kinded expressions have no semantics.
-/

namespace Nucleus.HolE.Named.Unsorted

set_option relaxedAutoImplicit true

abbrev EmptySig := Named.EmptySig

/-- An unsorted family denotes when checking it produces a sorted named family
with the corresponding named semantics. -/
def DenotesFam {types : List Kind} {kind : Kind}
    (typeScope : Named.TyScope types)
    (typeEnv : Nucleus.HolE.TypeEnv types)
    (family : Expr EmptySig)
    (semantic : Nucleus.HolE.DenoteKind kind) : Prop :=
  ∃ sortedFamily,
    check (.kind kind) family = some sortedFamily ∧
    Named.Kinded typeScope sortedFamily ∧
    Named.DenotesFam typeScope typeEnv sortedFamily semantic

/-- Evaluation of an unsorted term checks both the term and its type before
using the named semantics. -/
def Eval {types : List Kind} {depth : Nat}
    (typeScope : Named.TyScope types)
    (termScope : Named.TmScope EmptySig depth)
    (typeEnv : Nucleus.HolE.TypeEnv types)
    (Γ : Nucleus.HolE.BoundCtx EmptySig types depth)
    (boundEnv : Nucleus.HolE.RawBoundEnv depth)
    (term type : Expr EmptySig)
    (semantic : Nucleus.HolE.Pointed)
    (value : semantic.carrier) : Prop :=
  ∃ sortedTerm sortedType,
    check .tm term = some sortedTerm ∧
    check (.kind .star) type = some sortedType ∧
    Named.HasType typeScope termScope Γ sortedTerm sortedType ∧
    Named.Eval typeScope termScope typeEnv Γ boundEnv
      sortedTerm sortedType semantic value

theorem DenotesFam.sound {types : List Kind} {kind : Kind}
    {typeScope : Named.TyScope types}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {family : Expr EmptySig}
    {semantic : Nucleus.HolE.DenoteKind kind}
    (denotation : DenotesFam typeScope typeEnv family semantic) :
    ∃ sortedFamily,
      check (.kind kind) family = some sortedFamily ∧
      Named.Kinded typeScope sortedFamily ∧
      Named.DenotesFam typeScope typeEnv sortedFamily semantic :=
  denotation

theorem DenotesFam.complete {types : List Kind} {kind : Kind}
    {typeScope : Named.TyScope types}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {family : Expr EmptySig}
    {semantic : Nucleus.HolE.DenoteKind kind}
    {sortedFamily : Named.Fam EmptySig kind}
    (checked : check (.kind kind) family = some sortedFamily)
    (kinding : Named.Kinded typeScope sortedFamily)
    (denotation : Named.DenotesFam typeScope typeEnv sortedFamily semantic) :
    DenotesFam typeScope typeEnv family semantic :=
  ⟨sortedFamily, checked, kinding, denotation⟩

theorem Eval.sound {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types}
    {termScope : Named.TmScope EmptySig depth}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {Γ : Nucleus.HolE.BoundCtx EmptySig types depth}
    {boundEnv : Nucleus.HolE.RawBoundEnv depth}
    {term type : Expr EmptySig}
    {semantic : Nucleus.HolE.Pointed} {value : semantic.carrier}
    (evaluation : Eval typeScope termScope typeEnv Γ boundEnv term type semantic value) :
    ∃ sortedTerm sortedType,
      check .tm term = some sortedTerm ∧
      check (.kind .star) type = some sortedType ∧
      Named.HasType typeScope termScope Γ sortedTerm sortedType ∧
      Named.Eval typeScope termScope typeEnv Γ boundEnv
        sortedTerm sortedType semantic value :=
  evaluation

theorem Eval.complete {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types}
    {termScope : Named.TmScope EmptySig depth}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {Γ : Nucleus.HolE.BoundCtx EmptySig types depth}
    {boundEnv : Nucleus.HolE.RawBoundEnv depth}
    {term type : Expr EmptySig}
    {semantic : Nucleus.HolE.Pointed} {value : semantic.carrier}
    {sortedTerm : Named.Tm EmptySig} {sortedType : Named.Ty EmptySig}
    (termCheck : check .tm term = some sortedTerm)
    (typeCheck : check (.kind .star) type = some sortedType)
    (typing : Named.HasType typeScope termScope Γ sortedTerm sortedType)
    (evaluation : Named.Eval typeScope termScope typeEnv Γ boundEnv
      sortedTerm sortedType semantic value) :
    Eval typeScope termScope typeEnv Γ boundEnv term type semantic value :=
  ⟨sortedTerm, sortedType, termCheck, typeCheck, typing, evaluation⟩

/-- Denotation entails kinding in the unsorted typing relation. -/
theorem DenotesFam.kinded {types : List Kind} {kind : Kind}
    {typeScope : Named.TyScope types}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {family : Expr EmptySig}
    {semantic : Nucleus.HolE.DenoteKind kind}
    (denotation : DenotesFam typeScope typeEnv family semantic) :
    Kinded typeScope family kind := by
  obtain ⟨sortedFamily, checked, kinding, _⟩ := denotation
  exact Checks.complete checked rfl kinding

/-- Evaluation entails typing in the unsorted typing relation. -/
theorem Eval.hasType {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types}
    {termScope : Named.TmScope EmptySig depth}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {Γ : Nucleus.HolE.BoundCtx EmptySig types depth}
    {boundEnv : Nucleus.HolE.RawBoundEnv depth}
    {term type : Expr EmptySig}
    {semantic : Nucleus.HolE.Pointed} {value : semantic.carrier}
    (evaluation : Eval typeScope termScope typeEnv Γ boundEnv term type semantic value) :
    HasType typeScope termScope Γ term type := by
  obtain ⟨sortedTerm, sortedType, termCheck, typeCheck, typing, _⟩ := evaluation
  exact Checks.complete termCheck (by simp [checkClassification, typeCheck]) typing

theorem not_denotesFam_of_not_kinded {types : List Kind} {kind : Kind}
    {typeScope : Named.TyScope types}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {family : Expr EmptySig}
    {semantic : Nucleus.HolE.DenoteKind kind}
    (illKinded : ¬Kinded typeScope family kind) :
    ¬DenotesFam typeScope typeEnv family semantic :=
  fun denotation => illKinded denotation.kinded

theorem not_eval_of_not_hasType {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types}
    {termScope : Named.TmScope EmptySig depth}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {Γ : Nucleus.HolE.BoundCtx EmptySig types depth}
    {boundEnv : Nucleus.HolE.RawBoundEnv depth}
    {term type : Expr EmptySig}
    {semantic : Nucleus.HolE.Pointed} {value : semantic.carrier}
    (illTyped : ¬HasType typeScope termScope Γ term type) :
    ¬Eval typeScope termScope typeEnv Γ boundEnv term type semantic value :=
  fun evaluation => illTyped evaluation.hasType

/-- Every sorted named family denotation has an unsorted preimage. -/
theorem DenotesFam.ofSorted {types : List Kind} {kind : Kind}
    {typeScope : Named.TyScope types}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {family : Named.Fam EmptySig kind}
    {semantic : Nucleus.HolE.DenoteKind kind}
    (kinding : Named.Kinded typeScope family)
    (denotation : Named.DenotesFam typeScope typeEnv family semantic) :
    DenotesFam typeScope typeEnv (erase family) semantic :=
  ⟨family, check_erase family, kinding, denotation⟩

/-- Every sorted named evaluation has an unsorted preimage. -/
theorem Eval.ofSorted {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types}
    {termScope : Named.TmScope EmptySig depth}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {Γ : Nucleus.HolE.BoundCtx EmptySig types depth}
    {boundEnv : Nucleus.HolE.RawBoundEnv depth}
    {term : Named.Tm EmptySig} {type : Named.Ty EmptySig}
    {semantic : Nucleus.HolE.Pointed} {value : semantic.carrier}
    (typing : Named.HasType typeScope termScope Γ term type)
    (evaluation : Named.Eval typeScope termScope typeEnv Γ boundEnv
      term type semantic value) :
    Eval typeScope termScope typeEnv Γ boundEnv
      (erase term) (erase type) semantic value :=
  ⟨term, type, check_erase term, check_erase type, typing, evaluation⟩

theorem not_denotesFam_of_check_eq_none {types : List Kind} {kind : Kind}
    {typeScope : Named.TyScope types}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {family : Expr EmptySig}
    {semantic : Nucleus.HolE.DenoteKind kind}
    (rejected : check (.kind kind) family = none) :
    ¬DenotesFam typeScope typeEnv family semantic := by
  intro denotation
  obtain ⟨_, checked, _, _⟩ := denotation
  rw [rejected] at checked
  contradiction

theorem not_eval_of_term_check_eq_none {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types}
    {termScope : Named.TmScope EmptySig depth}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {Γ : Nucleus.HolE.BoundCtx EmptySig types depth}
    {boundEnv : Nucleus.HolE.RawBoundEnv depth}
    {term type : Expr EmptySig}
    {semantic : Nucleus.HolE.Pointed} {value : semantic.carrier}
    (rejected : check .tm term = none) :
    ¬Eval typeScope termScope typeEnv Γ boundEnv term type semantic value := by
  intro evaluation
  obtain ⟨_, _, checked, _, _, _⟩ := evaluation
  rw [rejected] at checked
  contradiction

theorem not_eval_of_type_check_eq_none {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types}
    {termScope : Named.TmScope EmptySig depth}
    {typeEnv : Nucleus.HolE.TypeEnv types}
    {Γ : Nucleus.HolE.BoundCtx EmptySig types depth}
    {boundEnv : Nucleus.HolE.RawBoundEnv depth}
    {term type : Expr EmptySig}
    {semantic : Nucleus.HolE.Pointed} {value : semantic.carrier}
    (rejected : check (.kind .star) type = none) :
    ¬Eval typeScope termScope typeEnv Γ boundEnv term type semantic value := by
  intro evaluation
  obtain ⟨_, _, _, checked, _, _⟩ := evaluation
  rw [rejected] at checked
  contradiction

end Nucleus.HolE.Named.Unsorted
