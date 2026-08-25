import Nucleus.HolE.FreeRenaming
import Nucleus.HolE.Named.Lower

/-!
# Equivariance of named lowering

An injective renaming of source names commutes with lowering when scopes are
renamed at the same time.  This is the reusable alpha-renaming fact needed by
hygienic library macros.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

noncomputable local instance (priority := low) {α : Type _} : DecidableEq α :=
  Classical.decEq α

/-- Rename every name stored in a type-variable scope. -/
def TyScope.mapNames (rename : Nat → Nat) : TyScope types → TyScope types
  | .nil => .nil
  | .cons name rest => .cons (rename name) (rest.mapNames rename)

/-- Rename every declaration stored in a term-variable scope. -/
def TmScope.mapNames (rename : Nat → Nat) : TmScope Sig depth → TmScope Sig depth
  | .nil => .nil
  | .cons declaration rest =>
      .cons ⟨rename declaration.name, Named.mapNames rename declaration.sort⟩
        (rest.mapNames rename)

private noncomputable def inverseOnRange (rename : Nat → Nat) : Nat → Nat :=
  fun encoded => by
    classical
    exact if witness : ∃ name, rename name = encoded then Classical.choose witness else 0

private theorem inverseOnRange_apply (rename : Nat → Nat)
    (injective : Function.Injective rename) (name : Nat) :
    inverseOnRange rename (rename name) = name := by
  classical
  unfold inverseOnRange
  split
  · rename_i witness
    exact injective (Classical.choose_spec witness)
  · rename_i absent
    exact False.elim (absent ⟨name, rfl⟩)

theorem Expr.mapNames_injective (rename : Nat → Nat)
    (injective : Function.Injective rename) :
    Function.Injective (Named.mapNames (Sig := Sig) (sort := sort) rename) := by
  intro left right equality
  have mapped := congrArg (Named.mapNames (Sig := Sig) (sort := sort)
    (inverseOnRange rename)) equality
  rw [Named.mapNames_comp, Named.mapNames_comp] at mapped
  have composition : inverseOnRange rename ∘ rename = id :=
    funext (inverseOnRange_apply rename injective)
  simpa only [composition, Named.mapNames_id] using mapped

private theorem tmDecl_map_injective (rename : Nat → Nat)
    (injective : Function.Injective rename) :
    Function.Injective (fun declaration : TmDecl Sig =>
      (⟨rename declaration.name, Named.mapNames rename declaration.sort⟩ :
        TmDecl Sig)) := by
  intro left right equality
  cases left with
  | mk leftName leftType =>
      cases right with
      | mk rightName rightType =>
          simp only [Decl.mk.injEq] at equality ⊢
          exact ⟨injective equality.1,
            Expr.mapNames_injective rename injective equality.2⟩

theorem lookupTy_mapNames (rename : Nat → Nat) (injective : Function.Injective rename)
    (scope : TyScope types) (name : Nat) (kind : Kind) :
    lookupTy ⟨rename name, kind⟩ (scope.mapNames rename) = lookupTy ⟨name, kind⟩ scope := by
  induction scope with
  | nil => rfl
  | @cons types currentKind current rest ih =>
      simp only [TyScope.mapNames, lookupTy]
      by_cases names : name = current
      · subst current
        simp [ih]
      · have renamedNames : rename name ≠ rename current :=
          fun equality => names (injective equality)
        simp [names, renamedNames, ih]

theorem lookupTm_mapNames (rename : Nat → Nat) (injective : Function.Injective rename)
    (scope : TmScope Sig depth) (declaration : TmDecl Sig) :
    lookupTm
        ⟨rename declaration.name, Named.mapNames rename declaration.sort⟩
        (scope.mapNames rename) =
      lookupTm declaration scope := by
  induction scope with
  | nil => rfl
  | cons current rest ih =>
      simp only [TmScope.mapNames, lookupTm]
      by_cases same : declaration = current
      · subst current
        simp
      · have mappedDifferent :
          (⟨rename declaration.name, Named.mapNames rename declaration.sort⟩ : TmDecl Sig) ≠
            ⟨rename current.name, Named.mapNames rename current.sort⟩ :=
          fun equality => same (tmDecl_map_injective rename injective equality)
        simp [same, mappedDifferent, ih]

private def LoweringEquivariant (rename : Nat → Nat) :
    Expr Sig Nat sort → Prop :=
  match sort with
  | .kind _ => fun family => ∀ {types} (typeScope : TyScope types),
      lowerFam (typeScope.mapNames rename) (Named.mapNames rename family) =
        (lowerFam typeScope family).map (Nucleus.HolE.renameFv rename)
  | .tm => fun term => ∀ {types depth} (typeScope : TyScope types)
      (termScope : TmScope Sig depth),
      lowerTm (typeScope.mapNames rename) (termScope.mapNames rename)
          (Named.mapNames rename term) =
        (lowerTm typeScope termScope term).map (Nucleus.HolE.renameFv rename)

private theorem loweringEquivariant (rename : Nat → Nat)
    (injective : Function.Injective rename) (expression : Expr Sig Nat sort) :
    LoweringEquivariant rename expression := by
  induction expression with
  | boolTy =>
      intro types typeScope
      simp [Named.mapNames, lowerFam, Nucleus.HolE.renameFv]
  | arr domain codomain ihDomain ihCodomain =>
      intro types typeScope
      simp only [Named.mapNames, lowerFam]
      rw [ihDomain typeScope, ihCodomain typeScope]
      cases lowerFam typeScope domain <;>
        cases lowerFam typeScope codomain <;>
          simp [Nucleus.HolE.renameFv]
  | tyApp function argument ihFunction ihArgument =>
      intro types typeScope
      simp only [Named.mapNames, lowerFam]
      rw [ihFunction typeScope, ihArgument typeScope]
      cases lowerFam typeScope function <;>
        cases lowerFam typeScope argument <;>
          simp [Nucleus.HolE.renameFv]
  | @tyLam domain codomain name body ih =>
      intro types typeScope
      simp only [Named.mapNames, lowerFam]
      have bodyEq := ih (.cons (kind := domain) name typeScope)
      simp only [TyScope.mapNames] at bodyEq
      rw [bodyEq]
      cases lowerFam (.cons name typeScope) body <;>
        simp [Nucleus.HolE.renameFv]
  | tyFv name kind =>
      intro types typeScope
      simp only [Named.mapNames, lowerFam]
      rw [lookupTy_mapNames rename injective]
      cases lookupTy ⟨name, kind⟩ typeScope <;>
        simp [Nucleus.HolE.renameFv]
  | sub carrier name predicate ihCarrier ihPredicate =>
      intro types typeScope
      simp only [Named.mapNames, lowerFam]
      rw [ihCarrier typeScope]
      have predicateEq := ihPredicate typeScope (.cons ⟨name, carrier⟩ .nil)
      simp only [TmScope.mapNames] at predicateEq
      rw [predicateEq]
      cases lowerFam typeScope carrier <;>
        cases lowerTm typeScope (.cons ⟨name, carrier⟩ .nil) predicate <;>
          simp [Nucleus.HolE.renameFv]
  | tyExists name predicate ih =>
      intro types depth typeScope termScope
      simp only [Named.mapNames, lowerTm]
      have predicateEq := ih (.cons (kind := .star) name typeScope) .nil
      simp only [TyScope.mapNames, TmScope.mapNames] at predicateEq
      rw [predicateEq]
      cases lowerTm (.cons name typeScope) .nil predicate <;>
        simp [Nucleus.HolE.renameFv]
  | tyForall name predicate ih =>
      intro types depth typeScope termScope
      simp only [Named.mapNames, lowerTm]
      have predicateEq := ih (.cons (kind := .star) name typeScope) .nil
      simp only [TyScope.mapNames, TmScope.mapNames] at predicateEq
      rw [predicateEq]
      cases lowerTm (.cons name typeScope) .nil predicate <;>
        simp [Nucleus.HolE.renameFv]
  | model name predicate ih =>
      intro types typeScope
      simp only [Named.mapNames, lowerFam]
      have predicateEq := ih (.cons (kind := .star) name typeScope) .nil
      simp only [TyScope.mapNames, TmScope.mapNames] at predicateEq
      rw [predicateEq]
      cases lowerTm (.cons name typeScope) .nil predicate <;>
        simp [Nucleus.HolE.renameFv]
  | primFam symbol =>
      intro types typeScope
      simp [Named.mapNames, lowerFam, Nucleus.HolE.renameFv]
  | primTm symbol =>
      intro types depth typeScope termScope
      simp [Named.mapNames, lowerTm, Nucleus.HolE.renameFv]
  | tmFv name type ih =>
      intro types depth typeScope termScope
      simp only [Named.mapNames, lowerTm]
      have lookupEq := lookupTm_mapNames rename injective termScope ⟨name, type⟩
      rw [lookupEq, ih typeScope]
      cases lookupTm ⟨name, type⟩ termScope <;>
        cases lowerFam typeScope type <;>
          simp [Nucleus.HolE.renameFv]
  | app function argument ihFunction ihArgument =>
      intro types depth typeScope termScope
      simp only [Named.mapNames, lowerTm]
      rw [ihFunction typeScope termScope, ihArgument typeScope termScope]
      cases lowerTm typeScope termScope function <;>
        cases lowerTm typeScope termScope argument <;>
          simp [Nucleus.HolE.renameFv]
  | lam name domain body ihDomain ihBody =>
      intro types depth typeScope termScope
      simp only [Named.mapNames, lowerTm]
      rw [ihDomain typeScope]
      have bodyEq := ihBody typeScope (.cons ⟨name, domain⟩ termScope)
      simp only [TmScope.mapNames] at bodyEq
      rw [bodyEq]
      cases lowerFam typeScope domain <;>
        cases lowerTm typeScope (.cons ⟨name, domain⟩ termScope) body <;>
          simp [Nucleus.HolE.renameFv]
  | bool value =>
      intro types depth typeScope termScope
      simp [Named.mapNames, lowerTm, Nucleus.HolE.renameFv]
  | eq type left right ihType ihLeft ihRight =>
      intro types depth typeScope termScope
      simp only [Named.mapNames, lowerTm]
      rw [ihType typeScope, ihLeft typeScope termScope, ihRight typeScope termScope]
      cases lowerFam typeScope type <;>
        cases lowerTm typeScope termScope left <;>
          cases lowerTm typeScope termScope right <;>
            simp [Nucleus.HolE.renameFv]
  | eps type predicate ihType ihPredicate =>
      intro types depth typeScope termScope
      simp only [Named.mapNames, lowerTm]
      rw [ihType typeScope, ihPredicate typeScope termScope]
      cases lowerFam typeScope type <;>
        cases lowerTm typeScope termScope predicate <;>
          simp [Nucleus.HolE.renameFv]
  | abs carrier name predicate value ihCarrier ihPredicate ihValue =>
      intro types depth typeScope termScope
      simp only [Named.mapNames, lowerTm]
      rw [ihCarrier typeScope]
      have predicateEq := ihPredicate typeScope (.cons ⟨name, carrier⟩ .nil)
      simp only [TmScope.mapNames] at predicateEq
      rw [predicateEq, ihValue typeScope termScope]
      cases lowerFam typeScope carrier <;>
        cases lowerTm typeScope (.cons ⟨name, carrier⟩ .nil) predicate <;>
          cases lowerTm typeScope termScope value <;>
            simp [Nucleus.HolE.renameFv]
  | rep carrier name predicate value ihCarrier ihPredicate ihValue =>
      intro types depth typeScope termScope
      simp only [Named.mapNames, lowerTm]
      rw [ihCarrier typeScope]
      have predicateEq := ihPredicate typeScope (.cons ⟨name, carrier⟩ .nil)
      simp only [TmScope.mapNames] at predicateEq
      rw [predicateEq, ihValue typeScope termScope]
      cases lowerFam typeScope carrier <;>
        cases lowerTm typeScope (.cons ⟨name, carrier⟩ .nil) predicate <;>
          cases lowerTm typeScope termScope value <;>
            simp [Nucleus.HolE.renameFv]

theorem lower_mapNames (rename : Nat → Nat) (injective : Function.Injective rename)
    (typeScope : TyScope types) (termScope : TmScope Sig depth)
    (expression : Expr Sig Nat sort) :
    lower (typeScope.mapNames rename) (termScope.mapNames rename)
        (Named.mapNames rename expression) =
      (lower typeScope termScope expression).map (Nucleus.HolE.renameFv rename) := by
  cases sort with
  | kind kind => exact loweringEquivariant rename injective expression typeScope
  | tm => exact loweringEquivariant rename injective expression typeScope termScope

@[simp] theorem lowerFam_mapNames_nil (rename : Nat → Nat)
    (injective : Function.Injective rename)
    (family : Fam Sig kind) :
    lowerFam .nil (Named.mapNames rename family) =
      (lowerFam .nil family).map (Nucleus.HolE.renameFv rename) :=
  lower_mapNames rename injective .nil .nil family

@[simp] theorem lowerTm_mapNames_nil (rename : Nat → Nat)
    (injective : Function.Injective rename)
    (term : Tm Sig) :
    lowerTm .nil .nil (Named.mapNames rename term) =
      (lowerTm .nil .nil term).map (Nucleus.HolE.renameFv rename) :=
  lower_mapNames rename injective .nil .nil term

end Nucleus.HolE.Named
