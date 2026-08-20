import Nucleus.HolE.Named.Unsorted.ProofRules

/-!
# Derived Boolean connectives for unsorted named HolE

The surface connectives are macros from `Macros`.  This file proves that their
hygienic binder lowers predictably and supplies checked construction and proof
laws without adding syntax or kernel rules.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

namespace TmScope

/-- Two term scopes implement a bound-variable renaming away from one reserved
name.  The exception is exactly the fresh binder inserted by conjunction. -/
def RenamesExcept (fresh : Nat) (ρ : Fin sourceDepth → Fin targetDepth)
    (source : TmScope Sig sourceDepth) (target : TmScope Sig targetDepth) : Prop :=
  ∀ wanted, wanted.name ≠ fresh →
    lookupTm wanted target = (lookupTm wanted source).map ρ

theorem RenamesExcept.cons {Sig : Signature}
    {source : TmScope Sig sourceDepth} {target : TmScope Sig targetDepth}
    (relation : RenamesExcept fresh ρ source target)
    (current : TmDecl Sig) :
    RenamesExcept fresh (Nucleus.HolE.liftRen ρ)
      (.cons current source) (.cons current target) := by
  intro wanted notFresh
  by_cases same : wanted = current
  · subst wanted
    simp [lookupTm, Nucleus.HolE.liftRen]
  · simp only [lookupTm, same, relation wanted notFresh]
    cases lookupTm wanted source <;> rfl

theorem renamesExcept_freshCons (fresh : Nat) (type : Ty Sig)
    (scope : TmScope Sig depth) :
    RenamesExcept fresh Fin.succ scope (.cons ⟨fresh, type⟩ scope) := by
  intro wanted notFresh
  have different : wanted ≠ (⟨fresh, type⟩ : TmDecl Sig) := by
    intro equality
    exact notFresh (congrArg Decl.name equality)
  simp [lookupTm, different]

end TmScope

/-- Lowering commutes with a scope renaming when a reserved name does not
occur anywhere in the named term.  Counting binder names as occurrences makes
the freshness premise deliberately strong and the implementation auditable. -/
theorem lowerTm_renameExcept
    {expression : Tm Sig} {lowered : Nucleus.HolE.Tm Sig types sourceDepth}
    (freshness : fresh ∉ Unsorted.names (Unsorted.erase expression))
    (scopes : TmScope.RenamesExcept fresh ρ sourceScope targetScope)
    (lowering : lowerTm typeScope sourceScope expression = some lowered) :
    lowerTm typeScope targetScope expression =
      some (Nucleus.HolE.rename ρ lowered) := by
  cases expression with
  | tyExists name predicate =>
      cases predicateLowering : lowerTm (.cons name typeScope) .nil predicate with
      | none =>
          simp only [lowerTm] at lowering
          rw [predicateLowering] at lowering
          simp at lowering
      | some loweredPredicate =>
          simp only [lowerTm] at lowering
          rw [predicateLowering] at lowering
          simp at lowering
          subst lowered
          simp [lowerTm, predicateLowering, Nucleus.HolE.rename]
  | primTm symbol =>
      simp [lowerTm] at lowering
      subst lowered
      simp [lowerTm, Nucleus.HolE.rename]
  | tmFv name type =>
      have nameNe : name ≠ fresh := by
        intro equality
        subst name
        simp [Unsorted.names, Unsorted.erase] at freshness
      have lookup := scopes ⟨name, type⟩ nameNe
      cases sourceLookup : lookupTm ⟨name, type⟩ sourceScope with
      | none =>
          have targetLookup : lookupTm ⟨name, type⟩ targetScope = none := by
            simpa [sourceLookup] using lookup
          cases typeLowering : lowerFam typeScope type with
          | none => simp [lowerTm, sourceLookup, typeLowering] at lowering
          | some loweredType =>
              simp [lowerTm, sourceLookup, typeLowering] at lowering
              subst lowered
              simp [lowerTm, targetLookup, typeLowering, Nucleus.HolE.rename]
      | some index =>
          have targetLookup :
              lookupTm ⟨name, type⟩ targetScope = some (ρ index) := by
            simpa [sourceLookup] using lookup
          simp [lowerTm, sourceLookup] at lowering
          subst lowered
          simp [lowerTm, targetLookup]
  | app function argument =>
      have freshParts :
          fresh ∉ Unsorted.names (Unsorted.erase function) ∧
          fresh ∉ Unsorted.names (Unsorted.erase argument) := by
        simpa [Unsorted.names, Unsorted.erase] using freshness
      cases functionLowering : lowerTm typeScope sourceScope function with
      | none => simp [lowerTm, functionLowering] at lowering
      | some loweredFunction =>
          cases argumentLowering : lowerTm typeScope sourceScope argument with
          | none => simp [lowerTm, functionLowering, argumentLowering] at lowering
          | some loweredArgument =>
              simp [lowerTm, functionLowering, argumentLowering] at lowering
              subst lowered
              have functionTarget := lowerTm_renameExcept freshParts.1 scopes
                functionLowering
              have argumentTarget := lowerTm_renameExcept freshParts.2 scopes
                argumentLowering
              simp [lowerTm, functionTarget, argumentTarget, Nucleus.HolE.rename]
  | lam name domain body =>
      have freshParts : fresh ≠ name ∧
          fresh ∉ Unsorted.names (Unsorted.erase domain) ∧
          fresh ∉ Unsorted.names (Unsorted.erase body) := by
        simpa [Unsorted.names, Unsorted.erase] using freshness
      cases domainLowering : lowerFam typeScope domain with
      | none => simp [lowerTm, domainLowering] at lowering
      | some loweredDomain =>
          cases bodyLowering : lowerTm typeScope (.cons ⟨name, domain⟩ sourceScope) body with
          | none => simp [lowerTm, domainLowering, bodyLowering] at lowering
          | some loweredBody =>
              simp [lowerTm, domainLowering, bodyLowering] at lowering
              subst lowered
              have bodyTarget := lowerTm_renameExcept freshParts.2.2
                (TmScope.RenamesExcept.cons scopes ⟨name, domain⟩) bodyLowering
              simp [lowerTm, domainLowering, bodyTarget, Nucleus.HolE.rename]
  | bool value =>
      simp [lowerTm] at lowering
      subst lowered
      simp [lowerTm, Nucleus.HolE.rename]
  | eq type left right =>
      have freshParts :
          fresh ∉ Unsorted.names (Unsorted.erase type) ∧
          fresh ∉ Unsorted.names (Unsorted.erase left) ∧
          fresh ∉ Unsorted.names (Unsorted.erase right) := by
        simpa [Unsorted.names, Unsorted.erase] using freshness
      cases typeLowering : lowerFam typeScope type with
      | none => simp [lowerTm, typeLowering] at lowering
      | some loweredType =>
          cases leftLowering : lowerTm typeScope sourceScope left with
          | none => simp [lowerTm, typeLowering, leftLowering] at lowering
          | some loweredLeft =>
              cases rightLowering : lowerTm typeScope sourceScope right with
              | none =>
                  simp [lowerTm, typeLowering, leftLowering, rightLowering] at lowering
              | some loweredRight =>
                  simp [lowerTm, typeLowering, leftLowering, rightLowering] at lowering
                  subst lowered
                  have leftTarget := lowerTm_renameExcept freshParts.2.1 scopes
                    leftLowering
                  have rightTarget := lowerTm_renameExcept freshParts.2.2 scopes
                    rightLowering
                  simp [lowerTm, typeLowering, leftTarget, rightTarget,
                    Nucleus.HolE.rename]
  | eps type predicate =>
      have freshParts :
          fresh ∉ Unsorted.names (Unsorted.erase type) ∧
          fresh ∉ Unsorted.names (Unsorted.erase predicate) := by
        simpa [Unsorted.names, Unsorted.erase] using freshness
      cases typeLowering : lowerFam typeScope type with
      | none => simp [lowerTm, typeLowering] at lowering
      | some loweredType =>
          cases predicateLowering : lowerTm typeScope sourceScope predicate with
          | none => simp [lowerTm, typeLowering, predicateLowering] at lowering
          | some loweredPredicate =>
              simp [lowerTm, typeLowering, predicateLowering] at lowering
              subst lowered
              have predicateTarget := lowerTm_renameExcept freshParts.2 scopes
                predicateLowering
              simp [lowerTm, typeLowering, predicateTarget, Nucleus.HolE.rename]
  | abs carrier name predicate value | rep carrier name predicate value =>
      have freshParts : fresh ≠ name ∧
          fresh ∉ Unsorted.names (Unsorted.erase carrier) ∧
          fresh ∉ Unsorted.names (Unsorted.erase predicate) ∧
          fresh ∉ Unsorted.names (Unsorted.erase value) := by
        simpa [Unsorted.names, Unsorted.erase] using freshness
      cases carrierLowering : lowerFam typeScope carrier with
      | none => simp [lowerTm, carrierLowering] at lowering
      | some loweredCarrier =>
          cases predicateLowering :
              lowerTm typeScope (.cons ⟨name, carrier⟩ .nil) predicate with
          | none => simp [lowerTm, carrierLowering, predicateLowering] at lowering
          | some loweredPredicate =>
              cases valueLowering : lowerTm typeScope sourceScope value with
              | none =>
                  simp [lowerTm, carrierLowering, predicateLowering,
                    valueLowering] at lowering
              | some loweredValue =>
                  simp [lowerTm, carrierLowering, predicateLowering,
                    valueLowering] at lowering
                  subst lowered
                  have valueTarget := lowerTm_renameExcept freshParts.2.2.2 scopes
                    valueLowering
                  simp [lowerTm, carrierLowering, predicateLowering, valueTarget,
                    Nucleus.HolE.rename]
termination_by sizeOf expression

end Nucleus.HolE.Named
