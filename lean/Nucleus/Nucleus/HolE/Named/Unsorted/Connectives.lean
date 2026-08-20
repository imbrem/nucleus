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

namespace Nucleus.HolE.Named.Unsorted

set_option relaxedAutoImplicit true

namespace Family

@[simp] theorem raw_boolTy {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    (typeScope : Named.TyScope types) :
    (Family.boolTy (Sig := Sig) typeScope).raw = .boolTy := rfl

end Family

namespace Term

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]

/-- Weaken a checked term through a named binder whose name is absent from the
entire surface term. -/
def weakenFresh (name : Nat) (binderType : Family Sig typeScope .star)
    (term : Term Sig typeScope termScope Γ type)
    (freshness : name ∉ Unsorted.names term.raw) :
    Term Sig typeScope
      (.cons ⟨name, binderType.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound binderType.lowered Γ) type :=
  ⟨term.expression, Nucleus.HolE.weaken term.lowered,
    lowerTm_renameExcept freshness
      (Named.TmScope.renamesExcept_freshCons name binderType.expression.sorted termScope)
      term.lowering,
    term.typing.weaken⟩

@[simp] theorem raw_weakenFresh (name : Nat)
    (binderType : Family Sig typeScope .star)
    (term : Term Sig typeScope termScope Γ type)
    (freshness : name ∉ Unsorted.names term.raw) :
    (weakenFresh name binderType term freshness).raw = term.raw := rfl

/-- Total checked conjunction.  The fresh binder selected by the raw macro is
also fresh for each operand, so both operands weaken without capture. -/
def and (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope) := by
  let boolType := Family.boolTy (Sig := Sig) typeScope
  let functionType := Family.arr boolType (Family.arr boolType boolType)
  let name := Unsorted.freshName left.raw right.raw
  have freshUnion : name ∉ Unsorted.names left.raw ∪ Unsorted.names right.raw := by
    exact Finset.freshNat_not_mem _
  have freshLeft : name ∉ Unsorted.names left.raw :=
    fun membership => freshUnion (Finset.mem_union_left _ membership)
  have freshRight : name ∉ Unsorted.names right.raw :=
    fun membership => freshUnion (Finset.mem_union_right _ membership)
  let extendedScope :=
    Named.TmScope.cons ⟨name, functionType.expression.sorted⟩ termScope
  let extendedContext := Nucleus.HolE.extendBound functionType.lowered Γ
  let function : Term Sig typeScope extendedScope extendedContext functionType :=
    Term.boundVariable name functionType 0 (by simp [extendedScope, Named.lookupTm]) rfl
  let left' := weakenFresh name functionType left freshLeft
  let right' := weakenFresh name functionType right freshRight
  let lhsBody := Term.app (Term.app function left') right'
  let lhs := Term.lam name functionType boolType lhsBody
  let extendedTruth : Term Sig typeScope extendedScope extendedContext boolType :=
    Term.truth
  let rhsBody := Term.app (Term.app function extendedTruth) extendedTruth
  let rhs := Term.lam name functionType boolType rhsBody
  exact Term.eq (Family.arr functionType boolType) lhs rhs

/-- Total checked disjunction by De Morgan's law. -/
def or (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope) :=
  Term.not (and (Term.not left) (Term.not right))

/-- Total checked implication, defined as `(left ∧ right) = left`. -/
def imp (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope) :=
  Term.eq (Family.boolTy typeScope) (and left right) left

@[simp] theorem raw_and (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    (and left right).raw = Unsorted.and left.raw right.raw := by
  rfl

@[simp] theorem raw_not (proposition :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    (Term.not proposition).raw = Unsorted.not proposition.raw := rfl

@[simp] theorem raw_eq (type : Family Sig typeScope .star)
    (left right : Term Sig typeScope termScope Γ type) :
    (Term.eq type left right).raw = .eq type.raw left.raw right.raw := rfl

@[simp] theorem raw_or (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    (or left right).raw = Unsorted.or left.raw right.raw := by
  simp only [or, Unsorted.or, raw_not, raw_and]

@[simp] theorem raw_imp (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    (imp left right).raw = Unsorted.imp left.raw right.raw := by
  simp only [imp, Unsorted.imp, raw_eq, raw_and, Family.raw_boolTy]

/-- The partial façade from `CheckedRules` succeeds on conjunction. -/
theorem and?_complete (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    ∃ result, Term.and? left right = some result ∧
      result.raw = Unsorted.and left.raw right.raw := by
  simpa [Term.and?, raw_and] using Term.ofRaw_complete (and left right)

/-- The partial façade from `CheckedRules` succeeds on disjunction. -/
theorem or?_complete (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    ∃ result, Term.or? left right = some result ∧
      result.raw = Unsorted.or left.raw right.raw := by
  simpa [Term.or?, raw_or] using Term.ofRaw_complete (or left right)

/-- The partial façade from `CheckedRules` succeeds on implication. -/
theorem imp?_complete (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    ∃ result, Term.imp? left right = some result ∧
      result.raw = Unsorted.imp left.raw right.raw := by
  simpa [Term.imp?, raw_imp] using Term.ofRaw_complete (imp left right)

/-! The following declarations are the small review surface for the derived
connectives.  Each statement mentions only the raw macro and its ordinary
unsorted typing judgment; the construction and lowering witnesses remain in
the checked term returned above. -/

theorem not_hasType (proposition :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    HasType typeScope termScope Γ (Unsorted.not proposition.raw) .boolTy := by
  rw [← raw_not]
  simpa [Term.rawType, Family.raw_boolTy] using (Term.not proposition).toHasType

theorem and_hasType (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    HasType typeScope termScope Γ (Unsorted.and left.raw right.raw) .boolTy := by
  rw [← raw_and]
  simpa [Term.rawType, Family.raw_boolTy] using (and left right).toHasType

theorem or_hasType (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    HasType typeScope termScope Γ (Unsorted.or left.raw right.raw) .boolTy := by
  rw [← raw_or]
  simpa [Term.rawType, Family.raw_boolTy] using (or left right).toHasType

theorem imp_hasType (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    HasType typeScope termScope Γ (Unsorted.imp left.raw right.raw) .boolTy := by
  rw [← raw_imp]
  simpa [Term.rawType, Family.raw_boolTy] using (imp left right).toHasType

end Term

end Nucleus.HolE.Named.Unsorted
