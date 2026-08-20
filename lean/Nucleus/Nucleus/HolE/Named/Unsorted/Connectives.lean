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

/-- The type quantified over by the equality-only conjunction encoding. -/
def andFunctionType (typeScope : Named.TyScope types) : Family Sig typeScope .star :=
  let boolType := Family.boolTy (Sig := Sig) typeScope
  Family.arr boolType (Family.arr boolType boolType)

def andName (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) : Nat :=
  Unsorted.freshName left.raw right.raw

theorem andName_left_not_mem (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    andName left right ∉ Unsorted.names left.raw := by
  intro membership
  exact Finset.freshNat_not_mem _ (Finset.mem_union_left _ membership)

theorem andName_right_not_mem (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    andName left right ∉ Unsorted.names right.raw := by
  intro membership
  exact Finset.freshNat_not_mem _ (Finset.mem_union_right _ membership)

/-- Body on the left of the defining conjunction equation. -/
def andLhsBody (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    BoolTerm typeScope
      (.cons ⟨andName left right, (andFunctionType typeScope).expression.sorted⟩
        termScope)
      (Nucleus.HolE.extendBound (andFunctionType typeScope).lowered Γ) := by
  let boolType := Family.boolTy (Sig := Sig) typeScope
  let functionType := andFunctionType (Sig := Sig) typeScope
  let name := andName left right
  let extendedScope :=
    Named.TmScope.cons ⟨name, functionType.expression.sorted⟩ termScope
  let extendedContext := Nucleus.HolE.extendBound functionType.lowered Γ
  let function : Term Sig typeScope extendedScope extendedContext functionType :=
    Term.boundVariable name functionType 0 (by simp [extendedScope, Named.lookupTm]) rfl
  let left' := weakenFresh name functionType left (andName_left_not_mem left right)
  let right' := weakenFresh name functionType right (andName_right_not_mem left right)
  exact Term.app (Term.app function left') right'

/-- Left side of the defining conjunction equation. -/
def andLhs (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Term Sig typeScope termScope Γ
      (Family.arr (andFunctionType typeScope) (Family.boolTy typeScope)) :=
  Term.lam (andName left right) (andFunctionType typeScope)
    (Family.boolTy typeScope) (andLhsBody left right)

/-- Body on the right of the defining conjunction equation. -/
def andRhsBody (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    BoolTerm typeScope
      (.cons ⟨andName left right, (andFunctionType typeScope).expression.sorted⟩
        termScope)
      (Nucleus.HolE.extendBound (andFunctionType typeScope).lowered Γ) := by
  let boolType := Family.boolTy (Sig := Sig) typeScope
  let functionType := andFunctionType (Sig := Sig) typeScope
  let name := andName left right
  let extendedScope :=
    Named.TmScope.cons ⟨name, functionType.expression.sorted⟩ termScope
  let extendedContext := Nucleus.HolE.extendBound functionType.lowered Γ
  let function : Term Sig typeScope extendedScope extendedContext functionType :=
    Term.boundVariable name functionType 0 (by simp [extendedScope, Named.lookupTm]) rfl
  let extendedTruth : Term Sig typeScope extendedScope extendedContext boolType :=
    Term.truth
  exact Term.app (Term.app function extendedTruth) extendedTruth

/-- Right side of the defining conjunction equation. -/
def andRhs (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Term Sig typeScope termScope Γ
      (Family.arr (andFunctionType typeScope) (Family.boolTy typeScope)) :=
  Term.lam (andName left right) (andFunctionType typeScope)
    (Family.boolTy typeScope) (andRhsBody left right)

/-- Total checked conjunction.  The fresh binder selected by the raw macro is
also fresh for each operand, so both operands weaken without capture. -/
def and (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope) :=
  Term.eq (Family.arr (andFunctionType typeScope) (Family.boolTy typeScope))
    (andLhs left right) (andRhs left right)

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

/-- The variable introduced at the head of a named term scope. -/
def headVariable {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types}
    (name : Nat) (type : Family Sig typeScope .star)
    (termScope : Named.TmScope Sig depth) (Γ : Nucleus.HolE.BoundCtx Sig types depth) :
    Term Sig typeScope (.cons ⟨name, type.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound type.lowered Γ) type :=
  Term.boundVariable name type 0 (by simp [Named.lookupTm]) rfl

/-- Body of the predicate `fun varied => varied = right`. -/
def eqToRightBody {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    (name : Nat) (type : Family Sig typeScope .star)
    (right : Term Sig typeScope termScope Γ type)
    (fresh : name ∉ Unsorted.names right.raw) :
    BoolTerm typeScope (.cons ⟨name, type.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound type.lowered Γ) :=
  Term.eq type (headVariable name type termScope Γ)
    (right.weakenFresh name type fresh)

/-- Body of the predicate `fun varied => left = varied`. -/
def eqFromLeftBody {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    (name : Nat) (type : Family Sig typeScope .star)
    (left : Term Sig typeScope termScope Γ type)
    (fresh : name ∉ Unsorted.names left.raw) :
    BoolTerm typeScope (.cons ⟨name, type.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound type.lowered Γ) :=
  Term.eq type (left.weakenFresh name type fresh)
    (headVariable name type termScope Γ)

/-- The body of the Boolean identity function. -/
def boolIdentityBody {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth} (name : Nat) :
    BoolTerm typeScope
      (.cons ⟨name, (Family.boolTy (Sig := Sig) typeScope).expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound (Family.boolTy (Sig := Sig) typeScope).lowered Γ) :=
  headVariable name (Family.boolTy typeScope) termScope Γ

@[simp] theorem eqToRightBody_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (name : Nat) (type : Family Sig typeScope .star)
    (right argument : Term Sig typeScope termScope Γ type)
    (fresh : name ∉ Unsorted.names right.raw) :
    Nucleus.HolE.openBound (eqToRightBody name type right fresh).lowered
      argument.lowered = (Term.eq type argument right).lowered := by
  simp [eqToRightBody, headVariable, weakenFresh, Term.eq,
    Term.boundVariable, Nucleus.HolE.openBound, Nucleus.HolE.instantiate]

@[simp] theorem eqFromLeftBody_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (name : Nat) (type : Family Sig typeScope .star)
    (left argument : Term Sig typeScope termScope Γ type)
    (fresh : name ∉ Unsorted.names left.raw) :
    Nucleus.HolE.openBound (eqFromLeftBody name type left fresh).lowered
      argument.lowered = (Term.eq type left argument).lowered := by
  simp [eqFromLeftBody, headVariable, weakenFresh, Term.eq,
    Term.boundVariable, Nucleus.HolE.openBound, Nucleus.HolE.instantiate]

@[simp] theorem boolIdentityBody_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (name : Nat) (proposition : BoolTerm typeScope termScope Γ) :
    Nucleus.HolE.openBound (boolIdentityBody (Sig := Sig) (typeScope := typeScope)
      (termScope := termScope) (Γ := Γ) name).lowered proposition.lowered =
      proposition.lowered := by
  simp [boolIdentityBody, headVariable, Term.boundVariable,
    Nucleus.HolE.openBound]

/-- Body of `fun varied => f x = varied x`. -/
def appFromLeftBody (name : Nat)
    (domain codomain : Family Sig typeScope .star)
    (function : Term Sig typeScope termScope Γ (Family.arr domain codomain))
    (argument : Term Sig typeScope termScope Γ domain)
    (functionFresh : name ∉ Unsorted.names function.raw)
    (argumentFresh : name ∉ Unsorted.names argument.raw) :
    BoolTerm typeScope
      (.cons ⟨name, (Family.arr domain codomain).expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound (Family.arr domain codomain).lowered Γ) :=
  let function' := function.weakenFresh name (Family.arr domain codomain) functionFresh
  let argument' := argument.weakenFresh name (Family.arr domain codomain) argumentFresh
  let varied := headVariable name (Family.arr domain codomain) termScope Γ
  Term.eq codomain (Term.app function' argument') (Term.app varied argument')

@[simp] theorem appFromLeftBody_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (name : Nat) (domain codomain : Family Sig typeScope .star)
    (function varied : Term Sig typeScope termScope Γ (Family.arr domain codomain))
    (argument : Term Sig typeScope termScope Γ domain)
    (functionFresh : name ∉ Unsorted.names function.raw)
    (argumentFresh : name ∉ Unsorted.names argument.raw) :
    Nucleus.HolE.openBound
      (appFromLeftBody name domain codomain function argument
        functionFresh argumentFresh).lowered varied.lowered =
      (Term.eq codomain (Term.app function argument)
        (Term.app varied argument)).lowered := by
  simp [appFromLeftBody, headVariable, weakenFresh, Term.eq, Term.app,
    Term.boundVariable, Nucleus.HolE.openBound, Nucleus.HolE.instantiate]

/-- Conjunction with a varying left operand. -/
def andLeftBody (name : Nat) (right : BoolTerm typeScope termScope Γ)
    (fresh : name ∉ Unsorted.names right.raw) :
    BoolTerm typeScope
      (.cons ⟨name, (Family.boolTy (Sig := Sig) typeScope).expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound (Family.boolTy (Sig := Sig) typeScope).lowered Γ) :=
  Term.and (headVariable name (Family.boolTy typeScope) termScope Γ)
    (right.weakenFresh name (Family.boolTy typeScope) fresh)

/-- Conjunction with a varying right operand. -/
def andRightBody (name : Nat) (left : BoolTerm typeScope termScope Γ)
    (fresh : name ∉ Unsorted.names left.raw) :
    BoolTerm typeScope
      (.cons ⟨name, (Family.boolTy (Sig := Sig) typeScope).expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound (Family.boolTy (Sig := Sig) typeScope).lowered Γ) :=
  Term.and (left.weakenFresh name (Family.boolTy typeScope) fresh)
    (headVariable name (Family.boolTy typeScope) termScope Γ)

@[simp] theorem andLeftBody_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (name : Nat) (right value : BoolTerm (Sig := Sig) typeScope termScope Γ)
    (fresh : name ∉ Unsorted.names right.raw) :
    Nucleus.HolE.openBound (andLeftBody name right fresh).lowered value.lowered =
      (Term.and value right).lowered := by
  simp [andLeftBody, Term.and, Term.andLhs, Term.andRhs, Term.andLhsBody,
    Term.andRhsBody, Term.andName, Term.andFunctionType, headVariable,
    weakenFresh, Term.eq, Term.app, Term.lam, Term.truth, Term.bool,
    Term.boundVariable,
    Nucleus.HolE.openBound, Nucleus.HolE.instantiate]
  rfl

@[simp] theorem andRightBody_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (name : Nat) (left value : BoolTerm (Sig := Sig) typeScope termScope Γ)
    (fresh : name ∉ Unsorted.names left.raw) :
    Nucleus.HolE.openBound (andRightBody name left fresh).lowered value.lowered =
      (Term.and left value).lowered := by
  simp [andRightBody, Term.and, Term.andLhs, Term.andRhs, Term.andLhsBody,
    Term.andRhsBody, Term.andName, Term.andFunctionType, headVariable,
    weakenFresh, Term.eq, Term.app, Term.lam, Term.truth, Term.bool,
    Term.boundVariable,
    Nucleus.HolE.openBound, Nucleus.HolE.instantiate]
  rfl

@[simp] theorem andLhsBody_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (left right : BoolTerm (Sig := Sig) typeScope termScope Γ)
    (operator : Term Sig typeScope termScope Γ (andFunctionType typeScope)) :
    Nucleus.HolE.openBound (andLhsBody left right).lowered operator.lowered =
      (Term.app (Term.app operator left) right).lowered := by
  simp [andLhsBody, andName, andFunctionType, weakenFresh,
    Term.boundVariable, Term.app, Nucleus.HolE.openBound,
    Nucleus.HolE.instantiate]

@[simp] theorem andRhsBody_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (left right : BoolTerm (Sig := Sig) typeScope termScope Γ)
    (operator : Term Sig typeScope termScope Γ (andFunctionType typeScope)) :
    Nucleus.HolE.openBound (andRhsBody left right).lowered operator.lowered =
      (Term.app (Term.app operator Term.truth) Term.truth).lowered := by
  simp [andRhsBody, andName, andFunctionType,
    Term.boundVariable, Term.app, Term.truth, Term.bool,
    Nucleus.HolE.openBound, Nucleus.HolE.instantiate]

/-- The Boolean identity function. -/
def boolIdentity (name : Nat) :
    Term Sig typeScope termScope Γ
      (Family.arr (Family.boolTy typeScope) (Family.boolTy typeScope)) :=
  Term.lam name (Family.boolTy typeScope) (Family.boolTy typeScope)
    (boolIdentityBody (Sig := Sig) (typeScope := typeScope)
      (termScope := termScope) (Γ := Γ) name)

/-- A deterministic name fresh for one checked term. -/
def freshFor {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {type : Family Sig typeScope .star}
    (term : Term Sig typeScope termScope Γ type) : Nat :=
  Unsorted.freshName term.raw term.raw

theorem freshFor_not_mem {types : List Kind} {depth : Nat}
    {typeScope : Named.TyScope types} {termScope : Named.TmScope Sig depth}
    {Γ : Nucleus.HolE.BoundCtx Sig types depth}
    {type : Family Sig typeScope .star}
    (term : Term Sig typeScope termScope Γ type) :
    freshFor term ∉ Unsorted.names term.raw := by
  intro membership
  exact Finset.freshNat_not_mem _ (Finset.mem_union_left _ membership)

/-- Body of the constant function returning a fixed Boolean. -/
def firstBoolBody (first : BoolTerm (Sig := Sig) typeScope termScope Γ) :
    BoolTerm (Sig := Sig) typeScope
      (.cons ⟨freshFor first, (Family.boolTy typeScope).expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound (Family.boolTy typeScope).lowered Γ) :=
  first.weakenFresh (freshFor first) (Family.boolTy typeScope)
    (freshFor_not_mem first)

/-- Constant function returning its first Boolean argument. -/
def firstBoolAfterFirst (first : BoolTerm (Sig := Sig) typeScope termScope Γ) :
    Term Sig typeScope termScope Γ
      (Family.arr (Family.boolTy typeScope) (Family.boolTy typeScope)) :=
  Term.lam (freshFor first) (Family.boolTy typeScope) (Family.boolTy typeScope)
    (firstBoolBody first)

/-- Boolean selector `fun first second => first`. -/
def firstBool : Term Sig typeScope termScope Γ
    (Family.arr (Family.boolTy typeScope)
      (Family.arr (Family.boolTy typeScope) (Family.boolTy typeScope))) :=
  let name := 0
  let first := headVariable name (Family.boolTy typeScope) termScope Γ
  Term.lam name (Family.boolTy typeScope)
    (Family.arr (Family.boolTy typeScope) (Family.boolTy typeScope))
    (firstBoolAfterFirst first)

/-- Boolean selector `fun first second => second`. -/
def secondBool : Term Sig typeScope termScope Γ
    (Family.arr (Family.boolTy typeScope)
      (Family.arr (Family.boolTy typeScope) (Family.boolTy typeScope))) :=
  let name := 0
  Term.lam name (Family.boolTy typeScope)
    (Family.arr (Family.boolTy typeScope) (Family.boolTy typeScope))
    (boolIdentity (Sig := Sig) (typeScope := typeScope)
      (termScope := .cons ⟨name, (Family.boolTy typeScope).expression.sorted⟩ termScope)
      (Γ := Nucleus.HolE.extendBound (Family.boolTy typeScope).lowered Γ) 1)

@[simp] theorem firstBool_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (first : BoolTerm (Sig := Sig) typeScope termScope Γ) :
    Nucleus.HolE.openBound
      (let name := 0
       let head := headVariable name (Family.boolTy typeScope) termScope Γ
       (firstBoolAfterFirst head).lowered)
      first.lowered = (firstBoolAfterFirst first).lowered := by
  simp [firstBoolAfterFirst, firstBoolBody, freshFor, headVariable, weakenFresh,
    Term.boundVariable,
    Term.lam, Nucleus.HolE.openBound, Nucleus.HolE.instantiate,
    Nucleus.HolE.weaken]
  rfl

@[simp] theorem firstBoolAfterFirst_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (first second : BoolTerm (Sig := Sig) typeScope termScope Γ) :
    Nucleus.HolE.openBound (firstBoolBody first).lowered second.lowered =
      first.lowered := by
  simp [firstBoolBody, weakenFresh, Nucleus.HolE.openBound]

@[simp] theorem secondBool_open (_typedContext : Nucleus.HolE.TypedCtx Γ)
    (first : BoolTerm (Sig := Sig) typeScope termScope Γ) :
    Nucleus.HolE.openBound
      (boolIdentity (Sig := Sig) (typeScope := typeScope)
        (termScope := .cons
          ⟨0, (Family.boolTy typeScope).expression.sorted⟩ termScope)
        (Γ := Nucleus.HolE.extendBound (Family.boolTy typeScope).lowered Γ) 1).lowered
      first.lowered =
      (boolIdentity (Sig := Sig) (typeScope := typeScope)
        (termScope := termScope) (Γ := Γ) 1).lowered := by
  simp [boolIdentity, boolIdentityBody, headVariable, Term.boundVariable,
    Term.lam, Nucleus.HolE.openBound, Nucleus.HolE.instantiate]

end Term

namespace TermEq

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
  [Nucleus.HolE.SigFamilyEquality Sig]

/-- The first Boolean selector computes to its first argument. -/
noncomputable def firstBool_apply (typedContext : Nucleus.HolE.TypedCtx Γ)
    (first second : BoolTerm (Sig := Sig) typeScope termScope Γ) :
    TermEq (Sig := Sig) typeScope termScope Γ (Family.boolTy typeScope)
      (Term.app (Term.app Term.firstBool first) second) first := by
  let name := 0
  let head := Term.headVariable name (Family.boolTy typeScope) termScope Γ
  let outerBody := Term.firstBoolAfterFirst head
  have outer : TermEq (Sig := Sig) typeScope termScope Γ
      (Family.arr (Family.boolTy typeScope) (Family.boolTy typeScope))
      (Term.app Term.firstBool first) (Term.firstBoolAfterFirst first) := by
    simpa [Term.firstBool, name, head, outerBody] using
      (TermEq.beta name typedContext (Family.boolTy typeScope)
        (Family.arr (Family.boolTy typeScope) (Family.boolTy typeScope))
        outerBody first (Term.firstBoolAfterFirst first)
        (Term.firstBool_open typedContext first).symm)
  have applied := TermEq.app outer (TermEq.refl second)
  have inner : TermEq (Sig := Sig) typeScope termScope Γ
      (Family.boolTy typeScope)
      (Term.app (Term.firstBoolAfterFirst first) second) first := by
    simpa [Term.firstBoolAfterFirst] using
      (TermEq.beta (Term.freshFor first) typedContext (Family.boolTy typeScope)
        (Family.boolTy typeScope) (Term.firstBoolBody first) second first
        (Term.firstBoolAfterFirst_open typedContext first second).symm)
  exact TermEq.trans applied inner

/-- The second Boolean selector computes to its second argument. -/
noncomputable def secondBool_apply (typedContext : Nucleus.HolE.TypedCtx Γ)
    (first second : BoolTerm (Sig := Sig) typeScope termScope Γ) :
    TermEq (Sig := Sig) typeScope termScope Γ (Family.boolTy typeScope)
      (Term.app (Term.app Term.secondBool first) second) second := by
  let boolType := Family.boolTy (Sig := Sig) typeScope
  let functionType := Family.arr boolType boolType
  let outerBody := Term.boolIdentity (Sig := Sig) (typeScope := typeScope)
    (termScope := .cons ⟨0, boolType.expression.sorted⟩ termScope)
    (Γ := Nucleus.HolE.extendBound boolType.lowered Γ) 1
  let identity := Term.boolIdentity (Sig := Sig) (typeScope := typeScope)
    (termScope := termScope) (Γ := Γ) 1
  have outer : TermEq (Sig := Sig) typeScope termScope Γ functionType
      (Term.app Term.secondBool first) identity := by
    simpa [Term.secondBool, boolType, functionType, outerBody, identity] using
      (TermEq.beta 0 typedContext boolType functionType outerBody first identity
        (Term.secondBool_open typedContext first).symm)
  have applied := TermEq.app outer (TermEq.refl second)
  have inner : TermEq (Sig := Sig) typeScope termScope Γ boolType
      (Term.app identity second) second := by
    simpa [identity, Term.boolIdentity] using
      (TermEq.beta 1 typedContext boolType boolType
        (Term.boolIdentityBody (Sig := Sig) (typeScope := typeScope)
          (termScope := termScope) (Γ := Γ) 1)
        second second (Term.boolIdentityBody_open typedContext 1 second).symm)
  exact TermEq.trans applied inner

/-- Applying the left side of the conjunction equation exposes both operands. -/
noncomputable def andLhs_apply (typedContext : Nucleus.HolE.TypedCtx Γ)
    (left right : BoolTerm (Sig := Sig) typeScope termScope Γ)
    (operator : Term Sig typeScope termScope Γ (Term.andFunctionType typeScope)) :
    TermEq (Sig := Sig) typeScope termScope Γ (Family.boolTy typeScope)
      (Term.app (Term.andLhs left right) operator)
      (Term.app (Term.app operator left) right) := by
  simpa [Term.andLhs] using
    (TermEq.beta (Term.andName left right) typedContext
      (Term.andFunctionType typeScope) (Family.boolTy typeScope)
      (Term.andLhsBody left right) operator
      (Term.app (Term.app operator left) right)
      (Term.andLhsBody_open typedContext left right operator).symm)

/-- Applying the right side of the conjunction equation exposes `true, true`. -/
noncomputable def andRhs_apply (typedContext : Nucleus.HolE.TypedCtx Γ)
    (left right : BoolTerm (Sig := Sig) typeScope termScope Γ)
    (operator : Term Sig typeScope termScope Γ (Term.andFunctionType typeScope)) :
    TermEq (Sig := Sig) typeScope termScope Γ (Family.boolTy typeScope)
      (Term.app (Term.andRhs left right) operator)
      (Term.app (Term.app operator Term.truth) Term.truth) := by
  simpa [Term.andRhs] using
    (TermEq.beta (Term.andName left right) typedContext
      (Term.andFunctionType typeScope) (Family.boolTy typeScope)
      (Term.andRhsBody left right) operator
      (Term.app (Term.app operator Term.truth) Term.truth)
      (Term.andRhsBody_open typedContext left right operator).symm)

end TermEq

namespace Proof

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
  [Nucleus.HolE.SigFamilyEquality Sig]

/-- Add one unused checked proposition to the hypothesis list. -/
noncomputable def weakenHyp (proposition : BoolTerm typeScope termScope Γ)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses conclusion) :
    Proof (Sig := Sig) typeScope termScope Γ
      (proposition :: hypotheses) conclusion :=
  premise.hypothesisMap (fun _candidate membership =>
    List.mem_cons_of_mem proposition membership)

/-- Eliminate one checked beta redex.  The named result is supplied explicitly;
its equation with locally nameless opening is the only bookkeeping premise. -/
def betaReduce (name : Nat) (typedContext : Nucleus.HolE.TypedCtx Γ)
    (domain : Family Sig typeScope .star)
    (body : Term Sig typeScope
      (.cons ⟨name, domain.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound domain.lowered Γ) (Family.boolTy typeScope))
    (argument : Term Sig typeScope termScope Γ domain)
    (result : BoolTerm typeScope termScope Γ)
    (resultEq : result.lowered =
      Nucleus.HolE.openBound body.lowered argument.lowered)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app (Term.lam name domain (Family.boolTy typeScope) body) argument)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses result :=
  premise.convert
    (TermEq.beta name typedContext domain (Family.boolTy typeScope)
      body argument result resultEq)

/-- Introduce one checked beta redex. -/
def betaExpand (name : Nat) (typedContext : Nucleus.HolE.TypedCtx Γ)
    (domain : Family Sig typeScope .star)
    (body : Term Sig typeScope
      (.cons ⟨name, domain.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound domain.lowered Γ) (Family.boolTy typeScope))
    (argument : Term Sig typeScope termScope Γ domain)
    (result : BoolTerm typeScope termScope Γ)
    (resultEq : result.lowered =
      Nucleus.HolE.openBound body.lowered argument.lowered)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses result) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app (Term.lam name domain (Family.boolTy typeScope) body) argument) :=
  premise.convert
    (TermEq.symm
      (TermEq.beta name typedContext domain (Family.boolTy typeScope)
        body argument result resultEq))

/-- Symmetry of object-language equality, derived by equality substitution. -/
noncomputable def eqSymm (typedContext : Nucleus.HolE.TypedCtx Γ)
    (type : Family Sig typeScope .star)
    (left right : Term Sig typeScope termScope Γ type)
    (equality : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq type left right)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq type right left) := by
  let name := Unsorted.freshName left.raw left.raw
  have fresh : name ∉ Unsorted.names left.raw := by
    intro membership
    exact Finset.freshNat_not_mem _
      (Finset.mem_union_left _ membership)
  let body := Term.eqToRightBody name type left fresh
  let predicate := Term.lam name type (Family.boolTy typeScope) body
  have atLeft : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq type left left) := Proof.eqRefl left
  have predicateAtLeft : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app predicate left) :=
    betaExpand name typedContext type body left (Term.eq type left left)
      (Term.eqToRightBody_open typedContext name type left left fresh).symm atLeft
  have predicateAtRight : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app predicate right) :=
    Proof.eqMp predicate left right equality predicateAtLeft
  exact betaReduce name typedContext type body right (Term.eq type right left)
    (Term.eqToRightBody_open typedContext name type left right fresh).symm
    predicateAtRight

/-- Transitivity of object-language equality, derived by equality substitution. -/
noncomputable def eqTrans (typedContext : Nucleus.HolE.TypedCtx Γ)
    (type : Family Sig typeScope .star)
    (left middle right : Term Sig typeScope termScope Γ type)
    (first : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq type left middle))
    (second : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq type middle right)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq type left right) := by
  let name := Unsorted.freshName left.raw left.raw
  have fresh : name ∉ Unsorted.names left.raw := by
    intro membership
    exact Finset.freshNat_not_mem _
      (Finset.mem_union_left _ membership)
  let body := Term.eqFromLeftBody name type left fresh
  let predicate := Term.lam name type (Family.boolTy typeScope) body
  have predicateAtMiddle : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app predicate middle) :=
    betaExpand name typedContext type body middle (Term.eq type left middle)
      (Term.eqFromLeftBody_open typedContext name type left middle fresh).symm first
  have predicateAtRight : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app predicate right) :=
    Proof.eqMp predicate middle right second predicateAtMiddle
  exact betaReduce name typedContext type body right (Term.eq type left right)
    (Term.eqFromLeftBody_open typedContext name type left right fresh).symm
    predicateAtRight

/-- Applying equal functions to one argument preserves object-language
equality. -/
noncomputable def appCongr (typedContext : Nucleus.HolE.TypedCtx Γ)
    (domain codomain : Family Sig typeScope .star)
    (function varied :
      Term Sig typeScope termScope Γ (Family.arr domain codomain))
    (argument : Term Sig typeScope termScope Γ domain)
    (equality : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.arr domain codomain) function varied)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq codomain (Term.app function argument)
        (Term.app varied argument)) := by
  let name := Unsorted.freshName function.raw argument.raw
  have freshUnion : name ∉
      Unsorted.names function.raw ∪ Unsorted.names argument.raw := by
    exact Finset.freshNat_not_mem _
  have functionFresh : name ∉ Unsorted.names function.raw :=
    fun membership => freshUnion (Finset.mem_union_left _ membership)
  have argumentFresh : name ∉ Unsorted.names argument.raw :=
    fun membership => freshUnion (Finset.mem_union_right _ membership)
  let functionType := Family.arr domain codomain
  let body := Term.appFromLeftBody name domain codomain function argument
    functionFresh argumentFresh
  let predicate := Term.lam name functionType (Family.boolTy typeScope) body
  have atFunction : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq codomain (Term.app function argument)
        (Term.app function argument)) := Proof.eqRefl _
  have predicateAtFunction :
      Proof (Sig := Sig) typeScope termScope Γ hypotheses
        (Term.app predicate function) :=
    betaExpand name typedContext functionType body function
      (Term.eq codomain (Term.app function argument)
        (Term.app function argument))
      (Term.appFromLeftBody_open typedContext name domain codomain function
        function argument functionFresh argumentFresh).symm atFunction
  have predicateAtVaried :
      Proof (Sig := Sig) typeScope termScope Γ hypotheses
        (Term.app predicate varied) :=
    Proof.eqMp predicate function varied equality predicateAtFunction
  exact betaReduce name typedContext functionType body varied
    (Term.eq codomain (Term.app function argument) (Term.app varied argument))
    (Term.appFromLeftBody_open typedContext name domain codomain function
      varied argument functionFresh argumentFresh).symm predicateAtVaried

/-- Equality of Booleans transports provability. -/
noncomputable def ofEqBool (typedContext : Nucleus.HolE.TypedCtx Γ)
    (left right : BoolTerm typeScope termScope Γ)
    (equality : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.boolTy typeScope) left right))
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses left) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses right := by
  let name := 0
  let body := Term.boolIdentityBody (Sig := Sig) (typeScope := typeScope)
    (termScope := termScope) (Γ := Γ) name
  let predicate := Term.lam name (Family.boolTy typeScope)
    (Family.boolTy typeScope) body
  have predicateAtLeft : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app predicate left) :=
    betaExpand name typedContext (Family.boolTy typeScope) body left left
      (Term.boolIdentityBody_open typedContext name left).symm premise
  have predicateAtRight : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app predicate right) :=
    Proof.eqMp predicate left right equality predicateAtLeft
  exact betaReduce name typedContext (Family.boolTy typeScope) body right right
    (Term.boolIdentityBody_open typedContext name right).symm predicateAtRight

/-- Every proved Boolean is provably equal to truth. -/
noncomputable def eqTrue (premise :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses proposition) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.boolTy typeScope) proposition Term.truth) :=
  Proof.antisymm proposition Term.truth
    Proof.truth (premise.weakenHyp Term.truth)

/-- Equality with truth can be eliminated back to the proposition. -/
noncomputable def ofEqTrue (typedContext : Nucleus.HolE.TypedCtx Γ)
    (equality : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.boolTy typeScope) proposition Term.truth)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses proposition :=
  ofEqBool typedContext Term.truth proposition
    (eqSymm typedContext (Family.boolTy typeScope) proposition Term.truth equality)
    Proof.truth

/-- The defining equation for conjunction is reflexive at `true, true`. -/
noncomputable def andTrueTrue :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.and Term.truth Term.truth) := by
  let boolType := Family.boolTy (Sig := Sig) typeScope
  let functionType := Family.arr boolType (Family.arr boolType boolType)
  let truth : BoolTerm (Sig := Sig) typeScope termScope Γ := Term.truth
  let name := Unsorted.freshName truth.raw truth.raw
  have fresh : name ∉ Unsorted.names truth.raw := by
    intro membership
    exact Finset.freshNat_not_mem _ (Finset.mem_union_left _ membership)
  let extendedScope :=
    Named.TmScope.cons ⟨name, functionType.expression.sorted⟩ termScope
  let extendedContext := Nucleus.HolE.extendBound functionType.lowered Γ
  let function : Term Sig typeScope extendedScope extendedContext functionType :=
    Term.boundVariable name functionType 0
      (by simp [extendedScope, Named.lookupTm]) rfl
  let truth' := truth.weakenFresh name functionType fresh
  let body := Term.app (Term.app function truth') truth'
  let abstraction := Term.lam name functionType boolType body
  have reflexive : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.arr functionType boolType) abstraction abstraction) :=
    Proof.eqRefl abstraction
  exact ⟨by
    simpa [Term.and, Term.andLhs, Term.andRhs, Term.andLhsBody,
      Term.andRhsBody, Term.andName, Term.andFunctionType,
      boolType, functionType, truth, name, extendedScope,
      extendedContext, function, truth', body, abstraction, Term.weakenFresh,
      Term.truth, Term.bool, Nucleus.HolE.weaken, Nucleus.HolE.rename]
      using reflexive.kernel⟩

/-- Standard conjunction introduction. -/
noncomputable def andIntro (typedContext : Nucleus.HolE.TypedCtx Γ)
    (left : Proof (Sig := Sig) typeScope termScope Γ hypotheses p)
    (right : Proof (Sig := Sig) typeScope termScope Γ hypotheses q) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.and p q) := by
  let truth : BoolTerm (Sig := Sig) typeScope termScope Γ := Term.truth
  have qTrue := eqTrue right
  have trueQ := eqSymm typedContext (Family.boolTy typeScope) q truth qTrue
  let rightName := Unsorted.freshName truth.raw truth.raw
  have truthFresh : rightName ∉ Unsorted.names truth.raw := by
    intro membership
    exact Finset.freshNat_not_mem _ (Finset.mem_union_left _ membership)
  let rightBody := Term.andRightBody rightName truth truthFresh
  let rightPredicate := Term.lam rightName (Family.boolTy typeScope)
    (Family.boolTy typeScope) rightBody
  have atTrue : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app rightPredicate truth) :=
    betaExpand rightName typedContext (Family.boolTy typeScope) rightBody truth
      (Term.and truth truth)
      (Term.andRightBody_open typedContext rightName truth truth truthFresh).symm
      andTrueTrue
  have atQ : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app rightPredicate q) :=
    Proof.eqMp rightPredicate truth q trueQ atTrue
  have truthAndQ : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.and truth q) :=
    betaReduce rightName typedContext (Family.boolTy typeScope) rightBody q
      (Term.and truth q)
      (Term.andRightBody_open typedContext rightName truth q truthFresh).symm atQ
  have pTrue := eqTrue left
  have trueP := eqSymm typedContext (Family.boolTy typeScope) p truth pTrue
  let leftName := Unsorted.freshName q.raw q.raw
  have qFresh : leftName ∉ Unsorted.names q.raw := by
    intro membership
    exact Finset.freshNat_not_mem _ (Finset.mem_union_left _ membership)
  let leftBody := Term.andLeftBody leftName q qFresh
  let leftPredicate := Term.lam leftName (Family.boolTy typeScope)
    (Family.boolTy typeScope) leftBody
  have atTruth : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app leftPredicate truth) :=
    betaExpand leftName typedContext (Family.boolTy typeScope) leftBody truth
      (Term.and truth q)
      (Term.andLeftBody_open typedContext leftName q truth qFresh).symm truthAndQ
  have atP : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.app leftPredicate p) :=
    Proof.eqMp leftPredicate truth p trueP atTruth
  exact betaReduce leftName typedContext (Family.boolTy typeScope) leftBody p
    (Term.and p q)
    (Term.andLeftBody_open typedContext leftName q p qFresh).symm atP

/-- Left elimination for equality-defined conjunction. -/
noncomputable def andElimLeft (typedContext : Nucleus.HolE.TypedCtx Γ)
    (conjunction : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.and p q)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses p := by
  let operator := Term.firstBool (Sig := Sig) (typeScope := typeScope)
    (termScope := termScope) (Γ := Γ)
  have applied := appCongr typedContext (Term.andFunctionType typeScope)
    (Family.boolTy typeScope) (Term.andLhs p q) (Term.andRhs p q)
    operator conjunction
  have leftReduction := TermEq.trans
    (TermEq.andLhs_apply typedContext p q operator)
    (TermEq.firstBool_apply typedContext p q)
  have rightReduction := TermEq.trans
    (TermEq.andRhs_apply typedContext p q operator)
    (TermEq.firstBool_apply typedContext Term.truth Term.truth)
  have first : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.boolTy typeScope) p
        (Term.app (Term.andRhs p q) operator)) :=
    eqTrans typedContext (Family.boolTy typeScope) p
      (Term.app (Term.andLhs p q) operator)
      (Term.app (Term.andRhs p q) operator)
      (eqSymm typedContext (Family.boolTy typeScope) _ _
        (Proof.eqOfTermEq leftReduction)) applied
  have equality : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.boolTy typeScope) p Term.truth) :=
    eqTrans typedContext (Family.boolTy typeScope) p
      (Term.app (Term.andRhs p q) operator) Term.truth first
      (Proof.eqOfTermEq rightReduction)
  exact ofEqTrue typedContext equality

/-- Right elimination for equality-defined conjunction. -/
noncomputable def andElimRight (typedContext : Nucleus.HolE.TypedCtx Γ)
    (conjunction : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.and p q)) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses q := by
  let operator := Term.secondBool (Sig := Sig) (typeScope := typeScope)
    (termScope := termScope) (Γ := Γ)
  have applied := appCongr typedContext (Term.andFunctionType typeScope)
    (Family.boolTy typeScope) (Term.andLhs p q) (Term.andRhs p q)
    operator conjunction
  have leftReduction := TermEq.trans
    (TermEq.andLhs_apply typedContext p q operator)
    (TermEq.secondBool_apply typedContext p q)
  have rightReduction := TermEq.trans
    (TermEq.andRhs_apply typedContext p q operator)
    (TermEq.secondBool_apply typedContext Term.truth Term.truth)
  have first : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.boolTy typeScope) q
        (Term.app (Term.andRhs p q) operator)) :=
    eqTrans typedContext (Family.boolTy typeScope) q
      (Term.app (Term.andLhs p q) operator)
      (Term.app (Term.andRhs p q) operator)
      (eqSymm typedContext (Family.boolTy typeScope) _ _
        (Proof.eqOfTermEq leftReduction)) applied
  have equality : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.eq (Family.boolTy typeScope) q Term.truth) :=
    eqTrans typedContext (Family.boolTy typeScope) q
      (Term.app (Term.andRhs p q) operator) Term.truth first
      (Proof.eqOfTermEq rightReduction)
  exact ofEqTrue typedContext equality

/-- Negation introduction, with negation represented as equality to false. -/
noncomputable def notIntro
    (proposition : BoolTerm (Sig := Sig) typeScope termScope Γ)
    (contradiction : Proof (Sig := Sig) typeScope termScope Γ
      (proposition :: hypotheses) Term.falsehood) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.not proposition) := by
  unfold Term.not
  exact Proof.antisymm proposition Term.falsehood contradiction
    (Proof.falseElim proposition (Proof.hyp (by simp)))

/-- Negation elimination is Boolean equality transport into false. -/
noncomputable def notElim (typedContext : Nucleus.HolE.TypedCtx Γ)
    (negated : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.not p))
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses p) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses Term.falsehood := by
  unfold Term.not at negated
  exact ofEqBool typedContext p Term.falsehood negated premise

/-- Implication introduction for the definition `(p ∧ q) = p`. -/
noncomputable def impIntro (typedContext : Nucleus.HolE.TypedCtx Γ)
    (consequence : Proof (Sig := Sig) typeScope termScope Γ
      (p :: hypotheses) q) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.imp p q) := by
  unfold Term.imp
  apply Proof.antisymm (Term.and p q) p
  · exact andElimLeft (p := p) (q := q) typedContext (Proof.hyp (by simp))
  · exact andIntro typedContext (Proof.hyp (by simp)) consequence

/-- Modus ponens for equality-defined implication. -/
noncomputable def impElim (typedContext : Nucleus.HolE.TypedCtx Γ)
    (implication : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.imp p q))
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses p) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses q := by
  unfold Term.imp at implication
  have expanded : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.and p q) :=
    ofEqBool typedContext p (Term.and p q)
      (eqSymm typedContext (Family.boolTy typeScope) (Term.and p q) p implication)
      premise
  exact andElimRight typedContext expanded

/-- Double-negation introduction. -/
noncomputable def doubleNegIntro (typedContext : Nucleus.HolE.TypedCtx Γ)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses p) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.not (Term.not p)) := by
  apply notIntro (Term.not p)
  have negated : Proof (Sig := Sig) typeScope termScope Γ
      (Term.not p :: hypotheses) (Term.not p) := Proof.hyp (by simp)
  exact notElim typedContext negated (premise.weakenHyp (Term.not p))

/-- Classical double-negation elimination via Boolean cases. -/
noncomputable def doubleNegElim (typedContext : Nucleus.HolE.TypedCtx Γ)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.not (Term.not p))) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses p := by
  apply Proof.boolCases p p
  · exact Proof.hyp (by simp)
  · have negated : Proof (Sig := Sig) typeScope termScope Γ
        (Term.not p :: hypotheses) (Term.not p) := Proof.hyp (by simp)
    have contradiction := notElim typedContext
      (premise.weakenHyp (Term.not p)) negated
    exact Proof.falseElim p contradiction

/-- Left introduction for De Morgan disjunction. -/
noncomputable def orIntroLeft (typedContext : Nucleus.HolE.TypedCtx Γ)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses p) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.or p q) := by
  let denied := Term.and (Term.not p) (Term.not q)
  apply notIntro denied
  have conjunction : Proof (Sig := Sig) typeScope termScope Γ
      (denied :: hypotheses) denied := Proof.hyp (by simp)
  have deniedP : Proof (Sig := Sig) typeScope termScope Γ
      (denied :: hypotheses) (Term.not p) :=
    andElimLeft (p := Term.not p) (q := Term.not q) typedContext conjunction
  have pProof : Proof (Sig := Sig) typeScope termScope Γ
      (denied :: hypotheses) p := premise.weakenHyp denied
  exact notElim typedContext deniedP pProof

/-- Right introduction for De Morgan disjunction. -/
noncomputable def orIntroRight (typedContext : Nucleus.HolE.TypedCtx Γ)
    (premise : Proof (Sig := Sig) typeScope termScope Γ hypotheses q) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses (Term.or p q) := by
  let denied := Term.and (Term.not p) (Term.not q)
  apply notIntro denied
  have conjunction : Proof (Sig := Sig) typeScope termScope Γ
      (denied :: hypotheses) denied := Proof.hyp (by simp)
  have deniedQ : Proof (Sig := Sig) typeScope termScope Γ
      (denied :: hypotheses) (Term.not q) :=
    andElimRight (p := Term.not p) (q := Term.not q) typedContext conjunction
  have qProof : Proof (Sig := Sig) typeScope termScope Γ
      (denied :: hypotheses) q := premise.weakenHyp denied
  exact notElim typedContext deniedQ qProof

/-- Eliminate De Morgan disjunction by nested Boolean cases. -/
noncomputable def orElim (typedContext : Nucleus.HolE.TypedCtx Γ)
    (disjunction : Proof (Sig := Sig) typeScope termScope Γ hypotheses
      (Term.or p q))
    (left : Proof (Sig := Sig) typeScope termScope Γ (p :: hypotheses) conclusion)
    (right : Proof (Sig := Sig) typeScope termScope Γ (q :: hypotheses) conclusion) :
    Proof (Sig := Sig) typeScope termScope Γ hypotheses conclusion := by
  apply Proof.boolCases p conclusion left
  apply Proof.boolCases q conclusion
  · exact right.hypothesisMap (fun candidate membership => by
      rcases List.mem_cons.mp membership with rfl | membership
      · simp
      · exact List.mem_cons_of_mem q (List.mem_cons_of_mem (Term.not p) membership))
  · let denied := Term.and (Term.not p) (Term.not q)
    have notQ : Proof (Sig := Sig) typeScope termScope Γ
        (Term.not q :: Term.not p :: hypotheses) (Term.not q) :=
      Proof.hyp (by simp)
    have notP : Proof (Sig := Sig) typeScope termScope Γ
        (Term.not q :: Term.not p :: hypotheses) (Term.not p) :=
      Proof.hyp (by simp)
    have deniedProof : Proof (Sig := Sig) typeScope termScope Γ
        (Term.not q :: Term.not p :: hypotheses) denied :=
      andIntro typedContext notP notQ
    have disjunctionProof : Proof (Sig := Sig) typeScope termScope Γ
        (Term.not q :: Term.not p :: hypotheses) (Term.or p q) :=
      disjunction.hypothesisMap (fun candidate membership =>
        List.mem_cons_of_mem (Term.not q)
          (List.mem_cons_of_mem (Term.not p) membership))
    have contradiction := notElim typedContext disjunctionProof deniedProof
    exact Proof.falseElim conclusion contradiction

end Proof

end Nucleus.HolE.Named.Unsorted
