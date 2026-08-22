import Nucleus.Hol.Ethane.Arena.OneBased.Inference

/-!
# Direct checking of resolved named Ethane syntax

The Rust kernel checks the named syntax reconstructed from an arena.  This
file specifies that pass directly.  Type binders are represented by their
exact syntactic `(name, kind)` pairs, as they are in Rust.  Term variables
already carry their types, so term binders do not affect inference.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true
set_option linter.unusedSimpArgs false

/-- The executable type equality used by the named checker. -/
def sameFamily (left right : EmptyTy) : Bool :=
  sameSyntax left.erase right.erase

theorem sameFamily_eq_true_iff (left right : EmptyTy) :
    sameFamily left right = true ↔ left = right := by
  rw [sameFamily, sameSyntax_eq_true_iff]
  exact Nucleus.Hol.Ethane.Expr.erase_injective.eq_iff

/-- Rust stores type binders from outermost to innermost. -/
def typeBindings : Nucleus.HolE.Named.TyScope types → List (Nat × Kind)
  | .nil => []
  | @Nucleus.HolE.Named.TyScope.cons _ boundKind name rest =>
      typeBindings rest ++ [(name, boundKind)]

theorem lookupTy_isSome_iff (wanted : Nucleus.HolE.Named.TyDecl) :
    (∃ index, Nucleus.HolE.Named.lookupTy wanted scope = some index) ↔
      (wanted.name, wanted.sort) ∈ typeBindings scope := by
  induction scope with
  | nil => simp [typeBindings, Nucleus.HolE.Named.lookupTy]
  | @cons types boundKind name rest ih =>
      by_cases names : wanted.name = name
      · subst name
        by_cases sorts : wanted.sort = boundKind
        · subst boundKind
          simp [typeBindings, Nucleus.HolE.Named.lookupTy]
        · simp [typeBindings, Nucleus.HolE.Named.lookupTy, sorts, ih]
      · simp [typeBindings, Nucleus.HolE.Named.lookupTy, names, ih]

/-- A named term scope and a locally nameless bound context classify every
captured `(name, type)` pair by the same lowered type. -/
def TmScopeAgrees (typeScope : Nucleus.HolE.Named.TyScope types)
    (termScope : Nucleus.HolE.Named.TmScope ArenaSig depth)
    (Γ : Nucleus.HolE.BoundCtx ArenaSig types depth) : Prop :=
  ∀ declaration index,
    Nucleus.HolE.Named.lookupTm declaration termScope = some index →
      ∃ loweredType,
        Nucleus.HolE.Named.lowerFam typeScope declaration.sort = some loweredType ∧
        Γ index = loweredType

theorem TmScopeAgrees.nil (typeScope : Nucleus.HolE.Named.TyScope types) :
    TmScopeAgrees typeScope (.nil : Nucleus.HolE.Named.TmScope ArenaSig 0)
      Nucleus.HolE.emptyBound := by
  intro declaration index found
  simp [Nucleus.HolE.Named.lookupTm] at found

theorem TmScopeAgrees.cons
    {domain : EmptyTy} {loweredDomain : Nucleus.HolE.Ty ArenaSig types}
    {name : Nat}
    (agrees : TmScopeAgrees typeScope termScope Γ)
    (lowering : Nucleus.HolE.Named.lowerFam typeScope domain.toHolE = some loweredDomain) :
    TmScopeAgrees typeScope
      (.cons ⟨name, domain.toHolE⟩ termScope)
      (Nucleus.HolE.extendBound loweredDomain Γ) := by
  intro declaration index found
  by_cases equal : declaration =
      ({ name := name, sort := domain.toHolE } : Nucleus.HolE.Named.TmDecl ArenaSig)
  · subst declaration
    have index_eq : index = 0 := by
      simpa [Nucleus.HolE.Named.lookupTm] using found.symm
    subst index
    exact ⟨loweredDomain, lowering, rfl⟩
  · simp only [Nucleus.HolE.Named.lookupTm, if_neg equal] at found
    obtain ⟨prior, priorFound, index_eq⟩ := Option.map_eq_some_iff.mp found
    subst index
    obtain ⟨loweredType, typeLowering, contextType⟩ :=
      agrees declaration prior priorFound
    exact ⟨loweredType, typeLowering, contextType⟩

@[simp] theorem lowerTy_boolTy (typeScope : Nucleus.HolE.Named.TyScope types) :
    (Nucleus.Hol.Ethane.Expr.boolTy : EmptyTy).lowerTy typeScope =
      some (Nucleus.HolE.Expr.boolTy : Nucleus.HolE.Ty ArenaSig types) := by
  simp [Nucleus.Hol.Ethane.Expr.lowerTy, Nucleus.Hol.Ethane.Expr.lowerFam,
    Nucleus.Hol.Ethane.Expr.lower, Nucleus.Hol.Ethane.Expr.toHolE,
    Nucleus.HolE.Named.lower, Nucleus.HolE.Named.lowerFam]

/-- The result of direct inference at each syntactic sort. -/
def Inferred : HolSort → Type 1
  | .kind _ => ULift Kind
  | .tm => EmptyTy

/-- Direct inference over the single sorted syntax family. -/
def inferNamed (scope : List (Nat × Kind)) :
    (expression : EmptyExpr sort) → Option (Inferred sort)
  | .boolTy => some ⟨.star⟩
  | .arr domain codomain => do
      let domainKind ← inferNamed scope domain
      let codomainKind ← inferNamed scope codomain
      if domainKind.down = .star ∧ codomainKind.down = .star then some ⟨.star⟩ else none
  | @Nucleus.Hol.Ethane.Expr.tyApp _ _ domain codomain function argument => do
      let functionKind ← inferNamed scope function
      let argumentKind ← inferNamed scope argument
      if functionKind.down = .arr domain codomain ∧ argumentKind.down = domain then
        some ⟨codomain⟩
      else none
  | @Nucleus.Hol.Ethane.Expr.tyLam _ _ domain codomain name body => do
      let bodyKind ← inferNamed (scope ++ [(name, domain)]) body
      if bodyKind.down = codomain then some ⟨.arr domain codomain⟩ else none
  | .tyFv name kind =>
      if (name, kind) ∈ scope then some ⟨kind⟩ else none
  | .model name predicate => do
      let inferred ← inferNamed (scope ++ [(name, .star)]) predicate
      if sameFamily inferred .boolTy then some ⟨.star⟩ else none
  | .primFam symbol => nomatch symbol
  | .tyExists name predicate => do
      let inferred ← inferNamed (scope ++ [(name, .star)]) predicate
      if sameFamily inferred .boolTy then some .boolTy else none
  | .primTm symbol => nomatch symbol
  | .tmFv _ type => do
      let kind ← inferNamed scope type
      if kind.down = .star then some type else none
  | .app function argument => do
      let .arr domain codomain ← inferNamed scope function | none
      let actual ← inferNamed scope argument
      if sameFamily actual domain then some codomain else none
  | .lam _ domain body => do
      let kind ← inferNamed scope domain
      if kind.down = .star then
        return .arr domain (← inferNamed scope body)
      else none
  | .bool _ => some .boolTy
  | .eq type left right => do
      let kind ← inferNamed scope type
      let leftType ← inferNamed scope left
      let rightType ← inferNamed scope right
      if kind.down = .star ∧ sameFamily leftType type ∧ sameFamily rightType type then
        some .boolTy
      else none
  | .eps type predicate => do
      let kind ← inferNamed scope type
      let predicateType ← inferNamed scope predicate
      if kind.down = .star ∧ sameFamily predicateType (.arr type .boolTy) then
        some type
      else none

/-- Infer the kind of a sorted named family. -/
def inferNamedFam (scope : List (Nat × Kind))
    (family : EmptyExpr (.kind kind)) : Option (ULift Kind) :=
  inferNamed scope family

/-- Infer the strict syntactic type of a sorted named term. -/
def inferNamedTm (scope : List (Nat × Kind)) (term : EmptyTm) : Option EmptyTy :=
  inferNamed scope term

namespace Value

/-- The logical pass implemented by `Value::is_well_formed` in Rust. -/
def rustCheck : Value → Bool
  | Value.kind _ => true
  | Value.family familyKind expression =>
      match inferNamedFam [] expression with
      | some actual => decide (actual.down = familyKind)
      | none => false
  | Value.term type expression =>
      match inferNamedFam [] type, inferNamedTm [] expression with
      | some ⟨.star⟩, some actual => sameFamily actual type
      | _, _ => false

end Value

/-- Constructor count used to share one induction between family and term
inference, including calls across `model` and `tyExists`. -/
def namedNodeCount : EmptyExpr sort → Nat
  | .boolTy => 1
  | .arr domain codomain => namedNodeCount domain + namedNodeCount codomain + 1
  | .tyApp function argument => namedNodeCount function + namedNodeCount argument + 1
  | .tyLam _ body => namedNodeCount body + 1
  | .tyFv _ _ => 1
  | .tyExists _ predicate => namedNodeCount predicate + 1
  | .model _ predicate => namedNodeCount predicate + 1
  | .primFam symbol | .primTm symbol => nomatch symbol
  | .tmFv _ type => namedNodeCount type + 1
  | .app function argument => namedNodeCount function + namedNodeCount argument + 1
  | .lam _ domain body => namedNodeCount domain + namedNodeCount body + 1
  | .bool _ => 1
  | .eq type left right =>
      namedNodeCount type + namedNodeCount left + namedNodeCount right + 1
  | .eps type predicate => namedNodeCount type + namedNodeCount predicate + 1

/-- Sound family results below a common named-syntax size. -/
def NamedFamSoundBelow (fuel : Nat) : Prop :=
  ∀ {types kind} (typeScope : Nucleus.HolE.Named.TyScope types)
    (family : EmptyExpr (.kind kind)),
    namedNodeCount family < fuel →
    inferNamedFam (typeBindings typeScope) family = some ⟨kind⟩ →
      ∃ loweredFamily,
        family.lowerFam typeScope = some loweredFamily ∧
        Nucleus.HolE.Kinded loweredFamily

/-- Sound term results below a common named-syntax size. -/
def NamedTmSoundBelow (fuel : Nat) : Prop :=
  ∀ {types depth} (typeScope : Nucleus.HolE.Named.TyScope types)
    (termScope : Nucleus.HolE.Named.TmScope ArenaSig depth)
    (Γ : Nucleus.HolE.BoundCtx ArenaSig types depth),
    Nucleus.HolE.TypedCtx Γ → TmScopeAgrees typeScope termScope Γ →
    ∀ (term : EmptyTm) (type : EmptyTy),
      namedNodeCount term < fuel →
      inferNamedTm (typeBindings typeScope) term = some type →
        ∃ loweredTerm loweredType,
          term.lowerTm typeScope termScope = some loweredTerm ∧
          type.lowerTy typeScope = some loweredType ∧
          Nucleus.HolE.HasType Γ loweredTerm loweredType

private theorem named_checker_sound_below (fuel : Nat) :
    NamedFamSoundBelow fuel ∧ NamedTmSoundBelow fuel := by
  induction fuel with
  | zero => simp [NamedFamSoundBelow, NamedTmSoundBelow]
  | succ fuel ih =>
      constructor
      · intro types kind typeScope family smaller accepted
        cases family with
        | boolTy =>
            exact ⟨.boolTy, by
              simp [Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerFam], .boolTy⟩
        | arr domain codomain =>
            simp only [inferNamedFam, inferNamed] at accepted
            obtain ⟨domainKind, domainInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            obtain ⟨codomainKind, codomainInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            split at accepted <;> try contradiction
            rename_i kinds
            have domainKindEq : domainKind = ⟨.star⟩ := by
              cases domainKind
              cases kinds.1
              rfl
            have codomainKindEq : codomainKind = ⟨.star⟩ := by
              cases codomainKind
              cases kinds.2
              rfl
            have domainInferred' :
                inferNamedFam (typeBindings typeScope) domain = some ⟨.star⟩ := by
              simpa [inferNamedFam, Inferred, domainKindEq] using domainInferred
            have codomainInferred' :
                inferNamedFam (typeBindings typeScope) codomain = some ⟨.star⟩ := by
              simpa [inferNamedFam, Inferred, codomainKindEq] using codomainInferred
            have domainResult := ih.1 typeScope domain (by
              have : namedNodeCount domain < namedNodeCount
                  (Nucleus.Hol.Ethane.Expr.arr domain codomain) := by
                simp [namedNodeCount]
              omega) domainInferred'
            have codomainResult := ih.1 typeScope codomain (by
              have : namedNodeCount codomain < namedNodeCount
                  (Nucleus.Hol.Ethane.Expr.arr domain codomain) := by
                simp [namedNodeCount]
              omega) codomainInferred'
            obtain ⟨loweredDomain, domainLowering, domainKinded⟩ := domainResult
            obtain ⟨loweredCodomain, codomainLowering, codomainKinded⟩ := codomainResult
            change Nucleus.HolE.Named.lowerFam typeScope domain.toHolE =
              some loweredDomain at domainLowering
            change Nucleus.HolE.Named.lowerFam typeScope codomain.toHolE =
              some loweredCodomain at codomainLowering
            exact ⟨.arr loweredDomain loweredCodomain, by
              simp [Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerFam, domainLowering, codomainLowering],
              .arr domainKinded codomainKinded⟩
        | tyApp function argument =>
            rename_i domain
            simp only [inferNamedFam, inferNamed] at accepted
            obtain ⟨functionKind, functionInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            obtain ⟨argumentKind, argumentInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            split at accepted <;> try contradiction
            rename_i kinds
            have functionKindEq : functionKind = ⟨.arr domain kind⟩ := by
              cases functionKind
              cases kinds.1
              rfl
            have argumentKindEq : argumentKind = ⟨domain⟩ := by
              cases argumentKind
              cases kinds.2
              rfl
            have functionInferred' : inferNamedFam (typeBindings typeScope) function =
                some ⟨.arr domain kind⟩ := by
              simpa [inferNamedFam, Inferred, functionKindEq] using functionInferred
            have argumentInferred' : inferNamedFam (typeBindings typeScope) argument =
                some ⟨domain⟩ := by
              simpa [inferNamedFam, Inferred, argumentKindEq] using argumentInferred
            have functionResult := ih.1 typeScope function (by
              have : namedNodeCount function < namedNodeCount
                  (Nucleus.Hol.Ethane.Expr.tyApp function argument) := by
                simp [namedNodeCount]
              omega) functionInferred'
            have argumentResult := ih.1 typeScope argument (by
              have : namedNodeCount argument < namedNodeCount
                  (Nucleus.Hol.Ethane.Expr.tyApp function argument) := by
                simp [namedNodeCount]
              omega) argumentInferred'
            obtain ⟨loweredFunction, functionLowering, functionKinded⟩ := functionResult
            obtain ⟨loweredArgument, argumentLowering, argumentKinded⟩ := argumentResult
            change Nucleus.HolE.Named.lowerFam typeScope function.toHolE =
              some loweredFunction at functionLowering
            change Nucleus.HolE.Named.lowerFam typeScope argument.toHolE =
              some loweredArgument at argumentLowering
            exact ⟨.tyApp loweredFunction loweredArgument, by
              simp [Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerFam, functionLowering, argumentLowering],
              .tyApp functionKinded argumentKinded⟩
        | @tyLam domain codomain name body =>
            simp only [inferNamedFam, inferNamed] at accepted
            obtain ⟨bodyKind, bodyInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            split at accepted <;> try contradiction
            rename_i bodyKindEq
            have bodyKindEq' : bodyKind = ⟨codomain⟩ := by
              cases bodyKind
              cases bodyKindEq
              rfl
            have bodyInferred' : inferNamedFam
                (typeBindings typeScope ++ [(name, domain)]) body = some ⟨codomain⟩ := by
              simpa [inferNamedFam, Inferred, bodyKindEq'] using bodyInferred
            have bodyResult := ih.1
              (.cons (kind := domain) name typeScope) body (by
                simp [namedNodeCount] at smaller
                omega) (by
                  simpa [typeBindings] using bodyInferred')
            obtain ⟨loweredBody, bodyLowering, bodyKinded⟩ := bodyResult
            change Nucleus.HolE.Named.lowerFam
              (.cons (kind := domain) name typeScope) body.toHolE =
                some loweredBody at bodyLowering
            exact ⟨.tyLam loweredBody, by
              simp [Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerFam, bodyLowering],
              .tyLam bodyKinded⟩
        | tyFv name kind =>
            simp only [inferNamedFam, inferNamed] at accepted
            split at accepted <;> try contradiction
            rename_i present
            cases Option.some.inj accepted
            obtain ⟨typeVariable, lookup⟩ :=
              (lookupTy_isSome_iff ⟨name, kind⟩).mpr present
            exact ⟨.tyBv typeVariable, by
              simp [Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerFam, lookup],
              .tyBv typeVariable⟩
        | model name predicate =>
            simp only [inferNamedFam, inferNamed] at accepted
            obtain ⟨predicateType, predicateInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            split at accepted <;> try contradiction
            rename_i predicateBool
            cases Option.some.inj accepted
            have predicateResult := ih.2
              (.cons (kind := .star) name typeScope)
              (.nil : Nucleus.HolE.Named.TmScope ArenaSig 0)
              Nucleus.HolE.emptyBound (fun index => Fin.elim0 index)
              (TmScopeAgrees.nil _) predicate .boolTy (by
                have : namedNodeCount predicate < namedNodeCount
                    (Nucleus.Hol.Ethane.Expr.model name predicate) := by
                  simp [namedNodeCount]
                omega) (by
                  have typeEq : predicateType = (.boolTy : EmptyTy) :=
                    (sameFamily_eq_true_iff _ _).mp predicateBool
                  simpa [inferNamedTm, Inferred, typeBindings, typeEq]
                    using predicateInferred)
            obtain ⟨loweredPredicate, loweredType, predicateLowering,
              typeLowering, predicateTyped⟩ := predicateResult
            have loweredTypeEq : loweredType = (.boolTy : Nucleus.HolE.Ty ArenaSig _) := by
              have opposite : (.boolTy : Nucleus.HolE.Ty ArenaSig _) = loweredType := by
                simpa using typeLowering
              exact opposite.symm
            subst loweredType
            change Nucleus.HolE.Named.lowerTm
              (.cons (kind := .star) name typeScope) .nil predicate.toHolE =
                some loweredPredicate at predicateLowering
            exact ⟨.model loweredPredicate, by
              simp [Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerFam, predicateLowering],
              .model predicateTyped⟩
        | primFam symbol => exact nomatch symbol
      · intro types depth typeScope termScope Γ typedContext agrees term type
          smaller accepted
        cases term with
        | tyExists name predicate =>
            simp only [inferNamedTm, inferNamed] at accepted
            obtain ⟨predicateType, predicateInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            split at accepted <;> try contradiction
            rename_i predicateBool
            have typeEq : (.boolTy : EmptyTy) = type := Option.some.inj accepted
            subst type
            have predicateResult := ih.2
              (.cons (kind := .star) name typeScope)
              (.nil : Nucleus.HolE.Named.TmScope ArenaSig 0)
              Nucleus.HolE.emptyBound (fun index => Fin.elim0 index)
              (TmScopeAgrees.nil _) predicate .boolTy (by
                have : namedNodeCount predicate < namedNodeCount
                    (Nucleus.Hol.Ethane.Expr.tyExists name predicate) := by
                  simp [namedNodeCount]
                omega) (by
                  have typeEq : predicateType = (.boolTy : EmptyTy) :=
                    (sameFamily_eq_true_iff _ _).mp predicateBool
                  simpa [inferNamedTm, Inferred, typeBindings, typeEq]
                    using predicateInferred)
            obtain ⟨loweredPredicate, loweredType, predicateLowering,
              typeLowering, predicateTyped⟩ := predicateResult
            have loweredTypeEq : loweredType = (.boolTy : Nucleus.HolE.Ty ArenaSig _) := by
              have opposite : (.boolTy : Nucleus.HolE.Ty ArenaSig _) = loweredType := by
                simpa using typeLowering
              exact opposite.symm
            subst loweredType
            change Nucleus.HolE.Named.lowerTm
              (.cons (kind := .star) name typeScope) .nil predicate.toHolE =
                some loweredPredicate at predicateLowering
            exact ⟨.tyExists loweredPredicate, .boolTy, by
              simp [Nucleus.Hol.Ethane.Expr.lowerTm, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerTm, predicateLowering], lowerTy_boolTy _,
              .tyExists predicateTyped⟩
        | primTm symbol => exact nomatch symbol
        | tmFv name family =>
            simp only [inferNamedTm, inferNamed] at accepted
            obtain ⟨familyKind, familyInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            split at accepted <;> try contradiction
            rename_i familyStar
            have typeEq : family = type := Option.some.inj accepted
            subst type
            have familyKindEq : familyKind = ⟨.star⟩ := by
              cases familyKind
              cases familyStar
              rfl
            have familyInferred' : inferNamedFam (typeBindings typeScope) family =
                some ⟨.star⟩ := by
              simpa [inferNamedFam, Inferred, familyKindEq] using familyInferred
            have familyResult := ih.1 typeScope family (by
              simp [namedNodeCount] at smaller
              omega) familyInferred'
            obtain ⟨loweredFamily, familyLowering, familyKinded⟩ := familyResult
            change Nucleus.HolE.Named.lowerFam typeScope family.toHolE =
              some loweredFamily at familyLowering
            cases found : Nucleus.HolE.Named.lookupTm ⟨name, family.toHolE⟩ termScope with
            | none =>
                exact ⟨.fv name loweredFamily, loweredFamily, by
                  simp [Nucleus.Hol.Ethane.Expr.lowerTm, Nucleus.Hol.Ethane.Expr.lower,
                    Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                    Nucleus.HolE.Named.lowerTm, found, familyLowering],
                  familyLowering, .fv name familyKinded⟩
            | some index =>
                obtain ⟨contextFamily, contextLowering, contextEq⟩ :=
                  agrees ⟨name, family.toHolE⟩ index found
                have contextFamilyEq : contextFamily = loweredFamily := by
                  rw [familyLowering] at contextLowering
                  exact Option.some.inj contextLowering.symm
                have contextFinal : Γ index = loweredFamily :=
                  contextEq.trans contextFamilyEq
                exact ⟨.bv index, loweredFamily, by
                  simp [Nucleus.Hol.Ethane.Expr.lowerTm, Nucleus.Hol.Ethane.Expr.lower,
                    Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                    Nucleus.HolE.Named.lowerTm, found],
                  familyLowering, .bv (contextFinal ▸ familyKinded) contextFinal⟩
        | app function argument =>
            simp only [inferNamedTm, inferNamed] at accepted
            obtain ⟨functionType, functionInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            obtain ⟨domain, codomain, functionTypeEq⟩ :
                ∃ domain codomain, functionType = .arr domain codomain := by
              cases functionType with
              | arr domain codomain => exact ⟨domain, codomain, rfl⟩
              | boolTy | tyApp | tyFv | model => simp_all
              | primFam symbol => exact nomatch symbol
            subst functionType
            obtain ⟨argumentType, argumentInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            split at accepted <;> try contradiction
            rename_i argumentEq
            have typeEq : codomain = type := Option.some.inj accepted
            subst type
            have functionResult := ih.2 typeScope termScope Γ typedContext agrees
              function (.arr domain codomain) (by
                have : namedNodeCount function < namedNodeCount
                    (Nucleus.Hol.Ethane.Expr.app function argument) := by
                  simp [namedNodeCount]
                omega) (by simpa [inferNamedTm, Inferred] using functionInferred)
            have argumentTypeEq : argumentType = domain :=
              (sameFamily_eq_true_iff _ _).mp argumentEq
            have argumentResult := ih.2 typeScope termScope Γ typedContext agrees
              argument domain (by
                have : namedNodeCount argument < namedNodeCount
                    (Nucleus.Hol.Ethane.Expr.app function argument) := by
                  simp [namedNodeCount]
                omega) (by simpa [inferNamedTm, Inferred, argumentTypeEq]
                  using argumentInferred)
            obtain ⟨loweredFunction, loweredFunctionType, functionLowering,
              functionTypeLowering, functionTyped⟩ := functionResult
            obtain ⟨loweredArgument, loweredDomain, argumentLowering,
              domainLowering, argumentTyped⟩ := argumentResult
            have codomainExists : ∃ loweredCodomain,
                codomain.lowerTy typeScope = some loweredCodomain := by
              cases codomainLowering : codomain.lowerTy typeScope with
              | none =>
                  have domainLowering' : Nucleus.HolE.Named.lowerFam typeScope
                      domain.toHolE = some loweredDomain := domainLowering
                  have codomainLowering' : Nucleus.HolE.Named.lowerFam typeScope
                      codomain.toHolE = none := codomainLowering
                  simp [Nucleus.Hol.Ethane.Expr.lowerTy,
                    Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                    Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                    Nucleus.HolE.Named.lowerFam, domainLowering',
                    codomainLowering'] at functionTypeLowering
              | some loweredCodomain => exact ⟨loweredCodomain, rfl⟩
            obtain ⟨loweredCodomain, codomainLowering⟩ := codomainExists
            have functionTypeEq : loweredFunctionType = .arr loweredDomain loweredCodomain := by
              have domainLowering' : Nucleus.HolE.Named.lowerFam typeScope
                  domain.toHolE = some loweredDomain := domainLowering
              have codomainLowering' : Nucleus.HolE.Named.lowerFam typeScope
                  codomain.toHolE = some loweredCodomain := codomainLowering
              have reduced : some (.arr loweredDomain loweredCodomain) =
                  some loweredFunctionType := by
                simpa [Nucleus.Hol.Ethane.Expr.lowerTy,
                  Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                  Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                  Nucleus.HolE.Named.lowerFam, domainLowering',
                  codomainLowering'] using functionTypeLowering
              exact (Option.some.inj reduced).symm
            subst loweredFunctionType
            change Nucleus.HolE.Named.lowerTm typeScope termScope function.toHolE =
              some loweredFunction at functionLowering
            change Nucleus.HolE.Named.lowerTm typeScope termScope argument.toHolE =
              some loweredArgument at argumentLowering
            exact ⟨.app loweredFunction loweredArgument, loweredCodomain, by
              simp [Nucleus.Hol.Ethane.Expr.lowerTm, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerTm, functionLowering, argumentLowering],
              codomainLowering, .app functionTyped argumentTyped⟩
        | lam name domain body =>
            simp only [inferNamedTm, inferNamed] at accepted
            obtain ⟨domainKind, domainInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            have domainStar : domainKind.down = .star := by
              by_contra rejected
              simp [rejected] at accepted
            simp only [domainStar, if_true] at accepted
            obtain ⟨codomain, bodyInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            have typeEq : (.arr domain codomain : EmptyTy) = type :=
              Option.some.inj accepted
            subst type
            have domainKindEq : domainKind = ⟨.star⟩ := by
              cases domainKind
              cases domainStar
              rfl
            have domainInferred' : inferNamedFam (typeBindings typeScope) domain =
                some ⟨.star⟩ := by
              simpa [inferNamedFam, Inferred, domainKindEq] using domainInferred
            have domainResult := ih.1 typeScope domain (by
              simp [namedNodeCount] at smaller
              omega) domainInferred'
            obtain ⟨loweredDomain, domainLowering, domainKinded⟩ := domainResult
            have bodyResult := ih.2 typeScope
              (.cons ⟨name, domain.toHolE⟩ termScope)
              (Nucleus.HolE.extendBound loweredDomain Γ)
              (Fin.cases domainKinded typedContext)
              (agrees.cons domainLowering) body codomain (by
                have : namedNodeCount body < namedNodeCount
                    (Nucleus.Hol.Ethane.Expr.lam name domain body) := by
                  simp [namedNodeCount]
                omega) (by simpa [inferNamedTm, Inferred] using bodyInferred)
            obtain ⟨loweredBody, loweredCodomain, bodyLowering,
              codomainLowering, bodyTyped⟩ := bodyResult
            change Nucleus.HolE.Named.lowerFam typeScope domain.toHolE =
              some loweredDomain at domainLowering
            change Nucleus.HolE.Named.lowerTm typeScope
              (.cons ⟨name, domain.toHolE⟩ termScope) body.toHolE =
                some loweredBody at bodyLowering
            change Nucleus.HolE.Named.lowerFam typeScope codomain.toHolE =
              some loweredCodomain at codomainLowering
            exact ⟨.lam loweredDomain loweredBody, .arr loweredDomain loweredCodomain, by
              simp [Nucleus.Hol.Ethane.Expr.lowerTm, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerTm, domainLowering, bodyLowering],
              by simp [Nucleus.Hol.Ethane.Expr.lowerTy,
                Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerFam, domainLowering, codomainLowering],
              .lam loweredBody domainKinded bodyTyped⟩
        | bool value =>
            simp only [inferNamedTm, inferNamed] at accepted
            have typeEq : (.boolTy : EmptyTy) = type := Option.some.inj accepted
            subst type
            exact ⟨.bool value, .boolTy, by
              simp [Nucleus.Hol.Ethane.Expr.lowerTm, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerTm], by
              simp [Nucleus.Hol.Ethane.Expr.lowerTy,
                Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerFam], .bool value⟩
        | eq family left right =>
            simp only [inferNamedTm, inferNamed] at accepted
            obtain ⟨familyKind, familyInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            obtain ⟨leftType, leftInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            obtain ⟨rightType, rightInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            split at accepted <;> try contradiction
            rename_i checks
            have typeEq : (.boolTy : EmptyTy) = type := Option.some.inj accepted
            subst type
            have familyKindEq : familyKind = ⟨.star⟩ := by
              cases familyKind
              cases checks.1
              rfl
            have familyInferred' : inferNamedFam (typeBindings typeScope) family =
                some ⟨.star⟩ := by
              simpa [inferNamedFam, Inferred, familyKindEq] using familyInferred
            have familyResult := ih.1 typeScope family (by
              simp [namedNodeCount] at smaller
              omega) familyInferred'
            obtain ⟨loweredFamily, familyLowering, familyKinded⟩ := familyResult
            have leftEq : leftType = family :=
              (sameFamily_eq_true_iff _ _).mp checks.2.1
            have rightEq : rightType = family :=
              (sameFamily_eq_true_iff _ _).mp checks.2.2
            have leftResult := ih.2 typeScope termScope Γ typedContext agrees left family
              (by
                simp [namedNodeCount] at smaller
                omega) (by simpa [inferNamedTm, Inferred, leftEq] using leftInferred)
            have rightResult := ih.2 typeScope termScope Γ typedContext agrees right family
              (by
                simp [namedNodeCount] at smaller
                omega) (by simpa [inferNamedTm, Inferred, rightEq] using rightInferred)
            obtain ⟨loweredLeft, leftFamily, leftLowering, leftTypeLowering, leftTyped⟩ :=
              leftResult
            obtain ⟨loweredRight, rightFamily, rightLowering, rightTypeLowering,
              rightTyped⟩ := rightResult
            change family.lowerTy typeScope = some loweredFamily at familyLowering
            have leftFamilyEq : leftFamily = loweredFamily := by
              rw [familyLowering] at leftTypeLowering
              exact Option.some.inj leftTypeLowering.symm
            have rightFamilyEq : rightFamily = loweredFamily := by
              rw [familyLowering] at rightTypeLowering
              exact Option.some.inj rightTypeLowering.symm
            subst leftFamily
            subst rightFamily
            change Nucleus.HolE.Named.lowerFam typeScope family.toHolE =
              some loweredFamily at familyLowering
            change Nucleus.HolE.Named.lowerTm typeScope termScope left.toHolE =
              some loweredLeft at leftLowering
            change Nucleus.HolE.Named.lowerTm typeScope termScope right.toHolE =
              some loweredRight at rightLowering
            exact ⟨.eq loweredFamily loweredLeft loweredRight, .boolTy, by
              simp [Nucleus.Hol.Ethane.Expr.lowerTm, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerTm, familyLowering, leftLowering, rightLowering],
              lowerTy_boolTy _, .eq familyKinded leftTyped rightTyped⟩
        | eps family predicate =>
            simp only [inferNamedTm, inferNamed] at accepted
            obtain ⟨familyKind, familyInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            obtain ⟨predicateType, predicateInferred, accepted⟩ :=
              Option.bind_eq_some_iff.mp accepted
            split at accepted <;> try contradiction
            rename_i checks
            have typeEq : family = type := Option.some.inj accepted
            subst type
            have familyKindEq : familyKind = ⟨.star⟩ := by
              cases familyKind
              cases checks.1
              rfl
            have familyInferred' : inferNamedFam (typeBindings typeScope) family =
                some ⟨.star⟩ := by
              simpa [inferNamedFam, Inferred, familyKindEq] using familyInferred
            have familyResult := ih.1 typeScope family (by
              simp [namedNodeCount] at smaller
              omega) familyInferred'
            obtain ⟨loweredFamily, familyLowering, familyKinded⟩ := familyResult
            have predicateTypeEq : predicateType = .arr family .boolTy :=
              (sameFamily_eq_true_iff _ _).mp checks.2
            have predicateResult := ih.2 typeScope termScope Γ typedContext agrees
              predicate (.arr family .boolTy) (by
                simp [namedNodeCount] at smaller
                omega) (by simpa [inferNamedTm, Inferred, predicateTypeEq]
                  using predicateInferred)
            obtain ⟨loweredPredicate, loweredPredicateType, predicateLowering,
              predicateTypeLowering, predicateTyped⟩ := predicateResult
            have predicateTypeExpected :
                loweredPredicateType = .arr loweredFamily .boolTy := by
              have familyLowering' : Nucleus.HolE.Named.lowerFam typeScope
                  family.toHolE = some loweredFamily := familyLowering
              have reduced : some (.arr loweredFamily .boolTy) =
                  some loweredPredicateType := by
                simpa [Nucleus.Hol.Ethane.Expr.lowerTy,
                  Nucleus.Hol.Ethane.Expr.lowerFam, Nucleus.Hol.Ethane.Expr.lower,
                  Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                  Nucleus.HolE.Named.lowerFam, familyLowering'] using predicateTypeLowering
              exact (Option.some.inj reduced).symm
            subst loweredPredicateType
            change Nucleus.HolE.Named.lowerFam typeScope family.toHolE =
              some loweredFamily at familyLowering
            change Nucleus.HolE.Named.lowerTm typeScope termScope predicate.toHolE =
              some loweredPredicate at predicateLowering
            exact ⟨.eps loweredFamily loweredPredicate, loweredFamily, by
              simp [Nucleus.Hol.Ethane.Expr.lowerTm, Nucleus.Hol.Ethane.Expr.lower,
                Nucleus.Hol.Ethane.Expr.toHolE, Nucleus.HolE.Named.lower,
                Nucleus.HolE.Named.lowerTm, familyLowering, predicateLowering],
              familyLowering, .eps familyKinded predicateTyped⟩

/-- The direct Rust family pass lowers to a valid locally nameless family. -/
theorem inferNamedFam_sound {family : EmptyExpr (.kind kind)}
    (accepted : inferNamedFam (typeBindings typeScope) family = some ⟨kind⟩) :
    ∃ loweredFamily, family.lowerFam typeScope = some loweredFamily ∧
      Nucleus.HolE.Kinded loweredFamily :=
  (named_checker_sound_below (namedNodeCount family + 1)).1 typeScope family
    (by omega) accepted

/-- The direct Rust term pass lowers to a valid locally nameless term. -/
theorem inferNamedTm_sound
    (typedContext : Nucleus.HolE.TypedCtx Γ)
    (agrees : TmScopeAgrees typeScope termScope Γ)
    {term : EmptyTm} {type : EmptyTy}
    (accepted : inferNamedTm (typeBindings typeScope) term = some type) :
    ∃ loweredTerm loweredType,
      term.lowerTm typeScope termScope = some loweredTerm ∧
      type.lowerTy typeScope = some loweredType ∧
      Nucleus.HolE.HasType Γ loweredTerm loweredType :=
  (named_checker_sound_below (namedNodeCount term + 1)).2 typeScope termScope Γ
    typedContext agrees term type (by omega) accepted

/-- The named checker used by Rust is sound for the trusted Ethane judgment. -/
theorem Value.rustCheck_sound {value : Value} (accepted : value.rustCheck = true) :
    value.WellFormed := by
  cases value with
  | kind value => trivial
  | family familyKind expression =>
      simp only [Value.rustCheck] at accepted
      cases inferred : inferNamedFam [] expression with
      | none => simp [inferred] at accepted
      | some actual =>
        have accepted' : decide (actual.down = familyKind) = true := by
          simpa [inferred] using accepted
        have actualEq : actual.down = familyKind := of_decide_eq_true accepted'
        have actualLiftEq : actual = ⟨familyKind⟩ := by
          cases actual
          cases actualEq
          rfl
        have exactInference : inferNamedFam
            (typeBindings (.nil : Nucleus.HolE.Named.TyScope [])) expression =
              some ⟨familyKind⟩ := by
          simpa [typeBindings, actualLiftEq] using inferred
        obtain ⟨lowered, lowering, kinded⟩ :=
          inferNamedFam_sound exactInference
        exact Nucleus.Hol.Ethane.Checks.complete lowering rfl kinded
  | term type expression =>
      simp only [Value.rustCheck] at accepted
      cases kindResult : inferNamedFam [] type with
      | none => simp [kindResult] at accepted
      | some liftedKind =>
        cases termResult : inferNamedTm [] expression with
        | none => simp [kindResult, termResult] at accepted
        | some inferredType =>
          cases liftedKind with
          | up kind =>
            cases kind with
            | arr domain codomain => simp [kindResult, termResult] at accepted
            | star =>
              have inferredTypeEq : inferredType = type :=
                (sameFamily_eq_true_iff _ _).mp (by
                  simpa [kindResult, termResult] using accepted)
              subst inferredType
              have exactInference : inferNamedTm
                  (typeBindings (.nil : Nucleus.HolE.Named.TyScope [])) expression =
                    some type := by
                simpa [typeBindings] using termResult
              obtain ⟨loweredTerm, loweredType, termLowering, typeLowering, typing⟩ :=
                inferNamedTm_sound (fun index => Fin.elim0 index)
                  (TmScopeAgrees.nil _) exactInference
              exact Nucleus.Hol.Ethane.Checks.complete termLowering (by
                change (do
                  let lowered ← type.lowerTy (.nil : Nucleus.HolE.Named.TyScope [])
                  pure (Nucleus.HolE.Classification.tm lowered)) =
                    some (Nucleus.HolE.Classification.tm loweredType)
                rw [typeLowering]
                rfl) typing

end Nucleus.Hol.Ethane.OneBased
