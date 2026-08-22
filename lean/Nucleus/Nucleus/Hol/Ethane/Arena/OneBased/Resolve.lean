import Nucleus.Hol.Ethane.Arena.OneBased.Structural
import Nucleus.Hol.Ethane.Typing

/-!
# Resolving one-based Ethane arenas

Raw rows elaborate relative to an abstract link resolver.  Literal imports
are immediate, null imports are unavailable, and links consult the resolver.
The resolver returns arenas rather than logical facts: kinding and typing are
reconstructed from the row graph below.

Resolution is fuel-bounded.  This makes cycles and adversarial import graphs
recoverably unavailable without changing the meaning of any acyclic graph.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus

abbrev ArenaSig : Signature := fun _ => Empty
abbrev EmptySyn := Nucleus.Hol.Ethane.Syn ArenaSig Nat
abbrev EmptyExpr (sort : HolSort) := Nucleus.Hol.Ethane.Expr ArenaSig Nat sort
abbrev EmptyTy := Nucleus.Hol.Ethane.Ty ArenaSig Nat
abbrev EmptyTm := Nucleus.Hol.Ethane.Tm ArenaSig Nat

/-- A fully classified value reconstructed from raw arena rows. -/
inductive Value where
  | kind (value : Kind)
  | family (kind : Kind) (expression : EmptyExpr (.kind kind))
  | term (type : EmptyTy) (expression : EmptyTm)

namespace Value

def tagSort : Value → TagSort
  | .kind _ => .kind
  | .family _ _ => .ty
  | .term _ _ => .tm

def syntax? : Value → Option EmptySyn
  | .kind _ => none
  | .family _ expression | .term _ expression => some expression.erase

/-- The second value classifies the first one. Kinds need no arena row for
the meta-sort above them. -/
def HasSort : Value → Value → Prop
  | .family expected _, .kind actual => expected = actual
  | .term expected _, .family .star actual => expected = actual
  | _, _ => False

/-- Forget classifications into the existing Ethane forest value. -/
def toForestValue : Value →
    Nucleus.Hol.Ethane.Arena.Value ArenaSig Nat
  | .kind value => .kind value
  | .family _ expression | .term _ expression => .syntax expression.erase

@[simp] theorem check_family (kind : Kind) (expression : EmptyExpr (.kind kind)) :
    Nucleus.Hol.Ethane.Syn.check (.kind kind) expression.erase = some expression :=
  Nucleus.Hol.Ethane.Expr.check_erase expression

@[simp] theorem check_term (expression : EmptyTm) :
    Nucleus.Hol.Ethane.Syn.check .tm expression.erase = some expression :=
  Nucleus.Hol.Ethane.Expr.check_erase expression

@[simp] theorem check_term_type (type : EmptyTy) :
    Nucleus.Hol.Ethane.Syn.check (.kind .star) type.erase = some type :=
  Nucleus.Hol.Ethane.Expr.check_erase type

end Value

/-- Abstract, retryable resolution of content-addressed arena links. -/
abbrev Resolver := Link → Option Arena

namespace Arena

/-- One-based lookup in the explicit import table. -/
def import? (arena : Arena) (source : ImportId) : Option Import :=
  arena.imports[(source.value.toNat - 1)]?

@[simp] theorem import?_mk (imports : List Import) (axs : Finset String)
    (defs : List detail.Row) (ctx : Finset Ref) (assume assert : List Meta)
    (source : ImportId) :
    (Arena.mk imports axs defs ctx assume assert).import? source =
      imports[(source.value.toNat - 1)]? := rfl

end Arena

/-- Resolve one raw import without traversing its definitions. -/
def resolveImport? (resolve : Resolver) : Import → Option Arena
  | .null => none
  | .literal arena => some arena
  | .link link => resolve link

@[simp] theorem resolveImport?_null (resolve : Resolver) :
    resolveImport? resolve .null = none := rfl

@[simp] theorem resolveImport?_literal (resolve : Resolver) (arena : Arena) :
    resolveImport? resolve (.literal arena) = some arena := rfl

@[simp] theorem resolveImport?_link (resolve : Resolver) (link : Link) :
    resolveImport? resolve (.link link) = resolve link := rfl

/-- Executable structural equality for empty-signature Ethane syntax. -/
def sameSyntax : EmptySyn → EmptySyn → Bool
  | .boolTy, .boolTy => true
  | .arr leftDomain leftCodomain, .arr rightDomain rightCodomain =>
      sameSyntax leftDomain rightDomain && sameSyntax leftCodomain rightCodomain
  | .tyApp leftDomain leftCodomain leftFunction leftArgument,
      .tyApp rightDomain rightCodomain rightFunction rightArgument =>
      decide (leftDomain = rightDomain) && decide (leftCodomain = rightCodomain) &&
        sameSyntax leftFunction rightFunction && sameSyntax leftArgument rightArgument
  | .tyLam leftDomain leftCodomain leftName leftBody,
      .tyLam rightDomain rightCodomain rightName rightBody =>
      decide (leftDomain = rightDomain) && decide (leftCodomain = rightCodomain) &&
        decide (leftName = rightName) && sameSyntax leftBody rightBody
  | .tyFv leftName leftKind, .tyFv rightName rightKind =>
      decide (leftName = rightName) && decide (leftKind = rightKind)
  | .tyExists leftName leftPredicate, .tyExists rightName rightPredicate =>
      decide (leftName = rightName) && sameSyntax leftPredicate rightPredicate
  | .model leftName leftPredicate, .model rightName rightPredicate =>
      decide (leftName = rightName) && sameSyntax leftPredicate rightPredicate
  | .primFam _ symbol, _ => nomatch symbol
  | .primTm symbol, _ => nomatch symbol
  | .tmFv leftName leftType, .tmFv rightName rightType =>
      decide (leftName = rightName) && sameSyntax leftType rightType
  | .app leftFunction leftArgument, .app rightFunction rightArgument =>
      sameSyntax leftFunction rightFunction && sameSyntax leftArgument rightArgument
  | .lam leftName leftDomain leftBody, .lam rightName rightDomain rightBody =>
      decide (leftName = rightName) && sameSyntax leftDomain rightDomain &&
        sameSyntax leftBody rightBody
  | .bool left, .bool right => decide (left = right)
  | .eq leftType leftLeft leftRight, .eq rightType rightLeft rightRight =>
      sameSyntax leftType rightType && sameSyntax leftLeft rightLeft &&
        sameSyntax leftRight rightRight
  | .eps leftType leftPredicate, .eps rightType rightPredicate =>
      sameSyntax leftType rightType && sameSyntax leftPredicate rightPredicate
  | _, _ => false

theorem sameSyntax_eq_true_iff (left right : EmptySyn) :
    sameSyntax left right = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [sameSyntax, Bool.and_eq_true, and_assoc] <;> aesop

/-- Elaborate one expression after all referenced values have been resolved.
The domain and codomain kinds of `ty.app` and `ty.lam`, and the operand type
of `tm.eq`, are recovered from their children. -/
private def tyFvName? {kind : Kind} : EmptyExpr (.kind kind) → Option Nat
  | .tyFv name _ => some name
  | _ => none

def elaborateExpr
    (lookupLocal : Ref → Option Value)
    (lookupForeign : ImportId → Ref → Option Value) : detail.Expr → Option Value
  | .kindStar => some (Value.kind .star)
  | .kindArr domain codomain => do
      let Value.kind domain ← lookupLocal domain | none
      let Value.kind codomain ← lookupLocal codomain | none
      return Value.kind (.arr domain codomain)
  | .boolTy => some (Value.family .star .boolTy)
  | .tyArr domain codomain => do
      let Value.family .star domain ← lookupLocal domain | none
      let Value.family .star codomain ← lookupLocal codomain | none
      return Value.family .star (.arr domain codomain)
  | .tyApp function argument => do
      let Value.family (.arr domain codomain) function ← lookupLocal function | none
      let Value.family actual argument ← lookupLocal argument | none
      if equality : actual = domain then
        return Value.family codomain (.tyApp function (equality ▸ argument))
      else none
  | .tyLam binder body => do
      let Value.family domain binder ← lookupLocal binder | none
      match tyFvName? binder with
      | none => none
      | some name => do
          let Value.family codomain body ← lookupLocal body | none
          return Value.family (.arr domain codomain) (.tyLam name body)
  | .tyFv name kind => do
      let Value.kind kind ← lookupLocal kind | none
      return Value.family kind (.tyFv name.toNat kind)
  | .tyExists name predicate => do
      let Value.term .boolTy predicate ← lookupLocal predicate | none
      return Value.term .boolTy (.tyExists name.toNat predicate)
  | .model name predicate => do
      let Value.term .boolTy predicate ← lookupLocal predicate | none
      return Value.family .star (.model name.toNat predicate)
  | .tmFv name type => do
      let Value.family .star type ← lookupLocal type | none
      return Value.term type (.tmFv name.toNat type)
  | .app function argument => do
      let Value.term (.arr domain codomain) function ← lookupLocal function | none
      let Value.term actual argument ← lookupLocal argument | none
      if sameSyntax actual.erase domain.erase then
        return Value.term codomain (.app function argument)
      else none
  | .lam binder body => do
      let Value.term domain (.tmFv name actual) ← lookupLocal binder | none
      let Value.term codomain body ← lookupLocal body | none
      if sameSyntax actual.erase domain.erase then
        return Value.term (.arr domain codomain) (.lam name domain body)
      else none
  | .bool value => some (Value.term .boolTy (.bool value))
  | .eq left right => do
      let Value.term type left ← lookupLocal left | none
      let Value.term actual right ← lookupLocal right | none
      if sameSyntax actual.erase type.erase then
        return Value.term .boolTy (.eq type left right)
      else none
  | .eps type predicate => do
      let Value.family .star type ← lookupLocal type | none
      let Value.term (.arr domain .boolTy) predicate ← lookupLocal predicate | none
      if sameSyntax domain.erase type.erase then
        return Value.term type (.eps type predicate)
      else none
  | .tmRef source foreignRef => do
      let value ← lookupForeign source foreignRef
      if value.tagSort = .tm then some value else none
  | .tyRef source foreignRef => do
      let value ← lookupForeign source foreignRef
      if value.tagSort = .ty then some value else none
  | .kindRef source foreignRef => do
      let value ← lookupForeign source foreignRef
      if value.tagSort = .kind then some value else none

/-- Apply an arena lookup function through the owner's import table. -/
def resolveForeignUsing?
    (resolveValue : Arena → Ref → Option Value) (resolve : Resolver)
    (owner : Arena) (source : ImportId) (foreignRef : Ref) : Option Value :=
  match owner.import? source with
  | none => none
  | some entry =>
      match resolveImport? resolve entry with
      | none => none
      | some imported => resolveValue imported foreignRef

/-- Resolve a row graph. Every local or imported edge consumes one unit of
fuel, so cycles and excessive nesting return `none`. -/
def resolveAt? : Nat → Resolver → Arena → Ref → Option Value
  | 0, _, _, _ => none
  | fuel + 1, resolve, arena, reference =>
      match arena.row? reference with
      | none => none
      | some row =>
          elaborateExpr
            (resolveAt? fuel resolve arena)
            (resolveForeignUsing? (resolveAt? fuel resolve) resolve arena)
            row.expr

/-- Resolve one foreign reference through the owner's import table. -/
def resolveForeignAt? (fuel : Nat) (resolve : Resolver)
    (owner : Arena) (source : ImportId) (foreignRef : Ref) : Option Value :=
  resolveForeignUsing? (resolveAt? fuel resolve) resolve owner source foreignRef

/-- A value is available when some finite resolution bound reconstructs it. -/
def Resolves (resolve : Resolver) (arena : Arena) (reference : Ref) (value : Value) : Prop :=
  ∃ fuel, resolveAt? fuel resolve arena reference = some value

/-- Every local row in a raw arena resolves to a classified value. -/
def FullyResolves (resolve : Resolver) (arena : Arena) : Prop :=
  ∀ reference, reference.value.toNat ≤ arena.defs.length →
    ∃ value, Resolves resolve arena reference value

/-- The raw sorting claim attached to one local row. -/
def SortingClaim (resolve : Resolver) (arena : Arena) (reference : Ref) : Prop :=
  ∃ sort value classifier,
    arena.sort? reference = some sort ∧
    Resolves resolve arena reference value ∧
    Resolves resolve arena sort classifier ∧
    value.HasSort classifier

/-- A foreign value is available through one entry of the owner's import
table.  This formulation deliberately hides whether that entry is literal or
content addressed. -/
def ForeignResolves (resolve : Resolver) (arena : Arena) (source : ImportId)
    (foreignRef : Ref) (value : Value) : Prop :=
  ∃ fuel, resolveForeignAt? fuel resolve arena source foreignRef = some value

/-- Sorting denotation of a sort-specific reference row, without choosing a
local row to contain it.  Kinds have no classifier expression in Ethane, so a
`meta.wf` record can witness only a type-family or term reference. -/
def ProxySortingClaim (expected : TagSort) (resolve : Resolver) (arena : Arena)
    (source : ImportId) (foreignRef sort : Ref) : Prop :=
  ∃ value classifier,
    ForeignResolves resolve arena source foreignRef value ∧
    value.tagSort = expected ∧
    Resolves resolve arena sort classifier ∧
    value.HasSort classifier

/-- Denotation of a premise or conclusion metadata record. -/
def MetaClaim (resolve : Resolver) (arena : Arena) : Meta → Prop
  | .valid source =>
      ∃ entry imported,
        arena.import? source = some entry ∧
        resolveImport? resolve entry = some imported ∧
        FullyResolves resolve imported
  | .wf source foreignRef sort =>
      ∃ entry imported value classifier,
        arena.import? source = some entry ∧
        resolveImport? resolve entry = some imported ∧
        Resolves resolve imported foreignRef value ∧
        Resolves resolve arena sort classifier ∧
        value.HasSort classifier

def Premises (resolve : Resolver) (arena : Arena) : Prop :=
  ∀ record ∈ arena.assume, MetaClaim resolve arena record

def Conclusions (resolve : Resolver) (arena : Arena) : Prop :=
  ∀ record ∈ arena.assert, MetaClaim resolve arena record

@[simp] theorem resolveForeignAt?_literal (fuel : Nat) (resolve : Resolver)
    (owner imported : Arena) (source : ImportId) (foreignRef : Ref)
    (lookup : owner.import? source = some (.literal imported)) :
    resolveForeignAt? fuel resolve owner source foreignRef =
      resolveAt? fuel resolve imported foreignRef := by
  simp [resolveForeignAt?, resolveForeignUsing?, lookup]

@[simp] theorem resolveForeignAt?_link (fuel : Nat) (resolve : Resolver)
    (owner imported : Arena) (source : ImportId) (foreignRef : Ref) (link : Link)
    (lookup : owner.import? source = some (.link link))
    (resolved : resolve link = some imported) :
    resolveForeignAt? fuel resolve owner source foreignRef =
      resolveAt? fuel resolve imported foreignRef := by
  simp [resolveForeignAt?, resolveForeignUsing?, lookup, resolved]

theorem literal_link_agree (fuel : Nat) (literalOwner linkedOwner imported : Arena)
    (source : ImportId) (foreignRef : Ref) (link : Link) (resolve : Resolver)
    (literalLookup : literalOwner.import? source = some (.literal imported))
    (linkLookup : linkedOwner.import? source = some (.link link))
    (resolved : resolve link = some imported) :
    resolveForeignAt? fuel resolve literalOwner source foreignRef =
      resolveForeignAt? fuel resolve linkedOwner source foreignRef := by
  rw [resolveForeignAt?_literal _ _ _ _ _ _ literalLookup,
    resolveForeignAt?_link _ _ _ _ _ _ _ linkLookup resolved]

theorem resolveAt?_tmRef (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (eq sort : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.tmRef source foreignRef, eq, sort⟩) :
    resolveAt? (fuel + 1) resolve arena reference =
      match resolveForeignAt? fuel resolve arena source foreignRef with
      | none => none
      | some value => if value.tagSort = .tm then some value else none := by
  simp only [resolveAt?, lookup, elaborateExpr, resolveForeignAt?]
  cases resolveForeignUsing? (resolveAt? fuel resolve) resolve arena source foreignRef <;> rfl

theorem resolveAt?_tyRef (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (eq sort : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.tyRef source foreignRef, eq, sort⟩) :
    resolveAt? (fuel + 1) resolve arena reference =
      match resolveForeignAt? fuel resolve arena source foreignRef with
      | none => none
      | some value => if value.tagSort = .ty then some value else none := by
  simp only [resolveAt?, lookup, elaborateExpr, resolveForeignAt?]
  cases resolveForeignUsing? (resolveAt? fuel resolve) resolve arena source foreignRef <;> rfl

theorem resolveAt?_kindRef (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (eq sort : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.kindRef source foreignRef, eq, sort⟩) :
    resolveAt? (fuel + 1) resolve arena reference =
      match resolveForeignAt? fuel resolve arena source foreignRef with
      | none => none
      | some value => if value.tagSort = .kind then some value else none := by
  simp only [resolveAt?, lookup, elaborateExpr, resolveForeignAt?]
  cases resolveForeignUsing? (resolveAt? fuel resolve) resolve arena source foreignRef <;> rfl

theorem foreignResolves_iff_import (resolve : Resolver) (arena : Arena)
    (source : ImportId) (foreignRef : Ref) (value : Value) :
    ForeignResolves resolve arena source foreignRef value ↔
      ∃ entry imported,
        arena.import? source = some entry ∧
        resolveImport? resolve entry = some imported ∧
        Resolves resolve imported foreignRef value := by
  constructor
  · rintro ⟨fuel, resolved⟩
    unfold resolveForeignAt? resolveForeignUsing? at resolved
    split at resolved
    next => contradiction
    next entry importLookup =>
      split at resolved
      next => contradiction
      next imported importResolved =>
        exact ⟨entry, imported, importLookup, importResolved, fuel, resolved⟩
  · rintro ⟨entry, imported, importLookup, importResolved, fuel, resolved⟩
    exact ⟨fuel, by
      simp only [resolveForeignAt?, resolveForeignUsing?, importLookup,
        importResolved]
      exact resolved⟩

theorem resolves_tmRef_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (eq sort : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.tmRef source foreignRef, eq, sort⟩) (value : Value) :
    Resolves resolve arena reference value ↔
      value.tagSort = .tm ∧
      ForeignResolves resolve arena source foreignRef value := by
  constructor
  · rintro ⟨fuel, resolved⟩
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      rw [resolveAt?_tmRef fuel resolve arena reference source foreignRef eq sort lookup]
        at resolved
      cases foreign : resolveForeignAt? fuel resolve arena source foreignRef with
      | none =>
        rw [foreign] at resolved
        contradiction
      | some actual =>
        rw [foreign] at resolved
        change (if actual.tagSort = .tm then some actual else none) =
          some value at resolved
        by_cases category : actual.tagSort = .tm
        · rw [if_pos category] at resolved
          have same : actual = value := Option.some.inj resolved
          subst actual
          exact ⟨category, fuel, foreign⟩
        · rw [if_neg category] at resolved
          contradiction
  · rintro ⟨category, fuel, foreign⟩
    refine ⟨fuel + 1, ?_⟩
    rw [resolveAt?_tmRef fuel resolve arena reference source foreignRef eq sort lookup,
      foreign]
    simp [category]

theorem resolves_tyRef_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (eq sort : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.tyRef source foreignRef, eq, sort⟩) (value : Value) :
    Resolves resolve arena reference value ↔
      value.tagSort = .ty ∧
      ForeignResolves resolve arena source foreignRef value := by
  constructor
  · rintro ⟨fuel, resolved⟩
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      rw [resolveAt?_tyRef fuel resolve arena reference source foreignRef eq sort lookup]
        at resolved
      cases foreign : resolveForeignAt? fuel resolve arena source foreignRef with
      | none =>
        rw [foreign] at resolved
        contradiction
      | some actual =>
        rw [foreign] at resolved
        change (if actual.tagSort = .ty then some actual else none) =
          some value at resolved
        by_cases category : actual.tagSort = .ty
        · rw [if_pos category] at resolved
          have same : actual = value := Option.some.inj resolved
          subst actual
          exact ⟨category, fuel, foreign⟩
        · rw [if_neg category] at resolved
          contradiction
  · rintro ⟨category, fuel, foreign⟩
    refine ⟨fuel + 1, ?_⟩
    rw [resolveAt?_tyRef fuel resolve arena reference source foreignRef eq sort lookup,
      foreign]
    simp [category]

theorem resolves_kindRef_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (eq sort : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.kindRef source foreignRef, eq, sort⟩) (value : Value) :
    Resolves resolve arena reference value ↔
      value.tagSort = .kind ∧
      ForeignResolves resolve arena source foreignRef value := by
  constructor
  · rintro ⟨fuel, resolved⟩
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      rw [resolveAt?_kindRef fuel resolve arena reference source foreignRef eq sort lookup]
        at resolved
      cases foreign : resolveForeignAt? fuel resolve arena source foreignRef with
      | none =>
        rw [foreign] at resolved
        contradiction
      | some actual =>
        rw [foreign] at resolved
        change (if actual.tagSort = .kind then some actual else none) =
          some value at resolved
        by_cases category : actual.tagSort = .kind
        · rw [if_pos category] at resolved
          have same : actual = value := Option.some.inj resolved
          subst actual
          exact ⟨category, fuel, foreign⟩
        · rw [if_neg category] at resolved
          contradiction
  · rintro ⟨category, fuel, foreign⟩
    refine ⟨fuel + 1, ?_⟩
    rw [resolveAt?_kindRef fuel resolve arena reference source foreignRef eq sort lookup,
      foreign]
    simp [category]

theorem sortingClaim_tmRef_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef sort : Ref)
    (eq : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.tmRef source foreignRef, eq, some sort⟩) :
    SortingClaim resolve arena reference ↔
      ProxySortingClaim .tm resolve arena source foreignRef sort := by
  constructor
  · rintro ⟨actualSort, value, classifier, sortMember, valueResolved,
      classifierResolved, sorted⟩
    have actualSortEq : actualSort = sort := by
      have reversed : sort = actualSort := by
        simpa [Arena.sort?, lookup] using sortMember
      exact reversed.symm
    subst actualSort
    rw [resolves_tmRef_iff resolve arena reference source foreignRef eq
      (some sort) lookup value] at valueResolved
    exact ⟨value, classifier, valueResolved.2, valueResolved.1,
      classifierResolved, sorted⟩
  · rintro ⟨value, classifier, foreignResolved, category,
      classifierResolved, sorted⟩
    exact ⟨sort, value, classifier, by simp [Arena.sort?, lookup],
      (resolves_tmRef_iff resolve arena reference source foreignRef eq
        (some sort) lookup value).2 ⟨category, foreignResolved⟩,
      classifierResolved, sorted⟩

theorem sortingClaim_tyRef_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef sort : Ref)
    (eq : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.tyRef source foreignRef, eq, some sort⟩) :
    SortingClaim resolve arena reference ↔
      ProxySortingClaim .ty resolve arena source foreignRef sort := by
  constructor
  · rintro ⟨actualSort, value, classifier, sortMember, valueResolved,
      classifierResolved, sorted⟩
    have actualSortEq : actualSort = sort := by
      have reversed : sort = actualSort := by
        simpa [Arena.sort?, lookup] using sortMember
      exact reversed.symm
    subst actualSort
    rw [resolves_tyRef_iff resolve arena reference source foreignRef eq
      (some sort) lookup value] at valueResolved
    exact ⟨value, classifier, valueResolved.2, valueResolved.1,
      classifierResolved, sorted⟩
  · rintro ⟨value, classifier, foreignResolved, category,
      classifierResolved, sorted⟩
    exact ⟨sort, value, classifier, by simp [Arena.sort?, lookup],
      (resolves_tyRef_iff resolve arena reference source foreignRef eq
        (some sort) lookup value).2 ⟨category, foreignResolved⟩,
      classifierResolved, sorted⟩

theorem metaWf_iff_proxy (resolve : Resolver) (arena : Arena)
    (source : ImportId) (foreignRef sort : Ref) :
    MetaClaim resolve arena (.wf source foreignRef sort) ↔
      ProxySortingClaim .tm resolve arena source foreignRef sort ∨
      ProxySortingClaim .ty resolve arena source foreignRef sort := by
  constructor
  · rintro ⟨entry, imported, value, classifier, importLookup, resolvedImport,
      valueResolved, classifierResolved, sorted⟩
    have foreignResolved :
        ForeignResolves resolve arena source foreignRef value :=
      (foreignResolves_iff_import resolve arena source foreignRef value).2
        ⟨entry, imported, importLookup, resolvedImport, valueResolved⟩
    cases value with
    | kind value => cases classifier <;> simp [Value.HasSort] at sorted
    | family kind expression =>
        right
        exact ⟨.family kind expression, classifier, foreignResolved, rfl,
          classifierResolved, sorted⟩
    | term type expression =>
        left
        exact ⟨.term type expression, classifier, foreignResolved, rfl,
          classifierResolved, sorted⟩
  · rintro (claim | claim) <;>
      rcases claim with ⟨value, classifier, foreignResolved,
        _category, classifierResolved, sorted⟩ <;>
      rcases (foreignResolves_iff_import resolve arena source foreignRef value).1
        foreignResolved with
        ⟨entry, imported, importLookup, resolvedImport, valueResolved⟩ <;>
      exact ⟨entry, imported, value, classifier, importLookup, resolvedImport,
        valueResolved, classifierResolved, sorted⟩

/-- `meta.wf` is exactly the inline sorting claim of an actual term proxy. -/
theorem metaWf_iff_tmRef_sortingClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef sort : Ref)
    (eq : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.tmRef source foreignRef, eq, some sort⟩)
    (category : ProxySortingClaim .tm resolve arena source foreignRef sort) :
    MetaClaim resolve arena (.wf source foreignRef sort) ↔
      SortingClaim resolve arena reference := by
  rw [metaWf_iff_proxy, sortingClaim_tmRef_iff resolve arena reference source
    foreignRef sort eq lookup]
  constructor
  · intro _claim
    exact category
  · exact Or.inl

/-- `meta.wf` is exactly the inline sorting claim of an actual type proxy. -/
theorem metaWf_iff_tyRef_sortingClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef sort : Ref)
    (eq : Option Ref)
    (lookup : arena.row? reference =
      some ⟨.tyRef source foreignRef, eq, some sort⟩)
    (category : ProxySortingClaim .ty resolve arena source foreignRef sort) :
    MetaClaim resolve arena (.wf source foreignRef sort) ↔
      SortingClaim resolve arena reference := by
  rw [metaWf_iff_proxy, sortingClaim_tyRef_iff resolve arena reference source
    foreignRef sort eq lookup]
  constructor
  · intro _claim
    exact category
  · exact Or.inr

end Nucleus.Hol.Ethane.OneBased
