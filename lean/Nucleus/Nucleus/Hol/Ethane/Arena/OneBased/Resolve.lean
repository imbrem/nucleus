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

/-- Elaborate one expression after all referenced values have been resolved.
The domain and codomain kinds of `ty.app` and `ty.lam`, and the operand type
of `tm.eq`, are recovered from their children. -/
private noncomputable def sameSyntax (left right : EmptySyn) : Bool := by
  classical
  exact decide (left = right)

private def tyFvName? {kind : Kind} : EmptyExpr (.kind kind) → Option Nat
  | .tyFv name _ => some name
  | _ => none

noncomputable def elaborateExpr
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
noncomputable def resolveForeignUsing?
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
noncomputable def resolveAt? : Nat → Resolver → Arena → Ref → Option Value
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
noncomputable def resolveForeignAt? (fuel : Nat) (resolve : Resolver)
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

/-- Sorting denotation of a virtual sort-specific reference row. -/
def ProxySortingClaim (expected : TagSort) (resolve : Resolver) (arena : Arena)
    (source : ImportId) (foreignRef sort : Ref) : Prop :=
  ∃ entry imported value classifier,
    arena.import? source = some entry ∧
    resolveImport? resolve entry = some imported ∧
    Resolves resolve imported foreignRef value ∧
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

theorem metaWf_iff_proxy (resolve : Resolver) (arena : Arena)
    (source : ImportId) (foreignRef sort : Ref) :
    MetaClaim resolve arena (.wf source foreignRef sort) ↔
      ProxySortingClaim .tm resolve arena source foreignRef sort ∨
      ProxySortingClaim .ty resolve arena source foreignRef sort := by
  constructor
  · rintro ⟨entry, imported, value, classifier, importLookup, resolvedImport,
      valueResolved, classifierResolved, sorted⟩
    cases value with
    | kind value => cases classifier <;> simp [Value.HasSort] at sorted
    | family kind expression =>
        right
        exact ⟨entry, imported, .family kind expression, classifier, importLookup,
          resolvedImport, valueResolved, rfl, classifierResolved, sorted⟩
    | term type expression =>
        left
        exact ⟨entry, imported, .term type expression, classifier, importLookup,
          resolvedImport, valueResolved, rfl, classifierResolved, sorted⟩
  · rintro (claim | claim) <;>
      rcases claim with ⟨entry, imported, value, classifier, importLookup,
        resolvedImport, valueResolved, _category, classifierResolved, sorted⟩ <;>
      exact ⟨entry, imported, value, classifier, importLookup, resolvedImport,
        valueResolved, classifierResolved, sorted⟩

end Nucleus.Hol.Ethane.OneBased
