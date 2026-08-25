import Nucleus.Hol.Ethane.Arena.OneBased.Structural
import Nucleus.Hol.Ethane.Typing
import Nucleus.Hol.Ethane.Semantics
import Nucleus.Hol.Ethane.Reference
import Nucleus.HolE.Named.Conversion

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
the meta-sort above them. Term classifiers are compared by family conversion,
not literal syntax: the checked fused conversion forest may replace a class
classifier by a semantically equal type. -/
def HasSort : Value → Value → Prop
  | .family expected _, .kind actual => expected = actual
  | .term expected _, .family .star actual =>
      Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) expected.toHolE actual.toHolE)
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

@[simp] theorem import?_withoutSyn (arena : Arena) (source : ImportId) :
    arena.withoutSyn.import? source = arena.import? source := by
  simp [import?]

@[simp] theorem import?_mk (imports : List Import) (axs : Finset String)
    (dense : Dense) (synFacts : List SynSlot) (synFree : Option SynFactId)
    (ctx : Finset Ref) (assume assert : List Meta)
    (source : ImportId) :
    (Arena.mk imports axs dense synFacts synFree ctx assume assert).import? source =
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

/-- Recognize the free-variable binder shape required by type-family lambdas. -/
def tyFvName? {kind : Kind} : EmptyExpr (.kind kind) → Option Nat
  | .tyFv name _ => some name
  | _ => none

/-- Recognize the free term-variable binder shape required by term lambdas. -/
def tmFvData? : EmptyTm → Option (Nat × EmptyTy)
  | .tmFv name type => some (name, type)
  | _ => none

/-- Advertise the classifier shared by every locally constructed term. -/
@[simp] noncomputable def elaborateTerm
    (lookupLocal : Ref → Option Value) (declaredSort : Option Ref)
    (expression : EmptyTm) : Option Value := do
  let some sort := declaredSort | none
  let Value.family .star advertisedType ← lookupLocal sort | none
  return Value.term advertisedType expression

/-- Elaborate one expression after all referenced values have been resolved.
Term syntax is reconstructed from its children, while its advertised type is
always the row's entry in the dense `sort` column. This distinction matters because Rust accepts
term classifiers modulo the type union-find rather than by literal syntax. -/
noncomputable def elaborateExpr
    (lookupLocal : Ref → Option Value)
    (lookupForeign : ImportId → Ref → Option Value)
    (declaredSort : Option Ref) : detail.Expr → Option Value
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
      let Value.term _ predicate ← lookupLocal predicate | none
      elaborateTerm lookupLocal declaredSort (.tyExists name.toNat predicate)
  | .tyForall name predicate => do
      let Value.term _ predicate ← lookupLocal predicate | none
      elaborateTerm lookupLocal declaredSort (.tyForall name.toNat predicate)
  | .model name predicate => do
      let Value.term _ predicate ← lookupLocal predicate | none
      return Value.family .star (.model name.toNat predicate)
  | .tmFv name type => do
      let Value.family .star syntacticType ← lookupLocal type | none
      elaborateTerm lookupLocal declaredSort (.tmFv name.toNat syntacticType)
  | .app function argument => do
      let Value.term _ function ← lookupLocal function | none
      let Value.term _ argument ← lookupLocal argument | none
      elaborateTerm lookupLocal declaredSort (.app function argument)
  | .lam binder body => do
      let Value.term _ binder ← lookupLocal binder | none
      let some (name, syntacticDomain) := tmFvData? binder | none
      let Value.term _ body ← lookupLocal body | none
      elaborateTerm lookupLocal declaredSort (.lam name syntacticDomain body)
  | .bool value => elaborateTerm lookupLocal declaredSort (.bool value)
  | .op1 op operand => do
      let Value.term _ operand ← lookupLocal operand | none
      elaborateTerm lookupLocal declaredSort (op.lower operand)
  | .op2 op left right => do
      let Value.term _ left ← lookupLocal left | none
      let Value.term _ right ← lookupLocal right | none
      elaborateTerm lookupLocal declaredSort (op.lower left right)
  | .eq type left right => do
      let Value.family .star syntacticType ← lookupLocal type | none
      let Value.term _ left ← lookupLocal left | none
      let Value.term _ right ← lookupLocal right | none
      elaborateTerm lookupLocal declaredSort (.eq syntacticType left right)
  | .eps type predicate => do
      let Value.family .star type ← lookupLocal type | none
      let Value.term _ predicate ← lookupLocal predicate | none
      elaborateTerm lookupLocal declaredSort (.eps type predicate)
  | .tmRef source foreignRef => do
      let value ← lookupForeign source foreignRef
      if value.tagSort = .tm then some value else none
  | .tyRef source foreignRef => do
      let value ← lookupForeign source foreignRef
      if value.tagSort = .ty then some value else none
  | .kindRef source foreignRef => do
      let value ← lookupForeign source foreignRef
      if value.tagSort = .kind then some value else none

/-- Every successful value in an optional computation has one category. -/
def HasTagSort (expected : TagSort) : Option Value → Prop
  | none => True
  | some value => value.tagSort = expected

namespace HasTagSort

theorem bind {α : Type u} {expected : TagSort} {input : Option α}
    {next : α → Option Value}
    (valid : ∀ value, HasTagSort expected (next value)) :
    HasTagSort expected (input.bind next) := by
  cases input <;> simp_all [HasTagSort]

theorem bindKind {expected : TagSort} {input : Option Value}
    {next : Kind → Option Value}
    (valid : ∀ kind, HasTagSort expected (next kind)) :
    HasTagSort expected (input.bind fun
      | .kind kind => next kind
      | _ => none) := by
  apply bind
  intro value
  cases value <;> simp_all [HasTagSort]

theorem bindFamily {expected : TagSort} {input : Option Value}
    {next : ∀ kind, EmptyExpr (.kind kind) → Option Value}
    (valid : ∀ kind expression, HasTagSort expected (next kind expression)) :
    HasTagSort expected (input.bind fun
      | .family kind expression => next kind expression
      | _ => none) := by
  apply bind
  intro value
  cases value <;> simp_all [HasTagSort]

theorem bindFamilyStar {expected : TagSort} {input : Option Value}
    {next : EmptyTy → Option Value}
    (valid : ∀ expression, HasTagSort expected (next expression)) :
    HasTagSort expected (input.bind fun
      | .family .star expression => next expression
      | _ => none) := by
  apply bind
  intro value
  cases value with
  | kind => simp [HasTagSort]
  | family kind expression =>
      cases kind <;> simp_all [HasTagSort]
  | term => simp [HasTagSort]

theorem bindFamilyArr {expected : TagSort} {input : Option Value}
    {next : ∀ domain codomain,
      EmptyExpr (.kind (.arr domain codomain)) → Option Value}
    (valid : ∀ domain codomain expression,
      HasTagSort expected (next domain codomain expression)) :
    HasTagSort expected (input.bind fun
      | .family (.arr domain codomain) expression =>
          next domain codomain expression
      | _ => none) := by
  apply bind
  intro value
  cases value with
  | kind => simp [HasTagSort]
  | family kind expression =>
      cases kind <;> simp_all [HasTagSort]
  | term => simp [HasTagSort]

theorem bindTerm {expected : TagSort} {input : Option Value}
    {next : EmptyTy → EmptyTm → Option Value}
    (valid : ∀ type expression, HasTagSort expected (next type expression)) :
    HasTagSort expected (input.bind fun
      | .term type expression => next type expression
      | _ => none) := by
  apply bind
  intro value
  cases value <;> simp_all [HasTagSort]

theorem elaborateTerm (lookupLocal : Ref → Option Value)
    (declaredSort : Option Ref) (expression : EmptyTm) :
    HasTagSort .tm
      (Nucleus.Hol.Ethane.OneBased.elaborateTerm lookupLocal declaredSort expression) := by
  cases declaredSort with
  | none => simp [Nucleus.Hol.Ethane.OneBased.elaborateTerm, HasTagSort]
  | some sort =>
      simp only [Nucleus.Hol.Ethane.OneBased.elaborateTerm]
      apply bindFamilyStar
      intro advertisedType
      simp [HasTagSort, Value.tagSort]

theorem checked {expected : TagSort} (input : Option Value) :
    HasTagSort expected (input.bind fun value =>
      if value.tagSort = expected then some value else none) := by
  apply bind
  intro value
  by_cases category : value.tagSort = expected <;>
    simp [category, HasTagSort]

theorem of_some {expected : TagSort} {result : Option Value} {value : Value}
    (valid : HasTagSort expected result)
    (found : result = some value) : value.tagSort = expected := by
  rw [found] at valid
  exact valid

end HasTagSort

/-- Successful expression elaboration preserves the syntactic category
declared by the raw row tag. -/
theorem elaborateExpr_tagSort
    (lookupLocal : Ref → Option Value)
    (lookupForeign : ImportId → Ref → Option Value)
    (declaredSort : Option Ref) (expression : detail.Expr) (value : Value)
    (found : elaborateExpr lookupLocal lookupForeign declaredSort expression =
      some value) :
    value.tagSort = expression.tag.sort := by
  apply HasTagSort.of_some (result := elaborateExpr lookupLocal lookupForeign
    declaredSort expression) (value := value) ?_ found
  cases expression with
  | kindStar => simp [elaborateExpr, HasTagSort, Value.tagSort,
      detail.Expr.tag, Tag.sort]
  | kindArr domain codomain =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindKind
      intro domainValue
      apply HasTagSort.bindKind
      intro codomainValue
      simp [HasTagSort, Value.tagSort]
  | boolTy => simp [elaborateExpr, HasTagSort, Value.tagSort,
      detail.Expr.tag, Tag.sort]
  | tyArr domain codomain =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindFamilyStar
      intro domainValue
      apply HasTagSort.bindFamilyStar
      intro codomainValue
      simp [HasTagSort, Value.tagSort]
  | tyApp function argument =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindFamilyArr
      intro domain codomain functionValue
      apply HasTagSort.bindFamily
      intro actual argumentValue
      by_cases equality : actual = domain <;>
        simp [equality, HasTagSort, Value.tagSort]
  | tyLam binder body =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindFamily
      intro domain binderValue
      cases name : tyFvName? binderValue with
      | none => simp [HasTagSort]
      | some name =>
          apply HasTagSort.bindFamily
          intro codomain bodyValue
          simp [HasTagSort, Value.tagSort]
  | tyFv name kind =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindKind
      intro kindValue
      simp [HasTagSort, Value.tagSort]
  | tyExists name predicate =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindTerm
      intro _ predicateValue
      exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | tyForall name predicate =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindTerm
      intro _ predicateValue
      exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | model name predicate =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindTerm
      intro _ predicateValue
      simp [HasTagSort, Value.tagSort]
  | tmFv name type =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindFamilyStar
      intro syntacticType
      exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | app function argument =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindTerm
      intro _ functionValue
      apply HasTagSort.bindTerm
      intro _ argumentValue
      exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | lam binder body =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindTerm
      intro _ binderValue
      cases binderData : tmFvData? binderValue with
      | none => simp [HasTagSort]
      | some data =>
          rcases data with ⟨name, syntacticDomain⟩
          apply HasTagSort.bindTerm
          intro _ bodyValue
          exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | bool value =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | op1 op operand =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindTerm
      intro _ operandValue
      exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | op2 op left right =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindTerm
      intro _ leftValue
      apply HasTagSort.bindTerm
      intro _ rightValue
      exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | eq type left right =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindFamilyStar
      intro syntacticType
      apply HasTagSort.bindTerm
      intro _ leftValue
      apply HasTagSort.bindTerm
      intro _ rightValue
      exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | eps type predicate =>
      simp only [elaborateExpr, detail.Expr.tag, Tag.sort]
      apply HasTagSort.bindFamilyStar
      intro syntacticType
      apply HasTagSort.bindTerm
      intro _ predicateValue
      exact HasTagSort.elaborateTerm lookupLocal declaredSort _
  | tmRef source foreignRef =>
      change HasTagSort .tm ((lookupForeign source foreignRef).bind fun value =>
        if value.tagSort = .tm then some value else none)
      exact HasTagSort.checked (expected := .tm) (lookupForeign source foreignRef)
  | tyRef source foreignRef =>
      change HasTagSort .ty ((lookupForeign source foreignRef).bind fun value =>
        if value.tagSort = .ty then some value else none)
      exact HasTagSort.checked (expected := .ty) (lookupForeign source foreignRef)
  | kindRef source foreignRef =>
      change HasTagSort .kind ((lookupForeign source foreignRef).bind fun value =>
        if value.tagSort = .kind then some value else none)
      exact HasTagSort.checked (expected := .kind) (lookupForeign source foreignRef)

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
            (arena.sort? reference)
            row

@[simp] theorem resolveAt?_withoutSyn (fuel : Nat) (resolve : Resolver)
    (arena : Arena) (reference : Ref) :
    resolveAt? fuel resolve arena.withoutSyn reference =
      resolveAt? fuel resolve arena reference := by
  induction fuel generalizing reference with
  | zero => rfl
  | succ fuel ih =>
      have localLookup : resolveAt? fuel resolve arena.withoutSyn =
          resolveAt? fuel resolve arena := by
        funext localReference
        exact ih localReference
      have foreignLookup :
          resolveForeignUsing? (resolveAt? fuel resolve) resolve arena.withoutSyn =
            resolveForeignUsing? (resolveAt? fuel resolve) resolve arena := by
        funext source foreignReference
        cases arena
        rfl
      simp only [resolveAt?, Arena.row?_withoutSyn]
      rw [localLookup, foreignLookup]
      simp only [Arena.sort?_withoutSyn]

/-- Resolve one foreign reference through the owner's import table. -/
noncomputable def resolveForeignAt? (fuel : Nat) (resolve : Resolver)
    (owner : Arena) (source : ImportId) (foreignRef : Ref) : Option Value :=
  resolveForeignUsing? (resolveAt? fuel resolve) resolve owner source foreignRef

/-- A value is available when some finite resolution bound reconstructs it. -/
def Resolves (resolve : Resolver) (arena : Arena) (reference : Ref) (value : Value) : Prop :=
  ∃ fuel, resolveAt? fuel resolve arena reference = some value

/-- Resolution can succeed only at a resident syntax row, and the resulting
value has exactly the syntactic category declared by that row's tag. The
classifier and equality columns do not participate in this category fact. -/
theorem Resolves.rowTag {resolve : Resolver} {arena : Arena}
    {reference : Ref} {value : Value}
    (resolved : Resolves resolve arena reference value) :
    ∃ expression,
      arena.row? reference = some expression ∧
      value.tagSort = expression.tag.sort := by
  rcases resolved with ⟨fuel, found⟩
  cases fuel with
  | zero => simp [resolveAt?] at found
  | succ fuel =>
      cases rowFound : arena.row? reference with
      | none => simp [resolveAt?, rowFound] at found
      | some expression =>
          refine ⟨expression, rfl, ?_⟩
          apply elaborateExpr_tagSort
          simpa only [resolveAt?, rowFound] using found

theorem Resolves.resident {resolve : Resolver} {arena : Arena}
    {reference : Ref} {value : Value}
    (resolved : Resolves resolve arena reference value) :
    arena.dense.expr? reference ≠ none := by
  obtain ⟨expression, found, _⟩ := resolved.rowTag
  exact Arena.row?_resident found

theorem Resolves.tagSort? {resolve : Resolver} {arena : Arena}
    {reference : Ref} {value : Value}
    (resolved : Resolves resolve arena reference value) :
    arena.dense.tagSort? reference = some value.tagSort := by
  obtain ⟨expression, found, category⟩ := resolved.rowTag
  change (arena.dense.expr? reference).map (·.tag.sort) = some value.tagSort
  change arena.dense.expr? reference = some expression at found
  rw [found, category]
  rfl

@[simp] theorem resolves_withoutSyn_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (value : Value) :
    Resolves resolve arena.withoutSyn reference value ↔
      Resolves resolve arena reference value := by
  simp [Resolves]

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
    (lookup : arena.row? reference = some (.tmRef source foreignRef)) :
    resolveAt? (fuel + 1) resolve arena reference =
      match resolveForeignAt? fuel resolve arena source foreignRef with
      | none => none
      | some value => if value.tagSort = .tm then some value else none := by
  simp only [resolveAt?, lookup, elaborateExpr, resolveForeignAt?]
  cases resolveForeignUsing? (resolveAt? fuel resolve) resolve arena source foreignRef <;> rfl

theorem resolveAt?_tyRef (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (lookup : arena.row? reference = some (.tyRef source foreignRef)) :
    resolveAt? (fuel + 1) resolve arena reference =
      match resolveForeignAt? fuel resolve arena source foreignRef with
      | none => none
      | some value => if value.tagSort = .ty then some value else none := by
  simp only [resolveAt?, lookup, elaborateExpr, resolveForeignAt?]
  cases resolveForeignUsing? (resolveAt? fuel resolve) resolve arena source foreignRef <;> rfl

theorem resolveAt?_kindRef (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (lookup : arena.row? reference = some (.kindRef source foreignRef)) :
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
    (lookup : arena.row? reference = some (.tmRef source foreignRef))
    (value : Value) :
    Resolves resolve arena reference value ↔
      value.tagSort = .tm ∧
      ForeignResolves resolve arena source foreignRef value := by
  constructor
  · rintro ⟨fuel, resolved⟩
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      rw [resolveAt?_tmRef fuel resolve arena reference source foreignRef lookup]
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
    rw [resolveAt?_tmRef fuel resolve arena reference source foreignRef lookup,
      foreign]
    simp [category]

theorem resolves_tyRef_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (lookup : arena.row? reference = some (.tyRef source foreignRef))
    (value : Value) :
    Resolves resolve arena reference value ↔
      value.tagSort = .ty ∧
      ForeignResolves resolve arena source foreignRef value := by
  constructor
  · rintro ⟨fuel, resolved⟩
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      rw [resolveAt?_tyRef fuel resolve arena reference source foreignRef lookup]
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
    rw [resolveAt?_tyRef fuel resolve arena reference source foreignRef lookup,
      foreign]
    simp [category]

theorem resolves_kindRef_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef : Ref)
    (lookup : arena.row? reference = some (.kindRef source foreignRef))
    (value : Value) :
    Resolves resolve arena reference value ↔
      value.tagSort = .kind ∧
      ForeignResolves resolve arena source foreignRef value := by
  constructor
  · rintro ⟨fuel, resolved⟩
    cases fuel with
    | zero => contradiction
    | succ fuel =>
      rw [resolveAt?_kindRef fuel resolve arena reference source foreignRef lookup]
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
    rw [resolveAt?_kindRef fuel resolve arena reference source foreignRef lookup,
      foreign]
    simp [category]

theorem sortingClaim_tmRef_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef sort : Ref)
    (lookup : arena.row? reference = some (.tmRef source foreignRef))
    (sortLookup : arena.sort? reference = some sort) :
    SortingClaim resolve arena reference ↔
      ProxySortingClaim .tm resolve arena source foreignRef sort := by
  constructor
  · rintro ⟨actualSort, value, classifier, sortMember, valueResolved,
      classifierResolved, sorted⟩
    have actualSortEq : actualSort = sort := by
      have reversed : sort = actualSort := by
        rw [sortLookup] at sortMember
        exact Option.some.inj sortMember
      exact reversed.symm
    subst actualSort
    rw [resolves_tmRef_iff resolve arena reference source foreignRef lookup value]
      at valueResolved
    exact ⟨value, classifier, valueResolved.2, valueResolved.1,
      classifierResolved, sorted⟩
  · rintro ⟨value, classifier, foreignResolved, category,
      classifierResolved, sorted⟩
    exact ⟨sort, value, classifier, sortLookup,
      (resolves_tmRef_iff resolve arena reference source foreignRef lookup value).2
        ⟨category, foreignResolved⟩,
      classifierResolved, sorted⟩

theorem sortingClaim_tyRef_iff (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef sort : Ref)
    (lookup : arena.row? reference = some (.tyRef source foreignRef))
    (sortLookup : arena.sort? reference = some sort) :
    SortingClaim resolve arena reference ↔
      ProxySortingClaim .ty resolve arena source foreignRef sort := by
  constructor
  · rintro ⟨actualSort, value, classifier, sortMember, valueResolved,
      classifierResolved, sorted⟩
    have actualSortEq : actualSort = sort := by
      have reversed : sort = actualSort := by
        rw [sortLookup] at sortMember
        exact Option.some.inj sortMember
      exact reversed.symm
    subst actualSort
    rw [resolves_tyRef_iff resolve arena reference source foreignRef lookup value]
      at valueResolved
    exact ⟨value, classifier, valueResolved.2, valueResolved.1,
      classifierResolved, sorted⟩
  · rintro ⟨value, classifier, foreignResolved, category,
      classifierResolved, sorted⟩
    exact ⟨sort, value, classifier, sortLookup,
      (resolves_tyRef_iff resolve arena reference source foreignRef lookup value).2
        ⟨category, foreignResolved⟩,
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
    (lookup : arena.row? reference = some (.tmRef source foreignRef))
    (sortLookup : arena.sort? reference = some sort)
    (category : ProxySortingClaim .tm resolve arena source foreignRef sort) :
    MetaClaim resolve arena (.wf source foreignRef sort) ↔
      SortingClaim resolve arena reference := by
  rw [metaWf_iff_proxy, sortingClaim_tmRef_iff resolve arena reference source
    foreignRef sort lookup sortLookup]
  constructor
  · intro _claim
    exact category
  · exact Or.inl

/-- `meta.wf` is exactly the inline sorting claim of an actual type proxy. -/
theorem metaWf_iff_tyRef_sortingClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) (source : ImportId) (foreignRef sort : Ref)
    (lookup : arena.row? reference = some (.tyRef source foreignRef))
    (sortLookup : arena.sort? reference = some sort)
    (category : ProxySortingClaim .ty resolve arena source foreignRef sort) :
    MetaClaim resolve arena (.wf source foreignRef sort) ↔
      SortingClaim resolve arena reference := by
  rw [metaWf_iff_proxy, sortingClaim_tyRef_iff resolve arena reference source
    foreignRef sort lookup sortLookup]
  constructor
  · intro _claim
    exact category
  · exact Or.inr

end Nucleus.Hol.Ethane.OneBased
