import Nucleus.Hol.Ethane.Arena.OneBased.Rules
import Nucleus.Hol.Ethane.Arena.OneBased.FusedTransitions

/-!
# Lean specification of the checked Rust API

Every Rust method accepts and returns the single raw `Ref` type. Sort checks
are repeated at the method boundary; there are no checked `KindIx`, `TyIx`, or
`TmIx` capabilities. These result structures specify the exact raw arena
mutation and retain the resulting `KernelValid` proof.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

namespace Arena

/-- Exact successful `Arena::push_row` mutation.  The expression is appended
to `defs`; a supplied classifier is recorded at the newly allocated reference
in the fused conversion column.  With no classifier the conversion column is
left byte-for-byte unchanged. -/
def pushRowRaw (arena : Arena) (row : detail.Row) (sort : Option Ref) : Arena :=
  let position := arena.dense.defs.length
  match arena with
  | .mk imports axs dense synFacts synFree ctx assume assert =>
      let dense := { dense with defs := dense.defs ++ [row.expr] }
      let dense := match sort with
        | none => dense
        | some classifier =>
            { dense with conv :=
                (Columns.Dense.setColumnNormalized dense.conv position
                  (some classifier)) }
      .mk imports axs dense synFacts synFree ctx assume assert

@[simp] theorem pushRowRaw_none (arena : Arena) (row : detail.Row) :
    arena.pushRowRaw row none = arena.pushRaw row := by
  cases arena
  rfl

@[simp] theorem defs_pushRowRaw (arena : Arena) (row : detail.Row)
    (sort : Option Ref) :
    (arena.pushRowRaw row sort).dense.defs = arena.dense.defs ++ [row.expr] := by
  cases arena
  cases sort <;> rfl

@[simp] theorem eq_pushRowRaw (arena : Arena) (row : detail.Row)
    (sort : Option Ref) :
    (arena.pushRowRaw row sort).dense.eq = arena.dense.eq := by
  cases arena
  cases sort <;> rfl

@[simp] theorem synEq_pushRowRaw (arena : Arena) (row : detail.Row)
    (sort : Option Ref) :
    (arena.pushRowRaw row sort).dense.synEq = arena.dense.synEq := by
  cases arena
  cases sort <;> rfl

@[simp] theorem conv_pushRowRaw_none (arena : Arena) (row : detail.Row) :
    (arena.pushRowRaw row none).dense.conv = arena.dense.conv := by
  cases arena
  rfl

@[simp] theorem conv_pushRowRaw_some_self (arena : Arena) (row : detail.Row)
    (classifier : Ref) :
    (arena.pushRowRaw row (some classifier)).dense.conv[arena.dense.defs.length]?.bind id =
      some classifier := by
  cases arena
  exact Columns.Dense.getElem?_setColumnNormalized_self _ _ _

def pushImportRaw (arena : Arena) (entry : Import) : Arena :=
  match arena with
  | .mk imports axs dense synFacts synFree ctx assume assert =>
      .mk (imports ++ [entry]) axs dense synFacts synFree ctx assume assert

def pushAssumptionRaw (arena : Arena) (record : Meta) : Arena :=
  match arena with
  | .mk imports axs dense synFacts synFree ctx assume assert =>
      .mk imports axs dense synFacts synFree ctx (assume ++ [record]) assert

def insertContextRaw (arena : Arena) (reference : Ref) : Arena :=
  match arena with
  | .mk imports axs dense synFacts synFree ctx assume assert =>
      .mk imports axs dense synFacts synFree (insert reference ctx) assume assert

def insertAxiomRaw (arena : Arena) (name : String) : Arena :=
  match arena with
  | .mk imports axs dense synFacts synFree ctx assume assert =>
      .mk imports (insert name axs) dense synFacts synFree ctx assume assert

/-- Replace one inline equality parent. `none` is the root marker used by
path compression. -/
def setEq? (arena : Arena) (reference : Ref) (parent : Option Ref) : Option Arena :=
  let position := reference.value.toNat - 1
  match arena.dense.defs[position]? with
  | none => none
  | some _ =>
      match arena with
      | .mk imports axs dense synFacts synFree ctx assume assert =>
          some (.mk imports axs
            { dense with eq := Columns.Dense.setColumnNormalized dense.eq position parent }
            synFacts synFree ctx assume assert)

end Arena

namespace Kernel

/-- Successful checked append of one row. -/
structure PushResult (before : Kernel resolve) (expr : detail.Expr)
    (sort : Option Ref) where
  after : Kernel resolve
  reference : Ref
  allocated : reference.value.toNat = before.arena.dense.defs.length + 1
  appended : after.arena = before.arena.pushRowRaw { expr } sort
  lookup : after.arena.row? reference = some expr
  classifier : after.arena.sort? reference = sort

abbrev StarResult (before : Kernel resolve) :=
  PushResult before .kindStar none

abbrev KindArrResult (before : Kernel resolve) (domain codomain : Ref) :=
  PushResult before (.kindArr domain codomain) none

abbrev BoolTyResult (before : Kernel resolve) (star : Ref) :=
  PushResult before .boolTy (some star)

abbrev TyArrResult (before : Kernel resolve) (domain codomain star : Ref) :=
  PushResult before (.tyArr domain codomain) (some star)

abbrev TyFvResult (before : Kernel resolve) (name : UInt64) (kind : Ref) :=
  PushResult before (.tyFv name kind) (some kind)

abbrev TyAppResult (before : Kernel resolve)
    (function argument codomain : Ref) :=
  PushResult before (.tyApp function argument) (some codomain)

/-- `ty_lam` first appends the inferred arrow kind, then the abstraction. -/
structure TyLamResult (before : Kernel resolve) (binder body domain codomain : Ref) where
  kind : Ref
  afterKind : Kernel resolve
  after : Kernel resolve
  kindAppended : afterKind.arena =
    before.arena.pushRowRaw ⟨.kindArr domain codomain⟩ none
  kindLookup : afterKind.arena.row? kind =
    some (.kindArr domain codomain)
  abstractionAppended : after.arena = afterKind.arena.pushRowRaw
    ⟨.tyLam binder body⟩ (some kind)

abbrev ModelResult (before : Kernel resolve)
    (name : UInt64) (predicate star : Ref) :=
  PushResult before (.model name predicate) (some star)

abbrev TyExistsResult (before : Kernel resolve)
    (name : UInt64) (predicate boolType : Ref) :=
  PushResult before (.tyExists name predicate) (some boolType)

abbrev TmFvResult (before : Kernel resolve) (name : UInt64) (type : Ref) :=
  PushResult before (.tmFv name type) (some type)

abbrev AppResult (before : Kernel resolve)
    (function argument codomain : Ref) :=
  PushResult before (.app function argument) (some codomain)

/-- `lam` first appends the inferred function type, then the abstraction. -/
structure LamResult (before : Kernel resolve)
    (binder body domain codomain star : Ref) where
  functionType : Ref
  afterType : Kernel resolve
  after : Kernel resolve
  typeAppended : afterType.arena = before.arena.pushRowRaw
    ⟨.tyArr domain codomain⟩ (some star)
  typeLookup : afterType.arena.row? functionType =
    some (.tyArr domain codomain)
  abstractionAppended : after.arena = afterType.arena.pushRowRaw
    ⟨.lam binder body⟩ (some functionType)

abbrev BoolResult (before : Kernel resolve) (value : Bool) (boolType : Ref) :=
  PushResult before (.bool value) (some boolType)

abbrev EqResult (before : Kernel resolve) (type left right boolType : Ref) :=
  PushResult before (.eq type left right) (some boolType)

abbrev EpsResult (before : Kernel resolve) (type predicate : Ref) :=
  PushResult before (.eps type predicate) (some type)

/-- Successful raw import-table append. -/
structure ImportResult (before : Kernel resolve) (entry : Import) where
  after : Kernel resolve
  source : ImportId
  appended : after.arena = before.arena.pushImportRaw entry
  lookup : after.arena.import? source = some entry

/-- Proxy constructors record their foreign sorting obligation as a premise,
then append a local row carrying the caller-supplied classifier. -/
structure ProxyResult (before : Kernel resolve) (record : Meta)
    (expr : detail.Expr) (sort : Option Ref) where
  afterPremise : Kernel resolve
  after : Kernel resolve
  reference : Ref
  allocated : reference.value.toNat = afterPremise.arena.dense.defs.length + 1
  premiseAppended : afterPremise.arena = before.arena.pushAssumptionRaw record
  rowAppended : after.arena = afterPremise.arena.pushRowRaw { expr } sort
  lookup : after.arena.row? reference = some expr
  classifier : after.arena.sort? reference = sort

abbrev KindRefResult (before : Kernel resolve) (source : ImportId) (foreign : Ref) :=
  ProxyResult before (.valid source) (.kindRef source foreign) none

abbrev TyRefResult (before : Kernel resolve)
    (source : ImportId) (foreign kind : Ref) :=
  ProxyResult before (.wf source foreign kind)
    (.tyRef source foreign) (some kind)

abbrev TmRefResult (before : Kernel resolve)
    (source : ImportId) (foreign type : Ref) :=
  ProxyResult before (.wf source foreign type)
    (.tmRef source foreign) (some type)

structure ContextResult (before : Kernel resolve) (proposition : Ref) where
  after : Kernel resolve
  inserted : after.arena = before.arena.insertContextRaw proposition

structure AxiomResult (before : Kernel resolve) (name : String) where
  after : Kernel resolve
  inserted : after.arena = before.arena.insertAxiomRaw name
  allowed : AllowedAxiom name

/-- Shared result of alpha, beta, and eta: one sound rule joins exactly the
two endpoint classes. -/
structure EqualityRuleResult (before : Kernel resolve) (left right : Ref) where
  after : Kernel resolve
  union : UnionResult before.arena after.arena left right

/-- Immutable `find` uses the same raw reference type as every constructor. -/
abbrev FindResult (kernel : Kernel resolve) (start representative : Ref) :=
  OneBased.FindResult kernel.arena start representative

/-- Mutable `find_mut` performs path compression while preserving all classes. -/
structure FindMutResult (before : Kernel resolve) (start : Ref) where
  after : Kernel resolve
  representative : Ref
  compression : CompressionResult before.arena after.arena start representative

theorem PushResult.valid {resolve : Resolver} {before : Kernel resolve}
    {expr : detail.Expr} {sort : Option Ref} (result : PushResult before expr sort) :
    result.after.arena.KernelValid resolve :=
  result.after.valid

theorem TyLamResult.valid {resolve : Resolver} {before : Kernel resolve}
    {binder body domain codomain : Ref}
    (result : TyLamResult before binder body domain codomain) :
    result.after.arena.KernelValid resolve :=
  result.after.valid

theorem LamResult.valid {resolve : Resolver} {before : Kernel resolve}
    {binder body domain codomain star : Ref}
    (result : LamResult before binder body domain codomain star) :
    result.after.arena.KernelValid resolve :=
  result.after.valid

theorem ImportResult.valid {resolve : Resolver} {before : Kernel resolve}
    {entry : Import} (result : ImportResult before entry) :
    result.after.arena.KernelValid resolve :=
  result.after.valid

theorem ProxyResult.valid {resolve : Resolver} {before : Kernel resolve}
    {record : Meta} {expr : detail.Expr} {sort : Option Ref}
    (result : ProxyResult before record expr sort) :
    result.after.arena.KernelValid resolve :=
  result.after.valid

theorem ContextResult.valid {resolve : Resolver} {before : Kernel resolve}
    {proposition : Ref} (result : ContextResult before proposition) :
    result.after.arena.KernelValid resolve :=
  result.after.valid

theorem AxiomResult.valid {resolve : Resolver} {before : Kernel resolve}
    {name : String} (result : AxiomResult before name) :
    result.after.arena.KernelValid resolve :=
  result.after.valid

theorem EqualityRuleResult.valid {resolve : Resolver} {before : Kernel resolve}
    {left right : Ref} (result : EqualityRuleResult before left right) :
    result.after.arena.KernelValid resolve :=
  result.after.valid

theorem FindMutResult.valid {resolve : Resolver} {before : Kernel resolve}
    {start : Ref} (result : FindMutResult before start) :
    result.after.arena.KernelValid resolve :=
  result.after.valid

end Kernel

end Nucleus.Hol.Ethane.OneBased
