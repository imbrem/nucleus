import Nucleus.Hol.Ethane.Arena.OneBased.Rules

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

def pushImportRaw (arena : Arena) (entry : Import) : Arena :=
  match arena with
  | .mk imports axs defs ctx assume assert =>
      .mk (imports ++ [entry]) axs defs ctx assume assert

def pushAssumptionRaw (arena : Arena) (record : Meta) : Arena :=
  match arena with
  | .mk imports axs defs ctx assume assert =>
      .mk imports axs defs ctx (assume ++ [record]) assert

def insertContextRaw (arena : Arena) (reference : Ref) : Arena :=
  match arena with
  | .mk imports axs defs ctx assume assert =>
      .mk imports axs defs (insert reference ctx) assume assert

def insertAxiomRaw (arena : Arena) (name : String) : Arena :=
  match arena with
  | .mk imports axs defs ctx assume assert =>
      .mk imports (insert name axs) defs ctx assume assert

/-- Replace one inline equality parent. `none` is the root marker used by
path compression. -/
def setEq? (arena : Arena) (reference : Ref) (parent : Option Ref) : Option Arena :=
  let position := reference.value.toNat - 1
  match arena.defs[position]? with
  | none => none
  | some _ =>
      match arena with
      | .mk imports axs defs ctx assume assert =>
          some (.mk imports axs
            (defs.modify position fun row => { row with eq := parent })
            ctx assume assert)

end Arena

namespace Kernel

/-- Successful checked append of one row. -/
structure PushResult (before : Kernel resolve) (row : detail.Row) where
  after : Kernel resolve
  reference : Ref
  appended : after.arena = before.arena.pushRaw row
  lookup : after.arena.row? reference = some row

abbrev StarResult (before : Kernel resolve) :=
  PushResult before ⟨.kindStar, none, none⟩

abbrev KindArrResult (before : Kernel resolve) (domain codomain : Ref) :=
  PushResult before ⟨.kindArr domain codomain, none, none⟩

abbrev BoolTyResult (before : Kernel resolve) (star : Ref) :=
  PushResult before ⟨.boolTy, none, some star⟩

abbrev TyArrResult (before : Kernel resolve) (domain codomain star : Ref) :=
  PushResult before ⟨.tyArr domain codomain, none, some star⟩

abbrev TyFvResult (before : Kernel resolve) (name : UInt64) (kind : Ref) :=
  PushResult before ⟨.tyFv name kind, none, some kind⟩

abbrev TyAppResult (before : Kernel resolve)
    (function argument codomain : Ref) :=
  PushResult before ⟨.tyApp function argument, none, some codomain⟩

/-- `ty_lam` first appends the inferred arrow kind, then the abstraction. -/
structure TyLamResult (before : Kernel resolve) (binder body domain codomain : Ref) where
  kind : Ref
  afterKind : Kernel resolve
  after : Kernel resolve
  kindAppended : afterKind.arena =
    before.arena.pushRaw ⟨.kindArr domain codomain, none, none⟩
  kindLookup : afterKind.arena.row? kind =
    some ⟨.kindArr domain codomain, none, none⟩
  abstractionAppended : after.arena = afterKind.arena.pushRaw
    ⟨.tyLam binder body, none, some kind⟩

abbrev ModelResult (before : Kernel resolve)
    (name : UInt64) (predicate star : Ref) :=
  PushResult before ⟨.model name predicate, none, some star⟩

abbrev TyExistsResult (before : Kernel resolve)
    (name : UInt64) (predicate boolType : Ref) :=
  PushResult before ⟨.tyExists name predicate, none, some boolType⟩

abbrev TmFvResult (before : Kernel resolve) (name : UInt64) (type : Ref) :=
  PushResult before ⟨.tmFv name type, none, some type⟩

abbrev AppResult (before : Kernel resolve)
    (function argument codomain : Ref) :=
  PushResult before ⟨.app function argument, none, some codomain⟩

/-- `lam` first appends the inferred function type, then the abstraction. -/
structure LamResult (before : Kernel resolve)
    (binder body domain codomain star : Ref) where
  functionType : Ref
  afterType : Kernel resolve
  after : Kernel resolve
  typeAppended : afterType.arena = before.arena.pushRaw
    ⟨.tyArr domain codomain, none, some star⟩
  typeLookup : afterType.arena.row? functionType =
    some ⟨.tyArr domain codomain, none, some star⟩
  abstractionAppended : after.arena = afterType.arena.pushRaw
    ⟨.lam binder body, none, some functionType⟩

abbrev BoolResult (before : Kernel resolve) (value : Bool) (boolType : Ref) :=
  PushResult before ⟨.bool value, none, some boolType⟩

abbrev EqResult (before : Kernel resolve) (left right boolType : Ref) :=
  PushResult before ⟨.eq left right, none, some boolType⟩

abbrev EpsResult (before : Kernel resolve) (type predicate : Ref) :=
  PushResult before ⟨.eps type predicate, none, some type⟩

/-- Successful raw import-table append. -/
structure ImportResult (before : Kernel resolve) (entry : Import) where
  after : Kernel resolve
  source : ImportId
  appended : after.arena = before.arena.pushImportRaw entry
  lookup : after.arena.import? source = some entry

/-- Proxy constructors record their foreign sorting obligation as a premise,
then append a local row carrying the caller-supplied classifier. -/
structure ProxyResult (before : Kernel resolve) (record : Meta)
    (row : detail.Row) where
  afterPremise : Kernel resolve
  after : Kernel resolve
  reference : Ref
  premiseAppended : afterPremise.arena = before.arena.pushAssumptionRaw record
  rowAppended : after.arena = afterPremise.arena.pushRaw row
  lookup : after.arena.row? reference = some row

abbrev KindRefResult (before : Kernel resolve) (source : ImportId) (foreign : Ref) :=
  ProxyResult before (.valid source) ⟨.kindRef source foreign, none, none⟩

abbrev TyRefResult (before : Kernel resolve)
    (source : ImportId) (foreign kind : Ref) :=
  ProxyResult before (.wf source foreign kind)
    ⟨.tyRef source foreign, none, some kind⟩

abbrev TmRefResult (before : Kernel resolve)
    (source : ImportId) (foreign type : Ref) :=
  ProxyResult before (.wf source foreign type)
    ⟨.tmRef source foreign, none, some type⟩

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
    {row : detail.Row} (result : PushResult before row) :
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
    {record : Meta} {row : detail.Row} (result : ProxyResult before record row) :
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
