import Nucleus.Hol.Ethane.Arena.OneBased.Kernel
import Nucleus.Hol.Ethane.Arena.OneBased.NamedInference

/-!
# Executable one-based kernel validation

This file states the finite-fuel predicate implemented by the Rust validator.
Unlike `Resolves`, the definitions below retain the particular fuel used by
an execution.  The main theorem forgets that operational detail and produces
the abstract `KernelValid` invariant.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

/-- Exact-fuel resolution used by one execution of the validator. -/
def ResolvesAt (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) (value : Value) : Prop :=
  resolveAt? fuel resolve arena reference = some value

theorem ResolvesAt.resolves
    (resolved : ResolvesAt fuel resolve arena reference value) :
    Resolves resolve arena reference value :=
  ⟨fuel, resolved⟩

/-- Exact-fuel check of an optional inline sorting member. -/
def SortingMemberClaimAt (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.sort? reference with
  | none => True
  | some sort =>
      ∃ value classifier,
        ResolvesAt fuel resolve arena reference value ∧
        ResolvesAt fuel resolve arena sort classifier ∧
        value.HasSort classifier

/-- Exact-fuel reflexivity check used for an inline equality member. -/
def ReflexiveEqualityClaimAt (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ value,
        ResolvesAt fuel resolve arena reference value ∧
        ResolvesAt fuel resolve arena right value ∧
        value.rustCheck = true

/-- Exact-fuel identity-beta specialization, retained as a small executable
example of the general root-beta relation below. -/
def IdentityBetaEqualityClaimAt (fuel : Nat) (resolve : Resolver)
    (arena : Arena) (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ type domain name argument loweredDomain loweredArgument,
        ResolvesAt fuel resolve arena reference
          (.term type (.app (.lam name domain (.tmFv name domain)) argument)) ∧
        ResolvesAt fuel resolve arena right (.term type argument) ∧
        (Value.term type
          (.app (.lam name domain (.tmFv name domain)) argument)).rustCheck = true ∧
        domain.lowerTy (.nil : TyScope []) = some loweredDomain ∧
        argument.lowerTm (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
          some loweredArgument

/-- Exact-fuel general root-beta check used by the Rust validator.  The
lowered target must be the locally nameless opening of the lowered body by the
lowered argument. -/
def RootBetaEqualityClaimAt (fuel : Nat) (resolve : Resolver)
    (arena : Arena) (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ (type domain : EmptyTy) (name : Nat)
        (body argument target : EmptyTm)
        (loweredDomain : Nucleus.HolE.Ty ArenaSig [])
        (loweredBody : Nucleus.HolE.Tm ArenaSig [] 1)
        (loweredArgument : Nucleus.HolE.Tm ArenaSig [] 0),
        ResolvesAt fuel resolve arena reference
          (.term type (.app (.lam name domain body) argument)) ∧
        ResolvesAt fuel resolve arena right (.term type target) ∧
        (Value.term type (.app (.lam name domain body) argument)).rustCheck = true ∧
        domain.lowerTy (.nil : TyScope []) = some loweredDomain ∧
        body.lowerTm (.nil : TyScope [])
          (.cons ⟨name, domain.toHolE⟩ (.nil : TmScope ArenaSig 0)) =
            some loweredBody ∧
        argument.lowerTm (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
          some loweredArgument ∧
        target.lowerTm (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
          some (Nucleus.HolE.openBound loweredBody loweredArgument)

/-- Exact equality alternatives in the current Rust validator. -/
def ExecutableEqualityClaimAt (fuel : Nat) (resolve : Resolver)
    (arena : Arena) (reference : Ref) : Prop :=
  ReflexiveEqualityClaimAt fuel resolve arena reference ∨
  RootBetaEqualityClaimAt fuel resolve arena reference

/-- Exact-fuel Boolean-context check. -/
def ContextClaimAt (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  ∃ expression,
    ResolvesAt fuel resolve arena reference (.term .boolTy expression) ∧
    (Value.term .boolTy expression).rustCheck = true

/-- Local portion of one Rust validation pass. -/
structure Arena.RustLocallyValidAt (fuel : Nat) (resolve : Resolver)
    (arena : Arena) : Prop where
  structural : arena.StructurallyValid
  sorts : ∀ reference, SortingMemberClaimAt fuel resolve arena reference
  equalities : ∀ reference, ExecutableEqualityClaimAt fuel resolve arena reference
  context : ∀ reference ∈ arena.ctx, ContextClaimAt fuel resolve arena reference
  axioms : ∀ name ∈ arena.axs, AllowedAxiom name

/-- Exact-fuel metadata validation.  `trusted` is instantiated with the
previous recursive fuel layer for `meta.valid`; `meta.wf` uses the current
fuel for both target and classifier resolution. -/
def RustMetaClaimAt (trusted : Arena → Prop) (fuel : Nat) (resolve : Resolver)
    (arena : Arena) : Meta → Prop
  | .wf source foreignRef sort =>
      ∃ entry imported value classifier,
        arena.import? source = some entry ∧
        resolveImport? resolve entry = some imported ∧
        ResolvesAt fuel resolve imported foreignRef value ∧
        ResolvesAt fuel resolve arena sort classifier ∧
        value.HasSort classifier
  | .valid source =>
      ∃ entry imported,
        arena.import? source = some entry ∧
        resolveImport? resolve entry = some imported ∧
        trusted imported

/-- Acceptance predicate of the recursive Rust validator.  Resolution and
recursive-import validation share the caller's resource bound. -/
def Arena.RustValidAt : Nat → Resolver → Arena → Prop
  | 0, resolve, arena =>
      arena.RustLocallyValidAt 0 resolve ∧
      ∀ record ∈ arena.assert,
        RustMetaClaimAt (fun _ => False) 0 resolve arena record
  | fuel + 1, resolve, arena =>
      arena.RustLocallyValidAt (fuel + 1) resolve ∧
      ∀ record ∈ arena.assert,
        RustMetaClaimAt (Arena.RustValidAt fuel resolve) (fuel + 1)
          resolve arena record

theorem sortingMemberClaimAt_sound
    (claim : SortingMemberClaimAt fuel resolve arena reference) :
    SortingMemberClaim resolve arena reference := by
  unfold SortingMemberClaimAt at claim
  unfold SortingMemberClaim
  split <;> try trivial
  rename_i sort member
  rw [member] at claim
  rcases claim with ⟨value, classifier, valueResolved, classifierResolved, sorted⟩
  exact ⟨sort, value, classifier, member,
    valueResolved.resolves, classifierResolved.resolves, sorted⟩

theorem reflexiveEqualityClaimAt_sound
    (claim : ReflexiveEqualityClaimAt fuel resolve arena reference) :
    ReflexiveEqualityClaim resolve arena reference := by
  unfold ReflexiveEqualityClaimAt at claim
  unfold ReflexiveEqualityClaim
  split <;> try trivial
  rename_i right member
  rw [member] at claim
  rcases claim with ⟨value, left, right, wellFormed⟩
  exact ⟨value, left.resolves, right.resolves,
    Value.rustCheck_sound wellFormed⟩

theorem identityBetaEqualityClaimAt_sound
    (claim : IdentityBetaEqualityClaimAt fuel resolve arena reference) :
    IdentityBetaEqualityClaim resolve arena reference := by
  unfold IdentityBetaEqualityClaimAt at claim
  unfold IdentityBetaEqualityClaim
  split <;> try trivial
  rename_i right member
  rw [member] at claim
  rcases claim with ⟨type, domain, name, argument, loweredDomain,
    loweredArgument, sourceResolved, targetResolved, wellFormed,
    domainLowering, argumentLowering⟩
  exact ⟨type, domain, name, argument, loweredDomain, loweredArgument,
    sourceResolved.resolves, targetResolved.resolves,
    Value.rustCheck_sound wellFormed,
    domainLowering, argumentLowering⟩

theorem rootBetaEqualityClaimAt_sound
    (claim : RootBetaEqualityClaimAt fuel resolve arena reference) :
    RootBetaEqualityClaim resolve arena reference := by
  unfold RootBetaEqualityClaimAt at claim
  unfold RootBetaEqualityClaim
  split <;> try trivial
  rename_i right member
  rw [member] at claim
  rcases claim with ⟨type, domain, name, body, argument, target,
    loweredDomain, loweredBody, loweredArgument,
    sourceResolved, targetResolved, wellFormed,
    domainLowering, bodyLowering, argumentLowering, targetLowering⟩
  exact ⟨type, domain, name, body, argument, target,
    loweredDomain, loweredBody, loweredArgument,
    sourceResolved.resolves, targetResolved.resolves,
    Value.rustCheck_sound wellFormed,
    domainLowering, bodyLowering, argumentLowering, targetLowering⟩

theorem executableEqualityClaimAt_sound
    (claim : ExecutableEqualityClaimAt fuel resolve arena reference) :
    ExecutableEqualityClaim resolve arena reference := by
  cases claim with
  | inl reflexive => exact Or.inl (reflexiveEqualityClaimAt_sound reflexive)
  | inr beta => exact Or.inr (rootBetaEqualityClaimAt_sound beta)

theorem contextClaimAt_sound
    (claim : ContextClaimAt fuel resolve arena reference) :
    ContextClaim resolve arena reference := by
  rcases claim with ⟨expression, resolved, wellFormed⟩
  exact ⟨expression, resolved.resolves, Value.rustCheck_sound wellFormed⟩

theorem Arena.RustLocallyValidAt.sound
    (valid : Arena.RustLocallyValidAt fuel resolve arena) :
    Arena.ExecutableLocallyValid resolve arena where
  structural := valid.structural
  sorts reference := sortingMemberClaimAt_sound (valid.sorts reference)
  equalities reference := executableEqualityClaimAt_sound (valid.equalities reference)
  context reference member := contextClaimAt_sound (valid.context reference member)
  axioms := valid.axioms

theorem RustMetaClaimAt.mono
    {trusted stronger : Arena → Prop}
    (implication : ∀ candidate, trusted candidate → stronger candidate)
    (claim : RustMetaClaimAt trusted fuel resolve arena record) :
    KernelMetaClaim stronger resolve arena record := by
  cases record with
  | wf source foreignRef sort =>
      rcases claim with ⟨entry, imported, value, classifier, importLookup,
        importResolved, valueResolved, classifierResolved, sorted⟩
      exact ⟨entry, imported, value, classifier, importLookup, importResolved,
        valueResolved.resolves, classifierResolved.resolves, sorted⟩
  | valid source =>
      rcases claim with ⟨entry, imported, importLookup, importResolved, valid⟩
      exact ⟨entry, imported, importLookup, importResolved,
        implication imported valid⟩

/-- The exact finite-fuel acceptance predicate implemented in Rust implies the
abstract recursively checked kernel invariant. -/
theorem Arena.rustValidAt_sound :
    ∀ fuel (resolve : Resolver) (arena : Arena),
      arena.RustValidAt fuel resolve → arena.KernelValidAt (fuel + 1) resolve
  | 0, resolve, arena, valid => by
      exact ⟨valid.1.sound.sound, fun record member =>
        RustMetaClaimAt.mono (fun _ impossible => False.elim impossible)
          (valid.2 record member)⟩
  | fuel + 1, resolve, arena, valid => by
      exact ⟨valid.1.sound.sound, fun record member =>
        RustMetaClaimAt.mono
          (fun imported importedValid =>
            Arena.rustValidAt_sound fuel resolve imported importedValid)
          (valid.2 record member)⟩

/-- Any arena accepted by some Rust validation run is an abstract kernel. -/
theorem Arena.rustValid_sound
    (accepted : ∃ fuel, Arena.RustValidAt fuel resolve arena) :
    Arena.KernelValid resolve arena := by
  rcases accepted with ⟨fuel, valid⟩
  exact ⟨fuel + 1, Arena.rustValidAt_sound fuel resolve arena valid⟩

/-- The checked Rust state, including the fuel of its successful validation.
The operational implementation stores the arena and fixed resolver; fuel is
proof data and may be discarded after `rustValid_sound`. -/
structure RustKernel (resolve : Resolver) where
  arena : Arena
  fuel : Nat
  accepted : arena.RustValidAt fuel resolve

namespace RustKernel

/-- Forget execution details to the abstract checked-kernel state. -/
def toKernel (kernel : RustKernel resolve) : Kernel resolve :=
  ⟨kernel.arena, Arena.rustValid_sound ⟨kernel.fuel, kernel.accepted⟩⟩

/-- Exact successful revalidation transition used after every Rust mutation. -/
def revalidate (arena : Arena) (fuel : Nat)
    (accepted : arena.RustValidAt fuel resolve) : RustKernel resolve :=
  ⟨arena, fuel, accepted⟩

end RustKernel

namespace Arena

/-- Append one raw import exactly as `Arena::push_import` does in Rust. -/
def pushImportRaw (arena : Arena) (entry : Import) : Arena :=
  match arena with
  | .mk imports axs defs ctx assume assert =>
      .mk (imports ++ [entry]) axs defs ctx assume assert

/-- Append one raw premise exactly as `Arena::push_assumption` does in Rust. -/
def pushAssumptionRaw (arena : Arena) (record : Meta) : Arena :=
  match arena with
  | .mk imports axs defs ctx assume assert =>
      .mk imports axs defs ctx (assume ++ [record]) assert

/-- Append one raw conclusion exactly as `Arena::push_assertion` does in Rust. -/
def pushAssertionRaw (arena : Arena) (record : Meta) : Arena :=
  match arena with
  | .mk imports axs defs ctx assume assert =>
      .mk imports axs defs ctx assume (assert ++ [record])

/-- Insert one Boolean-context reference exactly as Rust's `BTreeSet`-backed
`Arena::insert_context` does. -/
def insertContextRaw (arena : Arena) (reference : Ref) : Arena :=
  match arena with
  | .mk imports axs defs ctx assume assert =>
      .mk imports axs defs (insert reference ctx) assume assert

/-- Insert one named axiom capability exactly as Rust's `BTreeSet`-backed
`Arena::insert_axiom` does. -/
def insertAxiomRaw (arena : Arena) (name : String) : Arena :=
  match arena with
  | .mk imports axs defs ctx assume assert =>
      .mk imports (insert name axs) defs ctx assume assert

/-- Replace one row's inline equality member.  Failure means the one-based
reference was outside the dense definition vector. -/
def setEq? (arena : Arena) (reference right : Ref) : Option Arena :=
  let position := reference.value.toNat - 1
  match arena.defs[position]? with
  | none => none
  | some _ =>
      match arena with
      | .mk imports axs defs ctx assume assert =>
          some (.mk imports axs
            (defs.modify position fun row => { row with eq := some right })
            ctx assume assert)

end Arena

namespace RustKernel

/-- A successful checked row append, including the handle and classification
evidence returned to the caller. -/
structure PushResult (before : RustKernel resolve) (row : detail.Row)
    (expected : TagSort) where
  after : RustKernel resolve
  reference : Ref
  appended : after.arena = before.arena.pushRaw row
  lookup : after.arena.row? reference = some row
  value : Value
  resolved : ResolvesAt after.fuel resolve after.arena reference value
  category : value.tagSort = expected
  wellFormed : value.rustCheck = true

abbrev StarResult (before : RustKernel resolve) :=
  PushResult before ⟨.kindStar, none, none⟩ .kind

abbrev BoolTyResult (before : RustKernel resolve) :=
  PushResult before ⟨.boolTy, none, none⟩ .ty

abbrev TmFvResult (before : RustKernel resolve) (name : UInt64) (type : Ref) :=
  PushResult before ⟨.tmFv name type, none, none⟩ .tm

abbrev LamResult (before : RustKernel resolve) (binder body : Ref) :=
  PushResult before ⟨.lam binder body, none, none⟩ .tm

abbrev AppResult (before : RustKernel resolve) (function argument : Ref) :=
  PushResult before ⟨.app function argument, none, none⟩ .tm

abbrev EqResult (before : RustKernel resolve) (left right : Ref) :=
  PushResult before ⟨.eq left right, none, none⟩ .tm

abbrev BoolResult (before : RustKernel resolve) (value : Bool) :=
  PushResult before ⟨.bool value, none, none⟩ .tm

abbrev KindRefResult (before : RustKernel resolve)
    (source : ImportId) (foreign : Ref) :=
  PushResult before ⟨.kindRef source foreign, none, none⟩ .kind

abbrev TyRefResult (before : RustKernel resolve)
    (source : ImportId) (foreign : Ref) :=
  PushResult before ⟨.tyRef source foreign, none, none⟩ .ty

abbrev TmRefResult (before : RustKernel resolve)
    (source : ImportId) (foreign : Ref) :=
  PushResult before ⟨.tmRef source foreign, none, none⟩ .tm

/-- Successful recovery of a checked handle for an existing row. -/
structure IndexResult (kernel : RustKernel resolve) (reference : Ref)
    (expected : TagSort) where
  value : Value
  resolved : ResolvesAt kernel.fuel resolve kernel.arena reference value
  category : value.tagSort = expected
  wellFormed : value.rustCheck = true

/-- Successful import-table mutation and complete revalidation. -/
structure ImportResult (before : RustKernel resolve) (entry : Import) where
  after : RustKernel resolve
  source : ImportId
  appended : after.arena = before.arena.pushImportRaw entry
  lookup : after.arena.import? source = some entry

/-- Successful premise insertion.  Premises are deliberately not checked or
copied into conclusions. -/
structure AssumeResult (before : RustKernel resolve) (record : Meta) where
  after : RustKernel resolve
  appended : after.arena = before.arena.pushAssumptionRaw record

/-- Successful checked conclusion insertion. -/
structure AssertResult (before : RustKernel resolve) (record : Meta) where
  after : RustKernel resolve
  appended : after.arena = before.arena.pushAssertionRaw record

/-- Successful inline equality update followed by complete revalidation. -/
structure AssertEqResult (before : RustKernel resolve) (left right : Ref) where
  after : RustKernel resolve
  updated : before.arena.setEq? left right = some after.arena

/-- Successful checked context insertion and complete revalidation. -/
structure ContextResult (before : RustKernel resolve) (reference : Ref) where
  after : RustKernel resolve
  inserted : after.arena = before.arena.insertContextRaw reference
  checked : ContextClaimAt after.fuel resolve after.arena reference

/-- Successful checked axiom-capability insertion and complete revalidation. -/
structure AxiomResult (before : RustKernel resolve) (name : String) where
  after : RustKernel resolve
  inserted : after.arena = before.arena.insertAxiomRaw name
  allowed : AllowedAxiom name

/-- Every public checked append returns another abstract valid kernel. -/
theorem PushResult.valid {resolve : Resolver} {before : RustKernel resolve}
    {row : detail.Row} {expected : TagSort}
    (result : PushResult (resolve := resolve) before row expected) :
    result.after.arena.KernelValid resolve :=
  by simpa [toKernel] using result.after.toKernel.valid

/-- Every checked append returns a genuinely well-formed value of the
constructor's declared category. -/
theorem PushResult.value_wellFormed {resolve : Resolver}
    {before : RustKernel resolve} {row : detail.Row} {expected : TagSort}
    (result : PushResult (resolve := resolve) before row expected) :
    result.value.WellFormed :=
  Value.rustCheck_sound result.wellFormed

theorem IndexResult.value_wellFormed {resolve : Resolver}
    {kernel : RustKernel resolve} {reference : Ref} {expected : TagSort}
    (result : IndexResult kernel reference expected) :
    result.value.WellFormed :=
  Value.rustCheck_sound result.wellFormed

theorem ImportResult.valid {resolve : Resolver}
    {before : RustKernel resolve} {entry : Import}
    (result : ImportResult before entry) :
    result.after.arena.KernelValid resolve :=
  by simpa [toKernel] using result.after.toKernel.valid

theorem AssumeResult.valid {resolve : Resolver}
    {before : RustKernel resolve} {record : Meta}
    (result : AssumeResult before record) :
    result.after.arena.KernelValid resolve :=
  by simpa [toKernel] using result.after.toKernel.valid

theorem AssertResult.valid {resolve : Resolver}
    {before : RustKernel resolve} {record : Meta}
    (result : AssertResult before record) :
    result.after.arena.KernelValid resolve :=
  by simpa [toKernel] using result.after.toKernel.valid

theorem AssertEqResult.valid {resolve : Resolver}
    {before : RustKernel resolve} {left right : Ref}
    (result : AssertEqResult before left right) :
    result.after.arena.KernelValid resolve :=
  by simpa [toKernel] using result.after.toKernel.valid

theorem ContextResult.valid {resolve : Resolver}
    {before : RustKernel resolve} {reference : Ref}
    (result : ContextResult before reference) :
    result.after.arena.KernelValid resolve :=
  by simpa [toKernel] using result.after.toKernel.valid

theorem ContextResult.claim {resolve : Resolver}
    {before : RustKernel resolve} {reference : Ref}
    (result : ContextResult before reference) :
    ContextClaim resolve result.after.arena reference :=
  contextClaimAt_sound result.checked

theorem AxiomResult.valid {resolve : Resolver}
    {before : RustKernel resolve} {name : String}
    (result : AxiomResult before name) :
    result.after.arena.KernelValid resolve :=
  by simpa [toKernel] using result.after.toKernel.valid

end RustKernel

end Nucleus.Hol.Ethane.OneBased
