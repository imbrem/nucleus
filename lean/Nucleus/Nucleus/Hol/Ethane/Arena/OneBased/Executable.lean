import Nucleus.Hol.Ethane.Arena.OneBased.Kernel

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
        value.WellFormed

/-- Exact-fuel identity-beta check used for an inline equality member. -/
def IdentityBetaEqualityClaimAt (fuel : Nat) (resolve : Resolver)
    (arena : Arena) (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ type domain name argument loweredDomain loweredArgument,
        ResolvesAt fuel resolve arena reference
          (.term type (.app (.lam name domain (.tmFv name domain)) argument)) ∧
        ResolvesAt fuel resolve arena right (.term type argument) ∧
        Value.WellFormed
          (.term type (.app (.lam name domain (.tmFv name domain)) argument)) ∧
        domain.lowerTy (.nil : TyScope []) = some loweredDomain ∧
        argument.lowerTm (.nil : TyScope []) (.nil : TmScope ArenaSig 0) =
          some loweredArgument

/-- Exact equality alternatives in the current Rust validator. -/
def ExecutableEqualityClaimAt (fuel : Nat) (resolve : Resolver)
    (arena : Arena) (reference : Ref) : Prop :=
  ReflexiveEqualityClaimAt fuel resolve arena reference ∨
  IdentityBetaEqualityClaimAt fuel resolve arena reference

/-- Exact-fuel Boolean-context check. -/
def ContextClaimAt (fuel : Nat) (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  ∃ expression,
    ResolvesAt fuel resolve arena reference (.term .boolTy expression) ∧
    Value.WellFormed (.term .boolTy expression)

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
  exact ⟨value, left.resolves, right.resolves, wellFormed⟩

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
    sourceResolved.resolves, targetResolved.resolves, wellFormed,
    domainLowering, argumentLowering⟩

theorem executableEqualityClaimAt_sound
    (claim : ExecutableEqualityClaimAt fuel resolve arena reference) :
    ExecutableEqualityClaim resolve arena reference := by
  cases claim with
  | inl reflexive => exact Or.inl (reflexiveEqualityClaimAt_sound reflexive)
  | inr beta => exact Or.inr (identityBetaEqualityClaimAt_sound beta)

theorem contextClaimAt_sound
    (claim : ContextClaimAt fuel resolve arena reference) :
    ContextClaim resolve arena reference := by
  rcases claim with ⟨expression, resolved, wellFormed⟩
  exact ⟨expression, resolved.resolves, wellFormed⟩

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
  wellFormed : value.check = true

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
  Value.check_sound result.wellFormed

end RustKernel

end Nucleus.Hol.Ethane.OneBased
