import Nucleus.Hol.Ethane.Arena.OneBased.Cas
import Nucleus.Hol.Ethane.Arena.OneBased.Inference
import Nucleus.Hol.Ethane.Reference
import Nucleus.HolE.Named.ConversionLaws

/-!
# Checked one-based Ethane kernel states

Raw arenas may contain open, ill-typed, or unresolved rows.  Kernel validity is
instead attached to the claims the arena exposes: inline sorting and equality
members, the Boolean assumption context, metadata conclusions, and named axiom
capabilities.  Metadata in `assume` remains a premise and is not required to be
established by the arena that records it.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus

namespace Value
/-- Kernel equality for two resolved values.  Kind equality is syntactic;
family and term equality are certificates in the existing HolE kernel. -/
inductive Equal : Value → Value → Prop where
  | kind (kind : Kind) : Equal (.kind kind) (.kind kind)
  | family {kind : Kind}
      {left right : EmptyExpr (.kind kind)}
      (conversion : Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) left.toHolE right.toHolE)) :
      Equal (.family kind left) (.family kind right)
  | term {type : EmptyTy} {left right : EmptyTm}
      (conversion : Nonempty (Nucleus.Hol.Ethane.Reference.EqTm
        (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
        Nucleus.HolE.emptyBound left right type)) :
      Equal (.term type left) (.term type right)

/-- Reflexivity is available only after logical well-formedness has been
checked.  This is the first equality rule implemented by the Rust MVP. -/
theorem equal_self {value : Value} (wellFormed : value.WellFormed) :
    Equal value value := by
  cases value with
  | kind value => exact .kind value
  | family kind expression =>
      rcases wellFormed with
        ⟨loweredExpression, loweredClassification, lowering,
          classificationLowering, kinding⟩
      cases loweredClassification with
      | kind =>
          exact .family ⟨Nucleus.HolE.Named.FamEq.refl lowering⟩
  | term type expression =>
      rcases wellFormed with
        ⟨loweredExpression, loweredClassification, termLowering,
          classificationLowering, typing⟩
      cases loweredClassification with
      | tm loweredType =>
          have typeLowering :
              type.lowerTy (.nil : TyScope []) = some loweredType := by
            change (do
              let lowered ← type.lowerTy (.nil : TyScope [])
              pure (Nucleus.HolE.Classification.tm lowered)) =
                some (Nucleus.HolE.Classification.tm loweredType) at
                  classificationLowering
            cases lowered : type.lowerTy (.nil : TyScope []) <;>
              simp [lowered] at classificationLowering
            simpa [lowered] using classificationLowering
          exact .term ⟨Nucleus.Hol.Ethane.Reference.EqTm.complete
            termLowering termLowering typeLowering (.refl (.exact typing))⟩

/-- A well-typed root beta step is an Ethane kernel equality. -/
theorem equal_beta {type : EmptyTy} {source target : EmptyTm}
    (wellFormed : WellFormed (.term type source))
    (step : Nucleus.HolE.Named.TmBeta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      source.toHolE target.toHolE) :
    Equal (.term type source) (.term type target) := by
  rcases wellFormed with
    ⟨loweredSource, loweredClassification, sourceLowering,
      classificationLowering, sourceTyping⟩
  cases loweredClassification with
  | tm loweredType =>
      have namedTyping : Nucleus.HolE.Named.HasType
          (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
          Nucleus.HolE.emptyBound source.toHolE type.toHolE := by
        exact ⟨loweredSource, loweredType, sourceLowering,
          classificationLowering, sourceTyping⟩
      obtain ⟨conversion⟩ := step.toTmConv
        (fun index => Fin.elim0 index) namedTyping
      exact .term ⟨{
        loweredLeft := conversion.loweredLeft
        loweredRight := conversion.loweredRight
        loweredType := conversion.loweredType
        leftLowering := conversion.leftLowering
        rightLowering := conversion.rightLowering
        typeLowering := conversion.typeLowering
        derivation := conversion.derivation }⟩

end Value

/-- Meaning of the optional equality member on one row. -/
def EqualityClaim (resolve : Resolver) (arena : Arena) (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ leftValue rightValue,
        Resolves resolve arena reference leftValue ∧
        Resolves resolve arena right rightValue ∧
        Value.Equal leftValue rightValue

/-- The executable MVP equality check: both references resolve to the same
well-formed value.  More conversion rules extend this relation without
changing `EqualityClaim`. -/
def ReflexiveEqualityClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ value,
        Resolves resolve arena reference value ∧
        Resolves resolve arena right value ∧
        value.WellFormed

theorem reflexiveEqualityClaim_sound
    (claim : ReflexiveEqualityClaim resolve arena reference) :
    EqualityClaim resolve arena reference := by
  unfold ReflexiveEqualityClaim at claim
  unfold EqualityClaim
  split <;> try trivial
  rename_i right member
  rw [member] at claim
  rcases claim with ⟨value, left, right, wellFormed⟩
  exact ⟨value, value, left, right, Value.equal_self wellFormed⟩

/-- A checked root beta equality member. -/
def BetaEqualityClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right =>
      ∃ type source target,
        Resolves resolve arena reference (.term type source) ∧
        Resolves resolve arena right (.term type target) ∧
        Value.WellFormed (.term type source) ∧
        Nucleus.HolE.Named.TmBeta
          (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
          source.toHolE target.toHolE

theorem betaEqualityClaim_sound
    (claim : BetaEqualityClaim resolve arena reference) :
    EqualityClaim resolve arena reference := by
  unfold BetaEqualityClaim at claim
  unfold EqualityClaim
  split <;> try trivial
  rename_i right member
  rw [member] at claim
  rcases claim with ⟨type, source, target, sourceResolves, targetResolves,
    wellFormed, step⟩
  exact ⟨.term type source, .term type target, sourceResolves, targetResolves,
    Value.equal_beta wellFormed step⟩

/-- Meaning of the optional sorting member on one row. -/
def SortingMemberClaim (resolve : Resolver) (arena : Arena)
    (reference : Ref) : Prop :=
  match arena.sort? reference with
  | none => True
  | some _ => SortingClaim resolve arena reference

/-- A context reference denotes a well-typed Boolean term. -/
def ContextClaim (resolve : Resolver) (arena : Arena) (reference : Ref) : Prop :=
  ∃ expression,
    Resolves resolve arena reference (.term .boolTy expression) ∧
    Value.WellFormed (.term .boolTy expression)

/-- Capabilities understood by the initial empty-signature kernel. -/
def AllowedAxiom : String → Prop
  | "ax.inf" => True
  | _ => False

/-- A raw arena is a valid checked-kernel state relative to a resolver.

The resolver is a parameter because successful CAS resolution is persistent
but absence is retryable.  No premise in `assume` is silently promoted to an
assertion. -/
structure Arena.KernelValid (resolve : Resolver) (arena : Arena) : Prop where
  structural : arena.StructurallyValid
  sorts : ∀ reference, SortingMemberClaim resolve arena reference
  equalities : ∀ reference, EqualityClaim resolve arena reference
  context : ∀ reference ∈ arena.ctx, ContextClaim resolve arena reference
  axioms : ∀ name ∈ arena.axs, AllowedAxiom name
  conclusions : arena.Conclusions resolve

/-- An arena paired with the proof that its exposed claims were checked. -/
structure Kernel (resolve : Resolver) where
  arena : Arena
  valid : arena.KernelValid resolve

namespace Arena

@[simp] theorem empty_row? (reference : Ref) : empty.row? reference = none := by
  simp [empty, row?, defs]

@[simp] theorem empty_eq? (reference : Ref) : empty.eq? reference = none := by
  simp [eq?]

@[simp] theorem empty_sort? (reference : Ref) : empty.sort? reference = none := by
  simp [sort?]

/-- The empty arena is a checked kernel for every resolver. -/
theorem empty_kernelValid (resolve : Resolver) : empty.KernelValid resolve where
  structural := by simp [StructurallyValid, empty, defs, RowsValid]
  sorts := by simp [SortingMemberClaim]
  equalities := by simp [EqualityClaim]
  context := by simp [empty, ctx]
  axioms := by simp [empty, axs]
  conclusions := by simp [Conclusions, empty, assert]

end Arena

namespace Kernel

/-- The empty checked kernel. -/
def empty (resolve : Resolver) : Kernel resolve :=
  ⟨Arena.empty, Arena.empty_kernelValid resolve⟩

/-- Any asserted inline equality exposes an actual kernel equality
certificate, never merely a syntactic classification. -/
theorem equality_sound (kernel : Kernel resolve) {reference right : Ref}
    (member : kernel.arena.eq? reference = some right) :
    ∃ leftValue rightValue,
      Resolves resolve kernel.arena reference leftValue ∧
      Resolves resolve kernel.arena right rightValue ∧
      Value.Equal leftValue rightValue := by
  have claim := kernel.valid.equalities reference
  simp [EqualityClaim, member] at claim
  exact claim

/-- Every context entry is a genuinely well-typed Boolean term. -/
theorem context_sound (kernel : Kernel resolve) {reference : Ref}
    (member : reference ∈ kernel.arena.ctx) :
    ∃ expression,
      Resolves resolve kernel.arena reference (.term .boolTy expression) ∧
      Value.WellFormed (.term .boolTy expression) :=
  kernel.valid.context reference member

/-- Assertions are checked conclusions; assumptions are intentionally absent
from this theorem. -/
theorem conclusion_sound (kernel : Kernel resolve) {record : Meta}
    (member : record ∈ kernel.arena.assert) :
    MetaClaim resolve kernel.arena record :=
  kernel.valid.conclusions record member

end Kernel

end Nucleus.Hol.Ethane.OneBased
