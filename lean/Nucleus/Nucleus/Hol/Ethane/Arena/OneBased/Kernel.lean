import Nucleus.Hol.Ethane.Arena.OneBased.Resolve
import Nucleus.Hol.Ethane.Arena.OneBased.UnionFind
import Nucleus.Hol.Ethane.Reference
import Nucleus.HolE.Named.ConversionLaws

/-!
# Checked one-based Ethane kernel states

Raw arenas contain claims. A checked kernel pairs an arena with proofs that
every exposed sorting, equality, context, and metadata conclusion is sound.
Premise metadata remains a premise. Equality members are interpreted through
their whole union-find class; cycles require no special logical assumption.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

namespace Value

/-- Logical well-formedness of a resolved value in empty binder scopes. -/
def WellFormed : Value → Prop
  | .kind _ => True
  | .family _ expression =>
      Nucleus.Hol.Ethane.Kinded (.nil : TyScope []) expression
  | .term type expression =>
      Nucleus.Hol.Ethane.HasType (.nil : TyScope [])
        (.nil : TmScope ArenaSig 0) Nucleus.HolE.emptyBound expression type

/-- Equality certified by the existing Ethane/HolE proof theory. -/
inductive Equal : Value → Value → Prop where
  | kind (kind : Kind) : Equal (.kind kind) (.kind kind)
  | family {kind : Kind} {left right : EmptyExpr (.kind kind)}
      (conversion : Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) left.toHolE right.toHolE)) :
      Equal (.family kind left) (.family kind right)
  | term {type : EmptyTy} {left right : EmptyTm}
      (conversion : Nonempty (Nucleus.Hol.Ethane.Reference.EqTm
        (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
        Nucleus.HolE.emptyBound left right type)) :
      Equal (.term type left) (.term type right)

/-- Reflexivity is available for every well-formed value. -/
theorem equal_self {value : Value} (wellFormed : value.WellFormed) :
    Equal value value := by
  cases value with
  | kind value => exact .kind value
  | family kind expression =>
      rcases wellFormed with
        ⟨loweredExpression, loweredClassification, lowering,
          classificationLowering, kinding⟩
      cases loweredClassification with
      | kind => exact .family ⟨Nucleus.HolE.Named.FamEq.refl lowering⟩
  | term type expression =>
      rcases wellFormed with
        ⟨loweredExpression, loweredClassification, termLowering,
          classificationLowering, typing⟩
      cases loweredClassification with
      | tm loweredType =>
          have typeLowering : type.lowerTy (.nil : TyScope []) = some loweredType := by
            change (do
              let lowered ← type.lowerTy (.nil : TyScope [])
              pure (Nucleus.HolE.Classification.tm lowered)) =
                some (Nucleus.HolE.Classification.tm loweredType) at classificationLowering
            cases lowered : type.lowerTy (.nil : TyScope []) <;>
              simp [lowered] at classificationLowering
            simpa [lowered] using classificationLowering
          exact .term ⟨Nucleus.Hol.Ethane.Reference.EqTm.complete
            termLowering termLowering typeLowering (.refl (.exact typing))⟩

theorem Equal.symm {left right : Value} (equality : Equal left right) :
    Equal right left := by
  cases equality with
  | kind kind => exact .kind kind
  | family conversion =>
      rcases conversion with ⟨conversion⟩
      exact .family ⟨conversion.symm⟩
  | term conversion =>
      rcases conversion with ⟨conversion⟩
      exact .term ⟨{
        loweredLeft := conversion.loweredRight
        loweredRight := conversion.loweredLeft
        loweredType := conversion.loweredType
        leftLowering := conversion.rightLowering
        rightLowering := conversion.leftLowering
        typeLowering := conversion.typeLowering
        derivation := conversion.derivation.symm }⟩

/-- Transitivity requires the middle value to be well formed, matching the
premise of family-conversion transitivity. -/
theorem Equal.trans {left middle right : Value}
    (leftMiddle : Equal left middle) (middleWellFormed : middle.WellFormed)
    (middleRight : Equal middle right) : Equal left right := by
  cases leftMiddle with
  | kind kind =>
      cases middleRight
      exact .kind kind
  | family leftConversion =>
      cases middleRight with
      | family rightConversion =>
          rcases leftConversion with ⟨leftConversion⟩
          rcases rightConversion with ⟨rightConversion⟩
          rcases middleWellFormed with
            ⟨loweredMiddle, classification, middleLowering,
              _classificationLowering, middleKinded⟩
          cases classification with
          | kind =>
              change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) _ =
                some loweredMiddle at middleLowering
              rw [leftConversion.rightLowering] at middleLowering
              have same := Option.some.inj middleLowering
              subst loweredMiddle
              exact .family ⟨leftConversion.trans middleKinded rightConversion⟩
  | term leftConversion =>
      cases middleRight with
      | term rightConversion =>
          rcases leftConversion with ⟨leftConversion⟩
          rcases rightConversion with ⟨rightConversion⟩
          have middleLowering := rightConversion.leftLowering
          rw [leftConversion.rightLowering] at middleLowering
          have middleSame := Option.some.inj middleLowering
          have typeLowering := rightConversion.typeLowering
          rw [leftConversion.typeLowering] at typeLowering
          have typeSame := Option.some.inj typeLowering
          have rightDerivation : Nucleus.HolE.EqTm Nucleus.HolE.emptyBound
              leftConversion.loweredRight rightConversion.loweredRight
              leftConversion.loweredType := by
            simpa only [middleSame, typeSame] using rightConversion.derivation
          exact .term ⟨{
            loweredLeft := leftConversion.loweredLeft
            loweredRight := rightConversion.loweredRight
            loweredType := leftConversion.loweredType
            leftLowering := leftConversion.leftLowering
            rightLowering := rightConversion.rightLowering
            typeLowering := leftConversion.typeLowering
            derivation := leftConversion.derivation.trans rightDerivation }⟩

end Value

/-- Meaning of one optional equality parent. -/
def EqualityClaim (resolve : Resolver) (arena : Arena) (reference : Ref) : Prop :=
  match arena.eq? reference with
  | none => True
  | some right => ∃ leftValue rightValue,
      Resolves resolve arena reference leftValue ∧
      Resolves resolve arena right rightValue ∧
      leftValue.WellFormed ∧ rightValue.WellFormed ∧
      Value.Equal leftValue rightValue

/-- Semantic equality of two resident references. -/
def ReferenceEqual (resolve : Resolver) (arena : Arena) (left right : Ref) : Prop :=
  ∃ leftValue rightValue,
    Resolves resolve arena left leftValue ∧
    Resolves resolve arena right rightValue ∧
    leftValue.WellFormed ∧ rightValue.WellFormed ∧
    Value.Equal leftValue rightValue

/-- Meaning of one optional classifier. -/
def SortingMemberClaim (resolve : Resolver) (arena : Arena) (reference : Ref) : Prop :=
  match arena.sort? reference with
  | none => True
  | some _ => SortingClaim resolve arena reference

/-- A context member is a well-typed Boolean term. -/
def ContextClaim (resolve : Resolver) (arena : Arena) (reference : Ref) : Prop :=
  ∃ expression, Resolves resolve arena reference (.term .boolTy expression) ∧
    Value.WellFormed (.term .boolTy expression)

def AllowedAxiom : String → Prop
  | "ax.inf" => True
  | _ => False

/-- Semantic invariant of a checked arena. -/
structure Arena.KernelValid (resolve : Resolver) (arena : Arena) : Prop where
  structural : arena.StructurallyValid
  definitions : ∀ reference row, arena.row? reference = some row →
    ∃ value, Resolves resolve arena reference value ∧ value.WellFormed
  sorts : ∀ reference, SortingMemberClaim resolve arena reference
  equalities : ∀ reference, EqualityClaim resolve arena reference
  classes : ∀ {left right}, arena.row? left ≠ none → arena.row? right ≠ none →
    EqClass arena left right → ReferenceEqual resolve arena left right
  context : ∀ reference ∈ arena.ctx, ContextClaim resolve arena reference
  axioms : ∀ name ∈ arena.axs, AllowedAxiom name
  conclusions : Conclusions resolve arena

/-- An arena paired with its checked semantic invariant. -/
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

theorem empty_kernelValid (resolve : Resolver) : empty.KernelValid resolve where
  structural := by simp [StructurallyValid, empty, defs, RowsValid]
  definitions := by simp
  sorts := by simp [SortingMemberClaim]
  equalities := by simp [EqualityClaim]
  classes := by simp
  context := by simp [empty, ctx]
  axioms := by simp [empty, axs]
  conclusions := by simp [Conclusions, empty, assert]

end Arena

namespace Kernel

def empty (resolve : Resolver) : Kernel resolve :=
  ⟨Arena.empty, Arena.empty_kernelValid resolve⟩

theorem equality_sound (kernel : Kernel resolve) {reference right : Ref}
    (member : kernel.arena.eq? reference = some right) :
    ∃ leftValue rightValue,
      Resolves resolve kernel.arena reference leftValue ∧
      Resolves resolve kernel.arena right rightValue ∧
      leftValue.WellFormed ∧ rightValue.WellFormed ∧
      Value.Equal leftValue rightValue := by
  have claim := kernel.valid.equalities reference
  unfold EqualityClaim at claim
  rw [member] at claim
  exact claim

/-- Immutable union-find lookup returns a semantically equal resident row. -/
theorem find_sound (kernel : Kernel resolve) {start representative : Ref}
    (startResident : kernel.arena.row? start ≠ none)
    (representativeResident : kernel.arena.row? representative ≠ none)
    (found : FindResult kernel.arena start representative) :
    ReferenceEqual resolve kernel.arena start representative :=
  kernel.valid.classes startResident representativeResident found.connected

theorem context_sound (kernel : Kernel resolve) {reference : Ref}
    (member : reference ∈ kernel.arena.ctx) : ContextClaim resolve kernel.arena reference :=
  kernel.valid.context reference member

theorem conclusion_sound (kernel : Kernel resolve) {record : Meta}
    (member : record ∈ kernel.arena.assert) : MetaClaim resolve kernel.arena record :=
  kernel.valid.conclusions record member

end Kernel

end Nucleus.Hol.Ethane.OneBased
