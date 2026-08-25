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
      Nucleus.HolE.Named.HasTypeConv (.nil : TyScope [])
        (.nil : TmScope ArenaSig 0) Nucleus.HolE.emptyBound
        expression.toHolE type.toHolE

/-- Equality certified by the existing Ethane/HolE proof theory.

Term values deliberately carry their advertised row classifiers separately
from their syntax.  A primitive term equality therefore proves conversion of
those classifiers and a term conversion at the left classifier.  Symmetry and
transitivity below reindex the term certificate when an intermediate row was
advertised at a different, convertible type. -/
inductive Equal : Value → Value → Prop where
  | kind (kind : Kind) : Equal (.kind kind) (.kind kind)
  | family {kind : Kind} {left right : EmptyExpr (.kind kind)}
      (conversion : Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) left.toHolE right.toHolE)) :
      Equal (.family kind left) (.family kind right)
  | term {leftType rightType : EmptyTy} {left right : EmptyTm}
      (leftWellFormed : WellFormed (.term leftType left))
      (rightWellFormed : WellFormed (.term rightType right))
      (classifierConversion : Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) leftType.toHolE rightType.toHolE))
      (conversion : Nonempty (Nucleus.Hol.Ethane.Reference.EqTm
        (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
        Nucleus.HolE.emptyBound left right leftType)) :
      Equal (.term leftType left) (.term rightType right)

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
      have original := wellFormed
      rcases wellFormed with ⟨loweredExpression, loweredType, termLowering,
        typeLowering, typing⟩
      exact .term original original
        ⟨Nucleus.HolE.Named.FamEq.refl typeLowering⟩
        ⟨Nucleus.Hol.Ethane.Reference.EqTm.complete
          termLowering termLowering typeLowering (.refl typing)⟩

private theorem reindexTermConversion
    {sourceType targetType : EmptyTy}
    {source target witness : EmptyTm}
    (targetTypeWellFormed : WellFormed (.term targetType witness))
    (classifierConversion : Nucleus.HolE.Named.FamEq
      (.nil : TyScope []) sourceType.toHolE targetType.toHolE)
    (conversion : Nucleus.Hol.Ethane.Reference.EqTm
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      Nucleus.HolE.emptyBound source target sourceType) :
    Nonempty (Nucleus.Hol.Ethane.Reference.EqTm
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      Nucleus.HolE.emptyBound source target targetType) := by
  rcases targetTypeWellFormed with
    ⟨loweredWitness, loweredTargetType, witnessLowering,
      targetTypeLowering, witnessTyping⟩
  have sourceTypeLowering := conversion.typeLowering
  change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) sourceType.toHolE =
    some conversion.loweredType at sourceTypeLowering
  rw [classifierConversion.leftLowering] at sourceTypeLowering
  have sourceTypeSame := Option.some.inj sourceTypeLowering
  have targetTypeLowering' := targetTypeLowering
  change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) targetType.toHolE =
    some loweredTargetType at targetTypeLowering'
  rw [classifierConversion.rightLowering] at targetTypeLowering'
  have targetTypeSame := Option.some.inj targetTypeLowering'
  have familyConversion : Nucleus.HolE.FamEq ArenaSig
      conversion.loweredType loweredTargetType := by
    simpa only [sourceTypeSame, targetTypeSame] using
      classifierConversion.derivation
  let leftTyping : Nucleus.HolE.HasTypeDefEq Nucleus.HolE.emptyBound
      conversion.loweredLeft loweredTargetType :=
    .conv conversion.derivation.leftTyping witnessTyping.typeKinded
      familyConversion
  let rightTyping : Nucleus.HolE.HasTypeDefEq Nucleus.HolE.emptyBound
      conversion.loweredRight loweredTargetType :=
    .conv conversion.derivation.rightTyping witnessTyping.typeKinded
      familyConversion
  exact ⟨{
    loweredLeft := conversion.loweredLeft
    loweredRight := conversion.loweredRight
    loweredType := loweredTargetType
    leftLowering := conversion.leftLowering
    rightLowering := conversion.rightLowering
    typeLowering := by
      exact targetTypeLowering
    derivation := .conv leftTyping rightTyping conversion.derivation }⟩

theorem Equal.symm {left right : Value} (equality : Equal left right) :
    Equal right left := by
  cases equality with
  | kind kind => exact .kind kind
  | family conversion =>
      rcases conversion with ⟨conversion⟩
      exact .family ⟨conversion.symm⟩
  | term leftWellFormed rightWellFormed classifierConversion conversion =>
      rcases classifierConversion with ⟨classifierConversion⟩
      rcases conversion with ⟨conversion⟩
      obtain ⟨reindexed⟩ := reindexTermConversion rightWellFormed
        classifierConversion conversion
      exact .term rightWellFormed leftWellFormed ⟨classifierConversion.symm⟩ ⟨{
        loweredLeft := reindexed.loweredRight
        loweredRight := reindexed.loweredLeft
        loweredType := reindexed.loweredType
        leftLowering := reindexed.rightLowering
        rightLowering := reindexed.leftLowering
        typeLowering := reindexed.typeLowering
        derivation := reindexed.derivation.symm }⟩

/-- Transitivity requires the middle value to be well formed, matching the
premise of family-conversion transitivity. -/
theorem Equal.trans {left middle right : Value}
    (leftMiddle : Equal left middle) (middleWellFormed : middle.WellFormed)
    (middleRight : Equal middle right) : Equal left right := by
  cases leftMiddle with
  | kind kind => cases middleRight; exact .kind kind
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
  | term leftWellFormed _ leftClassifier leftConversion =>
      cases middleRight with
      | term _ rightWellFormed rightClassifier rightConversion =>
          rcases leftClassifier with ⟨leftClassifier⟩
          rcases rightClassifier with ⟨rightClassifier⟩
          rcases leftConversion with ⟨leftConversion⟩
          rcases rightConversion with ⟨rightConversion⟩
          obtain ⟨rightAtLeft⟩ := reindexTermConversion leftWellFormed
            leftClassifier.symm rightConversion
          have middleTermLowering := rightAtLeft.leftLowering
          rw [leftConversion.rightLowering] at middleTermLowering
          have middleTermSame := Option.some.inj middleTermLowering
          have commonTypeLowering := rightAtLeft.typeLowering
          rw [leftConversion.typeLowering] at commonTypeLowering
          have commonTypeSame := Option.some.inj commonTypeLowering
          have rightDerivation : Nucleus.HolE.EqTm Nucleus.HolE.emptyBound
              leftConversion.loweredRight rightAtLeft.loweredRight
              leftConversion.loweredType := by
            simpa only [middleTermSame, commonTypeSame] using rightAtLeft.derivation
          rcases middleWellFormed with
            ⟨loweredMiddle, loweredMiddleType, middleLowering,
              middleTypeLowering, middleTyping⟩
          change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) _ =
            some loweredMiddleType at middleTypeLowering
          rw [leftClassifier.rightLowering] at middleTypeLowering
          have middleTypeSame := Option.some.inj middleTypeLowering
          subst loweredMiddleType
          exact .term leftWellFormed rightWellFormed
            ⟨leftClassifier.trans middleTyping.typeKinded rightClassifier⟩ ⟨{
              loweredLeft := leftConversion.loweredLeft
              loweredRight := rightAtLeft.loweredRight
              loweredType := leftConversion.loweredType
              leftLowering := leftConversion.leftLowering
              rightLowering := rightAtLeft.rightLowering
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

/-- Object-logic axiom capabilities an arena may declare.

`ax.inf` is the axiom of infinity.  `ax.sub` is the guarded subtype-package
sentence, whose classical truth for every checked predicate is
`Nucleus.HolE.Empty.SubtypePackage.Eval.existsType_true`. -/
def AllowedAxiom : String → Prop
  | "ax.inf" => True
  | "ax.sub" => True
  | _ => False

/-- Semantic invariant of the cache-free logical portion of an arena. -/
structure Arena.CoreKernelValid (resolve : Resolver) (arena : Arena) : Prop where
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

/-- Cache slots are semantically inert for the ordinary HOL kernel.  Defining
core validity through `withoutSyn` makes every cache-only mutation preserve it
definitionally; `FullKernelValid` adds the cache invariants downstream. -/
abbrev Arena.KernelValid (resolve : Resolver) (arena : Arena) : Prop :=
  arena.withoutSyn.CoreKernelValid resolve

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

theorem empty_kernelValid (resolve : Resolver) : empty.KernelValid resolve := by
  change empty.CoreKernelValid resolve
  constructor
  · change True
    trivial
  · simp
  · simp [SortingMemberClaim]
  · simp [EqualityClaim]
  · simp
  · simp [empty, ctx]
  · simp [empty, axs]
  · simp [Conclusions, empty, assert]

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
  have coreMember : kernel.arena.withoutSyn.eq? reference = some right := by
    simpa using member
  rw [coreMember] at claim
  simpa using claim

/-- Immutable union-find lookup returns a semantically equal resident row. -/
theorem find_sound (kernel : Kernel resolve) {start representative : Ref}
    (startResident : kernel.arena.row? start ≠ none)
    (representativeResident : kernel.arena.row? representative ≠ none)
    (found : FindResult kernel.arena start representative) :
    ReferenceEqual resolve kernel.arena start representative := by
  have startCore : kernel.arena.withoutSyn.row? start ≠ none := by
    simpa using startResident
  have representativeCore :
      kernel.arena.withoutSyn.row? representative ≠ none := by
    simpa using representativeResident
  have connectedCore : EqClass kernel.arena.withoutSyn start representative := by
    have edges : EqEdge kernel.arena.withoutSyn = EqEdge kernel.arena := by
      funext left right
      simp [EqEdge]
    unfold EqClass
    rw [edges]
    exact found.connected
  simpa [ReferenceEqual] using
    kernel.valid.classes startCore representativeCore connectedCore

theorem context_sound (kernel : Kernel resolve) {reference : Ref}
    (member : reference ∈ kernel.arena.ctx) : ContextClaim resolve kernel.arena reference :=
  by simpa [ContextClaim] using
    kernel.valid.context reference (by simpa using member)

theorem conclusion_sound (kernel : Kernel resolve) {record : Meta}
    (member : record ∈ kernel.arena.assert) : MetaClaim resolve kernel.arena record :=
  by
    have claim := kernel.valid.conclusions record (by simpa using member)
    cases record <;> simpa [MetaClaim, FullyResolves] using claim

end Kernel

end Nucleus.Hol.Ethane.OneBased
