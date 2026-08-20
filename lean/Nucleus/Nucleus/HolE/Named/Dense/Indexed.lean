import Nucleus.HolE.Named.Dense

/-!
# Relations and finite support over abstract forests

All relations in this file are pullbacks along a partial forest.  Consequently
they are false when either referenced node is absent.  The logical laws are
stated once for an arbitrary relation on trees and then transported to indices.
-/

namespace Nucleus.HolE.Named.Unsorted.Dense

universe u v
set_option relaxedAutoImplicit true

/-- A partial forest whose defined indices are contained in a finite list. -/
def FiniteForest (ι : Type u) (α : Type v) :=
  { forest : Forest ι α // ∃ support : List ι,
      ∀ index value, forest index = some value → index ∈ support }

namespace FiniteForest

instance : Coe (FiniteForest ι α) (Forest ι α) := ⟨Subtype.val⟩

instance : CoeFun (FiniteForest ι α) (fun _ => ι → Option α) :=
  ⟨fun forest => forest.val.get⟩

noncomputable def support (forest : FiniteForest ι α) : List ι := forest.property.choose

theorem mem_support (forest : FiniteForest ι α)
    (defined : forest index = some value) : index ∈ forest.support :=
  forest.property.choose_spec index value defined

end FiniteForest

/-- Pull back a unary relation along a partial forest. -/
def lift₁ (forest : Forest ι α) (relation : α → Prop) (index : ι) : Prop :=
  ∃ value, forest index = some value ∧ relation value

/-- Pull back a binary relation along a partial forest. -/
def lift₂ (forest : Forest ι α) (relation : α → α → Prop) (left right : ι) : Prop :=
  ∃ leftValue rightValue,
    forest left = some leftValue ∧ forest right = some rightValue ∧
      relation leftValue rightValue

/-- Pull back a ternary relation along a partial forest. -/
def lift₃ (forest : Forest ι α) (relation : α → α → α → Prop)
    (first second third : ι) : Prop :=
  ∃ firstValue secondValue thirdValue,
    forest first = some firstValue ∧ forest second = some secondValue ∧
      forest third = some thirdValue ∧ relation firstValue secondValue thirdValue

/-- Literal syntactic equality of the trees denoted by two indices. -/
def SynEq (forest : Forest ι α) : ι → ι → Prop := lift₂ forest Eq

def ConvEq (forest : Forest ι α) (conversion : α → α → Prop) : ι → ι → Prop :=
  lift₂ forest conversion

def HasTy (forest : Forest ι α) (hasType : α → α → Prop) : ι → ι → Prop :=
  lift₂ forest hasType

/-- `Entails forest proves p q` means that the proposition at `p` proves the
proposition at `q`. -/
def Entails (forest : Forest ι α) (proves : α → α → Prop) : ι → ι → Prop :=
  lift₂ forest proves

def IsProvable (forest : Forest ι α) (provable : α → Prop) : ι → Prop :=
  lift₁ forest provable

def IsEq (forest : Forest ι α) (equal : α → α → Prop) : ι → ι → Prop :=
  lift₂ forest equal

/-- `CondEq i j k` reads: under the proposition at `i`, the terms at `j` and
`k` are equal. -/
def CondEq (forest : Forest ι α) (conditional : α → α → α → Prop) :
    ι → ι → ι → Prop :=
  lift₃ forest conditional

theorem synEq_iff (forest : Forest ι α) :
    SynEq forest left right ↔ ∃ value, forest left = some value ∧
      forest right = some value := by
  simp only [SynEq, lift₂]
  constructor
  · rintro ⟨leftValue, rightValue, leftLookup, rightLookup, rfl⟩
    exact ⟨leftValue, leftLookup, rightLookup⟩
  · rintro ⟨value, leftLookup, rightLookup⟩
    exact ⟨value, value, leftLookup, rightLookup, rfl⟩

/-- Tree-level conjunction of a context, with `true` as the empty context. -/
def contextTerm (truth : α) (and : α → α → α) : List α → α
  | [] => truth
  | proposition :: context => and proposition (contextTerm truth and context)

/-- An abstract deduction law is enough to transport the usual context-as-one-
proposition characterization to forest indices. -/
theorem entails_contextTerm_iff
    (forest : Forest ι α) (entails : List α → α → Prop)
    (binaryEntails : α → α → Prop) (truth : α) (and : α → α → α)
    (contextLaw : ∀ context conclusion,
      binaryEntails (contextTerm truth and context) conclusion ↔ entails context conclusion)
    (contextLookup : forest contextIndex = some (contextTerm truth and context))
    (conclusionLookup : forest conclusionIndex = some conclusion) :
    Entails forest binaryEntails contextIndex conclusionIndex ↔
      entails context conclusion := by
  simp only [Entails, lift₂]
  constructor
  · rintro ⟨contextValue, conclusionValue, contextLookup', conclusionLookup', proof⟩
    rw [contextLookup] at contextLookup'
    rw [conclusionLookup] at conclusionLookup'
    cases Option.some.inj contextLookup'
    cases Option.some.inj conclusionLookup'
    exact (contextLaw context conclusion).mp proof
  · intro proof
    exact ⟨contextTerm truth and context, conclusion, contextLookup,
      conclusionLookup, (contextLaw context conclusion).mpr proof⟩

theorem entails_iff_provable_implies
    (forest : Forest ι α) (entails : α → α → Prop) (provable : α → Prop)
    (implies : α → α → α)
    (deduction : ∀ premise conclusion,
      entails premise conclusion ↔ provable (implies premise conclusion))
    (premiseLookup : forest premiseIndex = some premise)
    (conclusionLookup : forest conclusionIndex = some conclusion)
    (implicationLookup : forest implicationIndex = some (implies premise conclusion)) :
    Entails forest entails premiseIndex conclusionIndex ↔
      IsProvable forest provable implicationIndex := by
  simp only [Entails, IsProvable, lift₁, lift₂]
  constructor
  · rintro ⟨premiseValue, conclusionValue, premiseLookup', conclusionLookup', proof⟩
    rw [premiseLookup] at premiseLookup'
    rw [conclusionLookup] at conclusionLookup'
    cases Option.some.inj premiseLookup'
    cases Option.some.inj conclusionLookup'
    exact ⟨implies premise conclusion, implicationLookup, (deduction premise conclusion).mp proof⟩
  · rintro ⟨implication, implicationLookup', proof⟩
    rw [implicationLookup] at implicationLookup'
    cases Option.some.inj implicationLookup'
    exact ⟨premise, conclusion, premiseLookup, conclusionLookup,
      (deduction premise conclusion).mpr proof⟩

theorem isEq_true_iff_provable
    (forest : Forest ι α) (equal : α → α → Prop) (provable : α → Prop) (truth : α)
    (law : ∀ proposition, equal proposition truth ↔ provable proposition)
    (propositionLookup : forest propositionIndex = some proposition)
    (truthLookup : forest truthIndex = some truth) :
    IsEq forest equal propositionIndex truthIndex ↔
      IsProvable forest provable propositionIndex := by
  simp only [IsEq, IsProvable, lift₁, lift₂]
  constructor
  · rintro ⟨left, right, leftLookup, rightLookup, proof⟩
    rw [propositionLookup] at leftLookup
    rw [truthLookup] at rightLookup
    cases Option.some.inj leftLookup
    cases Option.some.inj rightLookup
    exact ⟨proposition, propositionLookup, (law proposition).mp proof⟩
  · rintro ⟨value, valueLookup, proof⟩
    rw [propositionLookup] at valueLookup
    cases Option.some.inj valueLookup
    exact ⟨proposition, truth, propositionLookup, truthLookup,
      (law proposition).mpr proof⟩

/-- Consistency transports directly to any index which denotes false. -/
theorem not_isProvable_false
    (forest : Forest ι α) (provable : α → Prop) (falsehood : α)
    (consistent : ¬ provable falsehood)
    (falseLookup : forest falseIndex = some falsehood) :
    ¬ IsProvable forest provable falseIndex := by
  rintro ⟨value, valueLookup, proof⟩
  rw [falseLookup] at valueLookup
  cases Option.some.inj valueLookup
  exact consistent proof

/-- In a consistent theory with symmetric equality and `p = true ↔ ⊢ p`, the
indices denoting true and false cannot be equal. -/
theorem not_isEq_true_false
    (forest : Forest ι α) (equal : α → α → Prop) (provable : α → Prop)
    (truth falsehood : α) (symmetric : ∀ {left right}, equal left right → equal right left)
    (law : ∀ proposition, equal proposition truth ↔ provable proposition)
    (consistent : ¬ provable falsehood)
    (truthLookup : forest truthIndex = some truth)
    (falseLookup : forest falseIndex = some falsehood) :
    ¬ IsEq forest equal truthIndex falseIndex := by
  rintro ⟨left, right, leftLookup, rightLookup, equality⟩
  rw [truthLookup] at leftLookup
  rw [falseLookup] at rightLookup
  cases Option.some.inj leftLookup
  cases Option.some.inj rightLookup
  exact consistent ((law falsehood).mp (symmetric equality))

end Nucleus.HolE.Named.Unsorted.Dense
