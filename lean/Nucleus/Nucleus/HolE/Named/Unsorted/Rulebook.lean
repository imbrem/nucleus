import Nucleus.HolE.Named.Unsorted.CheckedRules

/-!
# Reviewable HolE rule inventory

These finite enumerations are kept beside the checked façade so an audit can
compare it mechanically with `HolE.Checks`, `HolE.EqTm`, and `HolE.Proves`.
The checked implementations are in `CheckedRules` and `ProofRules`.
-/

namespace Nucleus.HolE.Named.Unsorted

/-- Every syntax-directed rule in `HolE.Checks`.  Named variables split the
locally nameless variable rule into captured and free occurrences. -/
inductive TypingRule where
  | boolTy | arr | tyApp | tyLam | tyFv | sub | tyExists | model
  | primFam | primTm | boundFv | freeFv | app | lam | bool | eq | eps | abs | rep
  deriving DecidableEq, Repr

def TypingRule.all : List TypingRule :=
  [.boolTy, .arr, .tyApp, .tyLam, .tyFv, .sub, .tyExists, .model,
    .primFam, .primTm, .boundFv, .freeFv, .app, .lam, .bool, .eq, .eps, .abs, .rep]

theorem TypingRule.mem_all (rule : TypingRule) : rule ∈ TypingRule.all := by
  cases rule <;> simp [TypingRule.all]

@[simp] theorem TypingRule.length_all : TypingRule.all.length = 19 := rfl

/-- Every primitive term-equality certificate in `HolE.EqTm`. -/
inductive EqualityRule where
  | refl | symm | trans | app | lam | beta | eta
  deriving DecidableEq, Repr

def EqualityRule.all : List EqualityRule :=
  [.refl, .symm, .trans, .app, .lam, .beta, .eta]

theorem EqualityRule.mem_all (rule : EqualityRule) : rule ∈ EqualityRule.all := by
  cases rule <;> simp [EqualityRule.all]

@[simp] theorem EqualityRule.length_all : EqualityRule.all.length = 7 := rfl

/-- Every primitive proof certificate in `HolE.Proves`. -/
inductive ProofRule where
  | hyp | truth | falseElim | boolCases | eqRefl | eqMp | choice | generalize
  | weakenBound | hypothesisMap | convert | eqOfEqTm | antisymm | absRep
  | repAbs | repPredOfWitness | tyExistsIntro | modelSpec
  deriving DecidableEq, Repr

def ProofRule.all : List ProofRule :=
  [.hyp, .truth, .falseElim, .boolCases, .eqRefl, .eqMp, .choice, .generalize,
    .weakenBound, .hypothesisMap, .convert, .eqOfEqTm, .antisymm, .absRep,
    .repAbs, .repPredOfWitness, .tyExistsIntro, .modelSpec]

theorem ProofRule.mem_all (rule : ProofRule) : rule ∈ ProofRule.all := by
  cases rule <;> simp [ProofRule.all]

@[simp] theorem ProofRule.length_all : ProofRule.all.length = 18 := rfl

/-- Derived syntax whose typing follows from the primitive constructors. -/
inductive DerivedTypingRule where
  | letTm | not | and | or | imp
  deriving DecidableEq, Repr

def DerivedTypingRule.all : List DerivedTypingRule :=
  [.letTm, .not, .and, .or, .imp]

theorem DerivedTypingRule.mem_all (rule : DerivedTypingRule) :
    rule ∈ DerivedTypingRule.all := by
  cases rule <;> simp [DerivedTypingRule.all]

/-- Standard natural-deduction views intended for the derived connectives.
They are an explicit follow-up inventory, not primitive kernel rules. -/
inductive DerivedProofRule where
  | letBeta | notIntro | notElim | andIntro | andElimLeft | andElimRight
  | orIntroLeft | orIntroRight | orElim | impIntro | impElim
  | doubleNegIntro | doubleNegElim
  deriving DecidableEq, Repr

def DerivedProofRule.all : List DerivedProofRule :=
  [.letBeta, .notIntro, .notElim, .andIntro, .andElimLeft, .andElimRight,
    .orIntroLeft, .orIntroRight, .orElim, .impIntro, .impElim,
    .doubleNegIntro, .doubleNegElim]

theorem DerivedProofRule.mem_all (rule : DerivedProofRule) :
    rule ∈ DerivedProofRule.all := by
  cases rule <;> simp [DerivedProofRule.all]

/-- A small class exposing the auditable rule surface to tools and alternate
implementations.  The lists above are the canonical HolE instance. -/
class RuleInventory where
  typing : List TypingRule
  equality : List EqualityRule
  proof : List ProofRule
  derivedTyping : List DerivedTypingRule
  derivedProof : List DerivedProofRule
  typing_complete : ∀ rule, rule ∈ typing
  equality_complete : ∀ rule, rule ∈ equality
  proof_complete : ∀ rule, rule ∈ proof
  derivedTyping_complete : ∀ rule, rule ∈ derivedTyping
  derivedProof_complete : ∀ rule, rule ∈ derivedProof

instance : RuleInventory where
  typing := TypingRule.all
  equality := EqualityRule.all
  proof := ProofRule.all
  derivedTyping := DerivedTypingRule.all
  derivedProof := DerivedProofRule.all
  typing_complete := TypingRule.mem_all
  equality_complete := EqualityRule.mem_all
  proof_complete := ProofRule.mem_all
  derivedTyping_complete := DerivedTypingRule.mem_all
  derivedProof_complete := DerivedProofRule.mem_all

end Nucleus.HolE.Named.Unsorted
