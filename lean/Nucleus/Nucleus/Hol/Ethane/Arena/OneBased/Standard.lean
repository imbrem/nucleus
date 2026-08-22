import Nucleus.Hol.Ethane.Arena.OneBased.NamedInference
import Nucleus.Hol.Ethane.Standard

/-!
# Standard one-based arena interface

These are the stable row references exported by Rust's ordinary Ethane
initialization arena. The named definitions they designate live in
`Nucleus.Hol.Ethane.Standard`; this file fixes the shared numeric interface.
-/

namespace Nucleus.Hol.Ethane.OneBased.Standard

private def reference (value : UInt64) (nonzero : value ≠ 0 := by decide) : Ref :=
  ⟨value, nonzero⟩

/-- Stable public roots of the ordinary initialization arena. -/
structure Roots where
  star : Ref
  boolTy : Ref
  truth : Ref
  falsehood : Ref
  not : Ref
  and : Ref
  or : Ref
  imp : Ref
  infinity : Ref
  natExists : Ref
  nat : Ref
  zero : Ref
  succ : Ref
  deriving DecidableEq, Repr

def rowCount : Nat := 296

def roots : Roots where
  star := reference 1
  boolTy := reference 2
  truth := reference 4
  falsehood := reference 3
  not := reference 8
  and := reference 27
  or := reference 38
  imp := reference 48
  infinity := reference 89
  natExists := reference 161
  nat := reference 162
  zero := reference 296
  succ := reference 232

namespace Builder

private def typeName : UInt64 := 1
private def functionName : UInt64 := 2
private def zeroName : UInt64 := 3
private def xName : UInt64 := 4
private def yName : UInt64 := 5
private def predicateName : UInt64 := 7
private def valueName : UInt64 := 8
private def logicPName : UInt64 := 100
private def logicQName : UInt64 := 101
private def logicFunctionName : UInt64 := 102

private abbrev BuildM := StateT (List detail.Row) Option

private def emit (expression : detail.Expr) : BuildM Ref := do
  let definitions ← get
  let result ← Ref.ofUInt64? (UInt64.ofNat (definitions.length + 1))
  set (definitions ++ [{ expr := expression }])
  return result

private def kindStar : BuildM Ref := emit .kindStar
private def boolTy : BuildM Ref := emit .boolTy
private def bool (value : Bool) : BuildM Ref := emit (.bool value)
private def tyArr (domain codomain : Ref) : BuildM Ref := emit (.tyArr domain codomain)
private def tyFv (name : UInt64) (kind : Ref) : BuildM Ref := emit (.tyFv name kind)
private def tmFv (name : UInt64) (type : Ref) : BuildM Ref := emit (.tmFv name type)
private def app (function argument : Ref) : BuildM Ref := emit (.app function argument)
private def eq (left right : Ref) : BuildM Ref := emit (.eq left right)
private def eps (type predicate : Ref) : BuildM Ref := emit (.eps type predicate)
private def tyExists (name : UInt64) (predicate : Ref) : BuildM Ref :=
  emit (.tyExists name predicate)
private def model (name : UInt64) (predicate : Ref) : BuildM Ref :=
  emit (.model name predicate)

private def app₂ (function first second : Ref) : BuildM Ref := do
  let partialApplication ← app function first
  app partialApplication second

private def lam (name : UInt64) (domain body : Ref) : BuildM Ref := do
  let binder ← tmFv name domain
  emit (.lam binder body)

private def notTm (not : Ref) (proposition : Ref) : BuildM Ref :=
  app not proposition

private def andTm (and left right : Ref) : BuildM Ref :=
  app₂ and left right

private def impTm (imp antecedent consequent : Ref) : BuildM Ref :=
  app₂ imp antecedent consequent

private def forallTm (truth : Ref) (name : UInt64) (type body : Ref) : BuildM Ref := do
  let left ← lam name type body
  let right ← lam name type truth
  eq left right

private def existsTm (name : UInt64) (type body : Ref) : BuildM Ref := do
  let predicate ← lam name type body
  let witness ← eps type predicate
  app predicate witness

private def buildNot (boolType falsehood : Ref) : BuildM Ref := do
  let proposition ← tmFv logicPName boolType
  let body ← eq proposition falsehood
  lam logicPName boolType body

private def buildAnd (boolType truth : Ref) : BuildM Ref := do
  let boolToBool ← tyArr boolType boolType
  let binaryBool ← tyArr boolType boolToBool
  let left ← tmFv logicPName boolType
  let right ← tmFv logicQName boolType
  let function ← tmFv logicFunctionName binaryBool
  let applied ← app function left
  let leftBody ← app applied right
  let leftFunctionBinder ← tmFv logicFunctionName binaryBool
  let lhs ← emit (.lam leftFunctionBinder leftBody)
  let function ← tmFv logicFunctionName binaryBool
  let applied ← app function truth
  let rightBody ← app applied truth
  let rightFunctionBinder ← tmFv logicFunctionName binaryBool
  let rhs ← emit (.lam rightFunctionBinder rightBody)
  let body ← eq lhs rhs
  let rightBinder ← tmFv logicQName boolType
  let rightLambda ← emit (.lam rightBinder body)
  let leftBinder ← tmFv logicPName boolType
  emit (.lam leftBinder rightLambda)

private def buildOr (boolType notRef andRef : Ref) : BuildM Ref := do
  let left ← tmFv logicPName boolType
  let right ← tmFv logicQName boolType
  let notLeft ← app notRef left
  let notRight ← app notRef right
  let partialApplication ← app andRef notLeft
  let neither ← app partialApplication notRight
  let body ← app notRef neither
  let rightBinder ← tmFv logicQName boolType
  let rightLambda ← emit (.lam rightBinder body)
  let leftBinder ← tmFv logicPName boolType
  emit (.lam leftBinder rightLambda)

private def buildImp (boolType notRef andRef : Ref) : BuildM Ref := do
  let antecedent ← tmFv logicPName boolType
  let consequent ← tmFv logicQName boolType
  let notConsequent ← app notRef consequent
  let partialApplication ← app andRef antecedent
  let both ← app partialApplication notConsequent
  let body ← app notRef both
  let consequentBinder ← tmFv logicQName boolType
  let consequentLambda ← emit (.lam consequentBinder body)
  let antecedentBinder ← tmFv logicPName boolType
  emit (.lam antecedentBinder consequentLambda)

private structure Logic where
  boolType : Ref
  truth : Ref
  not : Ref
  and : Ref
  imp : Ref

private def reflectsEquality (logic : Logic) (carrier function : Ref) : BuildM Ref := do
  let x ← tmFv xName carrier
  let y ← tmFv yName carrier
  let functionX ← app function x
  let functionY ← app function y
  let imageEquality ← eq functionX functionY
  let sourceEquality ← eq x y
  let reflected ← eq imageEquality sourceEquality
  let allY ← forallTm logic.truth yName carrier reflected
  forallTm logic.truth xName carrier allY

private def missesPoint (logic : Logic) (carrier function zero : Ref) : BuildM Ref := do
  let x ← tmFv xName carrier
  let functionX ← app function x
  let hits ← eq functionX zero
  let misses ← notTm logic.not hits
  forallTm logic.truth xName carrier misses

private def infinityStructure (logic : Logic) (carrier function zero : Ref) : BuildM Ref := do
  let reflects ← reflectsEquality logic carrier function
  let misses ← missesPoint logic carrier function zero
  andTm logic.and reflects misses

private def peanoStructure (logic : Logic) (carrier function zero : Ref) : BuildM Ref := do
  let infinity ← infinityStructure logic carrier function zero
  let predicateType ← tyArr carrier logic.boolType
  let predicate ← tmFv predicateName predicateType
  let base ← app predicate zero
  let value ← tmFv valueName carrier
  let premise ← app predicate value
  let successor ← app function value
  let conclusion ← app predicate successor
  let step ← impTm logic.imp premise conclusion
  let step ← forallTm logic.truth valueName carrier step
  let cases ← andTm logic.and base step
  let value ← tmFv valueName carrier
  let holds ← app predicate value
  let all ← forallTm logic.truth valueName carrier holds
  let induction ← impTm logic.imp cases all
  let induction ← forallTm logic.truth predicateName predicateType induction
  andTm logic.and infinity induction

private def infinityTypePredicate (logic : Logic) (carrier : Ref) : BuildM Ref := do
  let endomap ← tyArr carrier carrier
  let function ← tmFv functionName endomap
  let zero ← tmFv zeroName carrier
  let structureTm ← infinityStructure logic carrier function zero
  let chooseZero ← existsTm zeroName carrier structureTm
  existsTm functionName endomap chooseZero

private def peanoTypePredicate (logic : Logic) (carrier : Ref) : BuildM Ref := do
  let endomap ← tyArr carrier carrier
  let function ← tmFv functionName endomap
  let zero ← tmFv zeroName carrier
  let structureTm ← peanoStructure logic carrier function zero
  let chooseZero ← existsTm zeroName carrier structureTm
  existsTm functionName endomap chooseZero

private def chosenSuccessor (logic : Logic) (nat : Ref) : BuildM Ref := do
  let endomap ← tyArr nat nat
  let function ← tmFv functionName endomap
  let zero ← tmFv zeroName nat
  let structureTm ← peanoStructure logic nat function zero
  let chooseZero ← existsTm zeroName nat structureTm
  let predicate ← lam functionName endomap chooseZero
  eps endomap predicate

private def chosenZero (logic : Logic) (nat successor : Ref) : BuildM Ref := do
  let zero ← tmFv zeroName nat
  let structureTm ← peanoStructure logic nat successor zero
  let predicate ← lam zeroName nat structureTm
  eps nat predicate

private def build : BuildM Roots := do
  let star ← kindStar
  let boolType ← boolTy
  let falsehood ← bool false
  let truth ← bool true
  let notRef ← buildNot boolType falsehood
  let andRef ← buildAnd boolType truth
  let orRef ← buildOr boolType notRef andRef
  let impRef ← buildImp boolType notRef andRef
  let logic : Logic :=
    { boolType, truth, not := notRef, and := andRef, imp := impRef }
  let carrier ← tyFv typeName star
  let infinityPredicate ← infinityTypePredicate logic carrier
  let infinity ← tyExists typeName infinityPredicate
  let peanoPredicate ← peanoTypePredicate logic carrier
  let natExists ← tyExists typeName peanoPredicate
  let nat ← model typeName peanoPredicate
  let succ ← chosenSuccessor logic nat
  let zero ← chosenZero logic nat succ
  return Roots.mk star boolType truth falsehood notRef andRef orRef impRef
    infinity natExists nat zero succ

/-- Result of the exact Lean transcription of the Rust standard builder. -/
def result? : Option (Roots × Arena) := do
  let (generatedRoots, definitions) ← build []
  let arena := Arena.mk [] ["ax.inf"].toFinset definitions ∅ [] []
  return (generatedRoots, arena)

private def fallback : Roots × Arena := (roots, Arena.empty)

/-- Standard arena reconstructed entirely from one-based core rows. -/
def result : Roots × Arena := result?.getD fallback

def generatedRoots : Roots := result.1
def arena : Arena := result.2

end Builder

/-- The Lean builder succeeds rather than selecting its total fallback. -/
theorem builder_succeeds : Builder.result?.isSome := by
  set_option maxRecDepth 100000 in decide

/-- Lean and Rust share the same frozen public references. -/
theorem generatedRoots_eq : Builder.generatedRoots = roots := by
  set_option maxRecDepth 100000 in decide

/-- Lean and Rust share the same number of standard definitions. -/
theorem generated_rowCount : Builder.arena.defs.length = rowCount := by
  set_option maxRecDepth 100000 in decide

private def noLinks : Resolver := fun _ => none
private def resolutionFuel : Nat := rowCount + 1

/-- Executable comparison of a family root with an exact expected type. -/
def familyRootMatches (root : Ref) (expected : EmptyTy) : Bool :=
  match resolveAt? resolutionFuel noLinks Builder.arena root with
  | some (.family .star actual) => sameSyntax actual.erase expected.erase
  | _ => false

/-- Executable comparison of a term root, including its reconstructed type. -/
def termRootMatches (root : Ref) (expectedType : EmptyTy) (expected : EmptyTm) : Bool :=
  match resolveAt? resolutionFuel noLinks Builder.arena root with
  | some (.term actualType actual) =>
      sameSyntax actualType.erase expectedType.erase &&
        sameSyntax actual.erase expected.erase
  | _ => false

theorem familyRootMatches_sound {root : Ref} {expected : EmptyTy}
    (accepted : familyRootMatches root expected = true) :
    resolveAt? resolutionFuel noLinks Builder.arena root =
      some (.family .star expected) := by
  unfold familyRootMatches at accepted
  cases resolved : resolveAt? resolutionFuel noLinks Builder.arena root with
  | none => simp [resolved] at accepted
  | some value =>
      cases value with
      | kind kind => simp [resolved] at accepted
      | family kind actual =>
          cases kind with
          | star =>
              have erased : actual.erase = expected.erase :=
                (sameSyntax_eq_true_iff actual.erase expected.erase).mp (by
                  simpa [resolved] using accepted)
              have actual_eq : actual = expected :=
                Nucleus.Hol.Ethane.Expr.erase_injective erased
              set_option maxRecDepth 100000 in
                exact congrArg (fun family => some (Value.family .star family)) actual_eq
          | arr domain codomain => simp [resolved] at accepted
      | term type term => simp [resolved] at accepted

theorem termRootMatches_sound {root : Ref} {expectedType : EmptyTy}
    {expected : EmptyTm} (accepted : termRootMatches root expectedType expected = true) :
    resolveAt? resolutionFuel noLinks Builder.arena root =
      some (.term expectedType expected) := by
  unfold termRootMatches at accepted
  cases resolved : resolveAt? resolutionFuel noLinks Builder.arena root with
  | none => simp [resolved] at accepted
  | some value =>
      cases value with
      | kind kind => simp [resolved] at accepted
      | family kind family => simp [resolved] at accepted
      | term actualType actual =>
          have both :
              sameSyntax actualType.erase expectedType.erase = true ∧
              sameSyntax actual.erase expected.erase = true := by
            simpa [resolved, Bool.and_eq_true] using accepted
          have typeErased : actualType.erase = expectedType.erase :=
            (sameSyntax_eq_true_iff actualType.erase expectedType.erase).mp both.1
          have termErased : actual.erase = expected.erase :=
            (sameSyntax_eq_true_iff actual.erase expected.erase).mp both.2
          have type_eq : actualType = expectedType :=
            Nucleus.Hol.Ethane.Expr.erase_injective typeErased
          have term_eq : actual = expected :=
            Nucleus.Hol.Ethane.Expr.erase_injective termErased
          set_option maxRecDepth 100000 in
            exact congrArg some (congrArg₂ Value.term type_eq term_eq)

theorem infinity_matches :
    termRootMatches roots.infinity .boolTy Nucleus.Hol.Ethane.Standard.infinity = true := by
  set_option maxRecDepth 100000 in decide

theorem natExists_matches :
    termRootMatches roots.natExists .boolTy Nucleus.Hol.Ethane.Standard.natExists = true := by
  set_option maxRecDepth 100000 in decide

theorem nat_matches :
    familyRootMatches roots.nat Nucleus.Hol.Ethane.Standard.nat = true := by
  set_option maxRecDepth 100000 in decide

theorem succ_matches :
    termRootMatches roots.succ
      (.arr Nucleus.Hol.Ethane.Standard.nat Nucleus.Hol.Ethane.Standard.nat)
      Nucleus.Hol.Ethane.Standard.succ = true := by
  set_option maxRecDepth 100000 in decide

theorem zero_matches :
    termRootMatches roots.zero Nucleus.Hol.Ethane.Standard.nat
      Nucleus.Hol.Ethane.Standard.zero = true := by
  set_option maxRecDepth 100000 in decide

/-- The frozen infinity root denotes the exact named Ethane sentence. -/
theorem infinity_resolves :
    resolveAt? resolutionFuel noLinks Builder.arena roots.infinity =
      some (.term .boolTy Nucleus.Hol.Ethane.Standard.infinity) :=
  termRootMatches_sound infinity_matches

/-- The frozen Peano-existence root denotes the exact named sentence. -/
theorem natExists_resolves :
    resolveAt? resolutionFuel noLinks Builder.arena roots.natExists =
      some (.term .boolTy Nucleus.Hol.Ethane.Standard.natExists) :=
  termRootMatches_sound natExists_matches

/-- The frozen natural carrier root is exactly `Model P`. -/
theorem nat_resolves :
    resolveAt? resolutionFuel noLinks Builder.arena roots.nat =
      some (.family .star Nucleus.Hol.Ethane.Standard.nat) :=
  familyRootMatches_sound nat_matches

/-- The frozen successor root denotes its exact Hilbert-choice definition. -/
theorem succ_resolves :
    resolveAt? resolutionFuel noLinks Builder.arena roots.succ =
      some (.term
        (.arr Nucleus.Hol.Ethane.Standard.nat Nucleus.Hol.Ethane.Standard.nat)
        Nucleus.Hol.Ethane.Standard.succ) :=
  termRootMatches_sound succ_matches

/-- The frozen zero root denotes its exact Hilbert-choice definition. -/
theorem zero_resolves :
    resolveAt? resolutionFuel noLinks Builder.arena roots.zero =
      some (.term Nucleus.Hol.Ethane.Standard.nat Nucleus.Hol.Ethane.Standard.zero) :=
  termRootMatches_sound zero_matches

private theorem infinity_checked :
    (Value.term .boolTy Nucleus.Hol.Ethane.Standard.infinity).rustCheck = true := by
  set_option maxRecDepth 100000 in decide

private theorem natExists_checked :
    (Value.term .boolTy Nucleus.Hol.Ethane.Standard.natExists).rustCheck = true := by
  set_option maxRecDepth 100000 in decide

private theorem nat_checked :
    (Value.family .star Nucleus.Hol.Ethane.Standard.nat).rustCheck = true := by
  set_option maxRecDepth 100000 in decide

private theorem succ_checked :
    (Value.term
      (.arr Nucleus.Hol.Ethane.Standard.nat Nucleus.Hol.Ethane.Standard.nat)
      Nucleus.Hol.Ethane.Standard.succ).rustCheck = true := by
  set_option maxRecDepth 100000 in decide

private theorem zero_checked :
    (Value.term Nucleus.Hol.Ethane.Standard.nat
      Nucleus.Hol.Ethane.Standard.zero).rustCheck = true := by
  set_option maxRecDepth 100000 in decide

/-- The exact infinity root passes the proved-sound logical checker. -/
theorem infinity_wellFormed :
    Value.WellFormed (.term .boolTy Nucleus.Hol.Ethane.Standard.infinity) :=
  Value.rustCheck_sound infinity_checked

/-- The exact Peano-existence root passes the proved-sound logical checker. -/
theorem natExists_wellFormed :
    Value.WellFormed (.term .boolTy Nucleus.Hol.Ethane.Standard.natExists) :=
  Value.rustCheck_sound natExists_checked

/-- The exact model-selected natural carrier is well kinded. -/
theorem nat_wellFormed :
    Value.WellFormed (.family .star Nucleus.Hol.Ethane.Standard.nat) :=
  Value.rustCheck_sound nat_checked

/-- The exact epsilon-selected successor is well typed. -/
theorem succ_wellFormed :
    Value.WellFormed (.term
      (.arr Nucleus.Hol.Ethane.Standard.nat Nucleus.Hol.Ethane.Standard.nat)
      Nucleus.Hol.Ethane.Standard.succ) :=
  Value.rustCheck_sound succ_checked

/-- The exact epsilon-selected zero is well typed. -/
theorem zero_wellFormed :
    Value.WellFormed (.term Nucleus.Hol.Ethane.Standard.nat
      Nucleus.Hol.Ethane.Standard.zero) :=
  Value.rustCheck_sound zero_checked

theorem forest_encoding (expression : EmptySyn) :
    (Nucleus.Hol.Ethane.Arena.Encoder.run expression).forest
        (Nucleus.Hol.Ethane.Arena.Encoder.run expression).root =
      some (.syntax expression) :=
  Nucleus.Hol.Ethane.Arena.Encoder.run_forest_root expression

/-- The one-based infinity root and the established forest encoder agree on
the exact named infinity sentence. -/
theorem infinity_forest_correspondence :
    resolveAt? resolutionFuel noLinks Builder.arena roots.infinity =
        some (.term .boolTy Nucleus.Hol.Ethane.Standard.infinity) ∧
      (Nucleus.Hol.Ethane.Arena.Encoder.run
          Nucleus.Hol.Ethane.Standard.infinity.erase).forest
          (Nucleus.Hol.Ethane.Arena.Encoder.run
            Nucleus.Hol.Ethane.Standard.infinity.erase).root =
        some ((Value.term .boolTy
          Nucleus.Hol.Ethane.Standard.infinity).toForestValue) := by
  exact ⟨infinity_resolves,
    forest_encoding Nucleus.Hol.Ethane.Standard.infinity.erase⟩

/-- The one-based Peano-existence root and the established forest encoder
agree on the exact named sentence. -/
theorem natExists_forest_correspondence :
    resolveAt? resolutionFuel noLinks Builder.arena roots.natExists =
        some (.term .boolTy Nucleus.Hol.Ethane.Standard.natExists) ∧
      (Nucleus.Hol.Ethane.Arena.Encoder.run
          Nucleus.Hol.Ethane.Standard.natExists.erase).forest
          (Nucleus.Hol.Ethane.Arena.Encoder.run
            Nucleus.Hol.Ethane.Standard.natExists.erase).root =
        some ((Value.term .boolTy
          Nucleus.Hol.Ethane.Standard.natExists).toForestValue) := by
  exact ⟨natExists_resolves,
    forest_encoding Nucleus.Hol.Ethane.Standard.natExists.erase⟩

/-- The one-based natural root and the established forest encoder agree on
the exact named natural-type syntax. -/
theorem nat_forest_correspondence :
    resolveAt? resolutionFuel noLinks Builder.arena roots.nat =
        some (.family .star Nucleus.Hol.Ethane.Standard.nat) ∧
      (Nucleus.Hol.Ethane.Arena.Encoder.run
          Nucleus.Hol.Ethane.Standard.nat.erase).forest
          (Nucleus.Hol.Ethane.Arena.Encoder.run
            Nucleus.Hol.Ethane.Standard.nat.erase).root =
        some ((Value.family .star Nucleus.Hol.Ethane.Standard.nat).toForestValue) := by
  exact ⟨nat_resolves, forest_encoding Nucleus.Hol.Ethane.Standard.nat.erase⟩

/-- The one-based successor root and the established forest encoder agree on
the exact named Hilbert-choice term. -/
theorem succ_forest_correspondence :
    resolveAt? resolutionFuel noLinks Builder.arena roots.succ =
        some (.term
          (.arr Nucleus.Hol.Ethane.Standard.nat Nucleus.Hol.Ethane.Standard.nat)
          Nucleus.Hol.Ethane.Standard.succ) ∧
      (Nucleus.Hol.Ethane.Arena.Encoder.run
          Nucleus.Hol.Ethane.Standard.succ.erase).forest
          (Nucleus.Hol.Ethane.Arena.Encoder.run
            Nucleus.Hol.Ethane.Standard.succ.erase).root =
        some ((Value.term
          (.arr Nucleus.Hol.Ethane.Standard.nat Nucleus.Hol.Ethane.Standard.nat)
          Nucleus.Hol.Ethane.Standard.succ).toForestValue) := by
  exact ⟨succ_resolves,
    forest_encoding Nucleus.Hol.Ethane.Standard.succ.erase⟩

/-- The one-based zero root and the established forest encoder agree on the
exact named Hilbert-choice term. -/
theorem zero_forest_correspondence :
    resolveAt? resolutionFuel noLinks Builder.arena roots.zero =
        some (.term Nucleus.Hol.Ethane.Standard.nat
          Nucleus.Hol.Ethane.Standard.zero) ∧
      (Nucleus.Hol.Ethane.Arena.Encoder.run
          Nucleus.Hol.Ethane.Standard.zero.erase).forest
          (Nucleus.Hol.Ethane.Arena.Encoder.run
            Nucleus.Hol.Ethane.Standard.zero.erase).root =
        some ((Value.term Nucleus.Hol.Ethane.Standard.nat
          Nucleus.Hol.Ethane.Standard.zero).toForestValue) := by
  exact ⟨zero_resolves,
    forest_encoding Nucleus.Hol.Ethane.Standard.zero.erase⟩

/-- Every exported root is a local row of the standard arena. -/
theorem roots_within_bounds :
    roots.star.value.toNat ≤ rowCount ∧
    roots.boolTy.value.toNat ≤ rowCount ∧
    roots.truth.value.toNat ≤ rowCount ∧
    roots.falsehood.value.toNat ≤ rowCount ∧
    roots.not.value.toNat ≤ rowCount ∧
    roots.and.value.toNat ≤ rowCount ∧
    roots.or.value.toNat ≤ rowCount ∧
    roots.imp.value.toNat ≤ rowCount ∧
    roots.infinity.value.toNat ≤ rowCount ∧
    roots.natExists.value.toNat ≤ rowCount ∧
    roots.nat.value.toNat ≤ rowCount ∧
    roots.zero.value.toNat ≤ rowCount ∧
    roots.succ.value.toNat ≤ rowCount := by
  decide

/-- Distinct exported names never alias the same standard row. -/
theorem roots_nodup :
    [roots.star, roots.boolTy, roots.truth, roots.falsehood, roots.not,
      roots.and, roots.or, roots.imp, roots.infinity, roots.natExists,
      roots.nat, roots.zero, roots.succ].Nodup := by
  decide

end Nucleus.Hol.Ethane.OneBased.Standard
