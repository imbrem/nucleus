import Nucleus.Classical.Tagged.Rules

/-! # Equivalence-preserving formula rewrites -/

namespace Nucleus.Classical.Tagged.RewriteRules

open Nucleus.Classical
open Nucleus.Classical.Tagged

universe u
variable {Atom : Type u}

def Equivalent (left right : Formula Atom) : Prop :=
  ∀ assignment, left.Eval assignment ↔ right.Eval assignment

theorem demorganAnd (children : List (Formula Atom)) :
    Equivalent (.and true children) (.or false (children.map Formula.neg)) := by
  classical
  intro assignment
  simp [Formula.Eval, Signed, Formula.evalAll_iff,
    Formula.evalAny_iff, Formula.eval_neg]

theorem demorganOr (children : List (Formula Atom)) :
    Equivalent (.or true children) (.and false (children.map Formula.neg)) := by
  classical
  intro assignment
  simp [Formula.Eval, Signed, Formula.evalAll_iff,
    Formula.evalAny_iff, Formula.eval_neg]

private theorem complementary_not_all (assignment : Assignment Atom)
    {children : List (Formula Atom)} {formula : Formula Atom}
    (positive : formula ∈ children) (negative : formula.neg ∈ children) :
    ¬ Formula.EvalAll children assignment := by
  intro all
  have formulaTrue := (Formula.evalAll_iff assignment children).mp all formula positive
  have negatedTrue := (Formula.evalAll_iff assignment children).mp all formula.neg negative
  exact (Formula.eval_neg formula assignment).mp negatedTrue formulaTrue

private theorem complementary_any (assignment : Assignment Atom)
    {children : List (Formula Atom)} {formula : Formula Atom}
    (positive : formula ∈ children) (negative : formula.neg ∈ children) :
    Formula.EvalAny children assignment := by
  by_cases truth : formula.Eval assignment
  · exact (Formula.evalAny_iff assignment children).mpr ⟨formula, positive, truth⟩
  · exact (Formula.evalAny_iff assignment children).mpr
      ⟨formula.neg, negative, (Formula.eval_neg formula assignment).mpr truth⟩

theorem contradictionAnd (negative : Bool) {children : List (Formula Atom)}
    {formula : Formula Atom} (positive : formula ∈ children)
    (complement : formula.neg ∈ children) :
    Equivalent (.and negative children) (.or negative []) := by
  intro assignment
  have impossible := complementary_not_all assignment positive complement
  cases negative <;> simp [Formula.Eval, Formula.EvalAny, Signed, impossible]

theorem contradictionOr (negative : Bool) {children : List (Formula Atom)}
    {formula : Formula Atom} (positive : formula ∈ children)
    (complement : formula.neg ∈ children) :
    Equivalent (.or negative children) (.and negative []) := by
  intro assignment
  have true := complementary_any assignment positive complement
  cases negative <;> simp [Formula.Eval, Formula.EvalAll, Signed, true]

theorem contradictionSat (negative : Bool) {children : List (Formula Atom)}
    {formula : Formula Atom} (positive : formula ∈ children)
    (complement : formula.neg ∈ children) :
    Equivalent (.sat negative children) (.or negative []) := by
  intro ambient
  have unsat : ¬ ∃ fresh : Assignment Atom, Formula.EvalAll children fresh := by
    rintro ⟨fresh, all⟩
    exact complementary_not_all fresh positive complement all
  cases negative <;> simp [Formula.Eval, Formula.EvalAny, Signed, unsat]

theorem evalAll_perm {left right : List (Formula Atom)} (permutation : left.Perm right)
    (assignment : Assignment Atom) :
    Formula.EvalAll left assignment ↔ Formula.EvalAll right assignment := by
  simp only [Formula.evalAll_iff]
  exact ⟨fun truth child member ↦ truth child (permutation.mem_iff.mpr member),
    fun truth child member ↦ truth child (permutation.mem_iff.mp member)⟩

theorem evalAny_perm {left right : List (Formula Atom)} (permutation : left.Perm right)
    (assignment : Assignment Atom) :
    Formula.EvalAny left assignment ↔ Formula.EvalAny right assignment := by
  simp only [Formula.evalAny_iff]
  exact ⟨fun ⟨child, member, truth⟩ ↦
      ⟨child, permutation.mem_iff.mp member, truth⟩,
    fun ⟨child, member, truth⟩ ↦
      ⟨child, permutation.mem_iff.mpr member, truth⟩⟩

theorem permuteAnd (negative : Bool) {left right : List (Formula Atom)}
    (permutation : left.Perm right) : Equivalent (.and negative left) (.and negative right) := by
  intro assignment
  cases negative <;> simp [Formula.Eval, Signed, evalAll_perm permutation assignment]

theorem permuteOr (negative : Bool) {left right : List (Formula Atom)}
    (permutation : left.Perm right) : Equivalent (.or negative left) (.or negative right) := by
  intro assignment
  cases negative <;> simp [Formula.Eval, Signed, evalAny_perm permutation assignment]

theorem permuteSat (negative : Bool) {left right : List (Formula Atom)}
    (permutation : left.Perm right) : Equivalent (.sat negative left) (.sat negative right) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Signed, evalAll_perm permutation]

theorem dedupAnd [DecidableEq (Formula Atom)] (negative : Bool)
    (children : List (Formula Atom)) :
    Equivalent (.and negative children) (.and negative children.dedup) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Signed, Formula.evalAll_iff]

theorem dedupOr [DecidableEq (Formula Atom)] (negative : Bool)
    (children : List (Formula Atom)) :
    Equivalent (.or negative children) (.or negative children.dedup) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Signed, Formula.evalAny_iff]

theorem dedupSat [DecidableEq (Formula Atom)] (negative : Bool)
    (children : List (Formula Atom)) :
    Equivalent (.sat negative children) (.sat negative children.dedup) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Signed, Formula.evalAll_iff]

def SameMembers (left right : List (Formula Atom)) : Prop :=
  ∀ formula, formula ∈ left ↔ formula ∈ right

theorem localDedup_sameMembers {children : List (Formula Atom)} {remove : Nat}
    {removed : Formula Atom} (selected : children[remove]? = some removed)
    (retained : removed ∈ children.eraseIdx remove) :
    SameMembers children (children.eraseIdx remove) := by
  intro formula
  obtain ⟨bound, atIndex⟩ := List.getElem?_eq_some_iff.mp selected
  have permutation := List.getElem_cons_eraseIdx_perm bound
  constructor
  · intro member
    have inCons : formula ∈ children[remove] :: children.eraseIdx remove :=
      permutation.mem_iff.mpr member
    rcases List.mem_cons.mp inCons with equal | remains
    · rw [atIndex] at equal
      simpa [equal] using retained
    · exact remains
  · intro member
    exact List.eraseIdx_subset member

theorem sameMembersAnd (negative : Bool) {left right : List (Formula Atom)}
    (same : SameMembers left right) :
    Equivalent (.and negative left) (.and negative right) := by
  intro assignment
  have allIff : Formula.EvalAll left assignment ↔
      Formula.EvalAll right assignment := by
    simp only [Formula.evalAll_iff]
    exact ⟨fun truth child member ↦ truth child ((same child).mpr member),
      fun truth child member ↦ truth child ((same child).mp member)⟩
  cases negative <;> simp [Formula.Eval, Signed, allIff]

theorem sameMembersOr (negative : Bool) {left right : List (Formula Atom)}
    (same : SameMembers left right) :
    Equivalent (.or negative left) (.or negative right) := by
  intro assignment
  have anyIff : Formula.EvalAny left assignment ↔
      Formula.EvalAny right assignment := by
    simp only [Formula.evalAny_iff]
    exact ⟨fun ⟨child, member, truth⟩ ↦
        ⟨child, (same child).mp member, truth⟩,
      fun ⟨child, member, truth⟩ ↦
        ⟨child, (same child).mpr member, truth⟩⟩
  cases negative <;> simp [Formula.Eval, Signed, anyIff]

theorem sameMembersSat (negative : Bool) {left right : List (Formula Atom)}
    (same : SameMembers left right) :
    Equivalent (.sat negative left) (.sat negative right) := by
  intro assignment
  have allIff (fresh : Assignment Atom) : Formula.EvalAll left fresh ↔
      Formula.EvalAll right fresh := by
    simp only [Formula.evalAll_iff]
    exact ⟨fun truth child member ↦ truth child ((same child).mpr member),
      fun truth child member ↦ truth child ((same child).mp member)⟩
  cases negative <;> simp [Formula.Eval, Signed, allIff]

private theorem evalAll_append (left right : List (Formula Atom))
    (assignment : Assignment Atom) :
    Formula.EvalAll (left ++ right) assignment ↔
      Formula.EvalAll left assignment ∧ Formula.EvalAll right assignment := by
  induction left with
  | nil => simp [Formula.EvalAll]
  | cons head tail ih => simp [Formula.EvalAll, ih, and_assoc]

private theorem evalAny_append (left right : List (Formula Atom))
    (assignment : Assignment Atom) :
    Formula.EvalAny (left ++ right) assignment ↔
      Formula.EvalAny left assignment ∨ Formula.EvalAny right assignment := by
  induction left with
  | nil => simp [Formula.EvalAny]
  | cons head tail ih => simp [Formula.EvalAny, ih, or_assoc]

theorem flattenAnd (negative : Bool) (before nested after : List (Formula Atom)) :
    Equivalent (.and negative (before ++ [.and false nested] ++ after))
      (.and negative (before ++ nested ++ after)) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Formula.EvalAll, Signed, evalAll_append]

theorem flattenOr (negative : Bool) (before nested after : List (Formula Atom)) :
    Equivalent (.or negative (before ++ [.or false nested] ++ after))
      (.or negative (before ++ nested ++ after)) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Formula.EvalAny, Signed, evalAny_append]

theorem flattenSat (negative : Bool) (before nested after : List (Formula Atom)) :
    Equivalent (.sat negative (before ++ [.and false nested] ++ after))
      (.sat negative (before ++ nested ++ after)) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Formula.EvalAll, Signed, evalAll_append]

private theorem evalAll_replace (before after : List (Formula Atom))
    {left right : Formula Atom} (equivalent : Equivalent left right)
    (assignment : Assignment Atom) :
    Formula.EvalAll (before ++ left :: after) assignment ↔
      Formula.EvalAll (before ++ right :: after) assignment := by
  simp [evalAll_append, Formula.EvalAll, equivalent assignment]

private theorem evalAny_replace (before after : List (Formula Atom))
    {left right : Formula Atom} (equivalent : Equivalent left right)
    (assignment : Assignment Atom) :
    Formula.EvalAny (before ++ left :: after) assignment ↔
      Formula.EvalAny (before ++ right :: after) assignment := by
  simp [evalAny_append, Formula.EvalAny, equivalent assignment]

theorem replaceAnd (negative : Bool) (before after : List (Formula Atom))
    {left right : Formula Atom} (equivalent : Equivalent left right) :
    Equivalent (.and negative (before ++ left :: after))
      (.and negative (before ++ right :: after)) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Signed, evalAll_replace before after equivalent assignment]

theorem replaceOr (negative : Bool) (before after : List (Formula Atom))
    {left right : Formula Atom} (equivalent : Equivalent left right) :
    Equivalent (.or negative (before ++ left :: after))
      (.or negative (before ++ right :: after)) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Signed, evalAny_replace before after equivalent assignment]

theorem replaceSat (negative : Bool) (before after : List (Formula Atom))
    {left right : Formula Atom} (equivalent : Equivalent left right) :
    Equivalent (.sat negative (before ++ left :: after))
      (.sat negative (before ++ right :: after)) := by
  intro assignment
  cases negative <;>
    simp [Formula.Eval, Signed, evalAll_replace before after equivalent]

/-- A formula-path context, represented without exposing packed addresses. -/
inductive Context (Atom : Type u) where
  | root
  | and (negative : Bool) (before after : List (Formula Atom)) (parent : Context Atom)
  | or (negative : Bool) (before after : List (Formula Atom)) (parent : Context Atom)
  | sat (negative : Bool) (before after : List (Formula Atom)) (parent : Context Atom)

def Context.plug : Context Atom → Formula Atom → Formula Atom
  | .root, formula => formula
  | .and negative before after parent, formula =>
      parent.plug (.and negative (before ++ formula :: after))
  | .or negative before after parent, formula =>
      parent.plug (.or negative (before ++ formula :: after))
  | .sat negative before after parent, formula =>
      parent.plug (.sat negative (before ++ formula :: after))

theorem Context.congruent (context : Context Atom) {left right : Formula Atom}
    (equivalent : Equivalent left right) :
    Equivalent (context.plug left) (context.plug right) := by
  induction context generalizing left right with
  | root => exact equivalent
  | and negative before after parent ih =>
      exact ih (replaceAnd negative before after equivalent)
  | or negative before after parent ih =>
      exact ih (replaceOr negative before after equivalent)
  | sat negative before after parent ih =>
      exact ih (replaceSat negative before after equivalent)

theorem sequentOfEquivalent {left right premise conclusion : Formula Atom}
    (equivalent : Equivalent left right) :
    (∀ assignment,
      (Sequent.mk left conclusion).Holds assignment ↔
        (Sequent.mk right conclusion).Holds assignment) ∧
    (∀ assignment,
      (Sequent.mk premise left).Holds assignment ↔
        (Sequent.mk premise right).Holds assignment) := by
  constructor <;> intro assignment <;>
    simp [Sequent.Holds, equivalent assignment]

theorem fromBothDirections {left right : Formula Atom}
    (forward : ∀ assignment, left.Eval assignment → right.Eval assignment)
    (backward : ∀ assignment, right.Eval assignment → left.Eval assignment) :
    Equivalent left right := fun assignment ↦ ⟨forward assignment, backward assignment⟩

/-- Checked model evidence is an assignment satisfying every child. -/
def Model (children : List (Formula Atom)) : Prop :=
  ∃ assignment : Assignment Atom, Formula.EvalAll children assignment

theorem proveSat (children : List (Formula Atom)) (model : Model children) :
    ∀ assignment, (Sequent.mk (.and false []) (.sat false children)).Holds assignment := by
  intro assignment _
  simpa [Model, Formula.Eval, Signed] using model

theorem modelSatImplication (premise conclusion : List (Formula Atom))
    (_premiseModel : Model premise) (conclusionModel : Model conclusion) :
    ∀ assignment,
      (Sequent.mk (.sat false premise) (.sat false conclusion)).Holds assignment := by
  intro assignment _
  simpa [Model, Formula.Eval, Signed] using conclusionModel

theorem satIntro (children : List (Formula Atom)) :
    ∀ assignment,
      (Sequent.mk (.and false children) (.sat false children)).Holds assignment := by
  intro assignment childrenTrue
  have all : Formula.EvalAll children assignment := by
    simpa [Formula.Eval, Signed] using childrenTrue
  simpa [Formula.Eval, Signed] using
    (⟨assignment, all⟩ : ∃ fresh : Assignment Atom,
      Formula.EvalAll children fresh)

theorem truthIntro (formula : Formula Atom) :
    ∀ assignment, (Sequent.mk formula (.and false [])).Holds assignment := by
  intro assignment _
  simp [Formula.Eval, Formula.EvalAll, Signed]

end Nucleus.Classical.Tagged.RewriteRules
