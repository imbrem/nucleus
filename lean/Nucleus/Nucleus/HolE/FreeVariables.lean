import Nucleus.HolE
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fold

/-!
# Free-variable indices of locally nameless HolE

Bound variables are represented by de Bruijn indices, so the support contains
exactly the indices introduced by `fv`.  The traversal includes predicates
inside types and type families.
-/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

/-- The finite set of term free-variable indices in an expression. -/
def fvarIndices : Expr Sig types sort depth → Finset Nat
  | .boolTy => ∅
  | .arr A B => fvarIndices A ∪ fvarIndices B
  | .tyApp F A => fvarIndices F ∪ fvarIndices A
  | .tyLam body => fvarIndices body
  | .tyBv _ => ∅
  | .sub A predicate => fvarIndices A ∪ fvarIndices predicate
  | .tyExists predicate => fvarIndices predicate
  | .model predicate => fvarIndices predicate
  | .primFam _ => ∅
  | .primTm _ => ∅
  | .bv _ => ∅
  | .fv name A => insert name (fvarIndices A)
  | .app function argument => fvarIndices function ∪ fvarIndices argument
  | .lam A body => fvarIndices A ∪ fvarIndices body
  | .bool _ => ∅
  | .eq A left right => fvarIndices A ∪ fvarIndices left ∪ fvarIndices right
  | .eps A predicate => fvarIndices A ∪ fvarIndices predicate
  | .abs A predicate value =>
      fvarIndices A ∪ fvarIndices predicate ∪ fvarIndices value
  | .rep A predicate value =>
      fvarIndices A ∪ fvarIndices predicate ∪ fvarIndices value

/-- One greater than every free-variable index in the expression. -/
def freshIndex (expression : Expr Sig types sort depth) : Nat :=
  (fvarIndices expression).fold max 0 id + 1

theorem lt_freshIndex {name : Nat} {expression : Expr Sig types sort depth}
    (membership : name ∈ fvarIndices expression) : name < freshIndex expression := by
  simp only [freshIndex, Nat.lt_add_one_iff, Finset.le_fold_max]
  exact Or.inr ⟨name, membership, le_rfl⟩

end Nucleus.HolE
