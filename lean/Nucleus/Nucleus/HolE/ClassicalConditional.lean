import Nucleus.HolE.ClassicalCoreKernelLaws

/-!
# Choice-defined polymorphic conditionals

This is the semantic design implemented by the Rust userspace conditional API.
It needs no new syntax constructor or kernel rule: Hilbert choice selects from
the graph `(condition ∧ z = then) ∨ (¬condition ∧ z = else)`.
-/

namespace Nucleus.HolE.ClassicalConditional

/-- The graph whose unique selected branch defines a conditional. -/
def Graph {α : Type} (condition : Bool) (thenBranch elseBranch candidate : α) : Prop :=
  (condition = true ∧ candidate = thenBranch) ∨
    (condition = false ∧ candidate = elseBranch)

theorem graph_inhabited {α : Type} (condition : Bool)
    (thenBranch elseBranch : α) :
    ∃ candidate, Graph condition thenBranch elseBranch candidate := by
  cases condition with
  | false => exact ⟨elseBranch, Or.inr ⟨rfl, rfl⟩⟩
  | true => exact ⟨thenBranch, Or.inl ⟨rfl, rfl⟩⟩

/-- Polymorphic conditional selected from its graph. -/
noncomputable def ite {α : Type} (condition : Bool)
    (thenBranch elseBranch : α) : α :=
  Classical.choose (graph_inhabited condition thenBranch elseBranch)

theorem ite_graph {α : Type} (condition : Bool)
    (thenBranch elseBranch : α) :
    Graph condition thenBranch elseBranch
      (ite condition thenBranch elseBranch) :=
  Classical.choose_spec (graph_inhabited condition thenBranch elseBranch)

@[simp] theorem ite_true {α : Type} (thenBranch elseBranch : α) :
    ite true thenBranch elseBranch = thenBranch := by
  rcases ite_graph true thenBranch elseBranch with branch | branch
  · exact branch.2
  · cases branch.1

@[simp] theorem ite_false {α : Type} (thenBranch elseBranch : α) :
    ite false thenBranch elseBranch = elseBranch := by
  rcases ite_graph false thenBranch elseBranch with branch | branch
  · cases branch.1
  · exact branch.2

theorem ite_eq_cond {α : Type} (condition : Bool)
    (thenBranch elseBranch : α) :
    ite condition thenBranch elseBranch =
      if condition then thenBranch else elseBranch := by
  cases condition <;> simp

end Nucleus.HolE.ClassicalConditional
