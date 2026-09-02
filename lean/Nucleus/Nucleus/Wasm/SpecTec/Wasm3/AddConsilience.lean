import Nucleus.Wasm.SpecTec.Wasm3.Deep
import Nucleus.Wasm.SpecTec.Wasm3.Shallow

/-!
# Consilience for the first Wasm 3.0 execution slice

This module relates two Lean-level models of the supported execution
fragment: a shallow transcription of named SpecTec rules and an independently
shaped instruction-list interpreter. Both prove the parametric behavior of the
body `local.get 0; local.get 1; i32.add`, with either explicit `return` or
structural function-body end.

This is reference metatheory, not the two-in-HOL route required for Wasm
acceleration. In particular it proves no binary parsing theorem, no connection
to the elaborated SpecTec S-expression, and no HOL quotation or lowering
theorem. The structural correspondence currently consists of the three
successful instruction bridges below, plus one-result fallthrough; it is not a
full equivalence for arbitrary interpreter states. Those stronger results
remain explicit future bridge obligations.
-/

namespace Nucleus.Wasm.SpecTec.Wasm3.AddConsilience

open Deep

/-- Termination forms covered by the selected one-result frame rules. -/
inductive Termination where
  | fallthrough
  | explicitReturn
  deriving DecidableEq, Repr

/-- The independently represented source body. -/
def body : Termination → List Deep.Instr
  | .fallthrough => [.localGet 0, .localGet 1, .i32Add]
  | .explicitReturn => [.localGet 0, .localGet 1, .i32Add, .return]

/-- Initial state of the deep interpreter for arbitrary input words. -/
def initial (termination : Termination) (left right : I32) : Deep.Machine where
  locals := [left, right]
  stack := []
  code := body termination

/-- Translate source instructions to the shallow model's administrative syntax. -/
def exposeInstr : Deep.Instr → Shallow.AdminInstr
  | .localGet index => .localGet index
  | .i32Add => .i32Add
  | .return => .return

/-- Expose a deep state as a shallow configuration.

Reversal reconciles the deep model's top-first stack with SpecTec's
bottom-to-top administrative value prefix.
-/
def expose (machine : Deep.Machine) : Shallow.Config :=
  .running machine.locals
    (machine.stack.reverse.map .const ++ machine.code.map exposeInstr)

theorem localGet_step_agrees
    (locals stack : List I32) (index : Nat) (value : I32) (code : List Deep.Instr)
    (found : locals[index]? = some value) :
    Shallow.Step
      (expose ⟨locals, stack, .localGet index :: code⟩)
      (expose ⟨locals, value :: stack, code⟩) := by
  simpa [expose, exposeInstr] using
    Shallow.Step.localGet locals stack.reverse index value (code.map exposeInstr) found

theorem localGet_tick_agrees
    (locals stack : List I32) (index : Nat) (value : I32) (code : List Deep.Instr)
    (found : locals[index]? = some value) :
    Deep.tick ⟨locals, stack, .localGet index :: code⟩ =
        some (.next ⟨locals, value :: stack, code⟩) ∧
      Shallow.Step
        (expose ⟨locals, stack, .localGet index :: code⟩)
        (expose ⟨locals, value :: stack, code⟩) := by
  constructor
  · simp [Deep.tick, found]
  · exact localGet_step_agrees locals stack index value code found

theorem i32Add_step_agrees
    (locals stack : List I32) (left right : I32) (code : List Deep.Instr) :
    Shallow.Step
      (expose ⟨locals, right :: left :: stack, .i32Add :: code⟩)
      (expose ⟨locals, Wasm.i32Add left right :: stack, code⟩) := by
  simpa [expose, exposeInstr] using
    Shallow.Step.binopI32Add locals stack.reverse left right (code.map exposeInstr)

theorem i32Add_tick_agrees
    (locals stack : List I32) (left right : I32) (code : List Deep.Instr) :
    Deep.tick ⟨locals, right :: left :: stack, .i32Add :: code⟩ =
        some (.next ⟨locals, Wasm.i32Add left right :: stack, code⟩) ∧
      Shallow.Step
        (expose ⟨locals, right :: left :: stack, .i32Add :: code⟩)
        (expose ⟨locals, Wasm.i32Add left right :: stack, code⟩) := by
  exact ⟨rfl, i32Add_step_agrees locals stack left right code⟩

theorem return_step_agrees
    (locals stack : List I32) (result : I32) (code : List Deep.Instr) :
    Shallow.Step
      (expose ⟨locals, result :: stack, .return :: code⟩)
      (.done result) := by
  simpa [expose, exposeInstr] using
    Shallow.Step.returnFrame locals stack.reverse result (code.map exposeInstr)

theorem return_tick_agrees
    (locals stack : List I32) (result : I32) (code : List Deep.Instr) :
    Deep.tick ⟨locals, result :: stack, .return :: code⟩ = some (.done result) ∧
      Shallow.Step
        (expose ⟨locals, result :: stack, .return :: code⟩)
        (.done result) := by
  exact ⟨rfl, return_step_agrees locals stack result code⟩

theorem fallthrough_agrees (locals : List I32) (result : I32) :
    Deep.tick ⟨locals, [result], []⟩ = some (.done result) ∧
      Shallow.Halts (expose ⟨locals, [result], []⟩) result := by
  constructor
  · rfl
  · simpa [expose] using Shallow.Halts.fallthrough locals result

/-- Initial shallow configuration corresponding to [`initial`]. -/
def shallowInitial (termination : Termination) (left right : I32) : Shallow.Config :=
  expose (initial termination left right)

theorem shallow_explicit_add (left right : I32) :
    Shallow.Exec (shallowInitial .explicitReturn left right) (Wasm.i32Add left right) := by
  let afterLeft : Shallow.Config :=
    .running [left, right] [.const left, .localGet 1, .i32Add, .return]
  let afterRight : Shallow.Config :=
    .running [left, right] [.const left, .const right, .i32Add, .return]
  let afterAdd : Shallow.Config :=
    .running [left, right] [.const (Wasm.i32Add left right), .return]
  refine ⟨.done (Wasm.i32Add left right), ?_, .returned _⟩
  apply Shallow.Steps.tail (next := afterLeft)
  · simpa [shallowInitial, initial, body, expose, exposeInstr, afterLeft] using
      Shallow.Step.localGet [left, right] [] 0 left [.localGet 1, .i32Add, .return] rfl
  apply Shallow.Steps.tail (next := afterRight)
  · simpa [afterLeft, afterRight] using
      Shallow.Step.localGet [left, right] [left] 1 right [.i32Add, .return] rfl
  apply Shallow.Steps.tail (next := afterAdd)
  · simpa [afterRight, afterAdd] using
      Shallow.Step.binopI32Add [left, right] [] left right [.return]
  apply Shallow.Steps.tail
  · simpa [afterAdd] using
      Shallow.Step.returnFrame [left, right] [] (Wasm.i32Add left right) []
  exact .refl _

theorem shallow_fallthrough_add (left right : I32) :
    Shallow.Exec (shallowInitial .fallthrough left right) (Wasm.i32Add left right) := by
  let afterLeft : Shallow.Config :=
    .running [left, right] [.const left, .localGet 1, .i32Add]
  let afterRight : Shallow.Config :=
    .running [left, right] [.const left, .const right, .i32Add]
  let afterAdd : Shallow.Config :=
    .running [left, right] [.const (Wasm.i32Add left right)]
  refine ⟨afterAdd, ?_, ?_⟩
  · apply Shallow.Steps.tail (next := afterLeft)
    · simpa [shallowInitial, initial, body, expose, exposeInstr, afterLeft] using
        Shallow.Step.localGet [left, right] [] 0 left [.localGet 1, .i32Add] rfl
    apply Shallow.Steps.tail (next := afterRight)
    · simpa [afterLeft, afterRight] using
        Shallow.Step.localGet [left, right] [left] 1 right [.i32Add] rfl
    apply Shallow.Steps.tail (next := afterAdd)
    · simpa [afterRight, afterAdd] using
        Shallow.Step.binopI32Add [left, right] [] left right []
    exact .refl _
  · simpa [afterAdd] using
      Shallow.Halts.fallthrough [left, right] (Wasm.i32Add left right)

theorem deep_explicit_add (left right : I32) :
    Deep.run 4 (initial .explicitReturn left right) = some (Wasm.i32Add left right) := by
  rfl

theorem deep_fallthrough_add (left right : I32) :
    Deep.run 4 (initial .fallthrough left right) = some (Wasm.i32Add left right) := by
  rfl

/-- Both models can produce the same wrapped sum for either termination form. -/
theorem add_body_witness (termination : Termination) (left right : I32) :
    Shallow.Exec (shallowInitial termination left right) (Wasm.i32Add left right) ∧
      Deep.run 4 (initial termination left right) = some (Wasm.i32Add left right) := by
  cases termination with
  | fallthrough => exact ⟨shallow_fallthrough_add left right, deep_fallthrough_add left right⟩
  | explicitReturn => exact ⟨shallow_explicit_add left right, deep_explicit_add left right⟩

theorem shallow_add_result_iff (termination : Termination) (left right result : I32) :
    Shallow.Exec (shallowInitial termination left right) result ↔
      result = Wasm.i32Add left right := by
  constructor
  · rintro ⟨final, steps, halts⟩
    have observed :
        Shallow.observe (shallowInitial termination left right) = some result :=
      steps.observe_eq.trans halts.observe_eq
    have expected :
        Shallow.observe (shallowInitial termination left right) =
          some (Wasm.i32Add left right) := by
      cases termination <;> rfl
    rw [expected] at observed
    exact (Option.some.inj observed).symm
  · intro resultEq
    subst result
    exact (add_body_witness termination left right).1

theorem deep_add_result_iff (termination : Termination) (left right result : I32) :
    Deep.run 4 (initial termination left right) = some result ↔
      result = Wasm.i32Add left right := by
  cases termination <;> simp [initial, body, Deep.run, Deep.tick, eq_comm]

/-- The two Lean models agree on every observed result for the add body. -/
theorem add_body_consilience
    (termination : Termination) (left right result : I32) :
    Shallow.Exec (shallowInitial termination left right) result ↔
      Deep.run 4 (initial termination left right) = some result :=
  (shallow_add_result_iff termination left right result).trans
    (deep_add_result_iff termination left right result).symm

end Nucleus.Wasm.SpecTec.Wasm3.AddConsilience
