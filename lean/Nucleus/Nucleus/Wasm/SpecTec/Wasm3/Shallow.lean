import Nucleus.Wasm.SpecTec.Wasm3.Selection
import Nucleus.Wasm.Word

/-!
# Shallow transcription of the Wasm 3.0 addition rules

This is a small Lean reference model, not a parser for SpecTec and not yet an
object inside Nucleus HOL. It is a flattened one-result trace abstraction
derived from these rules in the checked-in SpecTec 0.5 bundle for Wasm 3.0:

* `source/4.3-execution.instructions.spectec`: `Step_read/local.get`,
  `Step_pure/binop-val`, `Step_pure/frame-vals`, and
  `Step_pure/return-frame`;
* `source/3.1-numerics.scalar.spectec`: `$binop_(Inn, ADD, ...)` and
  `$iadd_(N, ...)`.

`Selection.executionSources` and `Selection.executionRoots` record the exact
raw-source and elaborated-IL locations consulted. No theorem below establishes
that those artifacts parse to these definitions. The explicit syntax and
relations are intended to be targets for a later checked artifact-to-HOL
quotation.
-/

namespace Nucleus.Wasm.SpecTec.Wasm3.Shallow

/-- Administrative instructions needed by the selected SpecTec rules. -/
inductive AdminInstr where
  | const (value : I32)
  | localGet (index : Nat)
  | i32Add
  | return
  deriving DecidableEq, Repr

/-- The selected fragment of a SpecTec execution configuration. -/
inductive Config where
  | running (locals : List I32) (instrs : List AdminInstr)
  | done (value : I32)
  deriving DecidableEq, Repr

/-- Trace-level instances derived from the selected SpecTec reduction rules.

Values before the redex are the containing frame's operand stack, ordered from
bottom to top. `localGet` and `binopI32Add` flatten their surrounding execution
context. `returnFrame` additionally flattens the `FRAME_` constructor, fixes the
result arity to one as in the example function, and discards the rest of that
frame.
-/
inductive Step : Config → Config → Prop where
  | localGet
      (locals values : List I32) (index : Nat) (value : I32) (rest : List AdminInstr)
      (found : locals[index]? = some value) :
      Step
        (.running locals (values.map .const ++ .localGet index :: rest))
        (.running locals (values.map .const ++ .const value :: rest))
  | binopI32Add
      (locals values : List I32) (left right : I32) (rest : List AdminInstr) :
      Step
        (.running locals
          (values.map .const ++ .const left :: .const right :: .i32Add :: rest))
        (.running locals (values.map .const ++ .const (Wasm.i32Add left right) :: rest))
  | returnFrame
      (locals values : List I32) (result : I32) (rest : List AdminInstr) :
      Step
        (.running locals (values.map .const ++ .const result :: .return :: rest))
        (.done result)

/-- Zero or more selected SpecTec steps. -/
inductive Steps : Config → Config → Prop where
  | refl (config : Config) : Steps config config
  | tail {first next last : Config} : Step first next → Steps next last → Steps first last

/-- A flattened one-result frame observation.

`returned` observes the result after the abstracted `return-frame` step;
`fallthrough` abstracts the selected `frame-vals` rule without pretending that
the reduced model contains a `FRAME_` constructor.
-/
inductive Halts : Config → I32 → Prop where
  | returned (value : I32) : Halts (.done value) value
  | fallthrough (locals : List I32) (value : I32) :
      Halts (.running locals [.const value]) value

/-- Multi-step execution of the selected one-result fragment. -/
def Exec (initial : Config) (result : I32) : Prop :=
  ∃ final, Steps initial final ∧ Halts final result

/-- Evaluate administrative instructions as a proof-side observation function.

This is not a Wasm decoder. It is used below to show that the selected
relational reductions cannot change the result they compute.
-/
def evalInstrs (locals stack : List I32) : List AdminInstr → Option I32
  | [] =>
      match stack with
      | [value] => some value
      | _ => none
  | .const value :: rest => evalInstrs locals (value :: stack) rest
  | .localGet index :: rest =>
      match locals[index]? with
      | some value => evalInstrs locals (value :: stack) rest
      | none => none
  | .i32Add :: rest =>
      match stack with
      | right :: left :: stack => evalInstrs locals (Wasm.i32Add left right :: stack) rest
      | _ => none
  | .return :: _ =>
      match stack with
      | result :: _ => some result
      | [] => none

/-- Result observed by the proof-side evaluator. -/
def observe : Config → Option I32
  | .running locals instrs => evalInstrs locals [] instrs
  | .done value => some value

theorem evalInstrs_constPrefix (locals values stack : List I32) (rest : List AdminInstr) :
    evalInstrs locals stack (values.map .const ++ rest) =
      evalInstrs locals (values.reverse ++ stack) rest := by
  induction values generalizing stack with
  | nil => rfl
  | cons value values ih =>
      simp only [List.map_cons, List.cons_append, evalInstrs, List.reverse_cons,
        List.append_assoc]
      exact ih (value :: stack)

/-- Every selected SpecTec reduction preserves the proof-side observation. -/
theorem Step.observe_eq {before after : Config} (step : Step before after) :
    observe before = observe after := by
  cases step with
  | localGet locals values index value rest found =>
      simp [observe, evalInstrs_constPrefix, evalInstrs, found]
  | binopI32Add locals values left right rest =>
      simp [observe, evalInstrs_constPrefix, evalInstrs]
  | returnFrame locals values result rest =>
      simp [observe, evalInstrs_constPrefix, evalInstrs]

/-- A finite sequence of selected reductions preserves its observation. -/
theorem Steps.observe_eq {before after : Config} (steps : Steps before after) :
    observe before = observe after := by
  induction steps with
  | refl => rfl
  | tail step _ ih => exact step.observe_eq.trans ih

theorem Halts.observe_eq {config : Config} {result : I32} (halts : Halts config result) :
    observe config = some result := by
  cases halts <;> rfl

end Nucleus.Wasm.SpecTec.Wasm3.Shallow
