import Nucleus.Bytes
import Nucleus.O256.Basic

/-! # Owned S-expression syntax and structural events -/

namespace Nucleus.SExprEvent

/-- The fixed owned atom vocabulary; numeric spelling remains verbatim. -/
inductive Atom where
  | symbol (value : String) | string (value : String) | bytes (value : Bytes)
  | number (spelling : String) | keyword (name : String) | directive (name : String)
  | o256 (value : O256)
  deriving DecidableEq

mutual
  /-- An atom or proper list. -/
  inductive Expr where
    | atom (value : Atom)
    | list (children : Exprs)

  /-- A first-order sequence representation avoids nesting `Expr` through a
  library container and gives executable structural recursion. -/
  inductive Exprs where
    | nil
    | cons (head : Expr) (tail : Exprs)
end

/-- A source document is a sequence of top-level expressions. -/
abbrev Document := Exprs

/-- Events contain no borrowed source data. -/
inductive Event where
  | open | atom (value : Atom) | close
  deriving DecidableEq

mutual
  /-- Emit one expression in lexical order. -/
  def Expr.events : Expr → List Event
    | .atom value => [.atom value]
    | .list children => .open :: children.events ++ [.close]

  /-- Emit a sequence without separators. -/
  def Exprs.events : Exprs → List Event
    | .nil => []
    | .cons head tail => head.events ++ tail.events
end

namespace Exprs

def toList : Exprs → List Expr
  | .nil => []
  | .cons head tail => head :: tail.toList

def ofList : List Expr → Exprs
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

@[simp] theorem ofList_toList : ∀ xs : Exprs, ofList xs.toList = xs
  | .nil => rfl
  | .cons head tail => by simp [toList, ofList, ofList_toList tail]

@[simp] theorem toList_ofList : ∀ xs : List Expr, (ofList xs).toList = xs
  | [] => rfl
  | head :: tail => by simp [toList, ofList, toList_ofList tail]

end Exprs

/-- Completed siblings are reversed; each entry in `frames` is one open list. -/
structure State where
  frames : List (List Expr) := []
  roots : Exprs := .nil

namespace State

def push (state : State) (expr : Expr) : State := match state.frames with
  | frame :: frames => { state with frames := .cons expr frame :: frames }
  | [] => { state with roots := .cons expr state.roots }

def pushExprs : State → Exprs → State
  | state, .nil => state
  | state, .cons head tail => pushExprs (state.push head) tail

theorem pushExprs_roots : ∀ (values : Exprs) (roots : Exprs),
    ({ roots := roots } : State).pushExprs values =
      { roots := Exprs.ofList (values.toList.reverse ++ roots.toList) }
  | .nil, roots => by simp [pushExprs, Exprs.toList]
  | .cons head tail, roots => by
      rw [pushExprs]
      simp only [State.push]
      rw [pushExprs_roots tail (.cons head roots)]
      simp [Exprs.toList, List.reverse_cons, List.append_assoc]

theorem pushExprs_frame : ∀ (values : Exprs) (state : State) (frame : List Expr),
    ({ state with frames := frame :: state.frames }).pushExprs values =
      { state with frames := (values.toList.reverse ++ frame) :: state.frames }
  | .nil, state, frame => by simp [pushExprs, Exprs.toList]
  | .cons head tail, state, frame => by
      rw [pushExprs]
      simp only [State.push]
      rw [pushExprs_frame tail state (head :: frame)]
      simp [Exprs.toList, List.reverse_cons, List.append_assoc]

def step (state : State) : Event → Option State
  | .open => some { state with frames := .nil :: state.frames }
  | .atom value => some (state.push (.atom value))
  | .close => match state.frames with
    | [] => none
    | frame :: frames => some ({ state with frames := frames }.push
        (.list (Exprs.ofList frame.reverse)))

end State

/-- Iterative event consumption with no fixed nesting limit. -/
def consume : List Event → State → Option State
  | [], state => some state
  | event :: events, state => do consume events (← state.step event)

def collect (events : List Event) : Option Document := do
  let state ← consume events {}
  if state.frames.isEmpty then some (Exprs.ofList state.roots.toList.reverse) else none

private theorem consume_append (a b : List Event) (state : State) :
    consume (a ++ b) state = consume a state >>= consume b := by
  induction a generalizing state with
  | nil => rfl
  | cons event events ih => simp [consume]; cases state.step event <;> simp [ih]

mutual
  private theorem consume_expr (expr : Expr) (tail : List Event) (state : State) :
      consume (expr.events ++ tail) state = consume tail (state.push expr) := by
    cases expr with
    | atom value => simp [Expr.events, consume, State.step]
    | list children =>
        simp only [Expr.events]
        rw [List.append_assoc, consume_append]
        simp only [consume, State.step]
        change (consume children.events { state with frames := [] :: state.frames } >>=
          consume ([Event.close] ++ tail)) = _
        have hc := consume_exprs children [] { state with frames := [] :: state.frames }
        have hc' : consume children.events { state with frames := [] :: state.frames } =
            some ({ state with frames := [] :: state.frames }.pushExprs children) := by
          simpa only [List.append_nil, consume] using hc
        rw [hc']
        rw [State.pushExprs_frame children state []]
        simp [consume, State.step, State.push]

  private theorem consume_exprs (values : Exprs) (tail : List Event) (state : State) :
      consume (values.events ++ tail) state =
        consume tail (state.pushExprs values) := by
    cases values with
    | nil => rfl
    | cons head rest =>
        simp only [Exprs.events, List.append_assoc]
        rw [consume_expr, consume_exprs]
        rfl
end

/-- Event traversal and structural collection are inverse on every document. -/
@[simp] theorem collect_events (document : Document) :
    collect document.events = some document := by
  simp only [collect]
  have h := consume_exprs document [] ({ } : State)
  have h' : consume document.events {} = consume [] (({} : State).pushExprs document) := by
    simpa using h
  rw [h']
  rw [State.pushExprs_roots]
  simp [consume, Exprs.toList]

/-- Emitted events always finish with an empty delimiter stack. -/
theorem emitted_wellFormed (document : Document) :
    ∃ state, consume document.events {} = some state ∧ state.frames = [] := by
  refine ⟨(({} : State).pushExprs document), ?_, ?_⟩
  · have h := consume_exprs document [] ({ } : State)
    simpa [consume] using h
  · rw [State.pushExprs_roots]

end Nucleus.SExprEvent
