# The REPL language

**Decision: a Forsp-shaped core with Scheme surface syntax, on a machine with a
reified continuation from day one.** Not "Scheme or Forsp" — both, at different
layers, because they answer different questions.

Not tonight. See §7.

---

## 1. The criterion: smallest base that keeps features out of it

The REPL is **not TCB**. Nobody reads it line by line, alternative REPLs are
fine and expected, and a rewrite costs an evening. So "you would have to rewrite
it" is not an argument here, and this note does not make one.

The real criterion is the stated goal: **maximize the simplicity of the base
while letting complex features — CAS, WIT, nondeterminism — be written down as
APIs plus a spec rather than built in.**

That is exactly what delimited handlers buy, and it is why they are worth having
early. They are the mechanism that moves features *out* of the base:

| In the base | Not in the base — a handler with a written signature |
| --- | --- |
| values, cons, closures | CAS: `fetch`, `put` |
| `lambda`, apply, `quote`, `if`, bind | kernel rules |
| `prompt`, `perform`, `resume` | SQLite |
| — | WIT/WASM imports |
| — | nondeterminism, `choose` |
| — | fuel and memory limits |
| — | IO, clock, randomness |

Eight forms in the base. Everything interesting is a signature. Without handlers
every row on the right becomes a builtin, the base grows without bound, and each
feature is baked in rather than specified.

One property makes that possible, and it is worth getting right the first time
even though the rewrite would be cheap:

> **The continuation is a value the interpreter holds, not the Rust call stack.**

A tree-walking `eval(expr, env)` that recurses in Rust spreads its continuation
across host frames where no program can reach it. That is not a disaster — it is
just a base that cannot express the right-hand column, so the right-hand column
has to move left.

### #706 is the wrong shape for this, and that is its value as a spike

`Nucleus/SExpr/Lisp.lean` (PR #706) is `evalM fuel environment expression` — a
fuelled big-step evaluator recursing on the Lean call stack, with a state monad
threaded through. It is clean, it is sorry-free, and **it cannot express
delimited control**, because there is no continuation to delimit.

That is exactly what a spike is for, and the lesson costs nothing: keep the
branch. A fuelled big-step evaluator remains the right shape for a **reference
semantics** — the thing the machine is tested against, and the other side of the
`eval_surface e = eval_core (compile e)` theorem in §2.

---

## 2. Why the core is Forsp-shaped: three things that want to be one thing

The typed-boundary requirement settles it. A handler declares argument types and
a result type; arguments arrive on the stack, results are returned on the stack.
Note what that description already is:

| | Shape |
| --- | --- |
| A handler signature | consumes `(A, B)` from the stack, produces `(R)` |
| A concatenative stack effect | `A B -- R` |
| A WASM function type | `[A B] -> [R]` |
| A WIT function | `func(a: A, b: B) -> R` |

**These are the same object.** In a stack-based core they are literally one
thing. In an applicative core they are three different things with two
translation layers between them, and those layers are where the WASM compilation
story gets expensive.

Which gives the punchline the whole design is worth building for:

> **A handler *is* a WIT interface.** "Install a handler" and "supply this WASM
> component's imports" become the same operation.

That is what makes CAS-as-a-handler more than an elegance: a Scheme handler and
a WASM component implementing the same WIT interface are interchangeable, and
the program above them cannot tell which it got.

### But the surface stays Scheme

A proof REPL's dominant activity is typing nested data — `'(lam bool (bound 0))`
— and nested literals are the one thing concatenative notation is worst at.
Forsp keeps S-expression syntax, so quoted data is unaffected either way; the
question is only whether *code* reads applicatively. It should.

Bonkoski's point about Forsp is that it *is* lambda calculus in disguise, with
translations both directions. So compile Scheme surface → stack core in one
pass, and later prove `eval_surface e = eval_core (compile e)` in Lean. That
theorem is the reason to keep #706 alive.

---

## 3. The machine

```
Value ::= nil | bool | int | bytes | sym | cons(Value, Value)
        | closure(Code, Env) | continuation(Vec<Frame>) | tag(PromptId)

Instr ::= Push(Value) | Lookup(Sym) | Bind(Sym) | Call | Quote(Value)
        | Perform(Op) | Prompt(Tag, HandlerSet) | Resume

Frame ::= Return { code: Code, env: Env }
        | Delimiter { tag: Tag, handlers: HandlerSet, answer: Type }

State ::= { stack: Vec<Value>, env: Env, code: Code, konts: Vec<Frame> }

step : State -> Result<State, Error>
```

`Perform(op)` walks `konts` from the top to the nearest `Delimiter` handling
`op`, splits the frame vector there, packages the prefix as a `continuation`
value, and enters the handler with the operation's arguments plus that
continuation on the stack. That is the entire mechanism. Roughly 50 lines once
the machine exists; impossible before it does.

In Lean the same state is a flat structure and `step` is a total function, so
determinism, progress, and preservation are ordinary inductions. This is
markedly nicer to formalize than a higher-order big-step evaluator — a second,
independent reason to prefer the flat machine.

---

## 4. Handlers as the typing boundary

Inside a handled region, the language is dynamically typed. At every effect
boundary it is checked. That is contracts-at-boundaries, and it is coherent:

```scheme
(interface cas
  (fetch (o256)  -> bytes)
  (put   (bytes) -> o256))

(with cas/sqlite
  (lambda () (check (fetch #o256:9f3c…))))
```

`fetch` pushes an `o256`, or the machine crashes at the boundary. It returns
`bytes`, or the machine crashes at the boundary. Between boundaries, nothing is
checked and nothing needs to be.

**Why this is the door to compilation:** a region between two typed boundaries
has known input and output types, so it can be monomorphized and compiled —
to WASM, whose function types are the boundary types unchanged. The dynamic
core stays for interactive use; the typed boundaries are where a compiler gets
purchase. You do not need a type system over the whole language to get efficient
compilation of the parts that matter.

### The honest gap: answer types

Operation signatures are only half of handler typing. The other half is the
**answer type** — the type the handled block returns, which is what the captured
continuation produces when resumed. Full handler calculi make handlers
polymorphic in it. **WIT cannot express that**, so WIT types alone will not
type-check handlers in general.

The livable restriction: **fix the answer type per `prompt`.** Handlers become
monomorphic — `Delimiter` carries a concrete `answer: Type` in §3 above — which
costs some expressiveness, keeps WIT sufficient, and keeps WASM compilation
trivial. Take this restriction deliberately and write down what it forbids;
do not discover it later.

---

## 5. The CAS handler, and the one rule that keeps it sound

`fetch : o256 -> bytes` as an effect makes eager and lazy content addressing two
handlers over the *same* program rather than a flag through the codebase, and
makes the AI-resolver CAS from the ladder a third. All three untrusted, all
three swappable.

> **Verification never lives in the handler.** The effect returns bytes. The
> check `hash(bytes) == requested` happens unconditionally where bytes cross
> into the kernel. A handler that could verify is a handler that could forge.

With that rule the trust story is undisturbed: effects change *what* you get,
never *whether it is valid*, because everything crosses the same checking
boundary regardless of which handler produced it. A useful corollary — a proof
script's own hash does not depend on which handler ran it. The program is
addressed; the handler is ambient.

---

## 6. Nondeterminism, and the multi-shot question

`choose : (list A) -> A` as an effect gives backtracking search, and for a proof
REPL that is tactic backtracking essentially for free — resume the continuation
once per alternative.

That requires **multi-shot** continuations, which conflict with effectful
handlers: resuming twice through a region that performed a write does the write
twice. The standard resolution applies —

- **one-shot by default**, which covers CAS, WIT, IO, and resource limits;
- **multi-shot opt-in per prompt**, for search;
- a prompt that permits multi-shot may not contain a one-shot-only effect.

Decide this when `choose` is implemented, not before, but leave the flag in
`Delimiter` from the start.

Resource limits are a handler too: fuel and memory ceilings for untrusted proof
producers (issue #553 M6) stop being special machinery and become an ordinary
handler that declines to resume.

---

## 6b. What is canonical is the interface set, not the implementation

Since alternative REPLs are fine, the thing to canonicalize is **the handler
signatures**, not the language that installs them. Two REPLs agree if they
implement the same interfaces; a WASM component and a Scheme closure are
interchangeable at the same boundary. That is the whole point of §2.

So the durable artifacts, in order of importance:

1. **`interfaces/*.wit`** — CAS, kernel, SQLite, limits. Version these. They are
   the spec, and they outlive every REPL that implements them.
2. **A conformance transcript per interface** — the same script, the same
   results, under any implementation. This is what makes "alternative REPLs are
   OK" checkable rather than aspirational.
3. **The canonical REPL** — one blessed implementation, replaceable.
4. The machine, the surface syntax, the compiler. All negotiable.

Get the ordering right and a rewrite is a Tuesday. Get it wrong — bake CAS into
the interpreter — and a rewrite takes the CAS semantics with it.

---

## 7. What this means for tonight

**Nothing. Lane D builds no language.**

Tonight's REPL is a fixed command dispatcher over the existing `sexpr::read` —
`(truth)`, `(beta …)`, `(check …)`, `(define …)` as a flat symbol table. No
lambdas, no closures, no machine. ~150 lines.

That is not a compromise; it is the correct scope. Tonight's question is whether
the *kernel* API is any good, and a language would obscure the answer while
consuming the evening. A dispatcher exercises the kernel API just as hard.

The machine is week-3 work and should be its own spike with its own note. Since
the rewrite is cheap, build the crudest machine that runs — no types, one-shot
only, CAS as the single handler — and let the *second* one be informed. Do not
design it fully before writing it; that is what produced this note's §4 gap.

## Sequencing after that

1. The machine — `step`, frames, no effects yet. Scheme surface compiles to it.
2. `prompt` / `perform` / one-shot resume. CAS as the first handler; verification stays outside.
3. Extract the handler signatures into `interfaces/*.wit` and write the conformance transcript. **This is the deliverable**; the REPL is scaffolding around it.
4. Typed boundaries with monomorphic answer types, generated from those `.wit` files both directions.
5. Multi-shot for `choose`, gated per prompt.
6. Compile typed regions to WASM. This is where the alignment in §2 pays off, or doesn't — and if it doesn't, that is the finding.

## Open questions worth spiking before committing

- Does Scheme-surface-to-stack-core survive contact with macros, or do macros want to see the core?
- Is `Delimiter` carrying a concrete answer type actually enough for the handlers we want, or does the first real use want polymorphism?
- Do WIT resources (handles) map onto handler-returned values cleanly, or do they need a separate mechanism?
