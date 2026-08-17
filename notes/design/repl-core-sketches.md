# Two sketches for the REPL core

**Status: design spike. Source material, not a decision.** Two concrete cores
are sketched far enough to implement, with an honest accounting of what each
costs. Companion to `repl-language.md`, which holds the settled parts —
handler frames in the continuation, the horizon rule, the root default handler,
cast-as-effect.

Written to be argued with. If a section reads as advocacy, it is a defect.

---

## 0. The part that is the same in both

Both sketches run the same machine and differ only in surface. That is the point
of writing them together: **the syntax choice is cheaper than it looks, and the
two primitives in §1 are orthogonal to it.**

```
Value ::= nil | bool | int | bytes | sym | cons(Value, Value)
        | closure(Code, Env) | continuation(Vec<Frame>) | type(TypeRepr)

Frame ::= Return   { code, env }
        | Handlers { map: HandlerMap }
        | ‹sketch-specific frames›

State ::= { stack, env, code, konts, horizon }

step : State -> State        -- total, via the root default handler
```

Shared semantics, from `repl-language.md` §3b: handler frames live *in* `konts`;
closures capture `env` but never handlers; a running handler searches from
`horizon = k-1`; unmatched operations reach a root default handler, so `perform`
is total. Types are inspectable data; `cast` is an operation whose failure is an
effect.

---

## 1. The two primitives: `with` and `capture`

There are two namespaces, and they have different scoping disciplines:

| | Lexical symbol table (`env`) | Runtime handler table (`Handlers` frames) |
| --- | --- | --- |
| Scoping | static — captured by closures | dynamic — *not* captured by closures |
| Resolved at | closure creation | `perform` |
| Lives in | `env` | `konts` |

The core's two most important operations are the conversions between them, and
they are exact duals:

```
with     : lexical → dynamic      install a closure as a handler for an extent
capture  : dynamic → lexical      freeze the current resolution as a value
```

### `with` — a lexical closure becomes ambient

```scheme
(with ((fetch f) (put g)) body)
```

Pushes `Handlers{fetch ↦ f, put ↦ g}`, runs `body`, pops. `f` is an ordinary
lexical closure; `perform fetch` inside `body` resolves to it **dynamically**,
so code written long before, and closed over a different environment, still
routes through `f`.

### `capture` — ambient authority becomes a value

```scheme
(capture fetch)   ⟶  a closure invoking whatever `fetch` resolves to *now*
```

The result is an ordinary first-class value: storable, passable, returnable, and
**it outlives the `with` that installed the handler**. Where `with` is late
binding, `capture` is early binding.

### Three consequences worth stating

**(a) A captured handler closes over its horizon.** If handler `f` was installed
at frame `k`, then `perform` inside `f` searches from `k-1` — and it must still
do so when `f` is invoked later, from a call site with an entirely different
`konts`. So the closure produced by `capture` carries the horizon, not just the
code. Getting this wrong makes captured handlers behave differently from
in-place ones, which is a bug that will not present as one.

**(b) Middleware falls out.** `capture` then `with` is handler wrapping:

```scheme
(let ((inner (capture fetch)))
  (with ((fetch (lambda (h) (log h) (inner h))))
    body))
```

Logging, caching, retry, and the eager-versus-lazy CAS variants are all this
shape. No mechanism is needed beyond the two primitives.

**(c) They are capability ⟷ ambient-authority conversions**, which is what makes
the trust story tractable. `with` grants authority for a dynamic extent;
`capture` turns that authority into a capability that escapes the extent.

> For sandboxed proof producers, that escape is exactly what must not happen —
> so **`capture` is itself an operation**, and a restrictive handler table
> denies it. The mechanism polices itself, and no separate sandbox machinery is
> required.

This pairing is the reflective `reify`/`reflect` duality in a small setting. It
is worth naming because the literature on reflective towers is where the sharp
edges have already been found.

---

## 1b. Revocation, not gated capture

The safety mechanism is **revocation at scope exit**: capture freely, and when
the granting scope ends the capability dies, so using an escaped one raises.

```scheme
(with-secure ((fetch f)) body)     ; ≡ (with ((fetch f)) body) + revoke on exit
```

This supersedes the earlier suggestion of gating `capture` as an operation, and
strictly dominates it:

| | Gate `capture` | Revoke on exit |
| --- | --- | --- |
| What the granter decides | a policy, anticipated in advance | the extent — which `with` already states |
| Granularity | all-or-nothing per scope | exact, and automatic |
| Legitimate capture inside the extent | forbidden | fine |
| Extra machinery | a policy mechanism | one monotonic bit |

The granter already writes down the extent by writing `with`. Revocation makes
that statement mean what it looks like it means, and nothing further has to be
reasoned about.

This is Redell's caretaker pattern; the object-capability literature is where
its sharp edges are already documented.

### The bit belongs to the frame, not the capability

Naïvely, `revoke` kills the capability you are holding. That is wrong in two
ways, and the fix is the same for both:

> **The `Handlers` frame owns one revocation cell. Every capability captured
> from that frame references *that* cell. Scope exit flips it once.**

- `capture` may be called any number of times, and revocation must kill every
  derived capability, not the one you happen to hold. One shared cell does this
  in O(1) rather than by tracking or scanning.
- **A captured continuation can otherwise resurrect the scope.** Since handler
  frames live in `konts` (§0), a continuation captured by an *outer* handler
  contains the inner `Handlers` frames; resuming it after scope exit would
  reinstate a live `fetch`. With the cell as the authority, lookups through a
  resurrected frame check the cell, find it dead, and raise. Frame presence is
  not authority; the cell is.

This second point is the one that would otherwise be found late and be very
confusing when it was.

### Four consequences to take deliberately

**1. Revocation fires on frame pop, not at the end of the body.** Otherwise a
non-local exit — a handler that declines to resume, an unwind — leaks a live
capability. Tying it to the pop makes it automatic and total.

**2. A revoked scope may not be re-entered.** Frame pop and multi-shot resume
conflict directly: resuming into a popped scope gets a dead one. Mark
`with-secure` frames one-shot and reject re-entry with a clear error, rather
than reference-counting re-entries. A security scope that can be re-entered
after revocation is confusing regardless of what the machine does.

**3. Use of a dead capability is an ordinary effect** — `perform revoked(cap)`,
resolved dynamically at the point of use, defaulting to the root printer. No new
error mechanism, and the policy is replaceable like every other.

**4. This is the only mutable state in the core, and it is monotonic.** A
language advertised as immutable now has a bit that changes. It is worth naming
as a deliberate exception rather than letting it in quietly. Monotonicity is
what keeps it small: alive → dead, never back, so it is a write-once latch and
general mutable state cannot be built from it.

### Two things it buys

**Attenuation, for free.** `capture` the real capability, wrap it in a
restricting closure, `with` the wrapper — and the wrapper revokes independently
of what it wraps. That is the caretaker pattern proper, out of primitives that
already exist.

**A safe default.** Since the long-lived grants — the REPL's own root handlers —
sit in scopes that never exit, they are never revoked, and revoking scopes cost
them nothing. So the recommendation is to invert the naming:

> **`with` revokes. `with-escaping` is the rare, explicitly-named opt-out.**

Safe by default, and the unsafe case is visible at the *grant* site, which is
where the trust decision is actually being made — not at the capture site, where
the code doing the capturing has no standing to make it.

### Naming

Prefer `revoke` to `destroy`. Revocation affects every holder of the capability,
not the caller's copy; `destroy` suggests otherwise and the difference is
exactly the thing a reader needs to have right.


---

## 2. Sketch A — a simple immutable Lisp

### Grammar

```
e ::= <literal> | <sym>
    | (quote d)
    | (if e e e)
    | (lambda (x ...) e)
    | (e e ...)
    | (perform op e ...)
    | (with ((op e) ...) e)
    | (capture op)
    | (cast e e)
```

Nine forms. `let` desugars to `((lambda (x) body) v)`; `define` exists only at
the REPL toplevel. Everything else is a primitive in the initial environment.

### Machine

CEK, with one extra frame kind to accumulate arguments:

```
Frame ::= Return { code, env }
        | Handlers { map }
        | App { done: Vec<Value>, todo: Vec<Expr>, env }
```

`App` is the cost of applicative syntax: evaluating `(f a b)` means remembering
"two of three subexpressions done, in this environment" across each subordinate
evaluation.

### For

- **Zero onboarding.** Every agent and every human already knows it. With
  Qwen/GLM lanes, not shipping a language spec with each task is a real saving.
- **Parentheses localize arity errors.** `(tm-succ x y)` is wrong at the call
  site, not three words later. This is the single largest practical advantage.
- **Nested construction reads directly** — `(tm-eq 'bool 'zero (tm-succ x))` —
  and a HOL REPL does that constantly.
- **#706 is nearly the reference semantics already.** A fuelled big-step
  evaluator for essentially this language exists, sorry-free, in Lean. The
  `eval_big e = run_machine e` agreement theorem is a genuine head start.
- Test programs are pleasant to hand-write, which matters for the corpus lane.

### Against

- **The machine is bigger.** `App` frames, and their invariants, are pure
  overhead against the few-page target.
- **Evaluation order becomes observable** the moment effects exist. Left-to-right
  must be pinned in the spec and preserved in Lean, and it is a decision that
  cannot later be changed.
- **The §2 alignment is lost.** Handler signature, stack effect, and WASM
  function type stop being the same object; a calling convention has to be
  specified to relate them. That is the translation layer the concatenative core
  was chosen to avoid, reappearing.
- Compiling a typed region to WASM needs an explicit stack-discipline pass that
  Sketch B does not need.

---

## 3. Sketch B — a Forsp dialect

### Grammar

```
item ::= <literal>          push
       | <sym>              look up and call
       | ^<sym>             push without calling
       | '<datum>           push quoted data
       | $<sym>             pop and bind in the current scope
       | ( item ... )       push a code block, closed over the current env
```

Six productions, and **no special forms at all.** `if`, `with`, `capture`,
`cast`, and `perform` are ordinary primitives taking quoted blocks:

```
cond (then-block) (else-block) if
^cas-sqlite ^fetch (body) with
^fetch capture $my-fetch
```

Control flow is not in the grammar and not in the machine. That is the property
that makes the core small enough to read in one sitting.

### Machine

```
Frame ::= Return   { code, env }
        | Handlers { map }
```

No third frame kind. The value stack accumulates arguments, so `App` is
unnecessary — the work `App` does in Sketch A is done by the data structure that
already exists.

### For

- **Smallest machine.** Two frame kinds, six grammar productions, no special
  forms. This is the sketch that actually hits "a few pages".
- **The §2 alignment is free.** A handler signature *is* a stack effect *is* a
  WASM function type. Nothing is engineered to make that true.
- **`perform` is uniform.** An operation of any arity is exactly a word; there is
  no calling convention to specify, in the spec or in Lean.
- **Evaluation order is not a decision.** It is the stack.
- Quoted blocks make `if` and `with` ordinary values, so adding a control
  construct never touches the machine.

### Against

- **Nothing localizes arity errors.** A word given two arguments instead of
  three silently consumes what was below it and fails elsewhere. Mitigated by
  early `cast` — see `repl-language.md` §2 — but mitigation is not absence, and
  this will cost debugging time every day.
- **No agent knows it.** Every lane needs the one-page spec inline, and models
  will drift toward Scheme-shaped output under load. A real cost across a fleet.
- **Refactoring is fragile.** Changing a word's arity silently changes what every
  downstream word sees, with no syntactic signal.
- **No Lean head start.** #706 is applicative, so the reference semantics is new
  work rather than an existing branch.
- Deeply nested construction takes practice to read, and the HOL REPL is exactly
  the workload that nests deeply.

---

## 4. Side by side

| | A — Lisp | B — Forsp |
| --- | --- | --- |
| Grammar productions | 9 special forms + application | 6, no special forms |
| Frame kinds | 3 | 2 |
| Arity errors localized | **yes, by parens** | no — needs `cast` |
| Handler sig = WASM type | needs a convention | **native** |
| Evaluation order | a spec decision | not a decision |
| Agent onboarding | **free** | one page per lane |
| Lean reference semantics | **#706, mostly there** | new work |
| Nested term entry | **direct** | needs practice |
| Few-page core | tight | **comfortable** |

The split is clean: **A is better to use, B is better to build, formalize, and
compile.** Neither dominates.

---

## 5. The option that may make the choice moot

The primitives in §1 are orthogonal to syntax, and the machine in §0 is shared.
So consider building **B, and adding a reader macro that expands applicative
notation into it**:

```
(f a b)   reads as   a b f
```

Applied recursively, `(tm-eq 'bool 'zero (tm-succ x))` reads as
`'bool 'zero x tm-succ tm-eq`. Perhaps thirty lines in the reader.

This is **not** the Scheme frontend rejected in `repl-language.md` §2. That was a
compiler with its own semantics and an equivalence theorem to maintain. This is a
purely syntactic transformation with no semantic content: there is one language,
one machine, one Lean development, and two ways of typing the same program.

If it works, it buys B's machine and A's ergonomics, and the arity-localization
objection largely evaporates for code written in the applicative notation.

**Reasons it might not work, which are the things to spike:**

- Does it survive macros? If macros see post-reader form, macro authors write
  postfix regardless, and the ergonomic benefit stops at the surface.
- Mixed notation in one file may read worse than either notation alone — a
  legibility question that only reading real code answers.
- Error messages report positions in expanded form. A source map is more than
  thirty lines.

An afternoon on the reader answers all three. That afternoon is the recommended
next step on this topic, and it comes after the machine runs, not before.

---

## 6. What is actually being asked

The decision is not "Lisp or Forsp". It is:

1. **Which machine?** — B's is smaller and formalizes more easily. This is the
   consequential choice, and the one to make on the merits above.
2. **Which notation?** — cheap, changeable, possibly both (§5).
3. **`with` and `capture` as the two primitives** — settled, and independent of
   1 and 2.

Recommendation, held loosely: build B's machine, implement §1 on it, then spend
one afternoon on §5's reader before deciding whether notation needs a second
opinion. If the reader works, the question dissolves; if it does not, A's
ergonomic case is strong enough to reopen properly rather than by default.
