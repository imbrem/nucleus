# Working in nucleus

Read this before doing anything. It is short on purpose.

---

## 1. What this repository is

Nucleus is a HOL kernel and the substrate under it: content-addressed storage,
CBOR and JSON codecs, S-expressions, SQLite, WASM components. The `covalence`
repo will eventually sit on top of it as a standard library.

Two halves, and they are not peers:

- **`lean/Nucleus/` is the specification.** It is where a design is decided and
  proven. It is not a build input — `glu build`, `glu check`, and `glu ci`
  never touch it.
- **`crates/` is the implementation.** Rust transcribes what Lean specifies.

When the two disagree, **Lean is right and Rust changes** — unless Rust found a
genuine Lean bug, which gets its own change and human review.

`notes/vision/ladder.md` is the long-range destination. `notes/plans/` holds the
current routes to it.

---

## 2. Open pull requests are spikes. Do not clean them up.

**This is the thing newcomers get wrong, every time.**

There are ~50 open pull requests and ~247 open issues. That is **deliberate**.
They are *spikes*: exploratory designs built off a common trunk so that
alternatives can be compared side by side before the real design is committed
to. Two independent Rust HOL kernel stacks are not duplicated effort — they are
two designs for the same component, kept alive so the third one can be informed
by both.

### Why they stay unmerged

Because the alternative was tried, in `imbrem/covalence`, and it failed. There,
carefully designed work kept getting **merged** — and then the design turned out
to be wrong in a way only visible once it was used. A Rust API reads fine on
paper and is unwieldy in practice; you find that out by writing against it, not
by reviewing it. The result was a trunk carrying many overlapping,
half-finished designs, which confused every agent that walked in and slowed
everything down.

So the protective mechanism here is inverted from the usual instinct:

> **Merging is the risky act. Leaving a spike open is the safe one.**

The trunk stays small and coherent; the exploration happens beside it. An open
spike costs nothing and confuses nobody, because `main` never claims it. A
merged half-design costs everyone, permanently.

The bar for opening a spike is therefore low, and **the bar for merging into
`main` is high**: the design has been used, not just written. An agent that
"helps" by merging spikes recreates the exact failure this repository is
organized to avoid.

Therefore:

- **Do not close a stale-looking PR.** Staleness is not a signal here.
- **Do not consolidate spikes**, "unify duplicated work", or open a PR that
  merely rebases one spike onto another.
- **Do not treat an open PR as debt** in any plan, estimate, or status summary.
- **Do not read PR count as a health metric.** It is a breadth metric.
- **Do not merge a spike to `main` on your own initiative**, however clean it
  looks. Merging is a human decision, made after the design has been used.

What *is* wanted: when you learn something from a spike, **write it down in
`notes/spikes/`** — what the design was, what it got right, where it fought the
grain. The spike is the experiment; the note is the result. A spike with no note
is the only kind that has actually gone to waste.

If you believe a spike should be closed, say so in your summary with your
reasoning and let a human decide. Never do it yourself.

---

## 3. The trust boundary

This is the only architectural distinction that constrains how you work.

| | Read by a human, line by line | Rules |
| --- | --- | --- |
| **TCB** — the kernel crate | **yes, every line** | `#![forbid(unsafe_code)]`. No new dependency without explicit human sign-off. Theorem and equality constructors are private; only a rule method mints one. Total functions — no panics on any input, adversarial included |
| **Userspace** — everything else | no | Ordinary care. Tests are the reviewer |
| **Lean** | no — only its gates | `lake build` green · zero `sorry`/`admit` · `#print axioms` on exported theorems shows no new axiom |

Keep the TCB small enough to be read in one sitting. If a transcription is
getting long, the *specification* is too complicated — simplify the Lean, do not
grow the budget.

**Never deserialize a checked term, equality, or theorem.** Everything crosses
one explicit checking boundary on the way in. Proof producers, importers,
codecs, and e-graphs all live outside it.

---

## 4. How to work

**Scope**
- One change, one concern. A change touching both TCB and userspace gets split.
- ≤ 400 net lines in TCB code per change. Unlimited in tests, fixtures, corpora —
  that is where volume is welcome.

**Stacking**
- Maximum stack depth 2. Do not base a change on a branch that is itself based
  on an unmerged branch. Spikes may sit open indefinitely; new work should not
  bury itself under them.

**Sequencing**
- **Fixture-first.** Write the accept case and the reject case before the
  implementation. A rule with neither does not exist.
- **Spec-first.** Point at the Lean theorem or corpus case that justifies your
  change. "It compiles" is not a justification.

**Parallel work**
- When several agents work at once, **one file has one owner.** Editing another
  lane's file is the one thing that reliably wrecks a parallel run. If you need
  a signature changed, ask — do not change it.

---

## 5. Commands

```sh
glu ci        # the complete CI validation — what the build gates on
glu check     # local validation, faster
glu fmt       # format everything
glu lint      # Rust + TypeScript linters
glu test      # test suites
glu deps      # Cargo dependency policy — run this if you touched Cargo.toml
glu loc       # source line counts
glu status    # project status headline

glu lean      # build the Lean developments (separate from glu ci by design)
cd lean/Nucleus && lake build
```

Rust is pinned to 1.97.1; Lean to `v4.33.0-rc1` with Mathlib pinned alongside.
Workspace lints already deny `clippy::all` and `clippy::pedantic`.

---

## 6. Conventions

- Comments explain *why*, at the density of the surrounding file. This codebase
  writes real prose in doc comments — match it, do not thin it out.
- Errors are structured and located: a code, a path, a message.
- Exact bounded integers for indices and IDs. Never route them through floats.
- Make allocation, arena layout, interning, and sharing observationally
  irrelevant. Prefer rechecking to caching until there is a measured reason.

---

## 7. When you finish

Say what you did, what you verified, and what you did not. If part of the task
was blocked, finish everything else and name what you left out and why. If you
learned something about a design — especially from a spike — write it into
`notes/` before you stop. That note is often worth more than the diff.
