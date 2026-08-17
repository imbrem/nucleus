# The 8-hour demo MVP

> **Partly superseded by `v0-mvp.md`.** The surface layer changed: there is no
> Scheme REPL and no parser — the shell is a Python prompt natively and a
> JavaScript prompt in the browser, over the same kernel. Lanes L1–L5 below, the
> skeleton-first protocol in §2, the model assignment in §3, and the machine
> plan in §4 all stand. Lanes L6 and L7 are replaced by the binding lanes in
> `v0-mvp.md` §6.

**Target:** by tonight, on `develop`, a Rust HOL kernel + S-expression REPL that
proves real theorems. Sloppy is fine. Unmerged is fine. The point is to have
something to point at, and to learn where the API hurts before the real build.

**Explicit non-goal:** anything from the fortnight plan. No `run_sound`, no Lean
work at all, no CBOR, no content addressing, no PRs, no review.

**What this is, precisely: the third Rust HOL kernel spike** — after
`#396–#399`/`#455` and `#587–#593` — and the first one built to be *written
against* the same day. It stays on `develop` and does not go near `main`. Its
primary output is not the code; it is a verdict on the Rust API, which is the
thing that reads fine on paper and turns out unwieldy in practice, and which
sank the equivalent designs in `imbrem/covalence`.

Before starting, read `notes/spikes/hol-kernel-rust.md` if it exists. If it does
not, the first 20 minutes of the evening are better spent skimming the two prior
stacks and writing it than writing Rust.

---

## 1. Scope: exactly what ships tonight

Transcribe **`HolLN`** — the merged, monomorphic one — into Rust by hand. Not
`Nucleus.Hol`. Monomorphism costs nothing for a demo, and #701 landing is the
one thing guaranteed not to fit in 8 hours.

The whole surface is 37 rules:

| From | Rules | Rust |
| --- | --- | --- |
| `Kinded` | 5 | `check.rs` |
| `HasType` | 12 | `check.rs` |
| `EqTm` | 8 | `eq.rs` |
| `Proves` | 12 | `proves.rs` |
| `openBound`, `weaken`, `instantiateOne`, `Fresh` | — | `subst.rs` |

Roughly 1300 lines of ordinary Rust. That is 8 hours *only if the lanes never
collide*, which is what section 2 is for.

**Reuse, do not rewrite:** `crates/repl/src/sexpr.rs` already has `Value` and
`read(&str) -> Result<Vec<Value>, ReadError>`. That is the reader. Do not write
another one.

### The demo transcript — this is the acceptance test

```
$ cargo run -p nucleus-hol
nucleus> (truth)
|- true

nucleus> (define f '(lam bool (bound 0)))
nucleus> (define app (list 'app f '(bool #t)))
nucleus> (check app)
: bool

nucleus> (define e (beta app))
nucleus> (eq-thm e)
|- (= bool (app (lam bool (bound 0)) (bool #t)) (bool #t))

nucleus> (check '(app (bool #t) (bool #t)))
error: not a function type at .0
```

Four things: it type-checks, it beta-reduces, it mints a theorem you cannot
forge, and it rejects garbage without panicking. That is a real HOL kernel.

### Cut list, in this order, if you are behind at T+5:00

1. `abs`/`rep` subtype rules · 2. `eps`/choice · 3. `succ`/`zero`/nat rules ·
4. `eta` · 5. pretty printer → `{:?}`

**Never cut:** `beta`, `refl`, `trans`, `app` congruence, `truth`, `hyp`,
`antisymm`. Those are the demo.

---

## 2. The one trick that makes 8 parallel agents work

**Hour 0 produces a skeleton where every function exists with its full
signature and a `todo!()` body, and `cargo check` is green.**

Then every lane owns exactly one file and never opens another. Rust makes this
work: a `todo!()` body still type-checks, so lane 5 can call `subst::open_bound`
on minute one while lane 2 is still writing it. No stubs to negotiate, no
interface drift, no merge conflicts — because **two agents never edit the same
file all night.**

This is worth 40 minutes of your time up front and it is the difference between
8 agents and 2.

```
crates/kernel/src/          ← TCB. You read every line of this, once, at T+7:00.
  lib.rs        ← frozen after hour 0. Nobody edits this.
  syntax.rs     L1     ~150 lines
  subst.rs      L2     ~120
  check.rs      L3     ~200
  eq.rs         L4     ~200
  proves.rs     L5     ~300
                       ─────  ≈ 970 lines, and that is your entire read budget
crates/userspace/src/       ← NOT read. Agents own it end to end.
  parse.rs      L6   ┐ same owner — the round-trip proptest is their oracle
  print.rs      L6   ┘
  session.rs    L7   handles, command dispatch
crates/kernel/tests/
  corpus.rs     L8   written from the Lean, never reading the Rust
crates/bin/hol/src/main.rs  L7
```

**Split the crate on the trust boundary at hour 0, not later.** Two crates,
`nucleus-kernel` and `nucleus-userspace`, with the theorem constructors `pub(crate)`
in the kernel. Then "what do I have to read" is answered by `ls`, not by judgement —
and it stays answered when the fortnight build starts.

Two hard rules, and they are the only process tonight:

- **One file, one owner.** Touching another lane's file is the only bannable offence.
- **Signatures are frozen at hour 0.** A lane that needs a signature changed
  posts in the shared channel and *you* make the edit in `lib.rs`. Never them.

---

## 3. Model assignment — by blast radius, not by benchmark

You are reading the kernel and nothing else — not the Lean, not userspace. So
the question per lane is **"if this model gets it subtly wrong, does anything
catch it before the demo?"** For userspace the answer is a test. For the five
TCB files the answer is *you*, once, at T+7:00 — so those should arrive as
close to right as possible, because a second pass will not fit.

| Lane | Work | | Model | Why |
| --- | --- | --- | --- | --- |
| L3 `check.rs` | `Kinded` + `HasType`, 17 rules | TCB | **Claude (Opus)** | A wrong side condition is invisible. Nothing catches it but reading |
| L4 `eq.rs` | `EqTm`, 8 rules | TCB | **Claude (Opus)** | Same. `beta`'s freshness/typing conditions are the subtlest thing tonight |
| L5 `proves.rs` | `Proves`, 12 rules | TCB | **Claude (Opus)** | Same. This is the soundness boundary |
| L2 `subst.rs` | open/close/weaken/instantiate | TCB | **Codex** | Has a naive reference implementation to diff against + proptests. Perfect autonomous grind-to-green |
| L7 `session.rs` + bin | handles, dispatch, error plumbing | user | **Codex** | High volume, low subtlety, long autonomous run |
| L1 `syntax.rs` | the 15-constructor enum, ctors, `Display` | TCB | **Qwen** | Pure data definitions. Compiler catches everything |
| L6 `parse.rs` + `print.rs` | S-expr ↔ `Hol` | user | **GLM** | Round-trip proptest is a total oracle. Wrong output is loud |
| L8 `tests/corpus.rs` | accept + reject fixtures | test | **GLM or Qwen** | Volume *is* the deliverable. 200 cases beats 20 careful ones |

**The decorrelation play:** L8 must be a different model family from L3/L4/L5,
must work from `Typing.lean`/`Kernel.lean` directly, and must never be shown the
Rust. Cross-family failure modes decorrelate; same-family ones don't. If the
corpus author and the rule author both misread the same Lean side condition,
you find out at the demo instead of at T+4.

### The highest-leverage 30 minutes: the transcription brief

Before any lane starts, **Claude reads `Typing.lean`, `Kernel.lean`,
`Substitution.lean` and writes `SPEC-<lane>.md`** — every rule as plain
pseudocode with every side condition spelled out, plus the exact error each
rejection should produce.

Then Qwen, GLM and Codex implement **from the brief, not from the Lean.** This
is the move most people skip, and it is what makes fast cheap models genuinely
effective on a formal transcription task: you have converted "read dependent
Lean correctly" (hard, invisible failure) into "implement this pseudocode"
(easy, compiler-checked).

### What replaces reading the Lean

You are not reading `HolLN`, tonight or in the fortnight. Three mechanical gates
stand in for it, and none of them costs you attention:

1. **`empty_not_proves_false` exists, is closed, and is assumption-free.** It
   already is. `#print axioms Nucleus.HolLN.empty_not_proves_false` is the whole
   check, and it is a CI line, not a reading task.
2. **The Rust API you expect is the API you got.** Write the expected public
   signature of `nucleus-kernel` *yourself* in hour 0 — that is the skeleton in
   section 2, and it is the only Lean-adjacent thing you author. Agents fill
   bodies under signatures you chose.
3. **The corpus agrees.** L8 derives fixtures from the Lean independently of
   L1–L5. Disagreement means someone misread; agreement across two model
   families is the evidence.

What you *do* read is the ~970 lines under `crates/kernel/src/`, once, looking
for exactly two things: **can a theorem be constructed without going through a
rule**, and **can any input panic**. Everything else in those files is a bug at
worst, not a soundness hole.

### One harness, four backends

Both z.ai (GLM) and Alibaba DashScope (Qwen) publish **Anthropic-compatible
endpoints** specifically so Claude Code can drive them. So you do not need four
different CLIs, four sets of muscle memory, four config formats:

```sh
# per-worktree, in each tmux pane
export ANTHROPIC_BASE_URL="https://…"   # z.ai or DashScope; verify current URL
export ANTHROPIC_AUTH_TOKEN="…"
claude                                   # same harness, different brain
```

Codex keeps its own CLI. That is one exception, not four.

---

## 4. Machines — and why you should rent none

> **Don't spin up rented boxes tonight.** Setup is 30–45 minutes of an 8-hour
> budget, and it buys nothing: your agents are API calls, not CPU. The only
> real compute bottleneck is `cargo build`, and that is fixed by `sccache`, not
> by more hosts.

| Machine | Job |
| --- | --- |
| **Laptop** | Your interactive session (orchestrator + integrator) and the demo terminal. Nothing else. Keep it responsive |
| **Hetzner** | Everything: the fast git remote, all 8 worktrees, all 8 agent panes, all builds |

### Hetzner bootstrap (~10 minutes)

```sh
# one bare repo as the fast remote — no GitHub in the loop tonight
git init --bare /srv/nucleus.git
cd /srv && git clone /srv/nucleus.git nucleus && cd nucleus
git remote add gh git@github.com:imbrem/nucleus.git
git fetch gh main && git checkout -b develop gh/main

# sccache: eight worktrees share one compilation cache for the dep graph
cargo install sccache && export RUSTC_WRAPPER=sccache

# one worktree + one tmux window per lane
for l in 1 2 3 4 5 6 7 8; do
  git worktree add ../lane$l -b lane$l develop
  tmux new-window -n lane$l -c /srv/lane$l
done
```

Each worktree gets its own `target/`; `sccache` means the dependency graph
compiles once, not eight times. That is the whole build-time story.

---

## 5. Timeline

| Time | Who | What |
| --- | --- | --- |
| **T+0:00** | you + Claude | Create `develop`. Skeleton crate: every module, every signature, `todo!()` bodies, `cargo check` green. Push |
| **T+0:20** | Claude | Write `SPEC-<lane>.md` × 8 from the Lean. **In parallel:** you run the Hetzner bootstrap |
| **T+0:50** | **all 8** | Launch. Every lane has a frozen signature and a brief |
| T+1:35 | integrator | Merge #1. `cargo check` — that is the entire review |
| T+2:20 | integrator | Merge #2 |
| T+3:05 | integrator | Merge #3 |
| **T+4:00** | — | **Gate A: `cargo test` proves `\|- true` in a unit test.** No REPL yet. If red, apply the cut list |
| T+4:45 | integrator | Merge #4 |
| T+5:30 | integrator | Merge #5. **Last call for the cut list** |
| **T+6:00** | — | **Gate B: the REPL runs the demo transcript end to end** |
| T+6:00–7:00 | all | Adversarial hour. Everyone fuzzes someone else's lane. Panics are the only bug class that matters |
| **T+7:00** | **you** | **Feature freeze**, then your one read pass: ~970 lines of `crates/kernel/src/`, in one sitting. Two questions only — can a theorem be minted outside a rule, can any input panic |
| T+8:00 | you | Demo. Record it with `asciinema` so you can replay it without a live kernel |

### The merge protocol — no PRs, none, at all

Every 45 minutes the integrator (one Claude session on the laptop) runs:

```sh
cd /srv/nucleus && git checkout develop
for l in 1 2 3 4 5 6 7 8; do
  git merge --no-edit lane$l || { git merge --abort; echo "SKIP lane$l"; }
done
cargo check --workspace && cargo test -p nucleus-kernel
git push origin develop
```

A lane that breaks the build is **skipped, not fixed** — the integrator tells
that lane, and merges the other seven. Nothing waits on anything.

PR review is precisely the mechanism that produced 50 stranded PRs. It is off
tonight. The compiler and `tests/corpus.rs` are the review.

---

## 6. What tonight is actually for

Three things you cannot get from planning, only from a running kernel:

1. **The API shape — this is the point of the evening.** You will find out
   within an hour whether opaque theorem handles want to be `Rc<Thm>`, an arena
   index, or a session-scoped `u32`; whether rule methods want to take handles
   or borrowed terms; whether the session needs to own the arena. Those
   decisions are currently unmade, they are the ones that were repeatedly got
   wrong in covalence, and no amount of review finds them — only writing
   `session.rs` and `corpus.rs` against the interface does.
2. **Where the Lean is awkward to transcribe.** Every place the Rust fights the
   Lean is a place `Kernel/Repr.lean` should differ from `HolLN`. Write these
   down as you hit them; they are the input to the fortnight's Lane A.
3. **Whether 8 cross-family lanes actually collaborate.** If the one-file-one-owner
   protocol holds for 8 hours, it holds for 14 days. If it doesn't, you have
   found that out for the price of one evening instead of one sprint.

**Write the spike note tonight, not tomorrow.** Keep `notes/spikes/hol-kernel-rust.md`
open and append to it as you go — every place the API fought back, every
signature you wanted to change at hour 3 and couldn't, every rule whose side
conditions were awkward to express. Append, do not rewrite: the two earlier
spikes belong in the same file so the three can be read against each other.

That file is the deliverable. The code is the experiment that produced it, and
it is allowed to be thrown away.

### Knock-on for the fortnight plan

The read policy makes §7 of `2026-08-hol-kernel-mvp.md` materially cheaper. That
plan budgeted ~3000 lines of TCB Rust **plus ~2500 lines of new Lean** at ~400
lines/day. Dropping the Lean read takes it to **~215 lines/day of Rust**, which
is comfortable rather than tight — and it frees the Friday-28 read pass from
being the only slot it fits in.

Two amendments follow:

- **Lane A becomes fully delegable.** `Kernel/Repr/Check/Tape/Run/Sound.lean` no
  longer needs your line-by-line attention, only its gates: `lake build` green,
  zero `sorry`, `#print axioms run_sound` clean, and the corpus it emits agreeing
  with Rust. Staff it with agents and read the theorem *statement* only.
- **Spend the freed budget on the corpus and the fuzzer, not on more features.**
  With the Lean unread, differential conformance stops being a nice-to-have and
  becomes the primary evidence that the transcription is faithful.
