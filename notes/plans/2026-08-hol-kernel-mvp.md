# Two-week plan: a playable HOL kernel

**Window:** Mon 2026-08-17 → Sun 2026-08-30.
**Goal:** an interactive HOL kernel you can sit in front of and poke, whose every
rule is proven sound in Lean *as implemented* — over the concrete arena, tape and
byte-string data structures the Rust kernel actually runs on, not only over the
abstract inductive families.

Everything else in the level ladder is deliberately postponed. The final section
maps the ladder onto the four weeks after this one.

---

## 1. Where we actually are

### Lean: far ahead, and genuinely finished

`lean/Nucleus` is 14.3k lines, **zero `sorry`, zero `admit`, no bespoke axioms**.

| Area | State |
| --- | --- |
| `HolLN` — locally nameless monomorphic HOL | syntax, kinding, `HasType`, `EqTm` (7 rules + `succ`), `Proves` (10 rules + 2 infinity), substitution, contexts |
| `HolLN.Semantics` / `.Soundness` / `.Consistency` | every `EqTm` and `Proves` constructor proven sound against a fixed internal model; `empty_not_proves_false` is closed and assumption-free |
| `HolLN.Array` | flat `Row`/`RawArena` representation, `validate`, `Arena.decodeOpen`, `elaborate`, JSON codec for rows, injectivity |
| `HolLN.Json` | schema-parametric tree codec, `encode_injective`, `decodeTy`/`decodeTm` |
| `HolLN.Variants` / `.VariantSoundness` | the erasure square between sorted/scoped/raw corners |
| `Cbor` (13 files) | data model, profiles, reasonable subset, `parse?`, `deterministic`, uniqueness of deterministic encoding, DAG + CAS layers |
| `Json` (20 files) | RFC parser, I-JSON, IPLD, patch/path, ordered, extensional, CAS/IpldStore, SQLite mapping |
| `SExpr` (16 files) | binary/proper/tagged models, lexer + parser, printers with soundness theorems, Rivest canonical form, pointer/memory/allocator models |
| `Lrat` | LRAT proof checker |
| PR #700 → #701 (unmerged) | `Nucleus.Hol`: **signature-parametric** HOL with kinded type variables, relational `SigTyping`, checked/raw proof equivalence, intrinsic soundness. 8.6k lines, 35 files, builds, sorry-free |
| PR #706 (unmerged) | fuelled lexically-scoped Lisp evaluator over `SExpr2` |

### Rust: thin, and there is no HOL kernel on `main` at all

| Crate | Lines | Real? |
| --- | --- | --- |
| `lib/sqlite` | 3895 | yes, incl. a VFS |
| `lib/hash` | 2089 | yes — `O256`/BLAKE3, multiformats |
| `repl` | 1810 | yes — but it is a *SQLite/CAS* REPL, not a Scheme |
| `neutron` | 1744 | yes — CAS VFS + SQL |
| `logic/lrat` | 629 | yes |
| `data/cas` | 498 | yes — in-memory CAS |
| `nucleus` | 534 | snapshot signing + WIT bindings |
| `browser` | 392 | wasm entry |
| `ffi/python`, `data/cas-http`, `data/container`, `logic/sat` | 148–989 | partial |
| `proton`, `data/basic`, `lib/json` | 1–16 | **empty stubs** |
| **HOL kernel** | **0** | **absent** |

There is no OpenTheory, Metamath, or Alethe code anywhere in the tree.

### The trunk is thin, and the spikes are not indexed

**247 open issues, ~50 open PRs — and this is deliberate.** They are *spikes*:
exploratory designs kept off the trunk so alternatives can be compared before
the real design is committed to. `imbrem/covalence` tried the opposite, merging
carefully designed work that only proved unwieldy once written against, and
ended up with a trunk of overlapping half-finished designs that confused every
agent who touched it. Here, merging is the risky act and an open spike is the
safe one. See `AGENTS.md` §2.

Most open PRs therefore sit in deep stacks based on other unmerged branches:

- `#396 → #397 → #398 → #399 → #455` — HOL kernel in Rust (Aug 6, all draft)
- `#587 → #588 → #589 → #591 → #593` — HOL kernel in Rust *again* (Aug 11, all draft)
- `#606 → #607 → #627 → #643 → #646` — propositional/SAT foundation (Aug 12, draft)
- `#625 → #626/#647 → #648 → #649 → #650 → #652 → #674` — proposition table
- `#499 → #500 → #501`, `#418 → #419`, `#456 → #474`, `#605 → #632`
- `#700 → #701 → #705/#711`

Two independent Rust HOL kernel stacks are two designs for the same component,
kept alive on purpose. The gap is not that they are open — it is that **nothing
records what either one proved.** `notes/spikes/` is empty, so the comparison
they exist to enable cannot actually be made, and a third attempt would start
from scratch rather than from what the first two learned.

That is the one thing to fix before building: not the count, the index.

---

## 2. The one decision to make on Day 0

**Which HOL is *the* kernel?**

`HolLN` is merged, proven, small — and **monomorphic**. It has no type
variables. That is a hard wall in front of OpenTheory import, in front of
`init.json` (#707–#710 need polymorphic `list`, `option`, product/coproduct),
and in front of essentially every application on the ladder.

`Nucleus.Hol` (#700 → #701) is signature-parametric with kinded type variables,
already has checked/raw proof equivalence and intrinsic soundness, already
builds sorry-free — but is 8.6k unmerged lines.

**Recommendation: land #700 → #701 in the first 48 hours and transcribe
`Nucleus.Hol` into Rust, not `HolLN`.** Writing the Rust kernel twice is the
single most expensive mistake available this fortnight, and both previous
attempts died precisely because their scope was re-litigated mid-flight.

Concretely, the Rust kernel takes the signature as a parameter from day one but
**the MVP instantiates it at exactly one concrete signature** (the `NatSig`
analogue). Parametricity in the types, monomorphism in the binary. That costs
almost nothing now and prevents the rewrite later.

> **Fallback trigger.** If #701 is not merged by end of Day 2, freeze on
> `HolLN`, ship a monomorphic MVP, and schedule the signature migration for
> week 3. Decide once, on Day 2, and do not revisit inside the fortnight.

---

## 3. What "proven sound exactly as implemented" has to mean

Today's soundness theorem quantifies over the *inductive family* `Proves`. That
is the right theorem, but it is not yet a statement about a program. The Rust
kernel will run a flat arena of `u32` rows and a proof tape, and nothing
currently connects those bytes to `Proves`.

So the kernel is built as three layers with two machine-checked bridges:

```
  L_spec    Proves / EqTm / HasType        (done: Soundness.lean, Consistency.lean)
     |
     |  Lean theorem: run_sound
     v
  L_impl    Lean executable checker over the REAL data structures
            Arena (flat u32 rows) + Tape (flat steps) + ByteArray names
            run : Arena -> Tape -> Except Err Sequent
     |
     |  differential conformance: golden corpus + fuzzing, both in CI
     v
  L_rust    Rust transcription, function-for-function, error-code-for-error-code
```

### The Lean bridge (Lane A — the critical path)

New modules under `Nucleus/Kernel/`:

| Module | Contents |
| --- | --- |
| `Repr.lean` | `Row` as concrete fixed-width fields; `Arena := Array Row`; `Name := ByteArray`; the concrete signature table |
| `Check.lean` | total `inferKind` / `inferType : Arena → Idx → Except Err Idx`. No fuel, no partiality, structural recursion on the validated prefix |
| `Tape.lean` | a **trace** of rule applications: a flat array of steps, step `i` referencing only steps `< i` and arena indices. Internal to the soundness statement — see the note below |
| `Run.lean` | `step : State → Step → Except Err State`; `run : Arena → Tape → Except Err Sequent` |
| `Sound.lean` | **`theorem run_sound : run arena tape = .ok seq → ∃ Γ H p, seq.decode arena = some ⟨Γ, H, p⟩ ∧ Nonempty (Proves Γ H p)`** |
| `Corpus.lean` | `#eval`-driven emitter producing the golden corpus as CBOR + JSON |

`run_sound` is the deliverable of this fortnight. It is what makes the phrase
"the kernel data structures themselves being modeled" literally true.

> **`Tape` is not a wire format.** It is the trace of API calls a proof program
> makes, and it exists so `run_sound` has something to quantify over. The project
> defines no proof format: a proof is a program that calls the rule methods, and
> checking one means running it. Nothing encodes a `Tape` to bytes, and nothing
> should. See `v0-mvp.md` §4(b).

Much of the groundwork exists: `HolLN/Array.lean` already gives
`RawArena.validate`, `Arena.decodeOpen` and `elaborate` with the same
backward-reference discipline. `Tape`/`Run`/`Sound` are the new work.

### The Rust bridge (Lane F)

Three gates, all in CI, all cheap:

1. **Correspondence table.** One checked-in table pairing every Rust
   constructor and rule with its Lean counterpart. A test asserts the Rust rule
   enum and the Lean `Proves` constructor list are the same length and the same
   names. A new Lean constructor breaks the Rust build. This is 40 lines and it
   is the thing that keeps the two from drifting.
2. **Golden corpus.** Lean `#eval`s `Corpus.lean`, emits accept/reject cases
   with **exact error codes**, and the corpus is committed. Rust replays it.
   Matching error codes rather than only accept/reject roughly triples the
   discriminating power for near-zero extra cost.
3. **Differential fuzzing.** `lake build` produces a native Lean binary. Fuzz
   random and mutated arenas/tapes through both binaries and diff the outputs.
   This is what makes "exactly as implemented" testable rather than aspirational
   — and it is available today, for free, because the Lean checker compiles.

**TCB budget: ≤ 3000 lines of Rust in the trusted crate, `#![forbid(unsafe_code)]`,
zero dependencies outside `core`/`alloc` plus a pinned hash crate.** If the
transcription exceeds 3000 lines, the Lean checker is too complicated and gets
simplified rather than the budget raised.

---

## 4. MVP scope — the Day-14 demo

```
$ nucleus repl
> (define id  (term '(lam bool (bound 0))))
> (define app (term (list 'app id '(bool #t))))
> (define e   (beta app))
> (define th  (eq-of-eq-tm e))
> th
#<thm |- (= bool (app (lam bool (bound 0)) (bool #t)) (bool #t))>
> (put th)
o256:9f3c…
> (cbor th)
h'a2016f…'
> (check (fetch o256:9f3c…))
#t
```

The same transcript runs natively, and in the browser through the existing WASM
path. `(put …)`/`(fetch …)` go through the existing `data/cas` + `neutron`
plumbing, which already works.

### In scope

| Ladder item | Target |
| --- | --- |
| Kernel L0 | in-memory syntax/typing — **full** |
| Kernel L0A | bytestrings + small unsigned ints as the accelerated base — **full** |
| Kernel L1 | CBOR ser/de of **statements** — hypotheses and a conclusion — using the merged Lean `Cbor` model. Trusted in both directions, because signing refuses re-derivation. Proofs get no format at all |
| Kernel L1 (PKI) | signed derivations in SQLite, keyed by hash — **partial**, reusing `nucleus/snapshot/signing.rs` |
| Kernel L2 | content-addressed links in CBOR terms — **eager resolution only**, lazy deferred |
| UI/UX L0 | S-expression REPL, prettyprinter + parser, CBOR and in-memory round-trip — **full** |
| CAS L0, L1 | in-memory and SQLite-backed — **already exists**, wire it to the kernel |
| Persistence L0 | proofs saved to the CAS **as programs** — the CAS addresses the program, and re-checking runs it. No proof encoding is defined |
| Applications L0 | the REPL, native + browser — **full** |

### Explicitly out, and not to be reopened before Day 14

Kernel L3 (SQLite + LRAT contexts) · L4 (tree↔array interconversion beyond what
the arena already needs) · L5 (E-graphs) · UI/UX L1 (REPL as general programming
language) · Persistence L1 (WASM amalgamations) · **all** of System Integration
(OpenTheory, Metamath, Alethe, bitblasting) · CAS L2–L4 · **all** of WASM
L0–L3 · Applications L1–L2 (VSCode, MCP) · **all** Tactics · **all** Metalogic ·
**all** PL Metatheory · **all** Mathematics.

That is roughly 85% of the ladder. Shipping the remaining 15% as something you
can genuinely iterate on is worth more than 40% of everything half-landed —
which, at 50 open PRs, is the state we are trying to escape.

---

## 5. Day 0 (Monday morning, ~3 hours, you personally)

Nothing else starts until this is done. It is the highest-leverage work in the
fortnight.

1. **Index the Rust-kernel spikes** into `notes/spikes/hol-kernel-rust.md`.
   `#396–#399`/`#455` and `#587–#589`/`#591`/`#593` are two designs for the
   thing Lane B is about to build for a third time. What did each get right,
   and where did each fight the grain — especially the API friction? Leave them
   open. This note is the input to Lane B, and it is worth more than any hour
   Lane B will spend.
2. **Index the propositional/SAT spikes** into `notes/spikes/proposition-tables.md`.
   Kernel L3 is out of scope for the fortnight, so the note is the deliverable
   and the branches stay exactly where they are.
3. **Land the cheap independents today**: `#481` (BLAKE3 consts), `#484` (direnv
   check), `#418 → #419` (SQLite wrapper) if still clean. These are finished
   work, not spikes.
4. **Merge `#700 → #701`** — or set the Day-2 fallback trigger.
5. **Label every issue `mvp` / `post-mvp` / `spike`.** Agents may only pick up
   `mvp`. Expect ~15 `mvp` labels out of 247; most of the rest are `spike`, and
   `spike` explicitly means *leave it alone*.
6. **`AGENTS.md` now exists** — written alongside this plan. It carries the
   spike model, the trust boundary, the read policy, and the working rules.
   Point every agent at it first.

**Target end state: `notes/spikes/` holds two real notes, ≤ 20 open `mvp`
issues, and every remaining PR is labelled a spike rather than looking like
debt.**

---

## 6. The fortnight, lane by lane

Eight lanes. Suggested staffing assumes agents are cheap and your review time is
not.

| Lane | What | Agents | Your time |
| --- | --- | --- | --- |
| **A** | Lean kernel-as-implemented + `run_sound` | 2 | **high** — this is yours |
| **B** | Rust kernel transcription | 2 | **high** — line-by-line, it is the TCB |
| **C** | CBOR ser/de, Rust side | 2 | low |
| **D** | Scheme REPL: Lean semantics → Rust interpreter | 3 | low |
| **E** | CAS + persistence wiring | 1 | low |
| **F** | Conformance harness, corpus, fuzzing, CI | 2 | medium |
| **G** | Browser/WASM + demo | 1 | low |
| **H** | Integrator: rebase, land, triage, docs | 1 | medium |

### Week 1 — Mon 17 → Sun 23: the kernel exists and is proven

| Day | A (Lean) | B (Rust) | C (CBOR) | D (REPL) | E/F/G/H |
| --- | --- | --- | --- | --- | --- |
| **Mon 17** | Day-0 triage (you). Then: `Kernel/Repr.lean` — concrete rows, names, signature table | read `Nucleus.Hol`; write the *type signatures only* of the Rust kernel, no bodies; get them reviewed | audit Lean `Cbor.Wire` against the Rust hash/CAS types | land #706; port the Lean Lisp evaluator's shape into a Rust `eval` skeleton | H: triage. F: scaffold the corpus crate |
| **Tue 18** | `Kernel/Check.lean`: total `inferKind`/`inferType`, `Except Err` with a fixed error-code enum | transcribe `Repr` — arena, rows, index newtypes; property tests vs. naive | Rust CBOR encode for the reasonable subset | reader: parse to `Value`, matching Lean `SExpr.Parser` | F: correspondence-table test (gate 1) |
| **Wed 19** | `Kernel/Tape.lean`: step encoding, backward-reference discipline | transcribe `Check`; error codes identical to Lean | Rust CBOR decode + round-trip proptests | printer: matching Lean `printSExpr?` exactly | H: **Gate 1** — ≤8 open PRs, #701 landed or fallback taken |
| **Thu 20** | `Kernel/Run.lean`: `step`, `run`, all `EqTm` rules | transcribe `Tape` + `Run` skeleton | deterministic encoding; uniqueness proptest | `define`, `quote`, `if`, `lambda`, application | F: corpus emitter runs end-to-end in CI |
| **Fri 21** | `Run.lean`: all `Proves` rules | transcribe all `EqTm` rules | CBOR ↔ arena rows | REPL drives the Rust kernel through opaque handles | G: WASM build of the kernel crate |
| **Sat 22** | **`Sound.lean`: `run_sound` for `EqTm`** | transcribe all `Proves` rules | wire CBOR into `data/cas` | `(put …)` / `(fetch …)` in the REPL | F: differential fuzzer, first run |
| **Sun 23** | **`run_sound` for `Proves`** | Rust passes the full golden corpus | corpus emitted in both CBOR and JSON | error reporting, source positions | H: **Gate 2 — kernel proven and transcribed** |

**Gate 2 (end of Sun 23), non-negotiable:** `run_sound` is proven with no
`sorry`; `#print axioms run_sound` shows only Lean/Mathlib standard axioms; the
Rust kernel accepts and rejects exactly the golden corpus, error code for error
code; the fuzzer has run ≥ 1M cases with zero divergences and zero panics.

If Gate 2 slips, **cut scope in Lane D, not Lane A.** A proven kernel with an
ugly REPL is the MVP. A pretty REPL over an unproven kernel is not.

### Week 2 — Mon 24 → Sun 30: it becomes playable

| Day | Focus |
| --- | --- |
| **Mon 24** | A: content-addressed links in the arena — the Lean rule and its soundness. B: link resolution *outside* the trusted boundary — resolve → verify hash → parse → check, never a shortcut. D: REPL macros. |
| **Tue 25** | A: PKI — signed derivation records, keyed by hash, in SQLite; the Lean statement of what a signature does and does not buy. E: schema + `nucleus/snapshot/signing.rs` reuse. |
| **Wed 26** | **Gate 3: the Day-14 transcript runs natively.** Everything from here is hardening and polish. G: the same transcript in the browser. |
| **Thu 27** | Adversarial pass. Every lane writes malformed inputs against its own layer. F: fuzz to 10M cases. B: `cargo-mutants` or equivalent on the TCB crate — every surviving mutant is a missing test. |
| **Fri 28** | **You read the entire TCB diff line by line, in one sitting.** ~3000 lines. Nothing else is scheduled for you this day. Anything you cannot justify gets deleted, not documented. |
| **Sat 29** | Fix what Friday found. H: `notes/` writeup — the architecture, the trust boundary, what is and is not proven. |
| **Sun 30** | **Gate 4: tag `v0.1.0-mvp`.** Freeze. Write the post-mortem *before* starting week 3. |

---

## 7. Rules for the agent team

These are not style preferences. Each one maps to a specific failure already
visible in the repository.

**Stacking**
- *Maximum stack depth 2* — **for MVP lanes only.** Spikes may stack as deep as
  they like; that is their nature. Work that has to land must not bury itself
  under work that is deliberately staying open.
- One open PR per lane at a time. A lane with an open PR writes tests, not more
  features.
- Lane H (integrator) is the only agent permitted to rebase another lane's
  branch, and does so daily.

**Size**
- ≤ 400 net lines in TCB crates per PR. Unlimited in test, fixture, and corpus
  crates — those are where volume is welcome.
- A PR that touches both TCB and non-TCB code gets split. Always.

**Gates, all automated, all blocking**
- Lean: `lake build` green · zero `sorry`/`admit` · `#print axioms` on every
  exported theorem shows no new axiom.
- Rust TCB: `#![forbid(unsafe_code)]` · no new dependency without your explicit
  sign-off · clippy pedantic (already configured) · corpus + fuzz green.
- Every PR states which Lean theorem or corpus case justifies it. "It compiles"
  is not a justification.

**Sequencing**
- *Fixture-first.* The agent writes the corpus case before the implementation.
  A rule with no accept case and no reject case does not exist.
- *Spec-first.* When Lean and Rust disagree, Lean is right and Rust changes —
  unless Rust found a genuine Lean bug, which gets its own PR and your review.

**Your review budget is the binding constraint.** ~3000 lines of TCB Rust plus
~2500 lines of new Lean over 14 days is ≈ 400 lines/day of careful reading.
That is the real capacity of this fortnight. Protect it: agents review
everything outside the TCB, and you read only the TCB and `Sound.lean`.

---

## 8. Risks

| Risk | Signal | Response |
| --- | --- | --- |
| `run_sound` is harder than it looks | `Sound.lean` not started by Thu 20 | Prove it for `EqTm` only; ship `Proves` soundness as the abstract theorem plus exhaustive differential testing, and say so plainly in the release notes |
| #701 review swamps Day 1–2 | not merged by Tue 18 EOD | Take the `HolLN` fallback. Monomorphic MVP, migrate in week 3 |
| A lane starts behaving like a spike | An MVP branch open > 2 days with no merge path | Fine for a spike, fatal for a lane. Lane H either lands it, or reclassifies it as a spike, writes the note, and re-plans the lane |
| An agent "cleans up" the spikes | Any PR closing or consolidating open branches | Revert, and re-point the agent at `AGENTS.md` §2. The spikes are source material |
| Rust/Lean drift | any fuzz divergence | Stop the lane. Divergence is a soundness bug until proven a test bug |
| Scope creep from the ladder | any PR touching WASM, tactics, or import frontends | Close it. Those lanes open on Day 15 |
| Mathlib in the Lean trust base | — | Accept and document. The Lean development is a specification, and Mathlib's axioms are already the ones `#print axioms` reports |

---

## 9. After the fortnight — the ladder, resequenced

The MVP's value is that it makes the next four weeks cheap, because everything
below now has one place to plug in.

**Weeks 3–4 — make it useful.** Kernel L3 (SQLite + LRAT on contexts; the
propositional stacks come *back* here, rebased onto the real kernel) ·
System Integration L0 (OpenTheory import — this is what forces the polymorphism
decision to have been right) · UI/UX L1 (REPL as a general language over the
kernel DB, SQLite, and the CAS) · Tactics L0 (rewriter, simplifier, tauto).

**Weeks 5–6 — make it fast and shareable.** Kernel L0B (bignat, string, list,
set, map as accelerated built-ins) · Kernel L4 (tree↔array interconversion,
formalized) · CAS L2 (HTTPS + S3) · Persistence L1 · WASM L0.

**Weeks 7–8 — make it impressive.** Kernel L5 (E-graphs) · Tactics L1–L2 ·
System Integration L1 (Metamath / set.mm) and L2 (Alethe via cvc5) ·
Applications L1 (VSCode) and L2 (MCP).

The Mathematics, PL Metatheory, and Metalogic ladders are *content*, not
infrastructure. They should start the day the REPL can hold a library — which,
if this fortnight lands, is roughly Day 30 — and they parallelize across agents
far better than any of the above.

---

## 10. The single most important thing

You do not have a production problem — fourteen thousand lines of sorry-free
Lean in a few weeks is exceptional throughput — and you do not have a backlog
problem, because the backlog is a deliberate spike orchard.

What you have is an **indexing** problem. Two Rust HOL kernel designs exist and
neither has been written up, so the comparison they were built to enable cannot
be made, and Lane B is about to become a third attempt starting from zero. The
same holds across the propositional stacks.

The fortnight's real precondition is therefore three hours of writing, not of
coding: turn the spikes into `notes/spikes/` entries. Do that, and Lane B starts
from two designs' worth of hard-won API knowledge instead of from the Lean
alone. Skip it, and the most likely outcome of this fortnight is a fourth spike.

Section 5 is therefore not preamble. It is the plan.
