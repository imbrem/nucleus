# Map: index

Entry point for the 2026-08-19 arena design push. Written for both the author
and agents. Everything here is either verified, cited to whoever claimed it, or
marked as an open question.

## The documents

| # | File | What it holds |
| --- | --- | --- |
| 00 | `00-index.md` | this file: the map, the citation convention, the question register |
| 01 | [`01-context.md`](./01-context.md) | current state of nucleus, covalence, Lean, Rust, as of 2026-08-19 |
| 02 | [`02-status.md`](./02-status.md) | PR / issue / docs status: what is open, grouped by design question |
| 03 | [`03-arena.md`](./03-arena.md) | the arena design and the plan to build it |
| 04 | [`04-evidence.md`](./04-evidence.md) | commands run and their output, for every `[v]` claim |
| 05 | [`05-pointers.md`](./05-pointers.md) | literature and systems, by the question each answers. From memory, unverified |
| 06 | [`06-plan.md`](./06-plan.md) | implementation order, S0–S6, with S1 sketched in detail |

Questions live in [`questions/`](./questions/), one file per round.

## Citation convention

Every non-obvious claim carries a marker:

- `[v:N]` — checked in this session; evidence item N in `04-evidence.md`.
- `[n:path]` — asserted in a repo note. Notes are agent-written unless stated;
  treat as a first pass, not as ground truth.
- `[c:path]` — from the covalence repo (read-only clone, last commit 2026-07-22).
- `[d]` — from the author's 2026-08-19 design dump.
- `[x]` — outside knowledge (prior art, other systems). Unverified against source.
- `[?R.L]` — open question L in round R; see below.

## Question register

Rounds are numbered. Question `2.B` means question B of round 2. Answers are
written back into the same file under each question, so the round file becomes
the Q/A log.

| Round | File | Opened | Answered |
| --- | --- | --- | --- |
| 1 | [`questions/round-1.md`](./questions/round-1.md) | 2026-08-19 | pending |

## Repositories

- **imbrem/nucleus** — this repo. HOL kernel plus substrate: CAS, CBOR, JSON,
  S-expressions, SQLite, WASM. `lean/Nucleus/` is the specification;
  `crates/` is the implementation. `AGENTS.md` (open in PR #712) states the rule:
  when the two disagree, Lean is right. [n:AGENTS.md]
- **imbrem/covalence** — the predecessor. LCF prover and VCS over WASM
  components, ~390k lines of Rust across 942 files, last commit 2026-07-22.
  [v:9] Source of both reusable designs and the merge-discipline lesson that
  shapes nucleus (§ `02-status.md`).

## Where things are

| Thing | Location |
| --- | --- |
| Specification | `lean/Nucleus/Nucleus/` — `Hol`, `HolE`, `HolLN`, `Cbor`, `Json`, `SExpr`, `Lrat` |
| Implementation | `crates/` — `data/*`, `lib/*`, `logic/*`, `nucleus`, `neutron`, `repl` |
| Arena spike (Rust) | `crates/logic/hol/` on branches `hol-*`; absent from `main` [v:5] |
| Long-range plan | `notes/vision/ladder.md`, in PR #712, not on `main` [v:4] |
| Working rules | `AGENTS.md`, in PR #712, not on `main` [v:4] |
| Theory bootstrap | `theories/init.json` + schema, on `main` |
| Component ABI | `wit/kernel/kernel.wit`, on `main` |

## Glossary

- **arena** — an indexed pile of HOL definitions plus imports, the unit of
  serialization. The subject of `03-arena.md`.
- **segment** — a range of arena indices supplied by an import rather than by a
  local definition.
- **fact** — a claim attached to an arena: a syntactic relation between two
  indices, or derivability of one index under a context.
- **stage** — how far an object has been checked. A number, not a kind.
- **O256** — a 256-bit BLAKE3 address. `crates/lib/hash`.
- **link** — `(address, format, class)`. Addresses raw bytes, not a structure.
- **HolLN** — the monomorphic locally nameless HOL in Lean.
- **HolE** — the signature-parametric HOL with subtype families, in Lean and in
  the Rust spike.
- **spike** — an exploratory branch kept open on purpose. Not debt.
