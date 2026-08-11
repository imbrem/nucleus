---
title: Covalence context
status: research
issues: [564, 566, 569, 570]
reviewed: 2026-08-11
source-revision: 01225078f58260d3527f05bd3aa62ffa521e0eb6
summary: What the previous system actually built, and how to read it from Nucleus.
---

Covalence is the system Nucleus is meant to eventually replace. It is not a
specification to reproduce; it is evidence. It contains a working LCF-style HOL
kernel with an audited trusted computing base, a large body of design decisions
taken under real pressure, and at least one soundness bug that was found,
understood, and written down. All three are worth having.

This directory is the curated map. Read this page first; it is written so you
can stop after it. [Kernel lessons](kernel-lessons.md) has the invariants and
the hazard checklist for anyone implementing the Rust kernel. [The migration
map](migration-map.md) has the decision table — what Nucleus should preserve,
adapt, defer, research, or reject, source by source.

## Authority

**Current Nucleus code and issues are authoritative.** Where a Covalence design
and a Nucleus decision disagree, the Nucleus decision wins and this note is the
thing that is out of date. Covalence is historical evidence and implementation
precedent, never a specification.

## How to read the claims here

Every substantial claim below is labelled, because the difference matters:

| Label           | Meaning                                                           |
| --------------- | ----------------------------------------------------------------- |
| _[implemented]_ | Code at the pinned revision does this. Verifiable by reading it.  |
| _[in-flight]_   | A rewrite that is partly landed. The code shows both states.      |
| _[design note]_ | Written intent from a design document, not necessarily built.     |
| _[inference]_   | My reading, not something Covalence states. Treat with suspicion. |

## The pinned revision

Everything here was read at
[`0122507`](https://github.com/imbrem/covalence/commit/01225078f58260d3527f05bd3aa62ffa521e0eb6)
(2026-07-22), the tip of `main`, on 2026-08-11. The reachable history is 1,796
commits spanning 2026-03-19 to 2026-07-22.

Issues [#564](https://github.com/imbrem/nucleus/issues/564) and
[#570](https://github.com/imbrem/nucleus/issues/570) name
`ac1fcea2a0b0a75501af4a59dfb71790f3953ba7` as the revision inspected for
[#553](https://github.com/imbrem/nucleus/issues/553). **That commit is not
reachable from any ref in the repository today** — a full-history fetch does not
contain it, and asking the remote for it directly returns `not our ref`. It was
presumably force-pushed away or lived on a deleted branch. Anyone re-checking
those earlier findings should use `0122507` and expect drift.

Some paths named in #570's "initial known sources" have also moved: there is no
`crates/kernel/hol/core/src/thm/certs.rs` (the certificate dispatch is now
`crates/kernel/hol/eval/src/certs.rs`, one tier up), and
`notes/vibes/kernel/kernel-design.md` has a `kernel/` component that the issue
omits.

## What Covalence actually is

81 crates. _[implemented]_ A monorepo containing, roughly in order of relevance
to Nucleus:

- **the kernel** — `crates/kernel/`, with the HOL tower under `hol/` and a
  smaller equality kernel under `base/`;
- **theory and surface language** — `crates/kernel/hol/init/` (~162k lines): the
  standard library, a `.cov` script language, tactics, and encodings of
  Metamath, K, and WebAssembly;
- **proof-format bridges** — `crates/proof/{alethe,egglog,lean,metamath,opentheory}`;
- **storage** — `crates/store/`, `crates/vcs/object/` (Git-compatible objects),
  `crates/lib/hash/`;
- **interfaces** — WIT worlds under `crates/lib/wasm/core/wit/`, an LSP and
  server under `crates/server/`, web apps under `apps/`.

Almost none of that is Nucleus's problem. The part that is: how the kernel keeps
a very large system from being able to mint a false theorem.

## The trust architecture

This is the single most transferable thing in the repository. _[implemented]_
Covalence's trust boundary is not a comment; it is a type, a manifest, and a
generated audit.

Three layers, innermost first:

1. **`covalence-pure-trusted`** — a closed-world equality kernel. A typed
   first-order signature plus an equational rewriting calculus, where the
   complete set of inferences a theory admits is "a closed, enumerable set of
   rules fixed statically (and diffable against a checked-in manifest)". `Thm`
   has private fields and no public constructor; the sole mint is a crate-private
   `Thm::new`, and the module documentation enumerates **every** call site for an
   auditor.
2. **`covalence-core`** — the HOL Light kernel. Its `Thm` is a newtype over
   `pure::Thm<L, IsThm(Γ, φ)>`. Only two logical primitives, `=` and `ε`; `T`
   and `F` are `bool` literals, and every connective and quantifier is an
   ordinary defined constant. Twenty-five rules, listed in
   `docs/deps/core-manifest.txt`.
3. **`covalence-hol-eval`** — the `CoreEval` tier, which extends the core
   language with computation-backed certificate rules (seventeen, in
   `docs/deps/eval-manifest.txt`). `Thm<CoreLang>` carries no computation trust;
   `Thm<CoreEval>` does. There is a path up (`Thm::lift`) and no path down.

Everything else — the builder API, serialization, tactics, the script language,
the proof-format bridges, the servers — is outside the TCB. As the kernel's own
crate documentation puts it: a bug there "cannot produce a false `Thm`".

The type parameter _is_ the trust declaration. That is the design idea worth
stealing: not "we are careful about what we trust" but "the thing you are
holding says, in its type, which axioms it depended on."

### Soundness rests on `admits()` alone

_[implemented]_ Each rule's `decide` reads its premises, checks side conditions,
and **derives** its conclusion. No rule accepts a caller-supplied conclusion. So
every rule is sound on all inputs, and admitting its `TypeId` is exactly what
confers soundness. The consequence is that the inner field of the `Thm` newtype
is documented as "hygiene-only" — even a hypothetically public field could only
wrap already-true theorems.

The rule catalogue, the `admits` predicate, and the static manifest are all
emitted from one macro invocation over a single source list, "so `admits()` and
the static manifest can never drift".

### The TCB is measured

_[implemented]_ `docs/deps/` holds generated, CI-gated artifacts. At the pinned
revision:

| Configuration     | Files | Non-test LoC | `unsafe` | Mint sites | Public items |
| ----------------- | ----: | -----------: | -------: | ---------: | -----------: |
| base              |    14 |        1,496 |        0 |         24 |          128 |
| base + HOL        |    57 |        6,951 |        0 |         24 |          510 |
| base + HOL + eval |    91 |       13,281 |        0 |         24 |          716 |

Five workspace crates and 23 external crates are inside the TCB closure
(`docs/deps/tcb.json`). A separate `purge-ratchet.json` counts call sites of
deprecated kernel surfaces per crate and **may only decrease** — an increase
fails CI and refuses regeneration.

The lesson is not the specific numbers. It is that the trusted surface has a
number at all, that the number is generated rather than asserted, and that
there is a ratchet stopping it from growing quietly.

## The documentation split

_[implemented]_ Covalence separates `docs/` from `notes/` on a contract Nucleus
should recognise, since [#569](https://github.com/imbrem/nucleus/issues/569)
adopts the same one:

> **Contract:** everything in here must be _true_ — what the codebase actually
> is, kept aggressively in sync with it. Aspirations, plans, and design
> exploration do NOT live here.
>
> — `docs/README.md`

Its `notes/` is explicitly the other half: "_Aspirational_: what we want, may
drift from what exists." Notes carry stable IDs, lifecycle state, and
contribution metadata in TOML front matter, and a script builds a SQLite graph
over them.

Two things to take from this and one to leave. Take: the true/aspirational
split, and generated documentation being "true by construction". Take: notes
carrying explicit status. Leave, for now: the note database. Covalence's
`notes/` is large enough to need one; ours is three files.

## Where to look for what

A short routing table, so a task can load one file instead of the tree. Paths
are relative to the Covalence repository at the pinned revision.

| If you are working on…            | Read                                                                  |
| --------------------------------- | --------------------------------------------------------------------- |
| Term and type representation      | `crates/kernel/hol/core/src/term/term.rs`, `ty/ty.rs`                 |
| Substitution and scope            | `crates/kernel/hol/core/src/subst.rs`                                 |
| The theorem type and rules        | `crates/kernel/hol/core/src/thm/{mod,rules,typedef}.rs`               |
| The trust boundary itself         | `crates/kernel/hol/core/src/{lib,seam}.rs`, `base/trusted/src/lib.rs` |
| Checked untrusted construction    | `crates/kernel/hol/core/src/term/cons.rs`                             |
| Computation certificates          | `crates/kernel/hol/eval/src/{certs,rules}.rs`                         |
| Testing method and known hazards  | `crates/kernel/hol/core/tests/*.rs`, `eval/tests/audit_reduce.rs`     |
| Serialization and content hashing | `crates/kernel/hol/init/src/{sexp,hash}.rs`                           |
| Imports and dependency ordering   | `crates/kernel/hol/init/src/project.rs`, `script/env.rs`              |
| Untrusted proof replay            | `crates/kernel/hol/init/src/metalogic/mm_replay.rs`                   |
| WIT and component interfaces      | `crates/lib/wasm/core/wit/{kernel,store}.wit`                         |
| The kernel's own design rationale | `notes/vibes/kernel/kernel-design.md`                                 |

Expand beyond this only when a specific question requires it. The tempting
mistake is to read `crates/kernel/hol/init/` — 162k lines of theory development
— looking for kernel design. The kernel is 7k lines and lives elsewhere.

## What not to bring across

Named here so it does not need re-deciding every time someone opens the
repository. Details and evidence are in [the migration map](migration-map.md).

- The `defs/` catalogue of derived constants and its coupling to the certificate
  tables. It is the source of the one confirmed soundness bug.
- Kernel literal leaves (`Nat`, `Int`, `SmallInt`, `Blob`, `Bool` as term
  constructors). Covalence is _[in-flight]_ removing them.
- Process-local identity — `Arc` pointer equality for defined constants and
  freshness tokens. It is the correct answer for a single-process LCF kernel and
  the wrong answer for a content-addressed one.
- The tier machinery, the trait layers, the theory/model/signature script
  language, SQLite schemas, and the surface compiler. All of these earned their
  keep in a system with multiple consumers. Nucleus has none yet.
