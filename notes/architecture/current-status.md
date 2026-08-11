---
title: Current status
status: active
issues: [564, 569]
reviewed: 2026-08-11
summary: What is actually implemented in the repository today, and what is not.
---

A snapshot of what exists in this repository, written so a new contributor or
agent can tell implemented behaviour from planned direction without reading the
whole issue tracker. Everything below was checked against the working tree on
the `reviewed` date; where it describes intent rather than code, it says so.

## The short version

Nucleus is a minimal kernel foundation intended eventually to host a rewritten
Covalence. It is not required to preserve Covalence APIs or storage formats.

The organising principle is a trust boundary: **serialization, imports,
databases, resolvers, proof programs, and e-graphs do not mint theorem
authority; checked kernel transitions do.** Every design decision below follows
from wanting that boundary to stay small and inspectable.

There are two current higher-order-logic lanes, and only one of them has code:

- the Lean development under [`lean/Nucleus`](../../lean/Nucleus), which is the
  proved semantic reference;
- a minimal JSON-first executable Rust kernel, which is planned in
  [#553](https://github.com/imbrem/nucleus/issues/553) and **does not exist
  yet**.

Nothing in `crates/` implements HOL today. The Rust side of the repository is
currently storage, hashing, content addressing, SQLite, and component
plumbing — the foundation the kernel will sit on, not the kernel.

## The Lean reference

`Nucleus.HolLN` is an intrinsically scoped, locally nameless higher-order logic
in about 2,500 lines of Lean, and it is proved, not sketched:

| Module                                                                              | What it establishes                                  |
| ----------------------------------------------------------------------------------- | ---------------------------------------------------- |
| [`Syntax.lean`](../../lean/Nucleus/Nucleus/HolLN/Syntax.lean)                       | One dependent family `Hol` indexed by sort and depth |
| [`Scope.lean`](../../lean/Nucleus/Nucleus/HolLN/Scope.lean)                         | Opening, closing, and scope arithmetic               |
| [`Substitution.lean`](../../lean/Nucleus/Nucleus/HolLN/Substitution.lean)           | Term substitution and its equations                  |
| [`TypeSubstitution.lean`](../../lean/Nucleus/Nucleus/HolLN/TypeSubstitution.lean)   | The same for types                                   |
| [`Typing.lean`](../../lean/Nucleus/Nucleus/HolLN/Typing.lean)                       | Well-typedness relative to free and bound contexts   |
| [`Kernel.lean`](../../lean/Nucleus/Nucleus/HolLN/Kernel.lean)                       | The `Proves` derivation rules                        |
| [`ProofSubstitution.lean`](../../lean/Nucleus/Nucleus/HolLN/ProofSubstitution.lean) | Derivations are stable under substitution            |
| [`Semantics.lean`](../../lean/Nucleus/Nucleus/HolLN/Semantics.lean)                 | The `Eval` model                                     |
| [`Soundness.lean`](../../lean/Nucleus/Nucleus/HolLN/Soundness.lean)                 | Derivations evaluate to `true`                       |
| [`Consistency.lean`](../../lean/Nucleus/Nucleus/HolLN/Consistency.lean)             | `empty_not_proves_false`, closed and assumption-free |

The syntax uses de Bruijn indices bounded by the term-depth index for bound
variables and stable natural-number names for free variables. Subtype
predicates always have depth one, so they carry a fixed one-variable context
and cannot mention ambient bound term variables.

This development is a specification, not a build input. It is deliberately
outside `glu build`, `glu check`, and `glu ci`, carries a Mathlib dependency
nothing else needs, and gets its own CI jobs. When the Rust kernel lands, the
correspondence between its rules and `Kernel.lean` is the thing to keep honest.

## The Rust workspace

Fourteen crates, all named `covalence-*`, all `publish = false` and version
`0.0.0`, on edition 2024 with `unsafe_code = "deny"` and clippy `all` and
`pedantic` denied workspace-wide. The generated crate metadata classifies
thirteen of them as trusted-computing-base and one — the CLI — as product; the
site's [crate graph](https://imbrem.github.io/nucleus/crates/) renders that
classification.

### Library primitives, `crates/lib`

External dependencies are reached through a facade crate rather than directly,
so the trusted surface is a set of crates we own rather than a set of versions
we happen to have resolved.

- `error` — error conventions over `miette` and `snafu`.
- `crypto` — Ed25519 via `ed25519-dalek`.
- `hash` — BLAKE3, SHA-256, and Git SHA-1, behind features.
- `json` — JSON via `serde_json`.
- `serde` — `serde` derive surface.
- `rand` — randomness, including the `wasm32-unknown-unknown` JavaScript-host
  path.
- `sqlite` — a safe wrapper over the SQLite C API, including a VFS layer and
  registry.

### Data, `crates/data`

- `cas` — content-addressed byte sources.
- `container` — const-indexed heterogeneous tuple projection, sealed on
  purpose: supporting another container is described in the crate as a trust
  decision rather than a structural one.
- `basic` — reserved; currently empty.

### The core, `crates/proton`, `crates/neutron`, `crates/nucleus`

- [`neutron`](../../crates/neutron/src/lib.rs) is uninterpreted relational
  machinery over SQLite: a connection with connection-local metadata, a
  content-addressed VFS (`CasVfs`, `register_cas`), image handling, and SQL
  helpers. Its own documentation calls it deliberately permeable — callers can
  reach the underlying SQLite connection, and it does not enforce semantic
  invariants.
- [`nucleus`](../../crates/nucleus/src/lib.rs) is the portable trusted core and
  the policy-enforcing layer above `neutron`. Today it holds the connection
  wrapper and snapshot signing (`Ed25519Signer`, `Ed25519Verifier`,
  `valid_snapshot_statement`), plus a `smoke` entry point used by cross-target
  tests. It builds as both `cdylib` and `rlib`, and exports a WIT component
  under `target_os = "wasi"`.
- [`proton`](../../crates/proton/src/lib.rs) is a placeholder for execution
  instances: a doc comment and nothing else.

Treat the Proton/Neutron split as an intended division of responsibility that
is only partly built. `neutron` is real; `proton` is a name.

### Interfaces

[`wit/kernel/kernel.wit`](../../wit/kernel/kernel.wit) and
[`wit/kernel/deps/cas/cas.wit`](../../wit/kernel/deps/cas/cas.wit) define the
kernel and content-addressed-store component ABIs — kernel identity as an
Ed25519 public key plus a contract address, and a SQL interface whose
connections attach store objects read-only and snapshot back to an address.
These are ABI definitions; the component that `crates/nucleus` currently
exports is the much smaller `nucleus:smoke` world in
[`crates/nucleus/wit/world.wit`](../../crates/nucleus/wit/world.wit).

The `packages/nucleus` npm package wraps the same core for browsers and Node,
by two routes: a `wasm-bindgen` build and a jco transpile of the component.

## Build and workflow

Cargo owns package topology and is authoritative. The Buck2 build is generated
from Cargo metadata and committed under
[`buck/cargo`](../../buck/cargo); it must be refreshed after any crate or
dependency change, and `glu buck check` fails when it is stale.

[`tools/glu`](../../tools/glu) is the repository task runner and the interface
worth learning: `glu doctor`, `fmt`, `lint`, `test`, `build`, `check`, `ci`,
`deps`, `buck sync|check`, `lean`, `loc`, `status`, and `docs`. `glu check`
runs format, lint, dependency policy, line counts, tests, and a full build;
`glu ci` is the same thing. Artifact actions under `glu artifact ...` are
invoked by the checked-in `BUCK` graph and are not a developer interface.

CI runs five gates plus deployment: `glu ci` under Nix, `nix flake check`, the
Lean build via `lean-action`, Lean documentation generation via doc-gen4, and a
dev-container smoke test. Only `main` deploys Pages.

## The published site

[`apps/docs`](../../apps/docs) is a SvelteKit static site and the presentation
layer for everything generated: the crate and dependency graphs from generated
JSON, line counts, Rustdoc under `/api`, Lean documentation under `/lean`, and
this corpus under `/notes`. One Pages deployment carries all of it; see
[the notes pipeline](notes-pipeline.md) for how the Markdown half works.

## What this repository does not have yet

Stated explicitly, because the issue tracker discusses all of it in the present
tense:

- No Rust HOL kernel, terms, types, theorems, or JSON encoding of any of them.
  That is [#553](https://github.com/imbrem/nucleus/issues/553).
- No import, replay, or resolver machinery.
- No e-graph or arena representations.
- No `proton` execution instances.
- No stability guarantee for anything. The pre-user JSON format in particular is
  intended to change; format churn is a feature until external users exist.
- No generic abstraction layer over kernels. Work concrete-first: the research
  APIs in [#503](https://github.com/imbrem/nucleus/issues/503) stay out of the
  minimal executable path until a second implementation justifies them.
