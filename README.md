# Nucleus

Nucleus is the kernel state machine for the
[Covalence](https://github.com/imbrem/covalence) theorem prover — an
experimental LCF-style prover and VCS using WebAssembly components.

The kernel has two cooperating parts:

- **Proton** — ephemeral in-memory terms, theorem values, inference state,
  and fast structural operations.
- **Neutron** — an in-memory SQLite database holding the relational and
  persistable portion of kernel state (evidence, provenance, persistence
  images).

Together they form the **nucleus**: one running kernel state machine whose
checked transitions are the sole source of theorem authority. Neither a
database row nor a query result can mint a fact; only a checked nucleus
transition constructs theorem authority.

## Architecture

```
┌─────────────────────────────────────────────────┐
│                   nucleus                       │
│  ┌──────────────┐       ┌────────────────────┐  │
│  │   proton     │◄─────►│     neutron        │  │
│  │  (in-memory  │       │  (SQLite relational │  │
│  │   terms,     │       │   state, evidence,  │  │
│  │   theorems)  │       │   persistence)      │  │
│  └──────────────┘       └────────────────────┘  │
└─────────────────────────────────────────────────┘
         ▲                         ▲
         │                         │
    lib/hash             lib/sqlite, lib/error
    lib/rand             lib/crypto
    data/*
```

**Layering rules.** Dependencies point downward and never form cycles:

| Layer | Crate | Role |
|-------|-------|------|
| Binary | `crates/bin/nucleus` | CLI entry point |
| Policy | `crates/nucleus` | Portable trusted core; no escape hatches to raw SQLite |
| Relational | `crates/neutron` | Uninterpreted relational machinery over SQLite; deliberately *permeable* |
| Execution | `crates/proton` | Execution instances (placeholder) |
| Data | `crates/data/*` | Core data structures (S-expressions, numbers, containers) |
| Lib | `crates/lib/*` | Opinionated dependency facades (hash, rand, error, sqlite, crypto, wasm) |

Neutron exposes raw SQLite access so callers *can* bypass its invariants.
Nucleus wraps Neutron and preserves a **complete-registry invariant** by
never exposing the inner connection.

## Crate map

| Crate | Path | Description |
|-------|------|-------------|
| `covalence-lib-error` | `crates/lib/error` | Re-exports `snafu` + `miette`; error-handling conventions |
| `covalence-lib-hash` | `crates/lib/hash` | `Obj<N>` namespaced identifiers, BLAKE3/SHA-256/Git hashing, Merkle tree ops |
| `covalence-lib-rand` | `crates/lib/rand` | Re-exports `rand`; JavaScript-hosted Wasm randomness |
| `covalence-lib-sqlite` | `crates/lib/sqlite` | Re-exports `rusqlite`; safe VFS trait API with FFI trampolines |
| `covalence-data-basic` | `crates/data/basic` | Basic data representations (placeholder) |
| `covalence-neutron` | `crates/neutron` | Connection metadata, content-addressed store, database images |
| `covalence-proton` | `crates/proton` | Execution instances (placeholder) |
| `covalence-nucleus` | `crates/nucleus` | Policy-enforcing trusted core; `cdylib` + `rlib` for Wasm |
| `covalence-bin-nucleus` | `crates/bin/nucleus` | CLI binary |

Separate workspace: `tools/glu/` — repository task runner (fmt, lint, test,
build, Buck sync, docs, CI).

## Building

The project uses two build systems:

- **Cargo** (authoritative for dependency topology)
- **Buck2** (parallel builds, artifact pipelines, Wasm packaging)

`glu` keeps them in sync; generated BUCK files are committed.

### Prerequisites

Enter the Nix dev shell (provides Rust 1.97, Buck2, pnpm, wasmtime, etc.):

```sh
nix develop          # or use direnv with the .envrc
```

### Common commands

```sh
glu doctor           # verify environment
glu fmt              # format (rustfmt + prettier)
glu lint             # clippy + prettier --check
glu test             # full test suite (Buck, Cargo, Wasm, pnpm)
glu test --cargo     # Cargo tests only (faster)
glu build            # build all targets
glu check            # cargo check + buck2 build
glu ci               # full CI pipeline
glu buck sync        # regenerate BUCK files from Cargo metadata
glu buck check       # verify BUCK files match Cargo
```

### Targets

The nucleus crate compiles for four targets:

| Target | Use |
|--------|-----|
| Native | Default; tests and CLI |
| `wasm32-unknown-unknown` | Browser via `wasm-bindgen` |
| `wasm32-wasip1` | WASI component (WIT interface) |
| `wasm32-wasip2` | WASI CLI component |

## Design principles

1. **Rows do not mint facts.** SQL operations manipulate state and evidence;
   only checked nucleus transitions construct theorem authority.

2. **Only a small SQL fragment is trusted.** Fixed typed query shapes are
   nucleus transitions; arbitrary SQL cannot promote candidate state.

3. **Positive observations are finite and explicit.** No universal claims
   about external worlds.

4. **Trust is inspectable.** Theorem/snapshot exposes assumptions,
   accelerators, signer policy, source state.

5. **Higher objects lower.** Terms, theorems, modules are blobs +
   interpretation, not extra hash primitives.

6. **Transactions are atomic nucleus transitions.** No externally visible
   half-transitions.

7. **Concrete first, traits later.** Implement concrete capabilities before
   extracting generic traits.

8. **Narrow permanent bootstrap.** The two-column bootstrap catalog
   `(table_name, interpretation)` is intentionally minimal and permanent.
   Extensions live in normalized extension relations above it.

## Relationship to Covalence

Nucleus is a focused extraction of the kernel layer from the
[Covalence](https://github.com/imbrem/covalence) monorepo. Covalence
contains the full theorem prover, standard library, web app, VS Code
extension, and multiple proof-format frontends. Nucleus contains only the
trusted kernel state machine and its immediate dependencies.

Design documents for the nucleus architecture live in the Covalence repo
under `notes/vibes/kernel/` — particularly `substrate-rewrite.md` (the
detailed rewrite plan) and `trusted-database-algebra.md` (the trusted SQL
fragment specification).

## License

[CC0-1.0](LICENSE) — all files, all contributions.
