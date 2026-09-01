---
name: lib-facade-crates
description: How Nucleus wraps third-party Rust dependencies in `crates/lib/*` facade crates, and the manifest, Buck, and workspace steps that adding or changing one requires. Use when adding a third-party dependency, creating any new crate, deciding whether a dependency needs a facade, or after changing a `Cargo.toml`.
---

# `crates/lib/*` facade crates

A crate under `crates/lib/` owns one third-party dependency on behalf of the
workspace and re-exports it. **The module doc saying _when to reach for it_ is
the payload; the re-export is just the mechanism.** A facade whose docs say
nothing has not earned its place.

Read `crates/lib/error/src/lib.rs` before writing a new one — it is the
archetype, and its docs explain _when_ to reach for each of the two libraries it
re-exports rather than just naming them.

## When a dependency needs a facade

Not every dependency does, and the repository does not pretend otherwise.
Reach for a facade when:

- the dependency's type vocabulary would otherwise leak into a public API
  across many crates;
- there is a policy about _when_ to use it that is worth stating once
  (`crates/lib/error` — snafu for domain errors, miette for surface
  diagnostics);
- we may want to swap the implementation later.

Depending on a third-party crate directly is fine when none of that applies.
`crates/data/cas-http` depends on `axum` and `tokio`, `crates/data/array` on
`zerocopy`, `crates/nucleus` on `bytes` — all deliberate.

**Nothing enforces this.** `glu deps` checks manifest fields, not dependency
routing. Treat it as a convention to apply with judgement, not an invariant.
Three of the ten current facades — `serde`, `json`, `cbor` — have no consumers
at all, so the pattern gets applied ahead of demand as well as behind it. A
facade with no consumers is not a bug, but it is not evidence for the pattern
either.

## The three shapes a facade takes

| Shape                        | Examples                              | What it contains                                                       |
| ---------------------------- | ------------------------------------- | ---------------------------------------------------------------------- |
| Bare re-export               | `serde`, `json`, `rand`, `cbor`       | `pub use <crate>;` and often `pub use <crate>::*;`                     |
| Re-export plus stated policy | `error`, `bigint`, `crypto`, `python` | the same, plus prose on when and how to use it                         |
| Real code                    | `hash`, `sqlite`                      | its own API; `sqlite` re-exports only `ffi`, `hash` re-exports nothing |

Two useful variants: `crates/lib/bigint` re-exports only `BigInt`, `BigUint`,
`Sign` and says product crates should expose semantic value types instead;
`crates/lib/sqlite` deliberately does **not** re-export `rusqlite` and says so.

## Always re-export the crate itself, not only its items

Derive macros emit absolute paths, so a caller that only sees `Snafu` or
`pyo3::prelude::*` will not compile. Facades therefore re-export the crate root
(`pub use snafu;`), and callers point derives back at it:

```rust
#[snafu(crate_root(covalence_lib_error::snafu))]
#[pyo3(crate = "covalence_lib_python::pyo3")]
```

If you add a facade over a crate with derive macros, check that a downstream
derive compiles without a direct dependency.

## Manifest boilerplate

Every one of the twenty-eight workspace members has this shape, with no
exceptions.
`glu deps` enforces six of these fields, so getting them wrong fails CI.

```toml
[package]
name = "covalence-<group>-<crate>"   # groups include lib, lang, exec, logic, data, ffi, bin
version.workspace = true
edition.workspace = true
rust-version.workspace = true
license.workspace = true
description = "..."                  # required, non-empty
publish = false

# [features] / [dependencies] ...

[lints]
workspace = true                     # always the last two lines
```

Path dependencies are `{ path = "../..." }` with no version. Dependencies are
alphabetised. No member sets `authors`, `readme`, `keywords`, `repository`, or
`homepage`.

`tools/glu` looks different because it is its own workspace root and cannot
inherit. It is outside this convention and outside `glu deps`.

## Version pinning

There is no `[workspace.dependencies]` table; every crate pins inline. The
granularity is genuinely inconsistent — `serde = "1.0"` in one crate and
`serde = "1"` in another — so match the neighbours and do not agonise.

One rule _is_ real: **an exact `=` pin means the crate is coupled to something
outside Cargo's control.** All seven occurrences are of that kind
(`libsqlite3-sys`, `sqlite-wasm-rs`, `wasm-bindgen`, `wit-bindgen-rt`). Use `=`
only for that reason, and say why in the crate's docs — see
`crates/lib/sqlite/src/lib.rs`, where `links = "sqlite3"` permits exactly one
copy of the C library per build graph.

## After adding a crate or a dependency

1. Add the crate to `members` in the root `Cargo.toml`, in its group. The list
   is grouped `lib → lang → exec → logic → data → ffi → top-level → bin`,
   not alphabetical.
2. Run **`glu buck sync`** and commit the result. Every `BUCK` file is marked
   `@generated by 'glu buck sync'; do not edit.` — hand-editing one will be
   overwritten and will fail `glu buck check`, which `glu ci` reaches through
   `glu build`. **This includes adding a test file**: a new `tests/*.rs` needs a
   generated `rust_test` target.
3. Run `glu deps` to confirm the manifest.
4. Run `glu check` (or `glu ci`) before pushing.

`REUSE.toml` annotates `**` in one blanket entry, so there is nothing to add
there and source files carry no SPDX headers.

To opt a crate out of Buck entirely, set `[package.metadata.glu] buck = false`
and say why in the manifest — the two PyO3 crates do this.
