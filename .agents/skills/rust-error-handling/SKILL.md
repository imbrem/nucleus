---
name: rust-error-handling
description: How Nucleus Rust crates define and propagate errors — snafu through the `covalence-lib-error` facade, message style, mandatory `# Errors` doc sections, and what the codebase actually does today versus what it is moving towards. Use when adding a fallible function, defining an error type, choosing how a failure crosses a crate boundary, or reviewing error handling.
---

# Errors in Nucleus Rust crates

`crates/lib/error/src/lib.rs` states the policy. Read it — the whole doc block
is thirteen lines. In short:

- **Production crates use `snafu`** for concrete domain errors and typed fault
  chains — errors that stay matchable by callers and preserve the context needed
  to handle or propagate a failure.
- **Orchestration and surface crates use `miette`** when failures need dynamic
  reports or user-understandable diagnostics. Rendering policy belongs in the
  surface crate.
- **Expected malformed input, warnings, and recoverable outcomes are not fatal
  failures by default.**

## Read this part before you cite the policy

The codebase does not yet match it, and a review that assumes it does will be
wrong. Counting error types on `main`:

| Mechanism | Types | Where |
|---|---:|---|
| Hand-rolled `impl Display` + `impl Error` | 17 | `repl`, `lib/sqlite`, `data/num`, `logic/lrat`, `data/cas`, `bin/cas-shell`, `logic/sat`, `lib/hash` |
| `#[derive(Snafu)]` | 7 | `nucleus`, `lib/hash`, `neutron`, `data/array` |
| `miette` | 0 | — |
| `anyhow`, `thiserror` | 0 | — |

So: **snafu is the direction, hand-rolled `Display` is the incumbent, and the
miette half of the policy has no users at all.** `crates/bin/nucleus` and
`crates/bin/cas-serve` return `Box<dyn Error>`; `crates/repl` hand-rolls.
`covalence-lib-error` has four dependents out of twenty-eight crates.

Write new error types with snafu. Do not convert existing hand-rolled types as a
drive-by — that is a migration, not a cleanup. Do not introduce `thiserror` or
`anyhow`.

None of the seventeen hand-rolled types implement `Error::source()`; every one is
`impl Error for X {}`, flattening the chain into the `Display` string by hand. Do
not copy that. Snafu gives you a real `source` for free.

## The snafu idiom

Depend on `covalence-lib-error`, never on `snafu` directly. No crate imports
`snafu` or `miette` any other way, and that part *is* settled.

Because the dependency is the facade, **`crate_root` is mandatory**: the derive
emits absolute `::snafu::…` paths that will not resolve otherwise.

Simple struct error — `crates/data/array/src/seq.rs`:

```rust
use covalence_lib_error::snafu;
use snafu::Snafu;

/// A noncanonical byte length.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Snafu)]
#[snafu(crate_root(snafu))]
#[snafu(display("expected a multiple of {WIDTH} bytes, found {len}"))]
pub struct WidthError {
    /// Actual byte length.
    pub len: usize,
}
```

Enum with context selectors — `crates/neutron/src/connection.rs`:

```rust
use covalence_lib_error::snafu::{ResultExt, Snafu};

/// Failure to open or initialize a Neutron connection.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ConnectionError {
    /// The raw `SQLite` connection could not be opened.
    #[snafu(display("could not open SQLite connection: {source}"))]
    Open {
        /// Underlying `SQLite` error.
        source: sqlite::Error,
    },
}
```

propagated as `sqlite::Connection::open(&path).context(OpenSnafu)?`.

Both `crate_root` spellings are in use. Prefer
`crate_root(covalence_lib_error::snafu)` for new code — it needs no companion
`use covalence_lib_error::snafu;` alias line.

Everything else snafu offers is currently unused: no `visibility`, `transparent`,
`context(false)`, `Whatever`, `ensure!`, `OptionExt`, or `Backtrace` fields
anywhere. Reach for them if a case genuinely needs one, but you are setting a
precedent, so say why.

The dominant propagation idiom repo-wide is still `map_err` with a manual
variant — about seventy sites — rather than `.context(XxxSnafu)`, of which there
are nineteen, all in `crates/neutron`. Prefer `.context()` in new snafu code.

## `# Errors` doc sections are mandatory

`clippy::pedantic` is denied workspace-wide and CI runs `-D warnings`, so
`missing_errors_doc` and `missing_panics_doc` are hard errors. Every public
fallible function carries a `# Errors` section; there are over a hundred in the
tree. The same lint group turns on `doc_markdown`, which is why doc prose
backticks identifiers — `` `SQLite` ``, `` `PyO3` ``.

## Message style

Consistent across every mechanism in the tree, so follow it even in a
hand-rolled `Display`:

- **lowercase first word**, proper nouns excepted;
- **no terminal punctuation**;
- **no backticks inside the message.** Interpolate bare (`{key}`, `{index}`) or
  Debug-quote (`{schema_name:?}`). Backticks belong in the doc comment above the
  variant, not in the string;
- wrapped errors end with `: {source}`.

Two shapes cover almost everything:

```text
could not open SQLite connection: {source}
could not serialize SQLite database: {source}

expected {expected} hexadecimal digits, found {actual}
database schema {schema_name:?} is already attached
integer encoding is not canonical
```

## Not every unhappy path is an error

The policy's last clause has teeth. `crates/lib/sqlite/src/statement.rs` models
`SQLITE_ROW` and `SQLITE_DONE` as `Ok(Step::Row)` and `Ok(Step::Done)`; only
other codes become `Err`. An expected outcome belongs in the success type.

There is deliberately **no shared diagnostic or outcome type** yet. Do not
invent one; `crates/lib/error` says it will be added when concrete consumers
establish what they need.
