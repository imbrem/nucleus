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

## What the codebase actually does

Every error type in hand-written code now uses snafu — twenty-four of them
across twelve crates, plus one in the facade's own test — and both binaries
render with miette. The one remaining hand-rolled `impl Error` is in generated
wit-bindgen code. `covalence-lib-error` has fourteen dependents.

So the policy is descriptive, not aspirational, and you should follow it
literally. Do not introduce `thiserror` or `anyhow`.

The exceptions are real and worth knowing, because they are not oversights:

- **`crates/browser`** raises `wasm_bindgen::JsError` and **`crates/ffi/python`**
  raises `PyErr`. Those are the host's error vocabulary at a boundary, which is
  the convention's "rendering policy belongs in surface-specific crates".
- **`crates/data/container`** defines no errors; it is infallible by
  construction.
- **`nucleus::SignError::Backend`** carries
  `source: Box<dyn Error + Send + Sync>` because it crosses an open `dyn Signer`
  trait, where the concrete error is not knowable.

## The snafu idiom

Depend on `covalence-lib-error`, never on `snafu` or `miette` directly. No
crate in the workspace does otherwise.

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

Both `crate_root` spellings are in use, roughly evenly. Prefer
`crate_root(covalence_lib_error::snafu)` for new code — it needs no companion
`use covalence_lib_error::snafu;` alias line.

Wrapping another crate's error unchanged is `#[snafu(transparent)]`; wrapping it
while adding a message of your own is `#[snafu(context(false))]`. Between them
they replace the hand-written `From` impls this codebase used to carry — see
`crates/repl/src/lib.rs`.

`map_err` with a manual variant is still the majority idiom by count, mostly
predating the conversion. Prefer `.context(XxxSnafu)` in new code: it is what
gives you a real `source` rather than a flattened message.

## Rendering: miette, in binaries only

A binary that reports failures to a person returns `miette::Result` from `main`
— `crates/bin/nucleus` and `crates/bin/cas-serve` both do. Everything below them
returns typed snafu errors; rendering happens once, at the top.

```rust
use covalence_lib_error::miette::{self, Context, IntoDiagnostic, miette};

fn main() -> miette::Result<()> {
    let bytes = std::fs::read(path)
        .into_diagnostic()
        .with_context(|| format!("could not read `{path}`"))?;
```

`.into_diagnostic()` lifts any `Error` into a report; `.context()` says what was
being attempted. That context is the point — it turns
`No such file or directory (os error 2)` into a message naming the file, with
the cause chained beneath it. Add one at every `?` in a binary.

Miette is built with its `fancy` renderer unconditionally. Without it the output
is worse than printing `Display`, and it costs nothing but compile time: the
renderer is dead code wherever no report is constructed, so the Wasm bundle is
byte-identical either way.

**Do not return `miette::Result` from a library.** A caller that wants to match
on a failure cannot, and a report is not matchable. `crates/repl` is the test
case — it is orchestration, but its callers do
`matches!(…, Err(ReplError::UnknownConnection { .. }))`, so it stays snafu and
its two hosts render.

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
