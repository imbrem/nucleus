# Nucleus — Claude instructions

Read `README.md` for project overview, architecture, and crate map.

## Build and test

```sh
glu test --cargo     # fast: Cargo tests only
glu test             # full: Buck + Cargo + Wasm + pnpm
glu lint             # clippy (deny all + pedantic) + prettier
glu fmt              # rustfmt + prettier
glu check            # cargo check + buck2 build
glu buck sync        # regenerate BUCK files after dependency changes
glu buck check       # verify BUCK files match Cargo metadata
```

After adding or removing crates or changing dependencies, always run
`glu buck sync` and commit the generated BUCK and JSON files.

## Code conventions

- **Edition 2024**, Rust 1.97, resolver 3.
- `#![deny(unsafe_code)]` on all crates except `crates/lib/sqlite/src/vfs/ffi.rs`.
- `clippy::all` and `clippy::pedantic` are denied workspace-wide.
- All crates: version `0.0.0`, license `CC0-1.0`, `publish = false`.
- External dependencies are wrapped in `crates/lib/*` facade crates; product
  code never depends directly on third-party crates.
- Dual build system: Cargo is authoritative; BUCK files are generated.
- Every new crate needs both `Cargo.toml` and a BUCK file via `glu buck sync`.

## Architecture invariants

- **Neutron is permeable**: it exposes raw SQLite access (`sqlite()`,
  `sqlite_mut()`, `into_sqlite()`).
- **Nucleus is opaque**: it wraps Neutron and never exposes the inner
  connection. All trusted state changes go through Nucleus.
- **Trust boundary**: rows do not mint facts. Only checked nucleus
  transitions construct theorem authority. No database row, URL, or
  imported data grants itself trust or effect capabilities.
- **Bootstrap catalog**: two-column `(table_name TEXT PK, interpretation
  TEXT NOT NULL)`. Never modify this schema. Extensions use normalized
  extension relations above it.
- **Connection metadata** lives in SQLite `TEMP` tables (prefixed
  `cov_conn_`). It is not serialized with database images.
- **CAS is connection-local**: the default content-addressed store is a
  `TEMP` table excluded from serialized images.

## Namespace and identity system

The core type is `Obj<N: Namespace>` — a `#[repr(transparent)]` fixed-width
identifier in a compile-time namespace. Key namespaces:

- `Cov` — interoperable 256-bit Covalence objects (`O256 = Obj<Cov>`)
- `Blake3` — unkeyed BLAKE3 digests
- `Git` — traditional 160-bit Git SHA-1 names
- `Opaque<N>` — type-erased namespace

Path derivation uses BLAKE3 keyed hashing: `COV_ROOT.tag("child")` derives
child identifiers. The `o256_path!` macro provides compile-time path syntax.

## Design philosophy

Follow the **concrete-first** approach: implement specific capabilities
(hardcoded BLAKE3 CAS, specific KV shapes) before extracting generic
traits. Extract traits only after at least two concrete consumers establish
the required interface shape.

Separate **relational denotation** (which tuples a relation contains) from
**computational realization** (how to obtain them). Resolvers are
untrusted computational capabilities; their output is always validated
before entering trusted state.

## Key source locations

- `crates/lib/hash/src/lib.rs` — `Obj<N>`, `Namespace` trait hierarchy, macros
- `crates/lib/hash/src/blake3/` — BLAKE3/Cov namespaces, tree operations
- `crates/lib/sqlite/src/vfs/` — VFS trait API, FFI, registry
- `crates/neutron/src/connection.rs` — Neutron connection + metadata init
- `crates/neutron/src/cas.rs` — Content-addressed store
- `crates/neutron/src/image.rs` — Database image serialize/deserialize
- `crates/nucleus/src/connection.rs` — Nucleus policy wrapper
- `tools/glu/` — Build tool (separate workspace)
