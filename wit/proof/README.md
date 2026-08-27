# Nucleus proof components

This package defines the first portable component interface for driving the
Nucleus Ethane kernel. The interface is deliberately low-level: syntax rows,
imports, and syntactic-fact slots are represented by integers, while ownership
is reserved for the host objects that must cross the component boundary.

The `standard-proof` world imports `nucleus:proof/host` and exports one
conventional entry point:

```wit
prove: async func(target: list<u8>) -> result<kernel, string>;
```

A standard loader calls `prove` with a prover-local `o256` request and takes
ownership of the returned checked kernel. The request need not be the returned
kernel's address; the all-zero value conventionally asks for the prover's
default result. A component may instead import the host interface under a
different world and implement any higher-level protocol it needs.

## Host resources

- `arena` is mutable, unvalidated Ethane wire data. Its constructors append raw
  rows and only check that integer arguments fit the wire representation.
- `kernel` is a checked arena. Its constructors and rules delegate to the Rust
  Ethane kernel, which is the trusted boundary.
- `table` is an immutable arena paired with the checked address of the CBOR
  bytes from which it was decoded.
- `bytes` wraps an immutable Rust `Bytes` buffer. Crossing from a component
  list into the host copies once; host-side slices and clones share storage.
- `blob` is a checked CAS fact `(address, bytes)`. `bytes.blob()` computes the
  address, `blob.check(address, bytes)` checks a claimed address, and
  `blob.bytes()` forgets the checked proposition while sharing the payload.
- `index-cas` is a component-private insertion-ordered CAS. The free
  `cas-*` functions access the loader's default host CAS instead.
- `cas-get-bytes` asynchronously returns untrusted bytes. `cas-get-fact`
  asynchronously returns an opaque checked whole-blob fact; its default path
  hashes the bytes, while a checked cache may avoid rehashing.

An arena reference, import ID, CAS object ID, or syntactic-fact slot is only
meaningful for the object that issued it. Arena references and syntactic-fact
slots are one-based; CAS object IDs are zero-based. Removing, replacing, or
truncating a syntactic-fact slot invalidates any integer previously used to
refer to that evidence. Components must not reuse such stale IDs.

Kernel cache operations are named by their fact family:
`syn-fact-count`, `remove-syn-fact`, `truncate-syn-facts`, and
`union-syn-fact`. This keeps them distinct from CAS facts and leaves room for
additional kernel fact families.

## Building the demo

The Rust demo exercises checked byte/blob conversions, both CAS views, and a
small Ethane derivation:

```sh
pnpm --filter @nucleus/nucleus build:proof-demo
wasm-tools validate \
  --features cm-async \
  target/wasm32-unknown-unknown/debug/covalence_proof_demo.component.wasm
cargo run -p covalence-nucleus --example load-proof -- \
  target/wasm32-unknown-unknown/debug/covalence_proof_demo.component.wasm
```

`covalence-proof-naturals` is a larger ABI proof of concept. It concludes
infinity, constructs the impredicative reachability predicate over an explicit
carrier, and carves a guarded subtype. It is intentionally not described as the
standard init proof: eliminating the infinity existential and proving the
Peano package still live only in the native derived layer.

```sh
pnpm --filter @nucleus/nucleus build:proof-naturals
cargo run -p covalence-nucleus --example load-proof -- \
  target/wasm32-unknown-unknown/debug/covalence_proof_naturals.component.wasm
```

The proof component imports no ambient WASI world. Its default capabilities are
the Nucleus kernel, default CAS, and secure randomness; loaders may add filtered
HTTP, VFS, named CAS, or other capabilities according to the proof's permission
profile. Tests may replace randomness with a deterministic seeded provider.
