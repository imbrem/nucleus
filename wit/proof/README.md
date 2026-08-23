# Nucleus proof components

This package defines the first portable component interface for driving the
Nucleus Ethane kernel. The interface is deliberately low-level: syntax rows,
imports, and syntactic-fact slots are represented by integers, while ownership
is reserved for the host objects that must cross the component boundary.

The `standard-proof` world imports `nucleus:proof/host` and exports one
conventional entry point:

```wit
prove: func() -> result<kernel, string>;
```

A standard loader calls `prove` and takes ownership of the returned checked
kernel. A component may instead import the host interface under a different
world and implement any higher-level protocol it needs.

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
cd crates/proof/demo
cargo component build
cd ../../..
wasm-tools validate \
  target/wasm32-wasip1/debug/covalence_proof_demo.wasm
cargo run -p covalence-nucleus --example load-proof -- \
  target/wasm32-wasip1/debug/covalence_proof_demo.wasm
```

The loader supplies a minimal WASI context with no inherited filesystem,
network, environment, or command-line capabilities. Nucleus resources are the
component's proof capabilities.
