# Nucleus proof components

This package defines the first portable component interface for driving the
Nucleus Ethane kernel. The interface is deliberately low-level: syntax rows,
imports, and syntactic-fact slots are represented by integers, while ownership
is reserved for the host objects that must cross the component boundary.

The `proof` world imports `nucleus:proof/host` and exports one minimal strategy
interface:

```wit
apply-tactic: async func(tactic-id: u64, arguments: list<u8>, kernel: option<kernel>)
    -> result<kernel, string>;
```

`strategy.apply-tactic` is the complete small stable kernel-transformer
protocol. An omitted input asks the strategy to choose a checked starting
kernel. Tactic arguments are a small copied `list<u8>`; larger inputs can travel
through a CAS or a future separately reviewed resource-bearing extension.

By convention tactic zero with empty arguments and no input kernel requests a
strategy's default starting/proved kernel. Tactic zero with 32 argument bytes
requests an addressed kernel. Tactic one conventionally interprets its
arguments as a UTF-8 strategy-local name. Retrieving bytes from a CAS is
insufficient: the strategy must reconstruct or independently validate its
result. A future trusted or signed kernel-hash cache can accelerate this same
operation without granting today's untrusted loader any theorem-producing
authority.

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

The same world can be implemented without Rust. The C micro-demo generates
bindings with `wit-bindgen`, compiles them with the WASI C compiler, validates
the native-async component, and runs under the same loader:

```console
pnpm --filter @nucleus/nucleus build:proof-c-demo
cargo run -p covalence-nucleus --example load-proof -- \
  target/wasm32-wasip1/covalence_proof_c_demo.component.wasm
```

The proof component imports no ambient WASI world. Its default capabilities are
the Nucleus kernel, default CAS, and secure randomness; loaders may add filtered
HTTP, VFS, named CAS, or other capabilities according to the proof's permission
profile. Tests may replace randomness with a deterministic seeded provider.
