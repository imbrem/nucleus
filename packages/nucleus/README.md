# Browser SQLite shell

The package also includes `proof.html`, a browser host for standard Nucleus
proof components. It accepts a component URL or local `.wasm` file, runs the
proof, and reports the checked kernel's CBOR address and row statistics.

The complete `nucleus:proof/host` interface is implemented by a Rust WebAssembly
component and exported from `@nucleus/nucleus/proof` as `proofHost`. Jco
generates both the JavaScript API and the canonical-ABI bridge, so browser code
and portable prover components operate on the same checked resources and method
definitions. The separate entry point keeps the kernel component out of pages
which only use the REPL.

Build the sample component with
`pnpm --filter @nucleus/nucleus build:proof-demo`, start the package server with
`glu demo`, then open `/proof.html` and select
`target/wasm32-wasip1/debug/covalence_proof_demo.wasm`.

The browser runs the upstream SQLite shell as a separate WebAssembly component.
JavaScript supplies an immutable VFS with `open`, `size`, and ranged `readAt`
operations. The default adapter reads the REPL local CAS; another host can
provide Promise-backed storage through the same interface.

This first implementation has deliberate constraints:

- The runtime must support JSPI.
- Shell invocations are single-flight because the Preview 2 stream handlers are
  process-global.
- The VFS is immutable and opens main databases only.
- Every command instantiates a fresh component so SQLite gets fresh globals.
- The native CLI shell host is deferred; `(sqlite ...)` currently runs in the
  browser REPL.

The WIT interface remains synchronous for current toolchain compatibility. Jco
selectively lowers its VFS imports and shell export through JSPI, so JavaScript
implementations may suspend on Promises. This can become native async WIT once
the Rust component toolchain supports it reliably.
