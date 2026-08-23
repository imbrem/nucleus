# Browser SQLite shell

The package also includes `proof.html`, a small browser host for standard
Nucleus proof components. It accepts a component URL or local `.wasm` file,
runs the proof through checked kernel operations, and reports the returned
kernel's CBOR address and row statistics. Diagnostic arena JSON is generated
only when opened (or immediately for small kernels).

The browser adapter intentionally implements only the proof operations used by
the demo component. Unimplemented imports fail instead of manufacturing an
unchecked result; the host surface can grow alongside the checked Rust API.

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
