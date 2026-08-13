# Browser SQLite shell

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

In the browser demo, `(sqlite [ADDRESS])` switches the prompt to `sqlite>` and
keeps that shell invocation alive. Enter `.quit` or `.exit` to return to the
`nucleus>` prompt. SQLite's stdout and stderr are displayed without rewriting.
`glu demo` also starts the untrusted CaDiCaL adapter and exposes it through the
page's same-origin `/sat` HTTP route; solver output is checked in the browser.
