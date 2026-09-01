# Compiled tactic demo

`program.tactic` is a deliberately bounded source language containing one
straight-line instruction:

```lisp
(rewrite-proposition forward)
```

`build.rs` parses it into `compiler::Instruction` and lowers that instruction
to a Rust function in `OUT_DIR`. Rust compiles that generated function into the
proof component's core Wasm. `wasm-tools component new` then wraps the module
using its embedded WIT metadata.

The selected instruction and rewrite direction are compiled. The proof name
handling, construction of a small checked example, WIT-generated canonical ABI
bindings, and result sanity check in `src/lib.rs` are fixed runtime glue. The
compiled instruction calls the imported userspace `tactics` interface; only
the host kernel operations behind that interface create checked theorems.

This is intentionally not an interpreter: the component contains no tactic
source parser and receives no tactic source at runtime. Extending the initial
IR with sequences and operands can happen after the component boundary is
proven useful.
