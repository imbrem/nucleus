# Ethane kernel correspondence contract

`operations.json` inventories the intended one-to-one correspondence between
the persistent Lean kernel operations and their Rust implementations.
`traces.json` supplies normalized, language-neutral examples for the first
empty/Boolean slice. The schemas version the formats; `validate.jq` checks
cross-file invariants that JSON Schema cannot express.

The registry records every old arena, the successful new arena, the tracked
assumption policy, use of the shared implicit CAS, named errors, the Lean
definition and soundness theorem, the persistent Rust symbol, any optimized
mutable Rust wrapper, and the fixtures covering the operation. A mutable
wrapper is not a second logical operation: it must be observationally
equivalent to its persistent symbol and leave the old value unchanged on
error.

All soundness annotations refer to the same implicit ideal CAS. Rust need not
carry that CAS at runtime. Kernel identity is deliberately absent from the
fixtures: arenas track assumptions, so terms and facts may cross kernels.

Run the dependency-free structural validator from the repository root:

```sh
jq -n \
  --slurpfile registry theories/ethane/conformance/operations.json \
  --slurpfile traces theories/ethane/conformance/traces.json \
  -f theories/ethane/conformance/validate.jq
```

These files are contract vectors, not evidence that arbitrary compiled Rust
execution equals Lean evaluation. Once both runners exist, CI should evaluate
the same vectors in each implementation and compare their normalized results.
Even that is conformance testing; the Lean preservation theorems establish
logical soundness relative to the assumed coherent implicit CAS. A
probabilistic refinement from a real BLAKE3 store to that ideal CAS is
deliberately deferred long-term. It is neither an MVP kernel operation nor an
MVP conformance obligation.
