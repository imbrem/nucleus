# Ethane kernel correspondence contract

`operations.json` inventories the intended one-to-one correspondence between
pure Lean arena operations and their Rust kernel implementations.
`traces.json` supplies normalized, language-neutral examples for the first
empty/Star/Boolean slice. The schemas version the formats; `validate.jq` checks
cross-file invariants that JSON Schema cannot express.

The registry records every old arena, the successful new arena, the tracked
assumption policy, use of the shared implicit CAS, named errors, the pure Lean
definition and soundness theorem, the specialized Rust method, and the
fixtures covering the operation. A Lean transition maps an old `Arena` to a
new `Arena`; its preservation theorem proves soundness of that result. Rust
implements the same transition in place through an inherent `&mut self`
method on `Kernel<dense::Arena>` (`dense::Kernel` for short). Mutation is only
an implementation optimization: rejection must leave the Rust kernel
unchanged.

The private `Row` is the single semantic vocabulary shared by wire decoding
and every arena representation. `RowSerde` is only its mechanical wire view.
`ArenaRepr` is the sealed representation capability, `Arena` is the public
representation-erased enum, and `Kernel<A>` is the owning wrapper asserting
that `A` is sound. There is no common mutation trait: dense and future segment
arenas receive separate inherent operation implementations.

All soundness annotations refer to the same implicit ideal CAS. Rust need not
carry that CAS at runtime. Facts are the optional `eq` and `sort` references
carried by rows; there is no standalone fact value or arena-level fact list.

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
probabilistic refinement from a real BLAKE3 store to that ideal CAS, including
any collision-bound accounting, is deliberately deferred long-term. It is
neither an MVP kernel operation nor an MVP conformance obligation.
