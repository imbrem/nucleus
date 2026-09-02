# Lean exports

This crate is the Lean logic frontend for Nucleus and reads the versioned
NDJSON format emitted by `lean4export`. Lean-provided definitions and other
objects are intended to be a first-class way to interact with Nucleus. The
adapter is outside the Nucleus TCB: parsing alone creates no theorem fact. The
`import` API streams typed records through a caller-selected `Backend`, which
drives a HOL kernel and returns both HOL-to-Lean correspondences and
theorem-to-derivation correspondences. Declaration safety is retained as input
data rather than treated as frontend policy; success means the selected
backend's checked constructions succeeded.

`direct::DirectHol` is the first intentionally small backend. It lowers a
monomorphic, non-dependent fragment directly into HOL and checks basic
implication proofs through resident HOL sequent rules. Lean proof lambdas and
bound hypotheses drive identity, weakening, and implication introduction;
successful theorem declarations return real `ThmId` correspondence entries.
It also exposes a proof-producing `ConversionTactic` boundary: beta, eta,
delta, iota, and zeta reduction belong in an LCF tactic whose successful steps
are checked by the kernel, whether its search uses normalization, an e-graph,
or another method.

The supported schema is pinned and inventoried in
[`docs/lean4export-3.1.md`](docs/lean4export-3.1.md). The `stream` module is
format-neutral and is intended to be reused by HOL-NDJSON rather than making
HOL records depend on Lean syntax.
