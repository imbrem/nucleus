# Lean exports

This crate is the Lean logic frontend for Nucleus and reads the versioned
NDJSON format emitted by `lean4export`. Lean-provided definitions and other
objects are intended to be a first-class way to interact with Nucleus. The
adapter is outside the Nucleus TCB: parsing alone creates no theorem fact. A
translation/checking stage separately turns parsed records into Nucleus
objects and submits semantic claims to a kernel.

The supported schema is pinned and inventoried in
[`docs/lean4export-3.1.md`](docs/lean4export-3.1.md). The `stream` module is
format-neutral and is intended to be reused by HOL-NDJSON rather than making
HOL records depend on Lean syntax.
