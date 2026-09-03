# Nucleus

Nucleus is a content-addressed theorem prover built around a small HOL kernel.
Other logics and computation systems can be represented and reasoned about
inside HOL. Proving a claim made in another logic need not construct or decide
a derivation in that logic.

WebAssembly is Nucleus's first-class executable grounding. Exact Wasm bytes,
the Wasm 3.0 semantics, and derived program propositions give tactics and
programmers a shared workface: prove that a module never reaches a failure
event, is deterministic or total under explicit assumptions, or refines
another module. The same interface can ground proof checkers, abstract
machines, and compiler transformations. See [`docs/wasm.md`](docs/wasm.md).

The kernel API follows the LCF pattern: callers can use theorem handles, but
only the kernel can create valid ones. Parsers, tactics, solvers, and importers
propose work for the kernel to check. Proof-producing tools are intended to run
as untrusted Wasm components. Hashes identify bytes; kernel-checked facts state
what those bytes mean.

The Rust workspace contains the running implementation. Lean contains its
formal models and deliberately explores multiple related designs; every
checked-in Lean module should build continuously.

## Repository map

- `crates/logic/`: checked logic and proof-format crates
- `lean/Nucleus/`: specifications, metatheory, and design comparisons
- `wit/`: component authority boundaries
- `lexicons/`: portable leaf-object schemas
- `crates/proof/`, `crates/repl/`, `crates/browser/`: proof guests and user surfaces
- `apps/docs/`: generated repository documentation
- `docs/wasm.md`: the Wasm-first executable-grounding direction
- `docs/research/`: scoped research notes, not a single normative roadmap
- `.agents/skills/`: task-specific contributor guidance

Start with the local README or module documentation nearest the code you are
changing. See `AGENTS.md` for repository-wide working rules and
`docs/glossary.md` for project terminology.
