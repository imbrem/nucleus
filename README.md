# Nucleus

Nucleus is a content-addressed theorem prover built around a small HOL kernel.
Other logics and computation systems can be represented and reasoned about
inside HOL. Proving a foreign judgment need not construct or decide a
derivation in the foreign system.

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
- `crates/proof/`, `crates/repl/`, `crates/browser/`: proof guests and user surfaces
- `apps/docs/`: generated repository documentation
- `docs/research/`: scoped research notes, not a single normative roadmap
- `.agents/skills/`: task-specific contributor guidance

Start with the local README or module documentation nearest the code you are
changing. See `AGENTS.md` for repository-wide working rules and
`docs/glossary.md` for project terminology.
