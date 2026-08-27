# Nucleus

Nucleus is a content-addressed theorem-prover substrate with a small checked
HOL kernel. Other logics and computation systems can be represented and
reasoned about inside HOL. Proving a foreign judgment need not construct or
decide a derivation in the foreign system.

Parsers, elaborators, tactics, solvers, importers, and executors do not carry
logical authority. They contribute through checked kernel operations. Hashes
identify bytes; checked relations establish what those bytes mean. Signatures
and execution records provide provenance without changing theorem meaning.

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
changing. See `AGENTS.md` for repository-wide working rules.
