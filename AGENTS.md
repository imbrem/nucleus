# Working in Nucleus

Read `README.md`, then the documentation nearest the code you will change.
Treat current code and tests as the implementation record; `docs/research/`
contains useful investigations, not one authoritative roadmap.

## Invariants

- HOL is the ambient semantic envelope. An embedded judgment may be proved
  without constructing or deciding an object-theory derivation.
- Only the kernel creates trusted theorem facts. Keep parsing, elaboration,
  automation, importing, execution, storage policy, and naming outside the TCB.
- A content address identifies bytes. Semantic claims about those bytes require
  checked evidence; signatures record provenance or policy.
- Rust has one running design. Lean may contain multiple named designs so they
  can be compared and related. All checked-in Lean modules must stay green.
- Keep the trusted surface small. State any new assumption, capability, wire
  commitment, or TCB expansion explicitly.

## Work

Use the task-routed skills in `.agents/skills/`. In particular:

- `change-logic` for checked logic, wire, WIT, or cross-language changes
- `formalize-in-lean` for Lean models, soundness, and design relations
- `lib-facade-crates` after any `Cargo.toml` change or when adding a crate
- `rust-error-handling` for fallible Rust APIs
- `work-on-docs-site` for `apps/docs`

Keep changes narrow, preserve unrelated work, and test the affected authority
boundary as well as its ordinary API. Build every Lean module affected by a
change. Do not leave a checked-in design outside normal validation.

Prefer short factual documentation with pointers to executable evidence.
Record temporary plans in issues; avoid copying volatile status into durable
guidance.
