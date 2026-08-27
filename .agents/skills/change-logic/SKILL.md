---
name: change-logic
description: Evolve Nucleus checked logic across Rust, Lean, wire encodings, WIT, bindings, and fixtures. Use when changing a logical constructor or rule, an arena row or tag, ways to create theorem facts, imports, canonical encoding, or a public kernel capability.
---

# Change logic

1. Locate the kernel or API boundary that creates trusted facts and read its
   nearest module documentation. Distinguish raw syntax, checked facts,
   userspace derivation, and provenance.
2. State any new assumption, capability, TCB code, or compatibility break.
3. Search Rust, Lean, WIT, bindings, fixtures, generated artifacts, and
   exhaustive matches for the affected tag or operation.
4. Keep frontends untrusted. Do not turn convenience, names, parsing, or
   acceleration into theorem authority.
5. Test malformed input and transactional failure as well as success. If bytes
   change, update canonical fixtures deliberately and test decoding and meaning.
6. Build the affected Rust crates and every Lean module mentioning the concept.
   Run the repository's strict CI entry point before handoff.

Use `formalize-in-lean` for substantial metatheory, `lib-facade-crates` after a
manifest change, and `rust-error-handling` for a new fallible Rust API.
