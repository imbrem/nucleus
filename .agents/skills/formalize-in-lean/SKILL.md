---
name: formalize-in-lean
description: Develop, compare, or review Nucleus formal designs in Lean. Use for new Lean modules, semantics, soundness or correspondence theorems, executable specifications, alternative representations, or Lean build and audit coverage.
---

# Formalize in Lean

1. Read the target module and its imports. Identify whether it models the Rust
   implementation, explores another design, or relates designs.
2. Keep distinct designs in distinct namespaces. Multiple Lean designs are
   intentional; Rust remains the single running implementation.
3. Share definitions when the abstraction expresses a useful invariant or
   correspondence. Do not erase meaningful differences to reduce duplication.
4. Make assumptions visible in theorem types. Prefer bridges from exact decoded
   artifacts to abstract semantics over trusting parsers, names, or compilers.
5. Avoid `sorry`. Inspect exported axioms and separate expected classical/HOL
   assumptions from accidental ones.
6. Add the module to normal build coverage. Build direct targets while
   iterating, then run the audit that builds every checked-in Lean module.
