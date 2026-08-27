# HOL init manifests

`init.json` remains the broad `array-v0` design sketch. It contains unresolved
surface notation and is not trusted or compiled.

`init-boolean.checked.json` is the first executable slice: an ordered list of
raw Ethane rows for `star`, `bool`, `bool->bool`, `true`, `false`, and `not`. The Rust
compiler rejects every tag outside its primitive allow-list, validates exact
backward dependencies, and typechecks every row through the existing kernel.
Its arena address is a golden test, so changing row order or content is an
explicit hash change.

The checked format intentionally has no theorem entry. Definitions add rows;
theorem statements and checked proofs need distinct future representations.
An unchecked external existence claim must remain explicit metadata rather
than becoming an Ethane axiom; existence may instead be established as an
internal HOL theorem. Before expanding this slice, its raw declaration
vocabulary should be folded into the shared Rust/Lean/Python constructor
manifest tracked by #745; the separate filename makes that migration visible
instead of presenting a competing permanent format.
