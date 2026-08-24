# Ethane compact builtin contract v1

`crates/logic/hol/builtins-v1.tsv` is the reviewed registry for compact syntax.
It is deliberately separate from the opcode-free init arena. Rust tests parse
every registry column and compare it with the executable enums; Lean defines
the same finite registry and evaluates the same row envelopes. Adding an entry
requires updating all three in one change, and their tests are the drift gate.

## Wire and compatibility

The version is part of the row tag (`tm.op1.v1` or `tm.op2.v1`), not an arena-
wide switch. `val` is the unsigned opcode and `ixs` contains exactly one or two
one-based references in left-to-right order. Decoders reject an unknown tag,
an unassigned code (all unlisted `u8` values are reserved), a code outside
`u8`, the wrong arity, extra fields, or a value of the wrong CBOR kind.

A `(version, family, code)` meaning is immutable. A compatible reader may read
only versions it implements; it must reject, rather than guess at, a future
version. New operations use unused codes when their existing family and wire
shape suffice, or a new versioned tag when the contract changes. Writers emit
only the version they declare.

## Meaning, equality, and limits

Compact nodes are macros. Their sole meaning is canonical, recursive expansion
to the opcode-free definitions in init. Lowering preserves operand order and
uses the init identity selected by the kernel; it never consults names or a
mutable rewrite set. `not p`, `p and q`, `p or q`, and `p imp q` lower to their
corresponding raw init definitions applied to their lowered operands.

Wire/structural equality compares the compact tag, opcode, and child references.
HOL syntactic equality compares canonical lowered terms. Consequently a compact
node and its raw expansion are syntactically equal after successful lowering,
but need not have identical wire rows.

Decoding one row is constant-space apart from its at-most-two references and
does no expansion. Implementations must reject an `ixs` array longer than two
before allocating proportional storage. Recursive lowering is fuel-bounded by
the caller and memoized per arena reference; exhaustion is a normal checked
failure and must not produce a kernel term. This keeps adversarial nesting from
turning a compact input into unbounded work inside the trusted kernel.
