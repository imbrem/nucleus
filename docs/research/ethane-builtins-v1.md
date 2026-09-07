# Ethane compact builtin contract v1

This historical design is retained in `Hol/Ethane/Builtin.lean` and its sibling
`builtins-v1.tsv` fixture. It is not the running Rust encoding. The current
implementation uses signed builtin references and ordinary application rows;
see [`crates/logic/hol/README.md`](../../crates/logic/hol/README.md).

The remainder describes the older model's contract.

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
