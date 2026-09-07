# Checked literals

`Kernel::literal`, `Kernel::literal_ty`, and `Kernel::builtin_const` construct
checked terms. Builtin constants have ordinary curried function types and take
arguments through ordinary `Kernel::app` rows. `Kernel::builtin` is a
full-application convenience, not another syntax form.
`Kernel::reduce_builtin` returns a result literal and a premise-free
theorem equating the original closed expression with that result. Constructing
a symbolic expression is separate from evaluating it: an undefined operation
can be represented but cannot produce a successful reduction theorem.

`Arena` constructors and deserialization produce raw syntax, not trusted facts.
Constant-table indices and entries are private. Callers use `LiteralValue` and
the checked kernel API, not storage indices.

Run `cargo run -p covalence-logic-hol --example literals` for a small complete
example, including a reusable partially applied builtin.

## Values and operations

| Carrier                   | Meaning                       | Builtin family                                                                                                                                               |
| ------------------------- | ----------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `I8`, `I16`, `I32`, `I64` | Fixed-width bit patterns      | `WordOp`: wrapping arithmetic, signed/unsigned division and remainder, comparisons, bitwise operations, masked shifts, rotations, bit counts, sign extension |
| `Nat`                     | Unbounded nonnegative integer | `NatOp`: arithmetic, zero-truncating subtraction/predecessor, powers, comparisons, min/max, bitwise operations and shifts                                    |
| `Int`                     | Unbounded integer             | `IntOp`: arithmetic, negation, absolute value, powers, comparisons, min/max, two's-complement bitwise operations and arithmetic shifts                       |
| `Bytes`                   | Finite list of octets         | `BytesOp`: list construction, concatenation/repetition, length, comparison, indexing/update, slicing/replacement, and fixed-word endian codecs               |

`CastOp` distinguishes range-checked conversions from explicitly wrapping
conversions. Signedness belongs to an operation, not a second family of word
types. Comparisons produce `Bool`. Integer division truncates toward zero;
remainder has the dividend's sign. Division by zero and signed word division
overflow are undefined. Signed minimum remainder by minus one is zero.
Word shifts and rotations mask their count modulo the word width.

Byte `Slice` and `Replace` take `(start, length)` with strict bounds. `Take`
and `Drop` clamp at the list length. `Decode` requires an exact word-sized
bytestring; `Read` and `Write` operate at an explicit byte offset. Floats,
Wasm execution, and general WIT values are outside this vocabulary.

## Storage contract

The ordinary constructor chooses inline storage for a natural in
`0..=i64::MAX` or an integer in `i64::MIN..=i64::MAX`. All other naturals and
integers, and all resident bytestrings, use the typed constant table.
Small naturals and integers are also valid table entries. Storage placement
does not change a value's type or meaning; it may change its serialized bytes
and content address.

The added rows use these fields:

| Rows                                                                  | Payload                                                                    |
| --------------------------------------------------------------------- | -------------------------------------------------------------------------- |
| `ty.i8`, `ty.i16`, `ty.i32`, `ty.i64`, `ty.nat`, `ty.int`, `ty.bytes` | No payload                                                                 |
| `tm.i8`, `tm.i16`, `tm.i32`, `tm.i64`                                 | `val`: integer in that width's signed range, encoding the full bit pattern |
| `tm.nat`, `tm.int`                                                    | `val`: inline integer in the ranges above                                  |
| `tm.const`                                                            | `val`: zero-based local `u32` constant index                               |
| `tm.builtin`                                                          | `op`: the serialized `Builtin` descriptor; no children                     |

For example, addition is `app(app(builtin(nat.add), left), right)`. Partial
application is ordinary syntax; a zero-argument builtin has its result type
directly. This keeps application, congruence, and future checked unfolding on
one path. A future function-definition equality can be shared across calls;
it is distinct from evaluating a particular closed application. The primitive
evaluator does not claim to construct lambda implementations for all builtins.

`hol.constants` is an array of `{tag, val}` records, omitted when empty:

- `nat`: minimal unsigned big-endian bytes; zero is `[0]`.
- `int`: minimal signed two's-complement big-endian bytes; zero is `[0]`.
- `bytes`: a CBOR byte string.
- `link`: a tag-42 BLAKE3 CID for raw bytes, reserved for later link reasoning.

A link supplies neither contents nor length. It never becomes a resident
literal through decoding or evaluation. Resident payloads are bounded by
`MAX_LITERAL_BYTES`; evaluation also takes explicit operational resource
limits. A resource failure produces no logical value or theorem.

These are per-value and traversal limits, not a process-wide memory quota.
The CBOR decoder may allocate a payload before checking its size, and closed
reduction retains intermediate values for the duration of the call.

This uses the existing arena CBOR envelope. Signed inline integers, byte
strings, and raw-byte CIDs fit the intended BDASL direction; this change does
not claim to convert the entire arena format to BDASL. No old experimental
literal encoding or compatibility adapter is retained.

## Trusted boundary and formal models

The literal type and successful-evaluation rules explicitly extend the trusted
kernel under `ax.inf`; they are not claims of opcode-free syntactic lowering.
The evaluator in `src/literals.rs` and the numeric operations it calls through
`covalence-data-num` (including `num-bigint`) are part of this trusted path.
Python conversion, serialization, storage policy, and later Wasm acceleration
do not acquire theorem authority.

The intrinsic Propane model lives in
`lean/Nucleus/Nucleus/Hol/Propane/{Literal,IntegerModel,Builtin,Syntax,Semantics,Kernel}.lean`.
`LiteralWire.lean` specifies validated payload fields after container parsing,
including equal meanings for inline and table-stored small numbers. It does
not prove a CBOR parser correct. `LiteralEncoding.lean` gives concrete minimal
numeric encoders and general canonicality and decoder round-trip theorems.

`Hol/Ethane/Literals.lean` constructs the natural-derived carriers and fixes
builtin meanings. `Hol/Ethane/LiteralArena.lean` models decoded type rows,
resolved classifiers, builtin constants, application spines, equality, and memoized
checked reduction; `Dag.check_sound` proves successful checked replay sound.
This does not verify compiled Rust, its stack scheduling, or union-find transport.
`Propane/LiteralCorrespondence.lean` relates the typed computation rule to the
constructed carriers; `LiteralAudit.lean` prints the proof assumptions.
Historical Lean designs retain their own namespaces and validation coverage.

Executable boundary tests are colocated with `constants`, `row`, `literals`,
and `kernel::literals`. They cover malformed encodings, exact theorem
conclusions, atomic failure, table relocation, and arithmetic boundary cases.
`literal-wire.json` and `literal-vectors.json` supply shared Rust/Lean payload
and builtin behavior checks; executable fixtures supplement the general proofs.
