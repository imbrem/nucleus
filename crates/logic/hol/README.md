# Checked literals

`Kernel::literal`, `Kernel::literal_ty`, and `Kernel::builtin_const` construct
checked terms. Builtin constants have ordinary curried function types and take
arguments through ordinary `Kernel::app` rows. `Kernel::builtin` is a
full-application convenience, not another syntax form.
Paired helpers such as `kernel.and(lhs, rhs)`, `kernel.not(prop)`, and
`kernel.add_i32(lhs, rhs)` construct these same applications.
`arena.match_and(term)`, `arena.match_not(term)`, and
`arena.match_add_i32(term)` return arguments only for the exact operation and
arity. Matchers inspect raw syntax; they establish no theorem or typing fact.
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
| `Bool`                    | Truth values                  | `BoolOp`: not, and, or, implication, equivalence                                                                                                             |
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

## References and storage

`Kernel` contains only `arena: Arena`. A `Ref` is a nonzero signed 32-bit index:
positive indices address local rows; negative indices name immutable globals.
There is no remembered init prefix, builtin-type cache, or allocated table of
tiny values. `src/global.rs` decodes the fixed vocabulary arithmetically.
Unknown negative encodings are rejected, including in serialized reference
fields. Naming a numeric global does not bypass the checked `ax.inf` gate.

Globals include `kind.star`, the eight scalar types, their curried builtin
signatures, Boolean values and functions, and tiny literals:

- Nat `0..=65535` and Int `-32768..=32767`;
- all I8 and I16 bit patterns;
- I32 and I64 values `0..=65535`;
- empty Bytes, identical to the nullary `BytesOp::Empty` constant.

The serialized global numbers are specified in `src/global.rs` and mirrored
by `Propane/LiteralRegistry.lean`; callers use descriptors, not numeric IDs.
Obvious aliases share a reference: one-byte endian variants and same-width
cast variants. Fully applying a same-width cast returns its argument.

Non-tiny Nat/Int values fitting `i64` are inline `tm.nat`/`tm.int` rows.
Larger values and nonempty Bytes use a private typed constant table through
one `tm.const` reference form. Small Nat/Int values may also appear in that
table. Non-tiny words use `tm.i32`/`tm.i64` rows whose signed payload preserves
the entire bit pattern. Storage placement changes neither type nor meaning;
it can change serialized bytes and content addresses.

For example, addition is `app(app(negative_nat_add, left), right)`. Partial
application is ordinary syntax; no argument-bearing builtin row exists.
Boolean functions unfold to fixed checked equality/lambda definitions, never
definitions selected by userspace names. This does not claim lambda
implementations for every numeric or Bytes operation.

Checked equality classes prefer negative roots. Equating distinct negative
roots is rejected transactionally; this cache restriction is not a proof that
their meanings differ. Semantic classes additionally prefer resident literal
roots to positive nonliteral rows. Reduction evaluates children, applies the
builtin, and caches each successful application against its result. Tiny
results allocate no value row; subsequent reductions can reuse cached values.

Theorem literals are a separate namespace: their magnitude is a **positive
local Boolean row**, and their sign denotes negation. `Kernel::lit` rejects a
global reference. Boolean constants use empty logical matrices instead:
true is CNF `[]` / DNF `[[]]`; false is CNF `[[]]` / DNF `[]`.
No zigzag encoding or synthetic Boolean theorem atom is used.

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

Numeric/Bytes carriers and successful evaluation explicitly extend the trusted
kernel under `ax.inf`. Boolean construction, evaluation, and fixed unfolding
need no infinity capability. These are separate checked rules, not claims
that all numeric operations already lower to primitive HOL syntax.
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
`LiteralRegistry.lean` and its companion modules prove canonical signed global
decoding, signature round trips, and the Boolean-global classification boundary.
`Ethane/LiteralRoots.lean` models immutable roots and checked semantic unions;
`LiteralTheoremBoundary.lean` separates signed theorem atoms from global refs.
`Propane/BooleanDefinition.lean` proves the fixed Boolean unfolding meanings.
These models do not verify compiled Rust or its CBOR parser and stack scheduling.
`Propane/LiteralCorrespondence.lean` relates the typed computation rule to the
constructed carriers; `LiteralAudit.lean` prints the proof assumptions.
Historical Lean designs retain their own namespaces and validation coverage.

Executable boundary tests are colocated with `constants`, `row`, `literals`,
and `kernel::literals`. They cover malformed encodings, exact theorem
conclusions, atomic failure, table relocation, and arithmetic boundary cases.
`literal-wire.json` and `literal-vectors.json` supply shared Rust/Lean payload
and builtin behavior checks; executable fixtures supplement the general proofs.
