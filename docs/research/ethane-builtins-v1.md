# Ethane compact builtin contract v1

`crates/logic/hol/builtins-v1.tsv` is the reviewed registry for compact syntax.
It is separate from the opcode-free init arena. Rust tests parse every column
and compare it with the executable enums; Lean defines the same registry and
evaluates the same row envelopes. Adding an entry means updating all three in
one change, and their tests are what catch drift.

## Wire and compatibility

The version is part of the row tag, not an arena-wide switch. `val` is the
unsigned opcode and `ixs` holds the operand references, left to right.

Decoders reject an unknown tag, an unassigned code (every unlisted `u8` is
reserved), a code outside `u8`, the wrong arity, extra fields, or a `val` of
the wrong CBOR kind.

A `(version, family, code)` meaning never changes. A reader may implement only
some versions; it must reject a later one rather than guess. New operations
take unused codes when the family and wire shape already fit, and a new
versioned tag otherwise. Writers emit only the version they declare.

## Families

| family | tag | operands |
| --- | --- | --- |
| `op1` | `tm.op1.v1` | one Boolean |
| `op2` | `tm.op2.v1` | two Boolean |
| `num1` | `tm.num1.v1` | one numeric |
| `num2` | `tm.num2.v1` | two numeric |

The numeric families are separate from the Boolean ones for two reasons:

- The kernel types a Boolean opcode directly, because `ty.bool` is a sort it
  defines itself. It cannot type a numeric one until the init slice defines
  `nat` and `int`.
- `op1` and `op2` mean "the Boolean connectives" throughout the Lean
  development. Adding arithmetic to them would perturb proofs about Boolean
  logic for no gain.

An assigned code promises a meaning. It does not claim the meaning is
constructible: a code whose init definition does not exist yet is well formed
on the wire and rejected by row validation, like an unlowered literal, until
that definition lands.

## Meaning, equality, and limits

Compact rows are macros. Their only meaning is canonical recursive expansion to
the opcode-free definitions in the init slice. Lowering keeps operand order and
uses the init identity the kernel selects; it never consults names or a mutable
rewrite set. `not p`, `p and q`, `p or q`, and `p imp q` expand to the matching
init definitions applied to their lowered operands.

Wire equality compares tag, opcode, and child references. HOL syntactic
equality compares lowered terms. So a compact row and its expansion are
syntactically equal after lowering, without having identical wire rows.

Decoding one row is constant space apart from its operands and does no
expansion. Implementations reject an over-long `ixs` array before allocating.
Recursive lowering is fuel-bounded by the caller and memoized per arena
reference; exhaustion is an ordinary checked failure and produces no kernel
term. This keeps nested input from turning into unbounded work inside the
kernel.

## Totality

Ethane has no partial operations, so each operation also fixes a result on the
inputs where the mathematical operation is undefined. That result is part of
the frozen meaning. The `total` column records it: `-` when the operation is
defined everywhere, otherwise what it returns on those inputs.

| case | result | column |
| --- | --- | --- |
| `nat.pred 0` | `0` | `zero` |
| `nat.sub a b` with `b > a` | `0` | `zero` |
| `nat.div` or `int.div` by zero | `0` | `zero` |
| `nat.mod` or `int.mod` by zero | the dividend | `dividend` |

Division by zero follows Lean, Coq, and Isabelle/HOL: `a / 0 = 0` and
`a % 0 = a`. Together these keep `a = b * (a / b) + a % b` at `b = 0`. Rust's
`/` panics on zero, so it settles the rounding convention below but not this
case.

## Numeric meaning

`int.div` truncates toward zero and `int.mod` takes the sign of the dividend,
matching Rust's `/` and `%` and `covalence-data-num::Int::div_rem`, so an
accelerated evaluator and the lowering compute the same results. `nat` division
is the same operation on non-negative operands.

`int.abs` lands in `nat`, since an absolute value is never negative; compose
with `nat.to_int` for the same-sort form. `int.sign` gives `-1`, `0`, or `1` in
`int`. `nat.le`, `nat.lt`, `int.le`, and `int.lt` are the usual orders.

## Casts

`nat.to_int` is the inclusion. The zigzag pair `int.to_nat.zigzag` and
`nat.to_int.zigzag` is the bijection `n >= 0 ? 2n : -2n-1` and its inverse, so
both directions are total and lossless.

## Not yet assigned

Byte operations, and any operation needing three operands. `bytes.slice` is
ternary, so it needs a family that does not exist yet. Both arrive with the
rest of the byte semantics.
