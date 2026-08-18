# Rust–Lean indexed syntax correspondence

See [`STACKS.md`](STACKS.md) for the packed-v1/plain-v2 comparison and why the
plain-context representation is the recommended MVP.

The normative Rust representation is the flat arena in `src/arena.rs`. Its
formal counterpart is `lean/Nucleus/Nucleus/HolSurface.lean`, with value-level
CBOR in `HolSurface/Cbor.lean` and the audited HolE mapping in
`HolSurface/RustMapping.lean`.

An `Ix`/Lean `Ref` is a nonzero integer no larger than `i32::MAX`. Every local
definition refers only to earlier indices. Imported ranges are lazy `Segment`s;
their `LinkRef` stores an import-table index, format, and object kind at the
reference site, and both Rust and Lean require the translated source range to
remain inside the positive-`i32` index space. The import table itself is only a
flat vector of `O256` values. Multiple IDs may name the same address: lookup is
the one-way function from an import ID to one `O256`. The `push` builder interns
an address by reusing its first existing ID, but uniqueness is not a decoding
invariant and wire duplicates retain their distinct indices.

Relation endpoints use an `i32`: zero is null, positive values are `Ix` values,
and negative values are negated `Ix` values. `i32::MIN` is rejected because its
magnitude is outside the `Ix` range.

## Expression wire shape

Every node is a CBOR map with a string `tag` and an `ix` array containing its
arena children in constructor order. Variable leaves additionally use `var`.
Scalar literal payloads, when an extension defines them, use a separately typed
field rather than masquerading as child indices.

The arena admits these constructors:

| Rust `Expr` | Lean `HolSurface.Expr` | Tag         | Children/payload          |
| ----------- | ---------------------- | ----------- | ------------------------- |
| `KindStar`  | `kindStar`             | `KIND_STAR` | none                      |
| `KindArr`   | `kindArr`              | `KIND_ARR`  | domain, codomain          |
| `TyBool`    | `tyBool`               | `TY_BOOL`   | none                      |
| `TyArr`     | `tyArr`                | `TY_ARR`    | domain, codomain          |
| `TyApp`     | `tyApp`                | `TY_APP`    | function, argument        |
| `TyLam`     | `tyLam`                | `TY_LAM`    | binder kind, body         |
| `TyBv`      | `tyBv`                 | `TY_BV`     | `var`                     |
| `TySub`     | `tySub`                | `TY_SUB`    | carrier, predicate        |
| `TyExists`  | `tyExists`             | `TY_EXISTS` | predicate                 |
| `TyModel`   | `tyModel`              | `TY_MODEL`  | predicate                 |
| `TmBv`      | `tmBv`                 | `TM_BV`     | `var`                     |
| `TmFv`      | `tmFv`                 | `TM_FV`     | type; `var` name          |
| `TmApp`     | `tmApp`                | `TM_APP`    | function, argument        |
| `TmLam`     | `tmLam`                | `TM_LAM`    | domain, body              |
| `TmBool`    | `tmBool`               | `TM_BOOL`   | Boolean `value`           |
| `TmEq`      | `tmEq`                 | `TM_EQ`     | left, right               |
| `TmEps`     | `tmEps`                | `TM_EPS`    | type, predicate           |
| `TmAbs`     | `tmAbs`                | `TM_ABS`    | carrier, predicate, value |
| `TmRep`     | `tmRep`                | `TM_REP`    | carrier, predicate, value |
| `TmCast`    | `tmCast`               | `TM_CAST`   | term, target type         |
| `TmNat`     | `tmNat`                | `TM_NAT`    | canonical unsigned `data` |
| `TmBytes`   | `tmBytes`              | `TM_BYTES`  | byte-string `data`        |

`SurfaceTag` names the wider HolE syntax. A named tag is not necessarily an
admitted arena expression: decoding succeeds only when
`Expr::from_parts` has a matching constructor with exactly the required
children and payload.

## Arena objects

`Arena<I, V>` is generic only over its optional import-table link and its sealed
storage family. `OwnedVec` uses `Vec`; `StaticVec` uses `&'static [T]`. Both
serialize through the same validated owned wire form. `Ctx` and `Seq` refer to
an arena and import table by optional links and encode logical facts as sparse,
relation-indexed pairs.

Each sequent stores one shared arena/import scope plus two ordinary context
bodies. Each body directly contains imported sequents and a
relation-indexed set of oriented pairs. Rust and Lean model the same nested
shape; there is no flag-packed representation or normalization projection in
the trusted core. Dense indexes and E-classes remain derived optimizations.

Rust and Lean both validate preferred-encoding round trips. Cached Rust
objects retain their value and typed `O256` address, not the source CBOR bytes.
The preferred encoding is not a canonicalization requirement: distinct CBOR
byte strings and therefore distinct addresses may
decode to the same logical value. An address identifies the exact bytes stored
under it; decoding and re-encoding an arbitrary source need not preserve that
source address.

## Foundational initializer

`INIT_ARENA` is an import-free `StaticArena` backed by `&'static [Expr]`. Its
readable builder is checked node-for-node against the frozen table, and
`HolSurface/Init.lean` mirrors that table exactly. It contains only core HolE
constructors: in particular, neither `TM_NAT` nor `TM_BYTES` occurs in it.

The initializer defines booleans and their basic connectives; a categorical
second-order Peano model with zero, successor, and recursively characterized
addition; the numeral 256 by repeated doubling; bytes as the subtype of
naturals below 256; and byte strings as the categorical list model over bytes.
Its canonical CBOR address is pinned by Rust and Python tests.
