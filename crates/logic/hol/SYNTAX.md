# Rust–Lean indexed syntax correspondence

The normative Rust representation is the flat arena in `src/arena.rs`. Its
formal counterpart is `lean/Nucleus/Nucleus/HolSurface.lean`, with value-level
CBOR in `HolSurface/Cbor.lean` and the audited HolE mapping in
`HolSurface/RustMapping.lean`.

An `Ix`/Lean `Ref` is a nonzero integer no larger than `i32::MAX`. Every local
definition refers only to earlier indices. Imported ranges are lazy `Segment`s;
their `LinkRef` stores an import-table index, format, and object kind at the
reference site. The import table itself is only a flat vector of `O256` values;
inserting an address already present reuses its first ID instead of appending a
duplicate.

Relation endpoints use an `i32`: zero is null, positive values are `Ix` values,
and negative values are negated `Ix` values. `i32::MIN` is rejected because its
magnitude is outside the `Ix` range.

## Expression wire shape

Every node is a CBOR map with a string `tag` and an `ix` array containing its
arena children in constructor order. Variable leaves additionally use `var`.
Scalar literal payloads, when an extension defines them, use a separately typed
field rather than masquerading as child indices.

The v0 base admits these constructors:

| Rust `Expr` | Lean `HolSurface.Expr` | Tag         | Children/payload   |
| ----------- | ---------------------- | ----------- | ------------------ |
| `KindStar`  | `kindStar`             | `KIND_STAR` | none               |
| `KindArr`   | `kindArr`              | `KIND_ARR`  | domain, codomain   |
| `TyBool`    | `tyBool`               | `TY_BOOL`   | none               |
| `TyArr`     | `tyArr`                | `TY_ARR`    | domain, codomain   |
| `TyApp`     | `tyApp`                | `TY_APP`    | function, argument |
| `TyLam`     | `tyLam`                | `TY_LAM`    | binder kind, body  |
| `TyBv`      | `tyBv`                 | `TY_BV`     | `var`              |
| `TySub`     | `tySub`                | `TY_SUB`    | carrier, predicate |
| `TyModel`   | `tyModel`              | `TY_MODEL`  | predicate          |

`SurfaceTag` also reserves names for later HolE and surface extensions. A
reserved tag is not an admitted expression: decoding succeeds only when
`Expr::from_parts` has a matching constructor with exactly the required
children and payload.

## Arena objects

`Arena<I, V>` is generic only over its optional import-table link and its sealed
storage family. `OwnedVec` uses `Vec`; `StaticVec` uses `&'static [T]`. Both
serialize through the same validated owned wire form. `Ctx` and `Seq` refer to
an arena and import table by optional links and encode logical facts as sparse,
relation-indexed pairs.

Rust and Lean both prove/validate preferred-encoding round trips. Cached Rust
objects retain their value and typed `O256` address, not the source CBOR bytes.
