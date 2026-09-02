# `lean4export` NDJSON 3.1.0

This note pins and inventories the external format consumed by this crate. It
describes bytes and reference integrity, not Lean soundness and not a Nucleus
translation.

## Pin and provenance

- repository: <https://github.com/leanprover/lean4export>
- commit: `411dce7db58a3afc60ecab2d211acd1042b593dc` (2026-08-25)
- `lean-toolchain`: `leanprover/lean4:v4.34.0-rc2`
- exporter version: `3.1.0`
- format version: `3.1.0`
- normative evidence at the pin: `Export.lean`, `Export/Parse.lean`, and
  `format_ndjson.md`

The upstream `examples/Nat.add_succ.ndjson` is intentionally **not** a 3.1
fixture: at this commit its metadata is still 3.0.0 and its `def`, `thm`, and
inductive payloads use the older array/group field shapes. This crate rejects
that skew rather than guessing. The local golden corpus is small and
independently hand-authored from the pinned exporter implementation.

## Stream and table invariants

The file is UTF-8 NDJSON: one complete JSON object per physical line. The first
and only first record is `meta`, containing exporter `{name, version}`, Lean
`{version, githash}`, and format `{version}`. Empty records and multiline JSON
are invalid here. Format version must equal `3.1.0`; exporter and Lean versions
are retained as provenance because a format version alone does not identify
producer behavior.

There are three independent explicit-index tables:

| index | contents         | implicit row  | defining kinds                 |
| ----- | ---------------- | ------------- | ------------------------------ |
| `in`  | Lean `Name`      | 0 = anonymous | `str`, `num`                   |
| `il`  | universe `Level` | 0 = zero      | `succ`, `max`, `imax`, `param` |
| `ie`  | Lean `Expr`      | none          | all expression kinds below     |

Every explicit index must equal the current table length. Thus gaps,
out-of-order rows, and duplicates all fail. Every reference is resolved before
its containing row is appended, so references are strictly backward (the two
implicit zero rows are already present). Index namespaces do not mix.
Declarations have no numeric table; declaration names must not repeat.

## Record inventory

Each primitive record has exactly its index key plus one kind key. Field names
whose values are `in`, `il`, or `ie` below are references into that table;
brackets mean an array of references.

| kind             | index | payload                                               |
| ---------------- | ----- | ----------------------------------------------------- |
| `str`            | `in`  | `pre: in`, `str: string`                              |
| `num`            | `in`  | `pre: in`, `i: nat`                                   |
| `succ`           | `il`  | `il`                                                  |
| `max`, `imax`    | `il`  | exactly `[il, il]`                                    |
| `param`          | `il`  | `in`                                                  |
| `bvar`           | `ie`  | de Bruijn `nat`                                       |
| `sort`           | `ie`  | `il`                                                  |
| `const`          | `ie`  | `name: in`, `us: [il]`                                |
| `app`            | `ie`  | `fn: ie`, `arg: ie`                                   |
| `lam`, `forallE` | `ie`  | `name: in`, `type: ie`, `body: ie`, `binderInfo` enum |
| `letE`           | `ie`  | `name: in`, `type/value/body: ie`, `nondep: bool`     |
| `proj`           | `ie`  | `typeName: in`, `idx: nat`, `struct: ie`              |
| `natVal`         | `ie`  | decimal natural as a string                           |
| `strVal`         | `ie`  | string literal payload                                |
| `mdata`          | `ie`  | `expr: ie`, `data: object`                            |

`binderInfo` is one of `default`, `implicit`, `strictImplicit`, or
`instImplicit`. `mdata.data` is metadata, not expression syntax; upstream's
own parser currently reconstructs it only as an empty map.

Declaration records have one top-level key and no explicit ID:

| kind        | fields                                                     |
| ----------- | ---------------------------------------------------------- |
| `axiom`     | common fields, `isUnsafe`                                  |
| `def`       | common fields, `value: ie`, `hints`, `safety`, `all: [in]` |
| `opaque`    | common fields, `value: ie`, `all: [in]`, `isUnsafe`        |
| `thm`       | common fields, `value: ie`, `all: [in]`                    |
| `quot`      | common fields, `kind`                                      |
| `inductive` | `types`, `ctors`, and `recs` arrays described below        |

Common fields are `name: in`, `levelParams: [in]`, and `type: ie`.
Definition `hints` is `opaque`, `abbrev`, or `{regular: nat}`; `safety` is
`unsafe`, `safe`, or `partial`; quotient kind is `type`, `ctor`, `lift`, or
`ind`.

An inductive `types` item adds `numParams`, `numIndices`, `all: [in]`,
`ctors: [in]`, `numNested`, `isRec`, `isUnsafe`, and `isReflexive`. A `ctors`
item adds `induct: in`, `cidx`, `numParams`, `numFields`, and `isUnsafe`. A
`recs` item adds `all: [in]`, `numParams`, `numIndices`, `numMotives`,
`numMinors`, `rules`, `k`, and `isUnsafe`; each rule is
`{ctor: in, nfields: nat, rhs: ie}`.

The exporter emits dependencies before declarations. Members of an inductive
group are carried in one record, ordered as types, constructors, then
recursors. Fields such as recursor types and generated quotient declarations
are redundant conveniences; a future checker must validate or ignore them by
an explicit policy, never accept them as authority.

## Generic versus Lean-specific

`stream::for_each` (physical-line framing and streaming JSON) and
`stream::DenseTable` (append-only explicit indices with backward lookup) are
generic. HOL-NDJSON can reuse them without importing Lean constructors.
Everything named in the inventory—three namespace names, record tags, binder
metadata, declaration grouping, and Lean references—is Lean-specific.

For HOL-NDJSON, explicit IDs are preferred for the shared streaming layer:
they survive interleaved metadata/export records and make duplicate/gap errors
local and explicit. Implicit array positions remain smaller and are natural for
the non-streaming arena view. The conversion should assign/check dense explicit
IDs at the NDJSON boundary and prove or test equality with the array-position
view, rather than making the in-memory DAG support two identity rules.

## Future semantic boundary

This reader stops after schema and reference validation. A future importer is
a separate translation/checking stage: reconstruct Lean syntax, choose and
document treatment of unsafe/partial declarations and metadata, translate a
supported fragment to Nucleus objects, and ask a Nucleus kernel to check every
fact it wants to expose. Lean definitions and declarations should be a
first-class frontend workflow; parsing a theorem record alone still does not
produce a theorem handle. Unsupported Lean syntax or declarations remain
explicit translation failures, independent of valid NDJSON framing.
