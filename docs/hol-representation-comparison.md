# HOL-omega syntax representation comparison

Status: comparison of the executable kind-slice experiments in #162 and #165.
Both are based on #160 and expose the same Rust API. This document recommends
the next experiment; it does not freeze the complete HOL-omega calculus or an
external interchange format.

## Candidates actually tried

### Constructor tables (#162)

The normalized prototype has one header table and one table per constructor:

```text
hol_kind(kind_id, rank)
hol_kind_star(kind_id)
hol_kind_arrow(kind_id, domain_id, codomain_id)
```

`star` and each arrow occupy two rows. Foreign keys and table shape express
some structural invariants. Reading a constructor uses joins across all kind
constructor tables. Rank is cached in the header.

### Wide universal row (discarded before PR)

The first universal-table sketch had columns for three children, an immediate,
annotations, inferred classifiers, two binder depths, and rank. Most were NULL
for every kind. Its CHECK constraint tried to restate constructor shapes in
SQL.

This was the least elegant option. It guessed the union of future constructor
payloads before the calculus is settled and duplicated admission logic in a
large tag-dependent constraint. It was replaced rather than preserved as a
third implementation.

### Compact tagged node (#165)

The selected universal-table experiment is only:

```text
hol_node(node_id, tag, lhs, rhs, ty)
```

The schema-qualified tag determines the sort, constructor, and meanings of the
three payload positions. A kind uses:

```text
KSTAR(NULL, NULL, NULL)
KARR(domain, codomain, NULL)
```

Likely term shapes include `APP(fun,arg,ty)`, `TYAPP(tyfun,tyarg,ty)`,
`IMPORT(src,ix,ty)`, `BV(index,NULL,ty)`, and `FV(symbol,NULL,ty)`. These names
are examples, not frozen constructors. For a type node, `ty` can hold its kind;
for a term node it can hold its type. In that sense it is the node's admitted
classifier, despite the deliberately short physical column name.

Nucleus validates tag shape, child sorts, typing/kinding, closure, and
acyclicity before insertion. SQL supplies strict scalar storage and partial
unique indexes for canonical constructors. There are intentionally no node
foreign keys: a raw SQLite connection is not an admission API, and an imported
database must be validated separately before use.

The five columns are the fixed logical core, not a ban on physical extension.
At database creation a user may declare additional metadata columns on
`hol_node` and create ordinary SQLite indexes over them. Internal Nucleus SQL
always names the core columns explicitly, so trailing metadata neither changes
decoding nor canonical identity. Metadata values are written/read through
policy-checked operations in the same transaction as admission. Column names,
SQLite storage classes, defaults, and index definitions are recorded in the
connection's schema description and checked when validating an import.
The kind-only PRs install the zero-metadata default; the schema builder and
typed metadata operations should be the next representation-independent API
shared by both experiments.

## Direct comparison

| Property                         | Constructor tables                          | Compact tagged node                                      |
| -------------------------------- | ------------------------------------------- | -------------------------------------------------------- |
| Data tables in kind prototype    | 3                                           | 1                                                        |
| Rows per admitted kind           | 2                                           | 1                                                        |
| Kind-arrow lookup                | constructor-table lookup plus header        | one partial-index lookup                                 |
| Constructor read                 | joins/constructor exclusivity check         | one row and tag match                                    |
| Child integrity in SQLite        | foreign keys                                | checked by Nucleus admission                             |
| Corruption diagnostics           | table-specific                              | tag/payload-specific Rust error                          |
| Kind/type/term IDs               | naturally separate spaces                   | one physical space, distinct Rust newtypes               |
| Mutually recursive type/term DAG | cross-table references                      | ordinary node references                                 |
| Generic recursive traversal      | UNION/view over constructors                | one recursive query                                      |
| Adding a constructor             | add a table and queries                     | add a tag, validator, and partial index                  |
| Adding a new payload shape       | add a narrow table                          | must fit `lhs/rhs/ty` or justify a representation change |
| User metadata columns/indexes    | extend object header or use satellite table | extend `hol_node` or use satellite table                 |
| Raw inspection                   | explicit but spread across tables           | compact and tag-readable                                 |
| SQL structural enforcement       | stronger                                    | deliberately minimal                                     |

The Rust implementation sizes (409 lines for #162 and 450 for #165 at the
kind slice) are not meaningful evidence against the tagged table. The latter
derives rank with memoized cycle detection and has an extra physical-shape
test; the former caches rank. Cached versus derived rank is independent of the
node representation and should be decided after measurement.

## Why textual tags

The experiment uses schema-versioned textual tags rather than magic integers
or a tag registry table. They make raw SQLite inspection, corruption reports,
and exports self-describing. An integer encoding would save space but requires
another versioned mapping and makes accidental schema confusion harder to see.
If tag bytes become material, a later schema can assign canonical integers;
the Rust API need not change.

## Trusted boundary

Both prototypes rely on `Connection<Hol<P>>`: protocol code, not callers,
constructs admitted IDs, and every public read/write is policy-visible. The
compact design moves elementary referential checks out of SQLite, but not out
of the trusted admission operation. It therefore does not reduce validation;
it keeps validation in one short Rust path rather than partially duplicating
it as SQL constraints.

An untrusted database is never attached to the trusted connection and assumed
to obey either schema. A separate validator checks its declared schema,
constructor payloads, references, cycles, classifiers, and typing rules before
any admitted use.

## Recommendation

Continue the next type/term slice with the compact tagged node from #165.

It best matches the mutually recursive syntax, makes the common operations one
row each, and keeps the physical design small while the formal calculus is
still moving. The five columns impose a useful discipline: constructors that
do not fit should first be represented compositionally. Add a payload table or
new representation only when a concrete constructor proves that necessary.

Keep #162 as the control implementation. Before committing to a durable schema,
run both through the same generated type/term corpus and measure database size,
admission time, constructor/classifier lookup, free-variable traversal, and
whole-database validation. The representation-independent Rust API makes that
comparison possible without maintaining two caller interfaces.

User metadata is deliberately excluded from hash-consing. A single-valued
property may live in a declared extra column and be indexed there. Metadata
with multiple producers, multiple values, independent lifetimes, or provenance
rows belongs in a user-owned satellite table keyed by the typed object ID. This
avoids forcing an arbitrary overwrite rule onto canonical syntax.

## What this is not

The tagged node is an internal admitted-syntax experiment. It is not
LeanNDJSON, a universal foreign-proof interchange table, or a reason to admit
foreign rows as trusted syntax. External proof data should become a HOL-omega
object and satisfy predicates such as `IsLeanDerivation`; see #163 and #164.

Likewise, query and CAS reflection are separate generic base-logic concerns.
An optional minimal SQL extension may introduce a theorem like
`⟦S⟧(⟦C⟧, ⟦D⟧)` for a small SQL fragment, while CAS facts are reflected
separately. Content addressing, Merkle structures, and format predicates are
then composed and proved inside HOL-omega rather than built into this table.
