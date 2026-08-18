# HolE arena stacks

This directory contains the common arena design explored by two sequent
representations. Both use checked, immutable arena nodes; one-based `Ix`
references; lazy imported segments; typed links; and the same HolE expression
surface and initializer. They differ only in how a sparse sequent stores its
two logical sides.

The recommendation for the first kernel protocol is **v2, the plain-context
stack**. The packed stack remains a useful implementation experiment, not a
better trusted interchange format.

## Shared object-identity rule

An `O256` addresses stored bytes. A CAS must map one address to one stored
object, and an import-table ID selects one address. The reverse maps need not
be injective: several byte encodings and therefore several addresses may
decode to the same logical arena, context, or sequent. Likewise, duplicate
addresses in a decoded import table would be semantically harmless even though
the preferred Rust builder interns them.

Consequently, neither stack requires canonical CBOR, a canonical hash for each
logical value, nor preservation of a source address after decode/re-encode.
The encoder is still deterministic and versioned so producers have a preferred
encoding and reproducible addresses.

## The two representations

| Concern                     | Packed stack (v1)                                                 | Plain-context stack (v2)                                  |
| --------------------------- | ----------------------------------------------------------------- | --------------------------------------------------------- |
| Shared scope                | One arena and import-table handle per `Seq`                       | Same                                                      |
| Imported sequents           | One map from link to premise/conclusion bits                      | One set in each context body                              |
| Relation facts              | One pair-keyed map with premise/conclusion relation masks         | One relation-keyed set of oriented pairs in each body     |
| Public CBOR                 | Six flat side-specific fields                                     | `premises` and `conclusion`, each an ordinary nested body |
| Rust serialization          | Private packed state projected through a wire struct              | Derived directly from the logical structs                 |
| Lean model                  | Public types plus masks, packed entries, and projection functions | The same `CtxBody`, `Ctx`, and `Seq` shape as Rust        |
| Dependencies                | `bitflags`                                                        | Standard collections and Serde only                       |
| Natural query bias          | “Which relations/sides contain this pair?”                        | “Which pairs inhabit this relation and side?”             |
| Facts present on both sides | One key with two masks                                            | Stored once per side                                      |

On the arena-base branches, v2 removes 307 net lines relative to v1 (247
insertions, 554 deletions). The two Rust sequent/relation modules shrink from
739 to 498 lines, and the main Lean surface model shrinks from 370 to 289
lines. These counts are only a maintenance signal; the more important change
is that a decoder no longer has to agree with an additional packed-to-public
projection.

## Why v2 is the MVP

The v2 in-memory representation, public API, wire representation, and Lean
model all expose the same idea: a sequent is a pair of contexts that agree on
their arena and imports. `Seq` stores that common scope once, while
`Seq::premises`, `Seq::conclusion`, and `Seq::from_contexts` witness the
isomorphism with a compatible pair of `Ctx` values.

This is a good TCB boundary because:

- invalid signed references and invalid segments are rejected while decoding;
- no bit layout or normalization projection has logical significance;
- adding a fact has an obvious set-insertion meaning;
- unsupported relation tags fail closed;
- Rust/Lean CBOR round trips are stated against the exact public structure;
- a future dense index can be discarded and rebuilt from the sparse facts.

The main costs are modest duplication when the same fact appears on both sides
and less compact in-memory storage. Neither cost should be optimized before
real theorem workloads are measured.

## What v1 still teaches us

The packed design is a plausible derived index. Pair-first masks efficiently
answer whether several relations or both sides contain one endpoint pair, and
they may serialize compactly in a future dense format. If profiling justifies
it, the packed map can sit behind v2 as a cache whose projection is checked
against the plain contexts. It should not silently become the logical source
of truth.

The comparison has already improved both stacks:

- `Segment` fields are private and deserialization now replays checked
  construction in both stacks;
- both forbid unsafe Rust in the HolE crate and identify it as TCB code;
- both document byte identity separately from decoded logical equality;
- v2 preserves v1's ordered sets, typed links, lazy resolution, and hostile
  decoder tests while dropping its packed proof burden.

## Evolution path

1. Freeze and test the minimal v2 arena, context, and sequent encodings.
2. Lower Rust kernel objects to those objects and check all asserted
   relations LCF-style.
3. Use the static initializer as an ordinary imported arena; keep its stable
   named references in Rust, Lean, and Python.
4. Add measured, untrusted indexes for frequent relation and type queries.
5. Study congruence closure and persistent E-classes as a derived view in
   [#739](https://github.com/imbrem/nucleus/issues/739).
6. Introduce another `(format, object kind)` only if a dense representation
   needs independent persistence and its projection can be checked.

This leaves room for an E-graph, SQLite indexes, and binary formats without
making any of them prerequisites for a correct version-2 kernel.
