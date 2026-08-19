# Iroh-style hash arrays in Rust

Research date: 2026-08-19

## Executive recommendation

Implement a small, repository-owned `O256` array abstraction in a data crate adjacent to `covalence-lib-hash`, and make its **canonical** byte representation exactly the Iroh `HashSeq` representation: the concatenation of 32-byte values, with no header, count, or padding. Preserve the distinction between (a) arbitrary CAS bytes, which always remain addressable and queryable through a checked API, and (b) canonical hash arrays, whose lengths are multiples of 32. Do **not** depend on `iroh-blobs` merely to reuse `iroh_blobs::hashseq::HashSeq`, and do **not** adopt `iroh-blake3`.

The local abstraction should:

- own or view a contiguous byte buffer whose length is divisible by 32;
- expose `len`, `is_empty`, `get`, borrowed and consuming iteration, conversion to/from bytes, and collection from `O256` iterators;
- offer zero-copy construction from `bytes::Bytes` if `bytes` is acceptable as a dependency, plus a borrowed `O256Slice`/`HashArrayRef` over `&[u8]` if theorem-prover hot paths benefit from it;
- state explicitly that byte-level interoperability with Iroh does not by itself guarantee semantic interoperability: every Iroh link is the ordinary unkeyed BLAKE3 digest of a blob, whereas the broader local `O256` namespace can also contain random, keyed, or context-derived values;
- put any `iroh_blobs::Hash`, `iroh_blobs::hashseq::HashSeq`, or `blake3::Hash` conversions behind a small optional interoperability feature or in a bridge crate. The wire format itself needs no Iroh dependency.
- treat the base value as morally `Vec<O256>`: positional order and duplicates are data, not an invariant that elements are sorted. Add sorted/distinct views as checked refinements when set algorithms need them.
- put operations behind a capability-style CAS extension so a byte-only cache can implement them by checked reads while SQLite or remote stores can answer them from validated indexes.

For malformed byte lengths, the recommended first policy is **strict checked interpretation**: every O256-level query returns `Result<_, HashArrayError>`, and a non-multiple-of-32 object produces a stable `NonCanonicalLength { byte_len, remainder }` result before any element answer is trusted. This gives every byte string defined query behavior without silently discarding or inventing bytes. Zero-extension, truncation, and an adjoined partial-element model are analyzed below and can still be selected if later logic requires a total element-valued interpretation rather than a total checked operation.

This preserves Iroh compatibility and gives this repository control of ergonomics, traits, `serde`, invariants, MSRV, and no-std/wasm choices. It also avoids pulling a network protocol, async runtime, stores, metrics, and serialization stack into a fundamental theorem-prover collection type.

## What “Iroh-style hash array” means

Iroh calls the format a **HashSeq**: “a blob that contains a sequence of links,” where a link is a 32-byte BLAKE3 hash and the blob length is a multiple of 32. There is no framing or embedded element count; the count is `byte_len / 32`. The current README states this directly ([iroh-blobs README](https://github.com/n0-computer/iroh-blobs/blob/main/README.md)).

This gives an unusually useful compatibility boundary:

```text
hash[0][0..32] || hash[1][0..32] || ... || hash[n-1][0..32]
```

The empty sequence is the empty blob. A HashSeq's content address is therefore ordinary BLAKE3 over those concatenated bytes. `BlobFormat::HashSeq` is metadata carried alongside that content address; it is not a tag embedded in the array bytes. In current `iroh-blobs`, `BlobFormat::Raw` maps to `0`, `HashSeq` maps to `1`, and textual `HashAndFormat` prepends `s` for a sequence ([source for `Hash`, `BlobFormat`, and `HashAndFormat`](https://docs.rs/iroh-blobs/latest/src/iroh_blobs/hash.rs.html)).

## Ecosystem inventory

| Crate/type | Current observed version | Purpose and representation | Status | Fit here |
|---|---:|---|---|---|
| [`blake3`](https://docs.rs/blake3/latest/blake3/) | 1.x | Canonical optimized BLAKE3 implementation; `Hash` is 32 bytes; ordinary, keyed, derive-key, incremental, XOF, rayon, SIMD, and stable `hazmat` subtree APIs | Active upstream, widely used | Keep using it; the repository already does |
| [`iroh-blake3`](https://docs.rs/iroh-blake3/latest/iroh_blake3/) | 1.4.5 | Fork of an older `blake3`, API-compatible for ordinary hashing, with faster arbitrary subtree hashing added for Iroh/Bao | Historical compatibility fork; superseded upstream | Do not add |
| [`bao-tree`](https://docs.rs/bao-tree/latest/bao_tree/) | 0.16.0 | BLAKE3/Bao tree geometry, outboards, multi-range verified streaming; re-exports ordinary `blake3` | Active and used by current Iroh blobs | Add only if verified range streaming/outboards become a requirement, not for arrays |
| [`iroh-blobs`](https://docs.rs/iroh-blobs/latest/iroh_blobs/) | 0.103.0 | Blob transfer protocol, stores, downloader, tickets, Bao validation, `Hash`, and `hashseq::HashSeq` | Active but current docs warn the post-0.35 redesign is not yet production quality | Too broad as a core array dependency; useful as an optional integration target |
| [`iroh_blobs::Hash`](https://docs.rs/iroh-blobs/latest/iroh_blobs/struct.Hash.html) | as above | Newtype over `bao_tree::blake3::Hash`, raw 32-byte binary serde, lowercase-hex human serde/display; parses 64-char hex or unpadded base32 | Active protocol-facing link type | Byte-compatible with `O256`, but its serde/text policy differs |
| [`iroh_blobs::hashseq::HashSeq`](https://docs.rs/iroh-blobs/latest/iroh_blobs/hashseq/struct.HashSeq.html) | as above | Validated `bytes::Bytes` backing; `new`, `iter`, `len`, `is_empty`, `get`, `pop_front`, `into_inner`, `FromIterator`, consuming iterator | Active and intentionally small | Best behavioral reference; reimplement the tiny boundary locally |
| [`bao`](https://docs.rs/bao/latest/bao/) | 0.13.x | Original Bao verified-streaming encoding | Maintained upstream, but Iroh uses `bao-tree` for multi-range/runtime geometry | Not relevant to a flat link array |

### Are there multiple “Iroh BLAKE crates”?

The crates.io package specifically named for an Iroh BLAKE fork is `iroh-blake3`. The other relevant packages are layers around standard BLAKE3 rather than alternative hash functions: `bao-tree` implements verified tree streaming, and `iroh-blobs` supplies the protocol-facing `Hash` and `HashSeq` types. Current `iroh-blobs` reaches BLAKE3 through `bao-tree`, which publicly re-exports `blake3` ([bao-tree crate docs](https://docs.rs/bao-tree/latest/bao_tree/)).

Older Iroh material may also mention `abao` or `bao-tree`'s predecessor work. Iroh's Bao resource index describes `abao` as a fork adding chunk groups and Tokio support, and `bao-tree` as the rewrite with runtime-configurable chunk groups and multi-range requests ([Iroh Bao resources](https://github.com/n0-computer/bao-docs)). Neither defines the flat list format or improves the local collection API.

## `iroh-blake3`: why it existed and why not to use it

`iroh-blake3` was a pragmatic fork. Verified streaming needs intermediate BLAKE3 chaining values and efficient hashing of subtrees, not just a final root. The old upstream `guts` API could hash individual chunks, but Iroh wanted to hand a group of chunks to BLAKE3 together so SIMD parallelism remained effective. Its fork added a subtree operation similar to:

```rust
pub fn hash_subtree(start_chunk: u64, data: &[u8], is_root: bool) -> Hash
```

Iroh's own retrospective says the fork caused symbol-collision/build problems when both BLAKE3 packages appeared in one graph and lagged upstream improvements. Upstream BLAKE3's stable `hazmat` API then made the fork unnecessary ([Iroh: “The new BLAKE3 hazmat API”](https://www.iroh.computer/blog/blake3-hazmat-api)). The `iroh-blobs` changelog records removal of the `iroh-blake3` dependency in 0.34.1 ([changelog](https://github.com/n0-computer/iroh-blobs/blob/main/CHANGELOG.md)).

The package remains downloadable and was observed on docs.rs as version 1.4.5, published 2026-06-08, with default `std` and optional `rayon`, `traits-preview`, `neon`, and `zeroize`. Its ordinary API mirrors old upstream BLAKE3: `hash`, `keyed_hash`, `derive_key`, `Hasher`, `OutputReader`, and a 32-byte `Hash` ([crate docs](https://docs.rs/iroh-blake3/latest/iroh_blake3/)). Continued publication should be treated as compatibility/maintenance availability, not a signal that new code should prefer it. Its repository description still calls it a temporary fork “until it gets upstreamed” ([repository](https://github.com/n0-computer/iroh-blake3)).

## Current Iroh APIs and layouts

### `iroh_blobs::Hash`

`Hash` is a copyable, ordered, hashable newtype over `blake3::Hash`. Its useful API includes:

- `Hash::new(bytes)` for ordinary BLAKE3;
- `Hash::EMPTY`;
- `from_bytes([u8; 32])`, `as_bytes()`, and conversions to/from `[u8; 32]` and `blake3::Hash`;
- lowercase 64-character hex `Display`/`to_hex`, ten-character `fmt_short`;
- parsing 64-character lowercase hex or unpadded base32;
- human-readable serde as its hex string, non-human-readable serde as exactly 32 bytes;
- fixed-width postcard maximum size of 32 bytes.

The implementation and wire-format test are visible in the [current source](https://docs.rs/iroh-blobs/latest/src/iroh_blobs/hash.rs.html). This type is more permissive in implicit byte borrowing than upstream `blake3::Hash`: it implements `AsRef<[u8]>` and `Borrow<[u8]>`. Upstream's type deliberately avoids those traits to reduce accidental loss of constant-time equality ([`iroh_blake3::Hash` documents the same policy as upstream](https://docs.rs/iroh-blake3/latest/iroh_blake3/struct.Hash.html)). Constant-time equality is not materially useful for public content addresses, so the local `O256`'s ordinary byte equality is reasonable.

### `iroh_blobs::hashseq::HashSeq`

`HashSeq` is a `Bytes`-backed sequence. Construction succeeds only when the byte length is divisible by 32. It supports random access and iteration by decoding each 32-byte chunk into a `Hash`, and `pop_front` can cheaply advance a `Bytes` view. Collection from owned or borrowed `Hash` iterators builds the flat bytes. Its complete public surface is small ([HashSeq rustdoc](https://docs.rs/iroh-blobs/latest/iroh_blobs/hashseq/struct.HashSeq.html)).

Notably absent are equality/ordering/hash traits, indexing, borrowed slice exposure, serde, mutation beyond front-pop, capacity management, and a first-class borrowed view. Those omissions make sense for a transfer helper but leave room for a theorem-prover-oriented API.

### Protocol semantics

Iroh distinguishes the same BLAKE3 root used with two interpretations by carrying `BlobFormat::{Raw, HashSeq}`. The flat bytes alone do not say “this is a sequence.” A local type should decide whether the Rust type is sufficient as the interpretation tag or whether persisted references also need an explicit format discriminant. If exporting tickets or talking to `iroh-blobs`, convert the computed root to `HashAndFormat::hash_seq(hash)`, not the default raw format.

Current Iroh documentation warns that the latest `iroh-blobs` line is not yet production quality and recommends 0.35 when production stability is required ([current crate docs](https://docs.rs/iroh-blobs/latest/iroh_blobs/)). That warning concerns the protocol/library evolution, not the flat HashSeq byte convention, which is simple and longstanding.

## Local repository context

`covalence-lib-hash` already provides nearly all element-level machinery:

- `Obj<N>` is `#[repr(transparent)]` over its namespace byte array;
- `O256 = Obj<Cov>` is exactly 32 bytes and implements copy, order, standard hash, display/parse, and raw construction;
- `O256::from_bytes` is ordinary BLAKE3, so a normal local content address has the same 32 digest bytes as Iroh;
- `Blake3Hash = Obj<Blake3>` makes the algorithm claim explicit and converts representation-preservingly into `O256`;
- the crate already depends optionally on upstream `blake3 = "1"` and already uses its stable `hazmat` API for BLAKE3 chaining values;
- `O256` serde is raw bytes, while algorithm-specific `Blake3Hash` serde is a DAG-JSON CID. Neither matches Iroh's human-readable hex-string serde automatically.

This means no hash implementation needs replacing. The missing piece is a collection/view and an explicit serialization policy.

## Repository design history: PR #456 and related issues

The repository has already explored this design in [PR #456, “Add flat hash arrays, sets, and index maps”](https://github.com/imbrem/nucleus/pull/456), implementing 1,782 lines on the `hash-arrays` branch. The PR follows [issue #449](https://github.com/imbrem/nucleus/issues/449), with the narrower refinements proposed in [#447 (flat sets)](https://github.com/imbrem/nucleus/issues/447) and [#448 (flat index maps)](https://github.com/imbrem/nucleus/issues/448). The code remains inspectable at commit [`cc2b5caf`](https://github.com/imbrem/nucleus/commit/cc2b5cafe52fe26749fa29e5b7dd1a01e1a40396).

PR #456 created `covalence-data-array`, correctly keeping richer data semantics adjacent to the hash primitive rather than inside it. Its key types were:

- `Hashes<'a, N>`, a borrowed checked view over `&[u8]`;
- `HashArray<N>`, an owned `Vec<u8>` builder and canonical byte value;
- `FlatSet<'a, N>`, a strictly ascending refinement over the same bytes;
- `FlatIndexMap<'a, N>`, an even-element-count `(key, value)` refinement.

It provided exact-size double-ended iteration, checked indexing and slicing, null detection, membership/count/position, bag and set relations, sorting/deduplication, and merge-based set operations. The generic `Namespace` parameter also allowed 20-byte Git hashes, an idea motivated in the PR by [directory-tree issue #454](https://github.com/imbrem/nucleus/issues/454). Issue #449 anticipated a CAS extension with batched reads, O256-oriented indexing, length/sortedness/non-nullness/membership, subset/subbag, and bag/set equality. It also explicitly allowed smart stores to use optimized internal representations so long as normal-form bytes could be reproduced and rehashed.

### Durable ideas worth reusing

- **Bare concatenation as canonical normal form.** It is both Iroh-compatible and independently useful.
- **Borrowed checked view plus owned builder.** Materializing an `O256` by value from each chunk avoids unsafe layout casts and fits this workspace's `unsafe_code = "deny"`.
- **Base sequence separate from refinements.** Sorted/distinct set and paired map interpretations should validate extra invariants without changing bytes.
- **Order and duplicates belong to the base sequence.** The earlier code did preserve them; sorting was an explicit builder operation. This matches the clarified “morally `Vec<O256>`” requirement.
- **Null is ordinary all-zero `O256`.** The old `contains_null`/`is_non_null` checks already used this representation.
- **Algorithms live above storage.** A naive implementation can scan bytes, while stores may accelerate the same observable operations.
- **No hashing policy in the data crate.** The CAS layer decides how result bytes are admitted and addressed.

### Assumptions now stale or incomplete

- PR #456's constructor declared bytes to be a hash array *exactly when* their length was a width multiple and rejected all others at construction. The clarified requirement is broader: arbitrary CAS bytes must have defined outcomes under checked O256-range queries, including malformed suffixes. The canonical type may remain strict, but the CAS query API must be total as a `Result` and must not make malformed objects disappear from the model.
- The old API mixed positional sequence queries, unordered bag/set comparisons, and the `FlatSet` canonical refinement on one type. These remain useful, but the new CAS surface needs named semantic families so `subset`, pointwise/indexed compatibility, bag containment, and byte/order-sensitive equality cannot be confused.
- The set merge code returned local `HashArray` values. A remote/smart CAS operation needs a separate convention: return bytes/value locally, or atomically admit canonical result bytes and return their `O256` address.
- `FlatIndexMap` paired consecutive hashes. That is not the same as the new **indexed subset** relation over arrays with null holes; the latter is pointwise and needs no alternating key/value representation.
- Issue #449 suggested truncated `u64`/`u32` internal representations reversed by zero-padding. That optimization is sound only when a verified schema proves omitted high bytes are zero. It must never be inferred from arbitrary O256s or used as the malformed-suffix policy.
- The PR waited for [ranged HTTP CAS issue #442](https://github.com/imbrem/nucleus/issues/442). The durable dependency is checked/range-readable CAS access, not HTTP specifically. The current trait should support an oblivious local byte cache first; verified Bao/HTTP range reads can implement the same capability later.
- The future dense and sparse map issues ([#450](https://github.com/imbrem/nucleus/issues/450), [#451](https://github.com/imbrem/nucleus/issues/451)) are downstream structures, not reasons to overload the base array with map semantics now.

## Clarified semantic model

### Base value

The base mathematical value is a finite positional sequence:

```text
HashArray = Vec<O256>
NULL      = O256([0; 32])
```

Thus `[a, b] != [b, a]`, duplicates are retained, and `NULL` is a real element used as a hole/sentinel rather than an absent byte range. “Not inherently ordered” should be read as “not required to be sorted,” not “sequence order is semantically erased.” An optional `SortedHashArray` and stricter `FlatSet` can validate ascending and strictly ascending subsets of values.

This distinction yields three explicit relation families:

| Family | Order | Multiplicity | Typical operations |
|---|---|---|---|
| Sequence/positional | Significant | Significant | `len`, `get`, `slice`, exact equality |
| Bag | Ignored | Significant | `is_subbag`, bag equality, multiset algebra if needed |
| Set | Ignored | Ignored | `contains`, `is_subset`, union/intersection/difference/symmetric difference/singleton |

Set-producing operations need deterministic output bytes if their result is to be content-addressed. The natural normal form is strictly bytewise ascending, deduplicated O256s—the earlier `FlatSet` representation—even though inputs need not be sorted. A naive backend sorts/deduplicates; a smart backend performs indexed set algebra. This ordered **result refinement** does not impose sortedness on general hash arrays.

Bag/multiset operations similarly need canonical output, but sort **without deduplicating**: each element appears consecutively according to its result multiplicity. This makes byte equality equivalent to multiset equality while retaining repeated elements. `NULL` is an ordinary element for membership and all set/bag operations; it is neither filtered nor treated as absence. A caller removes it explicitly by difference, intersection with a non-null universe, or a filter operation. It becomes special only for the separately named indexed/partial-information relations below.

“Multiset union” is conventionally ambiguous and the API must choose a name or document the multiplicity law:

- **join/max union:** `count(a ⊔ b, x) = max(count(a, x), count(b, x))`;
- **additive sum:** `count(a ⊎ b, x) = count(a, x) + count(b, x)` (with checked overflow/resource bounds).

Multiset intersection normally uses `min`, difference uses saturating subtraction `count(a − b, x) = count(a, x).saturating_sub(count(b, x))`, and symmetric difference commonly uses absolute difference. Expose `bag_union_max` and `bag_sum` rather than an ambiguous `bag_union`.

### Indexed subset / sparse refinement

The phrase “A null wherever B has values” admits two opposite-looking relations and must not ship unnamed:

1. **Sparse refinement (recommended meaning of indexed subset):**

   ```text
   A ⊑ B  iff  len(A) = len(B) and for every i,
                A[i] = NULL or A[i] = B[i].
   ```

   Here `A` is the less-defined sparse value and `B` fills some or all of its holes. Equivalently, every non-null value in `A` agrees with `B` at the same index. Example: `[x, NULL, z] ⊑ [x, y, z]`.

2. **Disjoint support:**

   ```text
   disjoint_support(A, B) iff for every i,
                              B[i] != NULL implies A[i] = NULL.
   ```

   This is the literal reading “A is null wherever B has values.” It is not ordinarily called subset: `[x, NULL]` and `[NULL, y]` satisfy it in both directions while neither refines the other.

If “indexed subset” instead means only `support(A) ⊆ support(B)`, decide whether overlapping non-null values must also be equal. For theorem data, requiring equality is safer; otherwise `[x]` would be an indexed subset of `[y]`. Suggested names are `is_sparse_refinement_of`, `has_support_subset_of`, and `has_disjoint_support_with`, leaving no argument-order ambiguity.

### Every byte string and malformed lengths

All CAS bytes remain valid **blobs**. Only lengths divisible by 32 are canonical `HashArray` encodings. Four query policies are possible:

| Policy | `len` for 33 bytes | element 1 | Benefit | Main problem |
|---|---:|---|---|---|
| Strict checked interpretation | error (`remainder = 1`) | error | No invented/lost bytes; matches Iroh canonicality | Callers must propagate `Result` |
| Zero-extend final chunk | 2 | one byte + 31 zeros | Total `O256` sequence | Collides semantically with a different 64-byte encoding; re-encoding changes address |
| Truncate suffix | 1 | absent | Simple prefix semantics | Silently ignores authenticated bytes; many blobs share semantics |
| Adjoin `PartialO256` | 2 logical elements | `Partial([u8; 1])` | Fully faithful and total | Every algebra must handle a non-O256 value that can never be a normal result |

Recommend strict checked interpretation first. It defines every checked query as either a value or a precise noncanonical-shape error and preserves injectivity of canonical encoding. Check the object's total byte length before answering even a range that happens to cover complete elements; otherwise a malicious/truncated suffix can be hidden by a successful prefix query. A low-level diagnostic API can separately expose `full_elements = byte_len / 32`, `remainder = byte_len % 32`, and raw suffix bytes.

If the logic later requires a value rather than an error for every byte string, prefer the explicit adjoined `PartialO256` model over zero-extension or truncation. Keep it outside `HashArray<O256>` and make canonicalization a visible fallible operation.

## Proposed API layering

### Layer 1: pure canonical value/view

Reuse the strongest part of PR #456 with a narrower base:

```rust
pub struct HashArrayRef<'a>(&'a [u8]); // invariant: len % 32 == 0
pub struct HashArray(Vec<u8>);         // same invariant

impl HashArrayRef<'_> {
    pub fn try_from_bytes(bytes: &[u8]) -> Result<Self, NonCanonicalLength>;
    pub fn len(&self) -> usize;
    pub fn get(&self, index: usize) -> Option<O256>;
    pub fn slice(&self, range: Range<usize>) -> Option<Self>;
    pub fn contains(&self, value: O256) -> bool;
    pub fn iter(&self) -> impl ExactSizeIterator<Item = O256> + DoubleEndedIterator;
}
```

Keep `SortedHashArrayRef`/`FlatSet` as checked refinements. Put bag and set algorithms in extension traits or free functions rather than making ambiguous `subset` methods on the base sequence.

### Layer 2: checked CAS query capability

The CAS extension operates on **addresses**, not assumed resident arrays:

```rust
trait HashArrayQuery {
    type Error;

    fn shape(&self, array: O256) -> Result<ArrayShape, Self::Error>;
    fn len(&self, array: O256) -> Result<u64, Self::Error>;
    fn get(&self, array: O256, index: u64) -> Result<Option<O256>, Self::Error>;
    fn slice(&self, array: O256, range: Range<u64>) -> Result<HashArray, Self::Error>;
    fn contains(&self, array: O256, value: O256) -> Result<bool, Self::Error>;
}
```

All methods return `NonCanonicalLength` for malformed source bytes. Use `u64` indexes/lengths at the storage boundary and checked conversion to `usize` inside an in-memory implementation. `slice` returns canonical bytes locally; a separate operation can admit it and return an address.

Default implementations require only the existing byte-oriented CAS `len`/`read` capability:

- `len`: fetch byte length, check `% 32`, divide;
- `get`: fetch/check total length, range-read exactly 32 bytes at checked `index * 32`;
- `contains`: stream 32-byte aligned ranges and scan;
- `slice`: range-read `start * 32 .. end * 32` after bounds checks.

This is the oblivious byte-cache implementation. It does not need to recognize arrays when objects are admitted.

### Layer 3: semantic relations and algebra

Use names that expose interpretation:

```rust
trait HashArrayRelations: HashArrayQuery {
    fn is_set_subset(&self, a: O256, b: O256) -> Result<bool, Self::Error>;
    fn is_subbag(&self, a: O256, b: O256) -> Result<bool, Self::Error>;
    fn is_sparse_refinement(&self, a: O256, b: O256) -> Result<bool, Self::Error>;
    fn has_disjoint_support(&self, a: O256, b: O256) -> Result<bool, Self::Error>;
}

trait HashArrayAlgebra: HashArrayRelations {
    fn singleton(&self, value: O256) -> Result<O256, Self::Error>;
    fn set_union(&self, a: O256, b: O256) -> Result<O256, Self::Error>;
    fn set_intersection(&self, a: O256, b: O256) -> Result<O256, Self::Error>;
    fn set_difference(&self, a: O256, b: O256) -> Result<O256, Self::Error>;
    fn set_symmetric_difference(&self, a: O256, b: O256) -> Result<O256, Self::Error>;

    fn bag_union_max(&self, a: O256, b: O256) -> Result<O256, Self::Error>;
    fn bag_sum(&self, a: O256, b: O256) -> Result<O256, Self::Error>;
    fn bag_intersection(&self, a: O256, b: O256) -> Result<O256, Self::Error>;
    fn bag_difference(&self, a: O256, b: O256) -> Result<O256, Self::Error>;
    fn bag_symmetric_difference(&self, a: O256, b: O256) -> Result<O256, Self::Error>;
}
```

Here algebra returns the `O256` address of a newly admitted canonical flat-set result. This should be explicit in documentation because a pure/read-only store cannot implement it without an admission/result sink. A cleaner split may be:

- pure functions return `HashArray` bytes;
- `HashArrayDerive<C: CasRead, W: CasAdmit>` computes, admits, and returns `O256`;
- a smart server exposes an equivalent atomic derive RPC.

Set and bag algebra always treat `NULL` as an ordinary member, including in `contains`, singleton construction, multiplicity counts, and every algebraic result. Indexed/sparse operations alone treat it as a hole. Never let the meaning switch implicitly based only on method internals.

V1 should have **no null-policy flags or strategy parameter**. There is one behavior to test and optimize: null is ordinary in set/bag algebra and special only in explicitly indexed partial-information operations. Possible later algebras could map null to the empty set/bag, or make null/idempotence interact specially with bag multiplicity, but those are different mathematical structures rather than runtime modes of the same operation. Defer them until a concrete consumer supplies laws and use cases; adding policy parameters now would multiply every default method, backend optimization, cache key, and conformance test.

### Future bind/flat-map shape (out of v1 scope)

After the map data structure exists, lists, sets, and bags are expected to gain monadic-style `bind`/`flat_map`: map each element to an addressed collection and combine the results using the collection's own flattening algebra. The current API should leave room for this without implementing it now:

- list bind concatenates mapped arrays in source order and preserves duplicates;
- set bind unions mapped sets and emits ascending, deduplicated normal form;
- bag bind combines multiplicities under a deliberately selected bag law and emits ascending multiplicity-preserving normal form.

This argues for keeping pure canonicalization/combination separate from CAS admission, and for naming collection semantics in traits rather than putting flags on one universal `flat_map`. It also reinforces the need to settle max-union versus additive bag sum before defining bag bind. No mapper protocol, map traversal, remote callback, or bind method belongs in the first hash-array/CAS extension.

### Layer 4: optimized/backend-specific implementation

A smart backend may override any default without changing results. It must validate that indexes correspond to the addressed canonical bytes—ideally when admitting the object, or lazily followed by caching—and fall back to byte verification when metadata is missing.

For SQLite, the suggested `(container, contained)` relation alone can accelerate distinct membership and set containment, but it loses order, multiplicity, null positions, and therefore cannot answer `get`, exact length, bag relations, slices, or sparse refinement. Use an ordinal relation as the faithful primary index:

```sql
CREATE TABLE object (
    id      INTEGER PRIMARY KEY,
    blake3  BLOB NOT NULL UNIQUE CHECK(length(blake3) = 32),
    bytes   BLOB NOT NULL
);

CREATE TABLE hash_array_element (
    container_id INTEGER NOT NULL REFERENCES object(id),
    ordinal      INTEGER NOT NULL CHECK(ordinal >= 0),
    contained    BLOB NOT NULL CHECK(length(contained) = 32),
    PRIMARY KEY (container_id, ordinal)
);

CREATE INDEX hash_array_member
    ON hash_array_element(container_id, contained);
```

If contained objects must exist locally, replace `contained BLOB` with `contained_id REFERENCES object(id)`; if arrays may link unavailable remote content, do not impose that foreign key. A derived distinct relation/view `(container_id, contained)` can serve set operations. Counts grouped by `(container_id, contained)` serve bags. The primary `(container_id, ordinal)` table preserves duplicates and all-zero holes and makes `get`/slice/indexed relations efficient.

Store `byte_len`, `array_status` (`canonical`, `noncanonical`, `unknown`), and perhaps element count as cached metadata if avoiding `length(bytes)` or supporting external blob storage. Metadata is an optimization, never authority: reconstructing ordered bytes and checking BLAKE3 against `object.blake3` is the audit path. Admission should update bytes and relation rows transactionally so queries cannot observe a partially indexed object.

For algebra returning `O256`, SQLite can perform relational set operations, order results by raw 32-byte value, concatenate, hash/admit, and return the resulting address. The oblivious backend must produce exactly the same ascending-deduplicated bytes.

## Adaptation options

### Option A — depend on and re-export Iroh's `HashSeq`

```rust
pub use iroh_blobs::hashseq::HashSeq;
```

Advantages: exact behavior; immediate access to protocol types.

Costs: `iroh-blobs` 0.98 already showed dependencies on `iroh`, `iroh-base`, `iroh-io`, `iroh-metrics`, `irpc`, Tokio, postcard, range collections, and more in addition to `bao-tree` ([docs.rs dependency listing](https://docs.rs/iroh-blobs/latest/src/iroh_blobs/hash.rs.html)). The current crate remains a protocol/store package, not a leaf data-types package. It also forces use of `iroh_blobs::Hash` at the iterator boundary and inherits an evolving pre-1.0 API.

Verdict: reject for the core abstraction.

### Option B — wrap Iroh's `HashSeq`

```rust
pub struct O256Array(iroh_blobs::hashseq::HashSeq);
```

Advantages: local API control and exact Iroh validation/storage.

Costs: retains the heavy dependency and requires conversions on every exposed element; offers little benefit because the invariant is only `len % 32 == 0`.

Verdict: reject except in an Iroh-specific adapter crate.

### Option C — repository-owned flat bytes type (recommended)

An illustrative surface, not a final design:

```rust
#[repr(transparent)]
pub struct O256Array(Bytes);

impl O256Array {
    pub fn from_bytes(bytes: Bytes) -> Result<Self, InvalidLength>;
    pub fn from_slice(bytes: &[u8]) -> Result<Self, InvalidLength>;
    pub fn as_bytes(&self) -> &[u8];
    pub fn into_bytes(self) -> Bytes;
    pub fn len(&self) -> usize;
    pub fn is_empty(&self) -> bool;
    pub fn get(&self, index: usize) -> Option<O256>;
    pub fn iter(&self) -> impl ExactSizeIterator<Item = O256> + DoubleEndedIterator + '_;
    pub fn split_at(&self, index: usize) -> (Self, Self); // cheap with Bytes
}

impl FromIterator<O256> for O256Array { /* concatenate raw arrays */ }
```

Advantages: exact Iroh bytes; tiny validation; ergonomic traits can match local usage; optional zero-copy slicing; no protocol coupling. Conversion to Iroh is simply byte conversion, and element conversion is `[u8; 32]`.

Costs: local responsibility for tests and API design; `bytes::Bytes` brings allocation/reference-counting semantics that may not be ideal everywhere.

Verdict: recommended.

### Option D — `Vec<O256>` as the owned form

Advantages: maximum conventional Rust ergonomics, mutable indexing, and no decoding copies on iteration. Because `O256` is transparent over `[u8; 32]`, the conceptual storage is contiguous 32-byte elements.

Costs: obtaining an Iroh byte slice from `&[O256]` without copying would require an unsafe cast, which conflicts with this workspace's `unsafe_code = "deny"`; serialization can still stream each element's bytes without an intermediate buffer. `Vec<O256>` also does not cheaply share or slice like `Bytes`.

Verdict: viable if mutation and typed in-memory access dominate. A useful design may have `O256Array(Vec<O256>)` as the ergonomic owned builder plus explicit encode/decode, but it is less naturally a zero-copy Iroh blob.

### Option E — borrowed and owned pair

```rust
pub struct O256Slice<'a>(&'a [u8]);
pub struct O256Array(Bytes);
```

The borrowed form validates once, then offers exact-size chunk iteration and indexing; the owned form dereferences or borrows as the view. This resembles `str`/`String` at the API level, without pretending `[O256]` and `[u8]` are safely interchangeable.

Verdict: best long-term ergonomics if the additional API surface is justified. Start with the owned form plus a simple view and avoid a large collection framework until usage reveals it.

## Serialization and interoperability policy

There are three distinct representations to specify:

1. **Canonical blob bytes:** always raw concatenated 32-byte values. This is the Iroh interoperability contract.
2. **Human-readable serialization:** choose deliberately. An array of 64-character hex strings is readable but not byte-identical to the blob. A single hex/base64 string is compact but visually opaque. Iroh's `HashSeq` itself provides no serde precedent.
3. **Binary serde:** `serialize_bytes` is compact in CBOR but may gain a length prefix in postcard/bincode; that is a container serialization, not the canonical blob bytes. Provide explicit `as_bytes`/`encode` APIs and never claim arbitrary serde output is the Iroh blob.

Element conversions should be representation preserving:

```rust
fn from_iroh(hash: iroh_blobs::Hash) -> O256 {
    O256::from_array(hash.into())
}

fn to_iroh(value: O256) -> iroh_blobs::Hash {
    iroh_blobs::Hash::from(value.into_bytes())
}
```

These should be optional and may deserve `TryFrom<O256>` if the API wants to enforce the semantic claim that the value is an unkeyed blob digest. At the byte level there is nothing to validate.

The safest semantic model is one of:

- store `Blake3Hash` elements internally and expose explicit conversion from/to `O256`; or
- store `O256`, name the type generically (`O256Array` rather than `IrohHashSeq`), and provide an Iroh adapter whose documentation requires each item to identify an ordinary BLAKE3 blob.

Given the stated theorem-prover requirement (“basically just a list of `O256`”), the second model is likely the least intrusive. A distinct validated newtype can be introduced later if Iroh fetchability becomes a static invariant.

## Dependency and feature implications

- **Upstream `blake3`:** already present; sufficient for array-root hashing and current local subtree work.
- **`bytes`:** already used elsewhere in the workspace but not currently by `covalence-lib-hash`. Adding it directly gives cheap clones/slices and direct Iroh `Bytes` interchange. If keeping the leaf hash crate minimal matters more, use `Box<[u8]>`/`Vec<u8>` or place the collection in an adjacent crate.
- **`iroh-blobs`:** keep optional and outside the core crate. Its latest dependency graph and pre-1.0 churn are disproportionate to a 32-byte chunk invariant.
- **`bao-tree`:** irrelevant to the list representation. Adopt only when partial verified reads or Iroh-compatible outboards are needed.
- **`serde`:** implement independently of the element's existing serde because serializing a sequence of `O256` values currently produces a sequence of byte arrays, not the canonical flat blob.
- **wasm/no-std:** `bytes` supports broad targets, but the current local hash crate already uses `std` APIs. Avoid tying the collection to Tokio or Iroh so browser builds remain modest.

## Risks

1. **Conflating representation with meaning.** Random or keyed `O256` values fit the wire layout but are not Iroh blob links. This is the most important design risk.
2. **Accidentally inventing framing.** A count, version byte, serde length prefix, or namespace marker would make the bytes no longer an Iroh HashSeq. Such metadata belongs outside the canonical blob.
3. **Format-tag loss.** When publishing through Iroh, the root must be paired with `BlobFormat::HashSeq`; the same hash tagged `Raw` has different traversal behavior.
4. **Resource limits.** Decoding untrusted bytes is structurally cheap, but allocation and `usize` arithmetic still need normal length limits at IO boundaries.
5. **API overgrowth.** Mirroring all of `Vec` over an encoded buffer can create awkward mutation semantics. Prefer immutable sequence operations and an explicit builder if contiguous bytes are the canonical owned form.
6. **Serde ambiguity.** Human/binary serde formats and canonical content bytes must be separately documented and tested.
7. **Upstream protocol churn.** Current `iroh-blobs` explicitly warns about production readiness. Isolating conversions protects the theorem-prover core from that churn.
8. **Empty array semantics.** The empty array is valid and hashes to BLAKE3(empty). Confirm that local higher-level formats do not require at least one link or reserve the empty root.
9. **Relation-name ambiguity.** A bare `subset` or `union` is insufficient when sequence, bag, set, and indexed partial-information readings coexist. Encode the reading and argument direction in names.
10. **Index drift.** An optimized relation table that is not transactionally tied to canonical bytes can return correct-looking but unauthenticated answers. Rehashable reconstruction and status metadata are required.

## Suggested conformance tests

- canonical value construction rejects raw buffers of lengths `1`, `31`, `33`, and `63`; accepts `0`, `32`, `64`; checked CAS queries return the specified `NonCanonicalLength` rather than pretending malformed blobs are absent;
- `collect::<O256Array>()` produces exact concatenation in input order;
- `len`, `get`, forward/reverse iteration, consuming iteration, split/slice, and front-pop agree with a reference `Vec<O256>`;
- all-zero, all-`0xff`, and arbitrary hashes round-trip bytes without canonicalization;
- the array root equals `blake3::hash(array.as_bytes())` and `O256::from_bytes(array.as_bytes())`;
- optional Iroh bridge round-trips `O256Array -> iroh HashSeq -> O256Array` byte-for-byte;
- Iroh integration marks the root `BlobFormat::HashSeq`, including the empty case;
- serde tests distinguish the chosen container serialization from `as_bytes()`;
- property tests cover arbitrary lists and arbitrary invalid trailing byte counts.
- set operations always emit ascending, deduplicated bytes and agree with a reference `BTreeSet`, including when `NULL` is present;
- bag operations always emit ascending bytes with multiplicity and agree with a reference count map; test max-union separately from additive sum;
- `NULL` survives `contains`, singleton, set union/intersection, and bag algebra exactly like any other O256;
- sparse refinement treats `NULL` as a hole and verifies argument direction with `[x, NULL] ⊑ [x, y]`, while disjoint support is tested as a separate relation;
- byte-scan and SQLite-indexed implementations return identical values and identical result addresses for every operation, including duplicates and null holes.

## Open design questions

1. Is “every element is an unkeyed BLAKE3 blob hash” an invariant the Rust type must enforce, or is `O256` intentionally opaque enough that only the transport adapter cares?
2. Is the primary value immutable/persistent, mutable during theorem construction, or usually borrowed from CAS bytes? That decides between `Bytes`, `Vec<O256>`, and an owned/view pair.
3. Should equality/order/hash compare the raw encoded bytes? That naturally yields lexicographic element order because each element has fixed width.
4. Should indexing return `O256` by value (cheap, safe, Iroh-like) or a borrowed typed reference? The latter is difficult without unsafe layout casting and probably not worth it for 32 bytes.
5. Is cheap prefix removal important? Iroh exposes `pop_front` because `Bytes` slicing makes it cheap, but a theorem prover may prefer an iterator/cursor that leaves the value immutable.
6. Should the empty sequence be valid at every layer?
7. Where should the type live? `covalence-lib-hash` gives natural access to `O256`; a separate data crate keeps `bytes` and richer collection policy out of a primitive crate.
8. What are the canonical human-readable and serde forms, if any? A theorem-prover syntax may matter more than matching Iroh's individual hash text syntax.
9. Is the array itself always addressed by ordinary BLAKE3, or should Covalence context-keying/domain separation apply? Iroh interoperability requires ordinary BLAKE3 for the blob address.
10. Will nested arrays be traversed as Iroh HashSeq children? If so, the external `BlobFormat` of each referenced object is not encoded per link, so higher-level schema must supply child interpretation.

## Bottom line

Iroh's durable contribution here is a wire convention, not a collection library: `N * 32` raw bytes plus an out-of-band `HashSeq` format tag. The existing local `O256` and upstream `blake3` implementation already satisfy the element and hashing requirements. Reuse PR #456's borrowed/owned normal-form split and checked refinements, but update it with total checked behavior for malformed blobs, explicitly separated sequence/bag/set/indexed semantics, canonical set and multiset results, and a CAS capability layer whose byte-scan and indexed backends are observationally identical. Adapt Iroh at the boundary; avoid adopting either the retired BLAKE3 fork or the full blobs protocol as a foundational dependency.
