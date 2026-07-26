# Incremental Merkle cache sketch

This sketch separates the trusted CV cache from every source of file bytes.
Readers, owned buffers, remote stores, and SQLite VFS adapters are higher-level
drivers. The core only records tree geometry, chaining values, and dirty state.

## Proposed surface

```rust
pub struct LeafIndex(pub u64);
pub struct Retention {
    pub start: u8,
    pub skip: u8,
}

pub struct DynamicGeometry {
    pub bytes: u64,
    pub retention: Retention,
}

pub struct StaticGeometry<
    const BYTES: u64,
    const START: u8,
    const SKIP: u8,
>;

pub struct NewCvs<I>(pub I);

pub struct LeafError<E> {
    pub index: LeafIndex,
    pub source: E,
}

pub struct CvTree<G, S> {
    // Geometry and CV/dirty-state storage only.
}

pub struct CleanTree<G, S>(CvTree<G, S>);

impl<G, S> CvTree<G, S> {
    pub fn dirty(&mut self, leaf: LeafIndex) -> Result<(), DirtyError>;
    pub fn dirty_range(
        &mut self,
        leaves: Range<LeafIndex>,
    ) -> Result<(), DirtyError>;

    pub fn update<I>(
        &mut self,
        cvs: NewCvs<I>,
    ) -> Result<UpdateReport, UpdateError>
    where
        I: IntoIterator<Item = (LeafIndex, Blake3Cv)>;

    pub fn normalize(&mut self) -> Result<(), StoreError>;
    pub fn refill_frontier(
        &self,
    ) -> impl Iterator<Item = LeafIndex> + '_;
    pub fn supply<I>(
        &mut self,
        cvs: NewCvs<I>,
    ) -> Result<SupplyReport, UpdateError>
    where
        I: IntoIterator<Item = (LeafIndex, Blake3Cv)>;

    pub fn try_root_with<E>(
        &mut self,
        leaf: impl FnMut(
            LeafIndex,
        ) -> Result<Blake3Cv, E>,
    ) -> Result<Blake3Hash, RebuildError<E>>;

    pub fn root_with(
        &mut self,
        leaf: impl FnMut(LeafIndex) -> Blake3Cv,
    ) -> Result<
        Blake3Hash,
        RebuildError<Infallible>,
    >;
}
```

`LeafError<E>` attaches the requested index to callback failures. A failed
callback leaves that leaf and its ancestors conservatively dirty, so retrying is
safe. The infallible API removes only the impossible callback-error case; store
and geometry errors remain possible.

`CleanTree` exposes `update` but no dirtying methods. Conversion from
`CleanTree` to `CvTree` is infallible. Conversion back checks the canonical
clean invariant. An incomplete update returns the dirty tree plus its missing
frontier instead of silently producing a clean wrapper.

## Geometry

Both static and dynamic configurations implement one sealed geometry trait.
The geometry includes logical byte length, because the final partial BLAKE3
chunk affects its CV.

Chunk CVs are level zero. Retained levels are:

```text
start + k * (skip + 1)
```

The lowest retained slot covers `2^start` chunks. Omitted levels are rebuilt
temporarily. The dirty/refill API still addresses actual chunk leaves rather
than retained slots.

Only dynamic geometry supports resizing:

```rust
resize(new_bytes)
append(new_bytes, NewCvs)
truncate(new_bytes)
truncate_clone(new_bytes)
```

These operations preserve the completed left forest and invalidate the right
frontier. Changing a partial final chunk requires a replacement CV.

## Dirty normal form

Dirty lowest-retained entries initially form a singly-linked list rooted in the
tree header. Each dirty internal entry is a reserved 32-byte marker containing
a two-bit `maybe_clean` mask:

- bit zero: the logical left half may remain clean;
- bit one: the logical right half may remain clean;
- `00`: the complete subtree may be dirty.

Normalization drains the linked list. For each leaf it walks toward the root,
clearing the corresponding child bit. It stops once that bit was already
clear. When both bits are clear, the entry becomes the fully-zero marker.
After normalization the linked list is empty and all dirty state is represented
by internal masks.

Rebuilding starts at the root:

- a clean CV returns immediately;
- a mask recursively rebuilds only cleared halves;
- a fully-zero node rebuilds both halves;
- repaired children are combined bottom-up and replace the marker.

The mask remains binary when levels are skipped: it describes two logical
halves. A missing intermediate CV is synthesized from lower retained nodes.

Exact reserved marker encodings make accidental clean-CV collisions roughly
`2^-254` or smaller. Recognizing only a 128-bit zero prefix would instead make
stale-root correctness probabilistic at approximately `2^-128` per relevant
test. Corrupt cache storage can forge either encoding, so independently trusted
roots remain necessary when cache integrity matters.

## Updates and async refill

`update(NewCvs)` normalizes, installs supplied actual chunk CVs, masks affected
ancestors, and repairs every node for which the batch is sufficient. With
`start > 0`, one replacement chunk is generally insufficient to reconstruct
its lowest retained group; the report exposes remaining leaves.

Async is an adapter over:

```text
normalize -> refill_frontier -> concurrent fetch -> supply
```

This avoids async traits and avoids holding `&mut CvTree` across awaits. The
same frontier can fetch local blocks, HTTP ranges, object-store fragments, or
SQLite pages.

## BLAKE3 root caveat

A single BLAKE3 chunk CV cannot be converted into its standard root digest:
the ROOT flag is applied to the chunk output state, not retrospectively to the
CV. The implementation must either retain richer final-leaf output metadata,
ask the callback for that evidence, or explicitly restrict the CV-only root API
to inputs spanning at least two chunks.

## Validation plan

Property tests should compare every small `start`/`skip` geometry with one-shot
BLAKE3 through random point/range invalidation, partial refill failure and
retry, batch update, append, truncate, and truncate-clone. Additional invariants
include idempotent normalization, monotonically clearing masks, exactly-once
linked-list reachability, no markers in `CleanTree`, and no clean stale root
after an interrupted operation.
