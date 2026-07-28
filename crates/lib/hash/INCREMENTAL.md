# Dynamic incremental Merkle cache

The first implementation deliberately supports one geometry: a runtime byte
length divided into fixed-width leaves. It stores the complete canonical tree
in contiguous memory. Retention depths, skipped levels, packed dirty lists,
static geometry, and external storage are follow-up work.

## Flat layout

For `n` leaves, allocate exactly `2n - 1` opaque 256-bit nodes. The layout is
the recursive in-order traversal of the canonical tree:

- leaf `i` is always slot `2i`;
- split a non-leaf span using the scheme's canonical left-subtree size;
- place the parent in the slot between its flattened children.

For three BLAKE3 chunks the vector is:

```text
[leaf 0, parent 0..2, leaf 1, parent 0..3, leaf 2]
```

This uses every slot for non-power-of-two inputs. A conventional complete heap
would need padding and special absent-child behavior, while post-order storage
would make leaf lookup less direct.

The node vector is `Vec<Opaque<32>>`. A parallel validity vector distinguishes
cached values from missing values without reserving a hash value as a sentinel.
The meaningful root output is cached separately because BLAKE3 root
finalization is not an ordinary parent CV.

## Updates and rebuilding

`dirty(leaf)` invalidates the leaf and its ancestors. A range initially repeats
that operation for each leaf; range summaries can be added after profiling.

`update` writes precomputed leaf evidence directly into its stable even-numbered
slot. `root_with` walks the canonical tree recursively:

1. return a valid cached node;
2. request an invalid leaf from the caller;
3. combine invalid internal nodes bottom-up;
4. finalize the top child pair as the root.

The source callback may fail. Errors retain the exact leaf index, and values
computed before the failure remain cached for a retry.

## Resizing

Leaf slots remain stable when the logical length changes. Resizing copies valid
leaves into a new exact-size vector and invalidates all internal nodes.
It also invalidates the old/new right-edge leaf because the final partial leaf
may represent a different byte range even when the leaf count does not change.

This conservative `O(n)` resize is intentionally simple. A later implementation
may preserve canonical complete subtrees after the semantics and workloads are
established.

## Future work

- use a packed validity bitset;
- add efficient range invalidation summaries;
- derive compact and streaming proofs from the same span/index arithmetic;
- add configurable retained levels only when memory measurements justify them;
- generalize storage after a second Merkle scheme validates the trait boundary.
