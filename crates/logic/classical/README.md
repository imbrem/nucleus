# Classical kernel

The running kernel stores formulas in one private arena of 32-bit words. Live
headers contain a constructor tag, size class, and reference count. A separate
length index avoids rescanning zero-terminated payloads during ordinary edits.
`Formula` is an untrusted construction value; `FormulaView` and `SequentView`
borrow checked storage without building a second syntax tree.

`Checked` establishes structural validity. Only the sealed `Theorem` and checked
kernel rules establish theorem facts. Path mutations copy shared ancestors as
needed and update owned storage directly. Reference-counted reclamation returns
unused blocks to intrusive size-class free rings. Rejected rewrite applicability
checks precede path copying. These operations are implemented under
`src/tagged/runtime/` and `src/tagged/kernel/`.

The only supported wire format is `io.github.imbrem.nucleus.classicalArena` in
`crates/data/classical`. It records sequents as flat preorder formula tokens,
independent of word size, allocation addresses, free rings, and reference counts.
The decoder accepts the exact current schema; there is no version dispatch or
legacy decoder. `lexicons/io/github/imbrem/nucleus/classicalArena.json` describes
that format. Changing the discriminator breaks older serialized objects.

Lean's `Tagged/Runtime/{Shared,SharedRuntime,SharedKernel,LengthIndex,SemanticWire,
TokenWire}.lean` models the running design's representation and semantic
contracts. These are model-level proofs, not mechanically verified Rust. In
particular, a theorem parameterized by an allocator or constructor contract does
not establish that the Rust implementation satisfies it.

`covalence_data_array::table::Table<H>` is a separate reusable word-array data
structure. Its default length/tag/sticky-sharing header and intrusive allocator
are modeled in `Classical/Array/Table.lean`. It is not connected to the running
classical arena and introduces no classical wire format or theorem capability.
Migrating the kernel to that layout, sticky sharing, or an embedded root array
requires a further change to its ownership operations and correspondence proofs.
