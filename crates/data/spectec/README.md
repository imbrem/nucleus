# SpecTec data

`covalence-data-spectec` owns reproducible, untrusted inputs for translating
the WebAssembly specification. It does not assign semantics to SpecTec or
create theorem facts.

The first bundle pins the official `wg-3.0` sources and the elaborated IL
S-expression emitted by upstream SpecTec 0.5. The canonical DRISL manifest
records exact source order, raw SHA-256 CIDs, generator arguments, AST metrics,
and license files. Its ATProto JSON form is for inspection only.

Normal builds consume the checked-in bundle without OCaml or network access.
Regenerate it only from the pinned upstream checkout:

```console
cargo run -p covalence-data-spectec --example generate-wasm3
```

Successful parsing proves only that the artifact has recognized syntax. HOL
validity and fidelity to the SpecTec source are separate checked obligations.

`IlDocument` additionally inventories every top-level declaration and every
member of a recursive group. It is the exhaustive source side of the
semi-trusted correspondence API in `covalence-nucleus-spectec`; it still assigns
no semantics and creates no theorem facts.
