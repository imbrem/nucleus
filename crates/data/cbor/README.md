# CBOR data

`covalence-data-cbor` owns Nucleus's reusable CBOR value models. The `drisl`
module is the checked, float-free ATProto profile: signed 64-bit integers,
string-keyed maps, canonical historical key order, and fixed-width CID links.
SHA-256 links follow ATProto; BLAKE3 is an explicit Nucleus policy extension.

The implementation wraps `serde_ipld_dagcbor` for strict deterministic
DAG-CBOR parsing, then applies the smaller DRISL value and CID policy. Schema
crates should translate their records to and from `drisl::Value`; they should
not implement CBOR canonicality themselves.

For wire debugging, convert standard input between ATProto JSON and DRISL:

```console
cargo run -p covalence-data-cbor --example drisl-json -- to-cbor < object.json > object.cbor
cargo run -p covalence-data-cbor --example drisl-json -- to-json < object.cbor
```

Add `--nucleus` to accept BLAKE3 CIDs. JSON is not canonical and is never
hashed; byte strings and links use the ATProto `$bytes` and `$link` wrappers.

The executable specification is in `lean/Nucleus/Nucleus/Cbor/Atproto/`.
