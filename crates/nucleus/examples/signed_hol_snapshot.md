# Signed HOL snapshot demo

This example proves and persists the closed beta theorem
`|- (\x:bool. x) true = true`, exports the exact SQLite image, signs its
schema-qualified hash, and consumes it through a second HOL connection.

Run it from the workspace root:

```sh
cargo run -p covalence-nucleus --example signed_hol_snapshot -- /tmp/hol-demo
```

It writes `beta.sqlite3` and a human-readable `beta.attestation.txt`. The
attestation format is intentionally a demo artifact, not a stabilized wire
format.

The receiving half keeps five boundaries visible:

1. **Authentication** verifies the exact byte hash, public-key identity, and
   Ed25519 signature over `(schema, image)`; it establishes no trust.
2. **Detached validation** checks SQLite and the current HOL schema in a
   disposable connection.
3. **Trust and acceptance** are explicit connection-local policy decisions.
4. **Import** records inert hash-first coordinates, persistent audit evidence,
   and a whole-namespace alias without fetching anything.
5. **Theorem authority** remains scoped to the immutable imported reader. An
   imported judgement is not convertible to a local LCF theorem capability.

The database stores canonical kernel state, including the explicitly persisted
judgement, but not the beta proof recipe. The recipe is ordinary consumer code
in the example and remains outside the trusted core.
