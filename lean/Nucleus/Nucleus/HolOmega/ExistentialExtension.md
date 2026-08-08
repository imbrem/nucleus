# Primitive existential raw/store extension

Primitive existential types are present in the intrinsic `Kernel`, but the
persisted vocabulary documented in `crates/nucleus/src/hol/semantics.txt` does
not currently assign them tags.  The raw constructors below are therefore an
explicit extension; they must not be decoded from any existing tag:

```text
tyEx RK A
tmPack RK A X t
tmUnpack RK A B k p
```

`tmUnpack` checks its continuation as

```text
(RK :: Δ); (A :: Γ.liftTy) ⊢ k : B.liftTy
```

so its answer type cannot depend on the hidden witness.  Its denotation uses
`Universe.exEquiv`, hence is a genuine dependent sum rather than an encoding
through `tyAll`.

The package beta law (`UNPACK_PACK`) substitutes the witness type and then the
payload into the continuation.  The package eta law (`PACK_ONTO`) unpacks a
package and immediately repacks its hidden witness and payload.  It does not
assert that one raw witness works uniformly for a package in every semantic
environment.
