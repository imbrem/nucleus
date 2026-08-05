# HOL first-class conversion proof guest

This untrusted no-WASI component asks its host to prove
`(lambda x:bool. x) ((lambda x:bool. x) true) = true`. It composes checked beta conversions with
conversion reflexivity, application congruence, and transitivity before explicitly turning the
closed conversion into an equality theorem.

The component holds only opaque recipe resources. It has no database, Nucleus, filesystem,
network, cryptography, or signing access. Guest success only seals a recipe; the host must replay
it through a fresh checked HOL connection before it may export or sign a database.

Build explicitly with:

```sh
cargo component build --locked -p covalence-hol-proof-guest-conversions \
  --target wasm32-unknown-unknown
```
