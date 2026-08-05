# HOL eta proof guest

This untrusted no-WASI component asks its host for the closed eta theorem
`(lambda x:bool. (lambda y:bool. y) x) = (lambda y:bool. y)` through opaque recipe
resources. It has no database, Nucleus, filesystem, network, cryptography, or signing access.
Guest success only seals a recipe; the host must replay it through a fresh checked HOL connection
before it may export or sign a database.

Build the component explicitly:

```sh
cargo component build --locked -p covalence-hol-proof-guest-eta \
  --target wasm32-unknown-unknown
```

Run the component through the hash-selected terminal integration by supplying its exact O256 and
component path to `nucleus --hash-wasm-hol`.
