# HOL beta proof guest

This untrusted component asks its host to build the closed-beta demo through opaque recipe
resources. It has no database, Nucleus, filesystem, network, cryptography, signing, or WASI
access. Guest success is only a recipe request; the host must replay it through a fresh checked
HOL connection before it can export or sign a database.

Build the no-WASI component explicitly:

```sh
cargo component build --locked -p covalence-hol-proof-guest-beta \
  --target wasm32-unknown-unknown
```

Run it through the bounded native host and caller-owned REPL integration. The
output directory must not already exist; the command never overwrites files:

```sh
cargo run -p covalence-bin-nucleus -- --wasm-hol \
  target/wasm32-unknown-unknown/debug/covalence_hol_proof_guest_beta.wasm \
  signed-beta-artifact
```
