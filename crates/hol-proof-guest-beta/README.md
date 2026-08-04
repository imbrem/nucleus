# HOL beta proof guest

This untrusted component asks its host to build the closed-beta demo through
opaque recipe resources. It has no database, Nucleus, filesystem, network,
cryptography, signing, or WASI access.

Build it with the no-WASI target explicitly:

```sh
cargo component build --locked -p covalence-hol-proof-guest-beta \
  --target wasm32-unknown-unknown
wasm-tools validate \
  target/wasm32-unknown-unknown/debug/covalence_hol_proof_guest_beta.wasm
```

A bare `cargo component build` selects `wasm32-wasip1` in this workspace and
adds imports which the deliberately no-WASI host rejects.

Run the native host and write the signed database artifact with:

```sh
cargo run -p covalence-repl --example wasm_signed_beta -- \
  target/wasm32-unknown-unknown/debug/covalence_hol_proof_guest_beta.wasm \
  signed-beta-artifact
```

Guest success is not proof authority. The host replays the recipe through a
fresh checked HOL connection and signs only after replay, persistence, and
namespace export all succeed.
