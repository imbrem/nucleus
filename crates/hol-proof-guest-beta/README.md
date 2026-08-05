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

`covalence_repl::run_hol_proof_component` runs the component with explicit Wasmtime limits,
replays its opaque recipe through a fresh checked HOL connection, and returns a signed artifact.
The caller owns any persistence or import policy; this layer never writes an artifact path.

Run it directly through the caller-owned terminal integration. The output directory must not
already exist, and the command never replaces either artifact file:

```sh
cargo run -p covalence-bin-nucleus -- --wasm-hol \
  target/wasm32-unknown-unknown/debug/covalence_hol_proof_guest_beta.wasm \
  signed-beta-artifact
```

The hash-selected terminal and browser demos additionally pin these exact component bytes before
compilation and exercise signed import into a retained receiver. Follow the
[end-to-end quickstart](../../docs/hash-selected-hol-quickstart.md) for those preferred flows.
