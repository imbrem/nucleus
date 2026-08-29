# C proof micro-demo

This is a deliberately small C implementation of the standard asynchronous
Nucleus proof component world. It implements address, text, numeric-index, and
owned byte-resource selectors and returns a host-created empty checked kernel.

The component is still untrusted: C code receives and returns opaque host
resources, while only the host kernel can construct theorem facts. The demo
performs an asynchronous CAS fetch and uses the generated subtask and callback
API when that fetch suspends. The same mechanism can drive other asynchronous
imports without changing the WIT world.

The byte-selector entry point demonstrates owned-resource cleanup explicitly:
it copies the borrowed contents needed for dispatch and drops the incoming
owned byte handle on both success and rejection. Every entry point likewise
drops an incoming kernel on rejection and transfers it exactly once on success.

From the repository development shell, build and run it with:

```console
pnpm --filter @nucleus/nucleus build:proof-c-demo
cargo run -p covalence-nucleus --example load-proof -- \
  target/wasm32-wasip1/covalence_proof_c_demo.component.wasm
cargo test -p covalence-proof-c-demo-test --test proof_c -- --ignored
```

The build generates C bindings from `wit/proof/proof.wit` rather than checking
generated glue into the repository. `wit-bindgen`, the WASI C compiler, and
`wasm-tools` are therefore build tools rather than runtime dependencies.
