# Direct browser HOL beta guest spike

This is a deliberately narrow sibling alternative to executing the Component
Model `hol-proof-guest.wit` contract in a browser. The guest is an ordinary
core-Wasm wasm-bindgen module. It receives one opaque JavaScript
`WebHolProofPlan`, appends the closed-beta recipe, and returns the selected
namespace offset.

It receives no database, Nucleus connection, filesystem, network, cryptography,
or signing operation. Recipe offsets are forgeable integers, so neither the
guest nor wasm-bindgen is trusted: the host structurally seals the graph, then
decodes it again and replays it through a fresh Nucleus HOL connection before
signing.

The artifact is a **two-file wasm-bindgen module**, not a standalone dynamically
loadable `.wasm`: its generated JavaScript glue defines the core-Wasm imports
which forward calls to `WebHolProofPlan`. Run the complete Chromium spike with:

```sh
pnpm --filter @nucleus/nucleus test:web-beta-spike
```

The test runs the glue, guest, and plan collector in a disposable Worker and
transfers only canonical recipe bytes to the separate key-holding kernel realm.
That keeps guest JavaScript from reaching or monkey-patching the live kernel.

> **Capability warning:** a disposable Worker is a key-isolation boundary, not
> an ambient-capability sandbox. Uploaded wasm-bindgen glue still has browser
> network, storage, timers, and Worker APIs. This alternative cannot claim the
> Component guest's current “no filesystem/network” property without a second
> isolation mechanism.

The spike intentionally implements only the beta recipe surface. Expanding it
to every HOL operation would duplicate the WIT API by hand; generation from a
single operation description should be a prerequisite for selecting this
architecture.

## Measured comparison

For the same release-mode closed-beta guest on this branch:

| carrier                |     Wasm | JavaScript | notes                                      |
| ---------------------- | -------: | ---------: | ------------------------------------------ |
| direct wasm-bindgen    |   26 KiB |    8.2 KiB | two uploaded files; 9.2 KiB + 2.1 KiB gzip |
| Component Model source |   31 KiB |          — | directly executable by native Wasmtime     |
| jco 1.27.0 output      | 25.1 KiB |    204 KiB | AOT output; 30.8 KiB gzip for JavaScript   |

The beta-only `WebHolProofPlan` wrapper also grows the release host by 48,005
Wasm bytes and 11,723 JavaScript bytes (10,253 + 1,488 bytes gzip). A generated
full 48-method surface would be larger.

The size difference is not the deciding factor. Direct wasm-bindgen duplicates
the WIT contract as Rust extern declarations and host methods, and its generated
JavaScript import names are versioned implementation details. jco preserves the
single WIT contract but requires a generated TypeScript host adapter for all 48
operations and produces AOT files for a particular component; browser
`WebAssembly` still cannot instantiate an arbitrary uploaded Component Model
binary directly.

If this sibling were pursued, keep each stage as a separate stacked PR:

1. Enable the existing canonical recipe sealer on wasm32 and expose only
   untrusted recipe bytes; no guest runtime or signing change.
2. Generate `WebHolProofPlan` and guest declarations from the same operation
   description as WIT; do not maintain two hand-written full rule surfaces.
3. Run collector and uploaded glue in a disposable Worker with node/byte/time
   bounds, transfer only canonical bytes, and document its remaining browser
   ambient capabilities.
4. Decode again in the key-holding Worker, replay through a fresh HOL
   connection, sign, detached-validate, and import through the ordinary path.
5. Add hash pinning and REPL upload UX for the exact JavaScript/Wasm pair, plus
   negative tests for wrong hashes, malformed plans, Worker timeout, prototype
   mutation, and attempts to send anything except bounded recipe bytes.

Until stages 2 and 3 have satisfactory answers, the simpler stable core-Wasm
byte ABI should remain the MVP direction.
