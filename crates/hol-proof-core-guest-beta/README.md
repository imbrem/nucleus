# Core-Wasm beta recipe guest

This is the capability-free alternative to the component/resource guest. It is an ordinary core
WebAssembly module with no imports. The ABI is intentionally tiny:

- export linear memory as `memory`;
- export `covalence_owned_bytes: () -> i64`;
- interpret the low 32 bits as an unsigned byte pointer and the high 32 bits as an unsigned byte
  length in that memory.

The host instantiates with no imports, invokes the function once, enforces a 64 KiB output bound,
checks `pointer + length` for overflow and against the post-call memory size, then copies the exact
bytes. Extra exports carry no host capability and are ignored. The copied bytes remain untrusted:
the existing canonical decoder and checked Nucleus replay are the only route to a theorem or signed
database.

The native prototype bounds encoded module bytes before Wasmtime compilation and fuel/meters the
instantiated module. The encoded-size bound is not itself a strict bound on compiler CPU or memory;
arbitrary-module compilation should move into a disposable, externally limited worker/process
before this becomes an exposed service.

The guest SDK and this guest have no Nucleus, database, filesystem, network, clock, randomness,
cryptography, or signing-key dependency.

Build the guest with:

```sh
cargo build --locked -p covalence-hol-proof-core-guest-beta --target wasm32-unknown-unknown
```

The repository-level artifact check builds that actual Rust guest without committing a `.wasm`,
validates the module, executes it through Proton's no-import runtime, compares its output with the
existing canonical closed-beta recipe, then decodes and replays it through a fresh checked kernel:

```sh
tools/check-core-wasm-beta-guest.sh
```

The underlying configured integration test accepts
`COVALENCE_CORE_WASM_BETA_GUEST=/path/to/guest.wasm`; without that variable it is a no-op so normal
host-only `cargo test` does not require a prebuilt cross-target artifact.
