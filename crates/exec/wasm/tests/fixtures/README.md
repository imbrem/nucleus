# Wasm execution fixtures

`add.wasm` is the exact 41-byte core module printed in `add.wat`. The binary,
not the WAT or a compiler invocation, is the fixture used by tests.

- SHA-256: `f61fd62f57c41269c3c23f360eeaf1090b1db9c38651106674d48bc65dba88ba`
- BLAKE3: `801ae5deb92905065f7f0baedcbec41ebf1c4f2206904f7da319a7e5f24e29a4`

It exports `add : i32 i32 -> i32` and contains only `local.get` and
`i32.add` instructions.
