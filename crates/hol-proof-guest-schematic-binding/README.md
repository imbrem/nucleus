# HOL schematic-binding proof guest

This untrusted no-WASI component constructs a beta equality over a free type and free term,
simultaneously instantiates that term, abstracts the replacement variable, and finally
instantiates the free type with `bool`. Its checked result is
`(lambda y:bool. (lambda z:bool. z) y) = (lambda y:bool. y)`.

Every guest value is an opaque recipe resource. The component has no database, Nucleus,
filesystem, network, cryptography, or signing access. Guest success only seals a recipe; the host
must replay it through a fresh checked HOL connection before exporting or signing a database.

Build the component explicitly:

```sh
cargo component build --locked -p covalence-hol-proof-guest-schematic-binding \
  --target wasm32-unknown-unknown
```

Run it through the hash-selected terminal or browser integration using its exact component O256.
