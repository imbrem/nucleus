# Hash-selected HOL proof quickstart

This demo builds a no-WASI WebAssembly component, admits it under its exact BLAKE3-256 content
address, replays its requested proof through the checked HOL kernel, signs the resulting SQLite
snapshot, and imports that snapshot into a caller-owned HOL connection.

The component is not trusted with a database, signing key, or kernel connection. In the browser
flow, its bytes remain provisioned at the native kernel; the page sends only the component hash.

## Set up

Enter the repository's development shell and install the locked JavaScript dependencies:

```sh
nix develop
pnpm install --frozen-lockfile
```

Build the no-WASI guest and compute its exact O256 address:

```sh
cargo component build --locked -p covalence-hol-proof-guest-beta \
  --target wasm32-unknown-unknown
component=target/wasm32-unknown-unknown/debug/covalence_hol_proof_guest_beta.wasm
digest="$(b3sum --no-names "$component")"
```

`O256` in these commands means the 32-byte unkeyed BLAKE3 digest rendered as 64 lowercase hex
characters. The native kernel independently checks this digest before compiling the component.

## Terminal: export a signed database

Choose an output directory which does not already exist:

```sh
cargo run -p covalence-bin-nucleus -- \
  --hash-wasm-hol "$digest" "$component" signed-beta-artifact
```

Successful output includes `imported_theorem 0 8` and paths to `proof.sqlite` and
`attestation.txt`. The command proves, persists, signs, validates, and imports before writing the
two files. It never replaces an existing directory or artifact.

The exported database is ordinary SQLite and can be inspected without changing its signed bytes:

```sh
sqlite3 -readonly signed-beta-artifact/proof.sqlite '.tables'
```

Treat the SQLite file and attestation as a pair. Any modification changes the image hash and
invalidates the signature recorded in `attestation.txt`.

## Terminal: keep using the imported receiver

Start the interactive REPL:

```sh
cargo run -p covalence-bin-nucleus
```

At its prompt, substitute the printed value of `$digest` for `DIGEST`:

```text
.hol hash-wasm DIGEST target/wasm32-unknown-unknown/debug/covalence_hol_proof_guest_beta.wasm signed-beta-repl
.connections
.hol reflexivity false
.quit
```

The hash-selected command retains and selects the imported HOL receiver, so subsequent HOL recipes
run on that ordinary connection. The browser demo below additionally exposes an explicit read-only
reread of the imported theorem.

## Browser: run the native guest by hash

Build and serve the browser package in one terminal:

```sh
pnpm --filter @nucleus/nucleus build
pnpm --filter @nucleus/nucleus serve-repl
```

In a second development-shell terminal, start the disposable loopback kernel. The allowed origin
must exactly match the page origin, with no trailing slash:

```sh
component=target/wasm32-unknown-unknown/debug/covalence_hol_proof_guest_beta.wasm
digest="$(b3sum --no-names "$component")"
cargo run -p covalence-bin-nucleus -- \
  --hash-wasm-hol-http "$digest" "$component" \
  127.0.0.1:0 http://127.0.0.1:4173
```

The kernel prints three tab-separated coordinates: `url`, `public_key`, and `component`. Open
<http://127.0.0.1:4173/repl.html>, paste those values into the corresponding fields, and choose
**Run and import**.

The imported receiver becomes the selected normal HOL connection. You can:

- choose **Reread imported theorem** to reauthenticate the retained artifact through the read-only
  import path;
- run another HOL recipe, such as `reflexivity false`, using the existing recipe control; and
- choose **Clean up receiver**, or the general **Close connection** button, to release it before
  another hash-selected run.

The native service deliberately remains alive after a signed session closes. Stop it with
<kbd>Ctrl</kbd>+<kbd>C</kbd> when finished. This prototype also has a finite 64-socket lifetime;
restart it if that disposable request budget is exhausted.
