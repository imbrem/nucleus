# Signed HOL file handoff

This demo moves one signed HOL kernel-state database between the terminal and browser REPLs. The
database is downloaded in full, authenticated in memory, imported, and then opened as ordinary HOL
state. The signing key is ephemeral: restarting either kernel creates a different identity.

## Set up

From the repository root:

```sh
nix develop
pnpm install --frozen-lockfile
cargo build -p covalence-bin-nucleus
pnpm --filter @nucleus/nucleus build
```

Start the browser REPL server in one terminal:

```sh
pnpm --filter @nucleus/nucleus serve-repl
```

Open <http://127.0.0.1:4173/repl.html>. Start the terminal REPL separately with:

```sh
cargo run -p covalence-bin-nucleus
```

## Trust boundary

The `public_key=` field inside `attestation.txt` is an **untrusted claim**. Never derive the
expected key pin from that field or from any other file delivered with the signed database. Obtain
the expected public key through a pre-established, authenticated out-of-band channel.

`.kernel identity` and the browser's separate **Download public-key pin** control expose candidate
public keys for that channel. Merely sending the key beside the database is not independent
authentication. The terminal prints the key as exactly 64 lowercase hexadecimal digits; the
browser consumes and produces the same 32 bytes in raw binary form. `signer` is a key identifier
derived from the public key, not a substitute for the key, and cannot be used to recover it. No
secret key material is exported.

Successful signature authentication proves only origin and integrity: the schema-qualified claim
for these exact database bytes was signed by the private key corresponding to the independently
pinned public key. It does **not** prove that any theorem in the database is true, or that the
database is authoritative HOL kernel state.

In this demo, choosing **Receive files** is the operator's explicit authorization to create a
receiver which trusts that authenticated signer for snapshot assertions, accepts this exact
schema-qualified snapshot, and records its imported theorem authority. Merely recording the signer
with `trust_snapshot_signer` grants no HOL authority by itself. The received theorem remains scoped
to the matched immutable reader. Choosing **Open trusted state** is a second, separate authorization:
the operator assumes that the exact matched signed bytes are authoritative serialized HOL state and
opens a private writable copy under a fresh child connection. The child starts with fresh
connection-local trust tables; its persisted judgement becomes usable only when the scoped child
proof session loads it.

## Terminal to browser

At the terminal REPL prompt, print the current kernel identity and create a fresh artifact
directory. The directory must not already exist:

```text
.kernel identity
.hol natlike-missing-zero /tmp/missing-zero-export
```

Send the `public_key` value to the browser operator through the authenticated out-of-band channel.
On their machine, convert that independently received hex value to the raw 32-byte pin file:

```sh
PUBLIC_KEY_HEX=0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
python -c 'import pathlib, sys; value = sys.argv[1]; len(value) == 64 and all(character in "0123456789abcdef" for character in value) or sys.exit("expected exactly 64 lowercase hex digits"); pathlib.Path(sys.argv[2]).write_bytes(bytes.fromhex(value))' "$PUBLIC_KEY_HEX" expected-public-key.bin
```

In the browser's **Receive signed HOL files** section, select:

- `/tmp/missing-zero-export/proof.sqlite` as **Signed SQLite image**;
- `/tmp/missing-zero-export/attestation.txt` as **Signed artifact sidecar**; and
- `expected-public-key.bin` as **Expected public-key pin (raw 32 bytes)**.

Choose **Receive files**. After it reports that the files were authenticated and retained, choose
**Open trusted state** to make the separate serialized-state authority decision described above.
The resulting connection is independent writable HOL state with provenance for the exact signed
source snapshot.

## Browser to terminal

In the browser's **Signed NatLike missing-zero theorem** section, choose **Prove missing zero**.
When the signed theorem is retained:

1. Choose **Download database + attestation**. This downloads `missing-zero.sqlite` and
   `missing-zero.attestation.txt`.
2. Choose **Download public-key pin**. This downloads
   `missing-zero.expected-public-key.bin`; convey those 32 bytes through the authenticated
   out-of-band channel, separately from the first two files.

Prepare the filenames expected by the terminal receiver and render the independently received raw
pin as lowercase hex:

```sh
mkdir -p incoming
cp /path/to/missing-zero.sqlite incoming/proof.sqlite
cp /path/to/missing-zero.attestation.txt incoming/attestation.txt
EXPECTED_PUBLIC_KEY_HEX="$(python -c 'import pathlib, sys; key = pathlib.Path(sys.argv[1]).read_bytes(); len(key) == 32 or sys.exit("expected exactly 32 key bytes"); print(key.hex())' /trusted/path/missing-zero.expected-public-key.bin)"
```

At the terminal REPL prompt, replace the placeholder with that exact 64-character value:

```text
.hol receive-signed incoming EXPECTED_PUBLIC_KEY_HEX
.hol open-state
.hol truth
```

The receive command rejects malformed sidecars, a modified image, the wrong schema, an invalid
signature, or a public key which does not match the explicit pin. For another export, choose a new
directory or remove the old demo directory deliberately after retaining any files you need.
