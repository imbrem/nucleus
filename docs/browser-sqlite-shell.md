# Browser SQLite shell boundary

Status: architecture contract only. This document does not claim that the web
REPL has a playable SQLite shell.

Issue #271 requires the browser frontend to open an exported database snapshot
in the actual SQLite shell. It must not grow another SQL command loop which
merely resembles that shell. The native sibling uses the system `sqlite3`
program. The browser counterpart should use SQLite's own Wasm Fiddle build.

## Upstream boundary

SQLite ships a standard JavaScript/Wasm API and documents an official
subproject package, `@sqlite.org/sqlite-wasm`:

- <https://sqlite.org/wasm/doc/tip/npm.md>
- <https://sqlite.org/wasm/doc/tip/api-index.md>

Those APIs expose SQLite, including Worker1 and its promise wrapper. They do
not expose the CLI shell. Building a terminal on Worker1's `exec` operation
would be a competing shell implementation and is out of scope.

SQLite Fiddle is the relevant upstream application: it wraps a Wasm build of
the SQLite CLI shell. SQLite describes Fiddle as not an officially supported
deliverable, however. Fiddle currently has its own user-facing import button,
and SQLite documents how an application can deserialize an owned image, but it
does not document a stable programmatic host-to-Fiddle import protocol or a
read-only import guarantee:

- <https://sqlite.org/fiddle/>
- <https://sqlite.org/wasm/doc/tip/building.md>
- <https://sqlite.org/wasm/doc/tip/cookbook.md>

The build documentation says that a generated `fiddle/` directory may be
copied and served as a unit. It is a generated asset bundle rather than a
small library dependency. We therefore do not vendor it, reach into its
private JavaScript objects, or claim a browser shell in the first native PR.

## Stable Nucleus side

The stable boundary is an owned, bounded SQLite database image:

```text
selected raw SQL connection + schema
        |
        | serialize snapshot
        v
owned bytes (at most MAX_IMAGE_BYTES)
        |
        | one-shot transfer
        v
isolated, version-pinned upstream Fiddle worker
```

The producer must use the same selection rule as the native shell:

- `main` is allowed for a deliberately unrestricted `Connection<Sql>`;
- a non-main schema is allowed only after its actual `sqlite3_vfs*` is checked
  against the immutable image VFS;
- arbitrary attached files and all trusted protocol connections are rejected.

The resulting bytes carry no trust. Opening them in a shell neither validates
their application schema nor admits any theorem or assumption.

## Proposed host adapter

The future web frontend may expose this host-only operation:

```typescript
interface BrowserSqliteShellHost {
  openSnapshot(request: {
    bytes: ArrayBuffer;
    displayName: string;
    maxBytes: number;
  }): Promise<void>;
}
```

This is not a kernel protocol method. The caller obtains owned bytes from a
selected raw SQL connection, checks `byteLength <= maxBytes`, makes a fresh
transfer buffer, and gives that buffer to the host adapter. No connection ID,
worker handle, VFS capability, signing key, or live database handle is passed.

The host adapter opens a dedicated shell page and worker from a pinned Fiddle
bundle. A small, version-specific adapter inside that bundle installs the
snapshot into the CLI shell's `main` database with SQLite deserialization's
read-only flag and enables `PRAGMA query_only`. The rest of the UI and command
semantics remain upstream Fiddle code.

Opening another database from shell dot commands must not expose a Nucleus
database. The shell origin receives no Nucleus VFS and should have no
persistent storage capability in the first demo.

## Window and transfer protocol

The opener and shell page must use an exact configured origin, a fresh random
nonce, and a dedicated `MessageChannel`. Wildcard origins are forbidden.

One possible versioned exchange is:

```text
opener -> shell window (exact targetOrigin):
  Init { version: 1, nonce }, transferred MessagePort

shell -> opener (dedicated port):
  Ready { version: 1, nonce }

opener -> shell (dedicated port, ArrayBuffer transfer list):
  OpenSnapshot { version: 1, nonce, displayName, bytes, readOnly: true }

shell -> opener (dedicated port):
  Opened { version: 1, nonce }
  or Error { version: 1, nonce, message }
```

The shell accepts exactly one `Init` and one `OpenSnapshot`. Both sides reject
the wrong origin, window, port, version, nonce, duplicate message, missing
transfer, and image larger than `MAX_IMAGE_BYTES`. The opener transfers a
fresh `ArrayBuffer`, detaching that transfer buffer, then closes its port after
`Opened` or `Error`. Closing the shell terminates its worker and releases the
deserialized copy.

The nonce and exact-origin checks prevent unrelated windows from confusing a
shell instance. They do not defend against malicious script already executing
within either trusted origin. Content Security Policy, dependency pinning, and
the browser's normal origin isolation remain part of that threat boundary.

## Acceptance gates for an implementation PR

Do not advertise a playable browser shell until a later PR satisfies all of
these gates:

1. Pin one SQLite release/source check-in and record hashes and licenses for
   every generated Fiddle asset. The build must be reproducible or consume a
   separately reviewed, immutable artifact.
2. Keep the full upstream Fiddle application recognizable. Any import adapter
   must be a narrow version-specific patch, not a replacement terminal or SQL
   evaluator.
3. Document and test the exact API used to install bytes into the shell's
   `main` database. Treat every upstream upgrade as requiring revalidation;
   Fiddle provides no stable import protocol today.
4. Serve the shell page and worker from an isolated exact origin with a strict
   Content Security Policy. Do not grant OPFS or another persistent Nucleus
   database capability in the first demo.
5. Enforce `MAX_IMAGE_BYTES` before copying or transferring, deserialize the
   copy read-only, enable `query_only`, and prove that writes fail.
6. Run a real Chromium test covering ready/nonce binding, one-shot transfer,
   successful queries, write rejection, worker cleanup, oversized input,
   duplicate messages, and hostile origin/nonce attempts.
7. Measure and record the generated asset delta. Keep Fiddle assets out of the
   Rust/Wasm kernel artifact and load them only for the shell frontend.

Until these gates are met, the web REPL should offer snapshot download only.
That is an honest, useful foundation and leaves the eventual actual shell as a
frontend concern transparent to Nucleus protocols.
