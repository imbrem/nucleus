# REPL, kernel, and transport architecture

Status: proposed direction after the local browser/native MVP.

## Decision

The REPL is a connection directory and user interface, not a Nucleus protocol
and not a kernel. Its durable model belongs in the `covalence-repl` crate and
its state belongs in an ordinary raw Neutron SQLite database.

A kernel is an independently identified protocol host. Each kernel instance
gets a fresh ephemeral Ed25519 secret key, even when several kernels live in
one OS process. The secret remains in the kernel instance. Directories,
transports, and peers see only its public key.

The stable boundary between a REPL and a kernel should become a small WIT API.
The same typed API can be hosted by:

- a kernel in the same native process;
- one or more browser Workers, each potentially on a different thread;
- a native kernel reached over WebSocket or HTTP;
- a local raw SQLite provider hosted behind a kernel adapter;
- eventually a proxy process hosting several independent kernel identities.

Every interaction that crosses a kernel boundary is authenticated using PKI.
Transport security such as TLS is useful but does not replace kernel identity.

## Layers

### Nucleus protocols

`nucleus::Connection<P>` remains the trusted protocol enclosure. Protocol
modules construct it, decide what may be read and persisted, and return only
protocol-specific statements, values, and proof objects.

The unrestricted `Sql` protocol is deliberately permeable. HOL-omega and later
protocols must not inherit that authority.

### Kernel instances

`nucleus::Kernel` owns one ephemeral signing capability and the connections
opened by that kernel identity. Multiple `Kernel` values in one process are
independent. A process acting as a proxy must not collapse their keys or trust
policies into a process-global identity.

The initial local implementation opens connections directly. Later revisions
should move connection ownership fully behind the kernel API so a caller
cannot accidentally bypass its authentication and policy hooks.

### Kernel API

Use versioned, protocol-specific WIT interfaces rather than a single untyped
"execute" endpoint. WIT has no useful equivalent of Rust's generic
`Connection<P>`; separate interfaces keep authority visible.

An illustrative first world is:

```wit
package covalence:kernel@0.1.0;

interface identity {
  record info {
    public-key: list<u8>,
  }
  info: func() -> info;
}

interface sql {
  variant value {
    null,
    integer(string),
    real(float64),
    text(string),
    blob(list<u8>),
  }

  record rows {
    columns: list<string>,
    values: list<list<value>>,
  }

  variant outcome {
    changed(u64),
    rows(rows),
  }

  resource connection {
    run: func(statement: string) -> result<outcome, string>;
    put-image: func(bytes: list<u8>) -> result<string, string>;
    attach-image: func(hash: string, schema: string) -> result<_, string>;
    serialize-main: func() -> result<list<u8>, string>;
  }

  open: func() -> result<connection, string>;
}
```

This is a direction, not a frozen wire specification. In particular:

- exact integers stay decimal strings across JavaScript boundaries;
- the first image API intentionally transfers the complete database;
- large images later need stream or CAS-resource handles;
- errors need a versioned structured form before remote transports ship;
- HOL interfaces should expose typed IDs and rule operations, never raw SQL.

### Immutable image store

The first immutable store is a process-local content-addressed store: one
lazily registered, totally immutable read-only VFS whose logical paths are
content addresses. Entries are only ever inserted, an address always serves
the same bytes, and `SQLite` resolves them on read.

- Admission is bounded by `MAX_IMAGE_BYTES` and transfers the complete image;
  there is no streaming, ranged, or partial access at this layer.
- Neutron stays hash-free. Content addressing lives in the Nucleus `Sql`
  protocol; Neutron and the VFS below it only move uninterpreted bytes.
- A VFS name is routing data only. Every attachment verifies the actual
  post-attach `sqlite3_vfs` pointer against the registered identity.
- The store makes no trust claims. Signature verification and trusted imports
  form a later, separate admission layer above the store.

Later storage layers compose with the store instead of replacing it: a
copy-on-write VFS can materialize writable overlays on top of content-addressed
baselines, streaming or paged backends can serve large images behind the same
VFS seam, and eviction becomes possible once open-handle tracking exists.

### Transport adapters

The REPL core should know only local kernel IDs, connection IDs, protocol IDs,
and transport metadata. Adapters implement the actual calls:

- `Local`: direct Rust calls in one process;
- `Worker`: structured-clone messages to one browser Worker;
- `WebSocket`: multiplexed, ordered calls to a native kernel;
- `HTTP`: independent request/response calls, useful for stateless operations;
- `RawSqlite`: a local kernel adapter around a native or Wasm SQLite runtime.

The current TypeScript Worker client is the first adapter. It should eventually
be generated from, or mechanically checked against, the WIT interface. Do not
wait for that tooling before finishing the local MVP.

The Rust REPL crate should gain a transport trait only when a second adapter is
implemented. Designing an async trait around one synchronous local adapter now
would create abstraction without evidence. The SQLite directory schema and
WIT values are the stable seams in the meantime.

### Frontends

Terminal and web frontends share connection lifecycle and result values from
`covalence-repl`. They differ only in presentation and host affordances:

- terminal values render as unambiguous text;
- web values may render as a table, graph, image, or a new browser tab;
- browser-only previews are frontend operations, not kernel protocol methods;
- an actual SQLite shell is a separate frontend over an exported snapshot or
  a later read-only VFS alias, not a shell reimplementation in the REPL core.

## REPL state database

The REPL database is intentionally inspectable and carries no logical trust.
The current tables are the beginning of this model:

```text
repl_kernel(kernel_id, transport, endpoint, public_key)
repl_connection(connection_id, kernel_id, protocol, remote_connection_id)
repl_state(singleton, active_connection_id)
```

Runtime resources cannot live in SQLite, so an in-memory map associates these
IDs with local handles. Directory mutations and active-selection changes are
transactional. A lost runtime handle makes the row stale; it never turns the
row into proof of a live or trusted connection.

Later tables can record:

```text
repl_transport(kernel_id, configuration, last_error, metadata)
repl_request(request_id, kernel_id, connection_id, state, metadata)
repl_view(connection_id, renderer, configuration)
repl_trust(subject_key, scope, connection_id?, decision, metadata)
```

Private keys do not belong in this database. Persisting the directory is
optional and must not persist ephemeral kernel secrets by accident.

## PKI boundary

Kernel authentication and logical trust are separate questions.

1. Authentication establishes which kernel key sent a request or response.
2. Process-level trust says what another kernel identity may do generally.
3. Connection-level trust may further restrict or extend authority for one
   protocol connection.
4. Protocol trust decides whether signed data is admissible as a logical
   assumption, a valid database image, or merely untrusted input.

The first remote transport should use a simple signed canonical envelope:

```text
version
protocol root
sender public-key ID
recipient public-key ID
request ID
fresh nonce or session sequence
payload hash
signature over every preceding field
```

A response additionally commits to the request hash. Receivers maintain replay
state for a live session. WebSocket may later derive session keys after a
signed challenge handshake, but signing each initial envelope is easier to
audit. HTTP requests and responses remain independently verifiable.

TLS authenticates the network endpoint and protects metadata in transit. It
must not be used as evidence that a message was produced by a particular
kernel key.

Trust relations are between keys, not processes. A proxy hosting keys A, B,
and C may allow A to trust B while distrusting C, even though all three share
an address space and transport endpoint.

## Raw SQLite connections

A raw database is data, not a kernel identity. The adapter that executes SQL
against it is a kernel and therefore has an ephemeral key. Local calls may be
direct, but any use of that adapter across a kernel boundary uses the same PKI
envelope as every other inter-kernel operation.

Two read-only modes should remain distinct:

- an exported immutable snapshot opened by the actual SQLite shell;
- a later VFS alias onto a live database that can never obtain an exclusive
  lock.

The latter is a separate PR and needs explicit concurrency semantics.

## Alternatives considered

### TypeScript-only orchestration

This is quickest for one Worker, but it duplicates lifecycle behavior in the
terminal, makes native clients second-class, and gives WIT no natural owner.
Keep TypeScript as a browser transport and presentation adapter instead.

### Put the REPL in Nucleus

This confuses orchestration with a trusted protocol and expands the TCB with UI
state. The REPL belongs in its own crate and uses Nucleus protocols as a
consumer.

### One process-global key

This prevents faithful proxying and forces unrelated trust decisions to share
one principal. Kernel-instance keys are cheap and preserve the intended trust
graph.

### One generic byte RPC

This makes protocol authority invisible and pushes decoding into every caller.
Use versioned typed WIT interfaces and reserve opaque bytes for explicitly
content-addressed payloads.

## Foundation for the HOL layer

The HOL milestone builds directly on these boundaries without new machinery:

1. `Connection<P>` is the enclosure an HOL protocol instantiates. An HOL
   connection admits a database and exposes typed judgments and rule
   applications; it never inherits the deliberately permeable authority of
   `Sql`. The TCB grows by one protocol module, not by REPL or transport code.
2. The immutable image store is how an HOL standard library arrives: a
   complete bounded snapshot, mounted read-only under its content address and
   pointer-verified. HOL adds signature and trust checks as its own admission
   layer above the store.
3. The REPL directory already orchestrates several connections over one
   kernel. An HOL proof session is one more `repl_connection` row with its own
   protocol ID, selectable and inspectable in SQLite exactly like a SQL
   session.
4. Kernel identities give future proof exchange a principal: a theorem
   imported from another kernel is evidence signed by that kernel's key, and
   the trust decision stays separate from transport security.

## Staged implementation

1. Keep the current local Rust and browser Worker adapters on the shared REPL
   directory.
2. Move all local connection creation behind `Kernel` and expose its public
   identity through the directory.
3. Write the minimal SQL WIT package and a conformance test against the Worker
   message API.
4. Add a second browser Worker adapter so one REPL demonstrably spans kernels
   and threads.
5. Define and test signed canonical request/response envelopes.
6. Add a native WebSocket adapter with explicit expected-peer keys.
7. Add HTTP for operations that benefit from independent requests.
8. Add trust-policy tables and protocol-specific admission only when a remote
   protocol needs them.
9. Add the real read-only SQLite shell and later the lock-denying VFS alias as
   separate changes.

Federation is an eventual consequence of these boundaries, not an MVP feature.
