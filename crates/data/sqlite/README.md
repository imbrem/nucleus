# SQLite userspace data support

`covalence-data-sqlite` contains untrusted conveniences built over the narrow
`covalence-lib-sqlite` boundary:

- a permeable connection wrapper with connection-local catalog metadata;
- typed query, parameter, transaction, and database-image helpers;
- a read-only SQLite VFS which opens immutable CAS objects by O256 address;
- an adapter exposing a format-neutral `covalence-data-vfs` resolver through
  SQLite's random-access file interface.

The resource interface deliberately does not interpret names as paths or
bytes as source text. Script trees can therefore resolve logical module names,
content addresses, SQLite databases, Wasm modules, and other resources through
one virtual store while applying format-specific interpretation separately.

This crate does not define valid Nucleus state and has no theorem or signing
authority. Proof tactics and applications may use arbitrary SQL through it;
any semantic result still needs checked evidence before it becomes trusted.

The `cov_conn_*` temporary table names are retained as a small on-connection
format commitment. They describe only the wrapper's local bookkeeping and are
not part of the Nucleus trusted core.
