# HOL proof recipe collector

This deliberately authority-free executable accepts one fixed, bounded
WebAssembly component on standard input and emits only bounded canonical HOL
recipe bytes. It has no dependency on Nucleus, Neutron, SQLite, signing, or the
REPL. Its output remains untrusted and must be decoded and replayed by the
key-holding kernel.

The current prototype isolates the signing key from Wasmtime and its JIT. It is
not an OS sandbox: the child still has whatever process authority the operating
system grants. The integration parent clears its environment, gives it a private
empty working directory, and configures only stdin/stdout with stderr discarded;
it does not claim to close ambient non-`CLOEXEC` descriptors or deny filesystem
and network syscalls.

The current parent integration is Unix-only. It kills the collector's fresh
process group before joining pipes, but a hostile descendant can escape with
`setsid`; this remains an availability boundary, not a sandbox. Cleanup removes
the private working directory only when it is empty. Attacker-created contents
are left behind for inspection rather than recursively traversed or deleted.
