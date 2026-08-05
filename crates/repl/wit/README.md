# Experimental kernel component boundary

`kernel.wit` is an alternative boundary above the selected Worker-message
prototype. It deliberately exposes only the complete signed-HOL recipe needed
by the current north star:

1. open an owned HOL connection;
2. prove beta, persist, export, snapshot, and sign; or
3. authenticate an untrusted artifact against a producer selected through the
   host directory, yielding an owned pinned-artifact resource without mutating
   receiver state; then
4. explicitly trust, import, and read through that capability.

The component instance is the independently keyed kernel. Connection resources
make ownership explicit. The transported artifact remains an untrusted record;
successful authentication converts it to a pinned capability, and only that
capability exposes the mutating trust/import operation.

This proposal does **not** generate bindings yet. The checked-in TypeScript
adapter mirrors this interface and is tested against two real Worker kernels;
`wasm-tools component wit crates/repl/wit` validates the source interface. That
keeps generated code and a component runtime out of the prototype until a host
is selected.

Compared with the existing message endpoint, this removes operation names,
request IDs, and connection IDs from consumers. Its cost is a second public
surface plus Canonical ABI copies of the SQLite image and byte fields. The
message endpoint remains the smaller implementation today; this WIT boundary is
most useful once native and Wasm-component hosts share the same guest API.
