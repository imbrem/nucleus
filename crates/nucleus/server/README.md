# Nucleus server

This crate is the untrusted native server assembly around
`covalence-nucleus-core`. It owns checked kernel state and composes userspace
services and transports without adding theorem authority.

The initial server exposes:

- `GET /nucleus` for a small observation of the current checked kernel;
- the composable CAS HTTP API under `/cas`.

Future kernel operations, Wasm-posting APIs, WebSockets, MCP, authentication,
and capability policy belong here or in services composed here—not in the
checked core.
