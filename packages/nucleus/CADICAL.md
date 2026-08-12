# CaDiCaL providers

`CadicalSolver` is an untrusted Node adapter. It invokes `cadical` directly
without a shell, gives each run a private temporary directory, and caps the
model, proof, standard output, and standard error. Cancellation, timeout, or a
limit violation kills and reaps the process before cleanup. Binary LRAT is the
default; `asciiProof: true` exists only for explicit debugging.

The native adapter uses POSIX process groups and is not available on Windows;
Windows and browser clients use `HttpSatSolver`. Process groups provide bounded
cleanup, not an OS security sandbox: deploy an actually hostile executable in
an appropriate container or sandbox.

`HttpSatSolver` and `createCadicalServer` carry the same injected `SatSolver`
capability over ordinary HTTP. The endpoint accepts `POST` with
`Content-Type: application/dimacs`. A successful response is either
`application/vnd.nucleus.sat-model` (signed decimal literals terminated by
zero) or `application/vnd.nucleus.lrat` (raw LRAT bytes). Request and response
bodies are streamed and bounded. There is no WIT or solver-specific transport.

The provider's answer remains untrusted. Only `Repl.completeSat` or
`Repl.completeUnsat` can admit it, using the local model/LRAT checker.

A browser-local CaDiCaL/Wasm artifact is deliberately deferred. Browsers use
the same `HttpSatSolver` capability for now; adding a local implementation does
not change the REPL or checker contract.

The minimal browser setup is an ordinary injected host capability:

```js
import { drive, init, Repl } from "@nucleus/nucleus";
import { HttpSatSolver } from "@nucleus/nucleus/sat-http";

await init();
const repl = new Repl();
const host = { sat: new HttpSatSolver("http://127.0.0.1:8080/") };
await drive(repl, host, "(sat-demo and-unsat)");
await drive(repl, host, "(sat-solve)");
```

The service can be bootstrapped in Node with
`createCadicalServer({ solver: new CadicalSolver(), allowedOrigins:
["https://repl.example"] })` from `@nucleus/nucleus/cadical-node`. Cross-origin
access is denied unless an exact origin is listed. The answer still crosses the
REPL's local checker before `(sat-checked)` can report it. `(sat-proof-text)`
renders the retained proof under a separate display bound, and `(sat-database)`
returns an immutable SQLite snapshot address for ordinary `(sqlite ADDRESS …)`
inspection.
