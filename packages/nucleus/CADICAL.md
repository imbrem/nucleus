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

The provider's answer remains untrusted. A consuming SAT continuation checks
the job and problem identities before the local model/LRAT checker may produce
a witness or admit a fact. Transporting a result never grants authority.

A browser-local CaDiCaL/Wasm artifact is deliberately deferred. Browsers use
the same `HttpSatSolver` capability for now; adding a local implementation does
not change the REPL or checker contract.
