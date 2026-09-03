# Wasm as executable grounding

Nucleus uses HOL as its ambient semantic envelope and SpecTec as the source
semantics for WebAssembly. Exact Wasm bytes provide the concrete executable
objects about which Nucleus proves HOL theorems.

The primary workflow is to compile an ordinary program to Wasm, state a
program property, and let an untrusted strategy attempt the proof. A strategy
may use symbolic execution, lemmas, SAT, SMT, abstraction, or program
transformation. Only the kernel creates the resulting theorem fact.

The first program properties concern observable execution:

- exact bytes decode and validate as a module;
- a module may, must, or never call an import matching an event predicate;
- a module never calls a reserved `assert(false)` event;
- a module is deterministic or total under explicit host and resource
  assumptions; and
- two modules are observationally equivalent or refine one another.

These are derived from one versioned eventful execution relation. Inputs, host
behavior, resources, profiles, and existential or universal quantification over
executions remain explicit. Symbolic module composition, linking, trace safety,
and later temporal properties build on the same relation rather than becoming
separate kernel APIs.

This makes Wasm a common grounding for more than application code. Small Wasm
checkers can be related to HOL accounts of proof formats such as Metamath and
LRAT. Wasm implementations of abstract machines can be related to their
mathematical models. Compiler and validator optimizations can be accepted only
after a checked equivalence, refinement, or soundness result.

Wasm execution is not inherently trusted. Parsers, SpecTec tooling, compilers,
validators, tactics, AI searches, and native engines remain outside the TCB by
default. Content addresses identify bytes but make no semantic claim about
them. Accelerator-free facts lower to ordinary HOL; any accelerator authority
or semantic assumption is explicit and cannot silently enter an
assumption-free arena.

The first vertical is a reproducibly compiled Rust module with a small assertion
ABI, checked decoding and validation, and a theorem that every allowed
execution avoids the failure event. A nearby unsafe module supplies a concrete
counterexample. This common goal API is the initial workface for both automated
proof research and verified Wasm optimization.

The evolving roadmap and acceptance criteria live in
[north-star issue #1244](https://github.com/imbrem/nucleus/issues/1244).
[Epic #1173](https://github.com/imbrem/nucleus/issues/1173) tracks the executable
semantics and program-property implementation graph, and
[#1238](https://github.com/imbrem/nucleus/issues/1238) tracks the first
nontrivial `callsAssert` laws.
