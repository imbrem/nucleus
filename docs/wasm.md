# Wasm as executable grounding

Nucleus uses HOL as its ambient semantic envelope and SpecTec as the source
semantics for WebAssembly. Exact Wasm bytes provide the concrete executable
objects about which Nucleus proves HOL theorems.

The semantic target is the complete pinned Wasm 3.0 SpecTec specification. We
do not define a handwritten instruction subset and later call it Wasm. The
SpecTec-to-HOL lowering may begin as a draft, but it should be generic over the
SpecTec constructs used by the full specification. Development is incremental
in examples, proof automation, and performance—not in the meaning of Wasm.

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

The first examples deliberately work above binary decoding. Construct symbolic
Wasm programs `TRUE`, `FALSE`, `AND`, and `OR` through the draft SpecTec
lowering and prove their `callsAssert` laws manually. These results demonstrate
that the lowering supports non-vacuous program proofs before the byte and
linking layers are complete.

Next, define observational equivalence of Wasm programs and prove that it
preserves derived observations such as `callsAssert`. A small equational theory
can then cover transformations such as dead-code elimination, linking, and
inlining. In particular, a Wasm transformer is itself a program that consumes
Wasm and produces Wasm. An optimizer is a transformer whose successful output
is equivalent to its input; failure or partiality must be observable, for
example as a trap or reserved `fail` call. Identity and composition should give
these verified transformers a reusable algebra.

After canonical HOL bytes are available, connect the symbolic examples to
exact byte vectors through checked decoding and validation. Re-prove the
`TRUE` and `FALSE` results from bytes first. `AND` and `OR` then exercise the
real linking representation and provide a stronger end-to-end test. Missing
byte support is therefore a dependency of exact-artifact theorems, not a
reason to invent a smaller Wasm semantics or postpone useful symbolic proofs.

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

Once these end-to-end examples work, autoresearch can improve their proof cost,
extend tactic coverage across the generated semantics, discover useful lemmas,
and propose faster equivalent validators and transformers. Every successful
result still ends as checked evidence for the same HOL propositions.

The evolving roadmap and acceptance criteria live in
[north-star issue #1244](https://github.com/imbrem/nucleus/issues/1244).
[Epic #1173](https://github.com/imbrem/nucleus/issues/1173) tracks the executable
semantics and program-property implementation graph, and
[#1238](https://github.com/imbrem/nucleus/issues/1238) tracks the first
nontrivial `callsAssert` laws.
