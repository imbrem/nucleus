# WebAssembly semantic grounding

The target program-logic interface is defined by four theorem families over
actual WebAssembly modules:

```text
callsAssert(TRUE)
not callsAssert(FALSE)
callsAssert(OR(P, Q)) = callsAssert(P) or callsAssert(Q)
callsAssert(AND(P, Q)) = callsAssert(P) and callsAssert(Q)
```

`callsAssert(M)` means that there exist an exported-function invocation,
arguments, and behaviors for imports other than `assert` such that the
WebAssembly 3.0 execution relation reaches an attempted call to the distinguished
`assert` import. Host execution itself is outside the core SpecTec relation, so
the observation point is the reachable configuration immediately before that
host call. `neverCallsAssert(M)` is its HOL negation. This makes assertion calls
Sigma-style witnesses while negative claims require excluding every permitted
invocation and imported behavior.

The current parameterized lowering does **not** yet establish these theorems.
It represents SpecTec structural constructors, sequences, records, literals,
and primitive operations as free HOL interpretation symbols. The complete
theory constrains SpecTec declaration predicates, but does not constrain those
free symbols to be a faithful algebraic representation. In particular, a
permitted interpretation may map the `TRUE` and `FALSE` module structures to
the same HOL value. No sound proof can distinguish their execution behavior
from the current theory alone.

Grounding therefore requires all of the following:

1. A faithful HOL representation of the SpecTec value algebra, including the
   constructor disjointness/injectivity and sequence operations used by these
   modules. These must be definitions and checked derivations, or explicit
   theorem premises—not facts minted by a frontend.
2. HOL terms for the exact `TRUE`, `FALSE`, `OR(P,Q)`, and `AND(P,Q)` module
   structures. Until byte literals and a checked decoder are available, these
   may be structural module terms; a content-hash claim additionally requires
   checked evidence relating the exact bytes to that structure.
3. A `callsAssert` definition built from SpecTec instantiation, invocation, and
   reflexive-transitive execution relations plus the pre-host-call observation.
4. Proofs of the four equations above using the complete SpecTec theory and
   the concrete value interpretation. The theorem sequents must expose every
   remaining assumption.
5. Interpreter comparisons kept as differential tests only. Interpreter output
   never creates a theorem or discharges a semantic premise.

The empty-module experiment already keeps these two evidence classes separate:
`empty_wasm_module` constructs the structural HOL term from the pinned SpecTec
vocabulary, while `empty_module_agrees_with_wasmtime_observation` independently
checks the canonical eight-byte module with Wasmtime. The matching shape is a
useful regression signal, but it is not the still-missing checked theorem that
relates those bytes to the structural term or proves non-reachability.
The companion `forwarding_module_calls_assert_in_wasmtime` test supplies an
`assert` host function, invokes the module's exported imported function, and
observes the call. It is the positive runtime oracle for `TRUE`, under the same
strict separation from theorem evidence.

`forwarding_wasm_module` now constructs the corresponding structural HOL term
from the exact pinned Wasm AST constructors: one nullary function type, one
function import at type index zero, and one export of function index zero. Its
three names are inputs in the generic SpecTec value representation. This keeps
the structural program API usable before byte literals land while isolating the
eventual checked UTF-8/name decoding law instead of hiding it in the builder.

This boundary adds no trusted component. The existing HOL kernel remains the
only theorem authority; the SpecTec compiler, concrete interpretation, module
builder, proof search, byte decoder, and interpreter are all checkable
userspace producers.

The broader intended use is to treat WebAssembly as a universal mathematical
substrate. A checker for a mathematical predicate can call `assert` when it
finds a witness; for example, consistency of a formal theory can be stated as
the claim that its proof-validator module never calls `assert` on any purported
derivation. Positive reachability, universal non-reachability, determinism, and
output exclusion then become ordinary HOL properties of content-addressed
program semantics rather than special kernel capabilities.
