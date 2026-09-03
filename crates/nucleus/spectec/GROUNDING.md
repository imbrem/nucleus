# WebAssembly semantic grounding

The generic program-property thin waist is an immutable `RunRelation` with
the checked HOL shape
`Runs(profile, module, entry, inputs, host, trace, outcome)`. A `RunDomain`
adds an explicit profile- and module-sensitive admissibility policy, reusable
across predicates over traces and outcomes. A `RunObservation` derives `may`,
vacuous-universal `every`, per-invocation non-vacuous `must`, and `never`
propositions from that one relation. `every` states trace safety independently
of progress, while `must` additionally requires an observed execution for each
admissible invocation. Calls, traps, returns, and compound trace properties are
observation adapters rather than separate execution semantics. Unary trace and
outcome predicates have checked adapters that explicitly ignore the other
component, covering the common call/safety and return/trap cases without
hand-built lambdas. Observations compose pointwise through immutable `and`,
`or`, and negation operations; binary composition rejects different run domains
so host policies cannot be mixed silently. A domain also defines `same_runs`
as equality of two immutable characteristic functions: the admissible
invocations and the complete allowed run graph. This representation gives
checked reflexivity, symmetry, and transitivity directly from HOL equality.
Every behavior proposition is an application of a shared pure observer to those
two functions. Checked congruence therefore proves that `same_runs` preserves
every `may`, `every`, `must`, and `never` observation, including a trace
predicate for `callsAssert`, without trusting an evaluator or a special-purpose
preservation axiom.
The same mechanism is exposed as `RunProperty`: any checked
`admissibility-function -> run-function -> bool` term becomes a reusable module
predicate with generic `same_runs` preservation and contextual-observation
adapters. Contextual run equivalence generically preserves every such property,
and checked negative evidence for one refutes contextual run equivalence. The
properties compose pointwise through immutable conjunction, disjunction, and
negation. The four behavior quantifiers lower through this API rather than
forming a privileged property family.
`RunDomain::in_context` attaches and validates a reusable linking operation and
context admissibility predicate. The resulting `RunContext` owns that domain,
so mixing observations or equivalence evidence from another execution policy
is rejected at the construction boundary rather than threaded through every
method call. Its `equivalent` proposition defines observational equivalence as
complete run equality in every admissible closing context, independently of
any one observer. A checked elimination theorem maps that contextual relation
to ordinary contextual equivalence for any selected run property.
Premise-free reflexivity and premise-preserving symmetry and transitivity are
themselves checked derivations, rather than frontend declarations that the
relation is an equivalence.
`RunTransformation` packages a checked pure `module -> module` function under
one context schema and semantic profile. Its `sound` proposition is exactly
that every input module is contextually observationally equivalent to the
transformed module. Transformations compose immutably, while mismatched context
schemas or profiles are rejected before composition. `SoundRunTransformation`
is the proof-carrying form: it can only be constructed by checking positive
kernel evidence against that exact soundness proposition, and it retains every
premise of the supplied theorem.
The identity transformation has a premise-free checked soundness derivation,
providing the neutral proof-carrying transformation without any semantic
assumption. Proof-carrying transformations compose by checked universal
specialization and transitivity of contextual observational equivalence, while
retaining the premises of both component proofs.
Any proof-carrying sound transformation also generically preserves every
`RunProperty` in all admissible linking contexts. This includes composed
contracts and `callsAssert` observations without adding transformation- or
property-specific proof rules. The same checked theorem specializes directly
to a concrete module, yielding contextual equivalence for that observation on
the program and its transformed image. Given positive admissibility evidence
for a selected linking context, a further checked elimination yields the
actual observation equality on the two resulting closed modules; the bare
program equation therefore requires an admissible identity context.
`RunDomain::closed_context` supplies that canonical context generically: its
linker is definitionally the identity, its admissibility predicate is
definitionally true, and `ClosedRunContext::prove_admissible` derives the
required fact without premises. Its `prove_preserves` operation packages those
steps and returns the canonical observation equation whose plug applications
are definitionally identities. Its `transport` operation is the corresponding
one-call path for carrying positive or negative closed-program evidence across
a sound transformation; no explicit context or admissibility evidence is
required from the caller.
That equality checkedly transports either positive or negative observation
evidence from the original closed program to the transformed one. Negative
transport is derived by equality symmetry and contradiction rather than by an
unchecked polarity convention.
Conversely, checked negative evidence for any one contextual observation
refutes `equivalent`. Thus, once `callsAssert` is supplied as a trace
observation, its distinction between `TRUE` and `FALSE` is sufficient to prove
that they are not contextually run-equivalent; the API does not require
comparing their complete graphs by inspection.
The domain additionally defines directional `refines_runs`: an implementation
has the same admissible invocation domain and may remove, but not add, behaviors
of its specification, but must retain some behavior whenever the specification
has a run. Thus refinement cannot encode partiality merely by deleting every
result. Its checked reflexivity and transitivity derivations make this
progress-sensitive relation a preorder without assuming anything about the
underlying execution relation. Complete run equality checkedly induces
refinement in both directions, preserving the original equality premises.
Existential behavior transports forward from an implementation to its
specification by opening, transporting, and reintroducing the concrete run
witness; this makes counterexamples compositional across refinement. Its
checked contrapositive transports `never` properties from a specification to
every refining implementation, including eventual `never callsAssert` safety.
Positive universal invariants (`every`) transport in the same
specification-to-implementation direction, while existential counterexamples
(`may`) transport from implementation to specification. Non-vacuous universal
properties (`must`) also transport to the implementation: refinement's reverse
progress clause supplies a retained execution and forward inclusion preserves
the observation of every retained execution. One public
`prove_refinement_preserves` operation selects these checked derivations by
quantifier; `refinement_direction` makes the required premise side explicit.
The domain also derives explicit determinism and totality propositions.
Totality here means that every admissible invocation has a modeled trace and
outcome; the profile and outcome representation determine whether traps or
divergence count. Checked preservation theorems carry totality and determinism
from a specification to every refining implementation, using respectively
refinement's reverse progress and forward run-inclusion clauses. Both
predicates are reusable `RunProperty` schemas, so they compose with
other properties through pointwise negation, conjunction, disjunction,
implication, and logical equivalence and inherit generic
contextual-equivalence preservation; the
module-specific methods are thin applications. Premise-free checked reflexivity theorems establish the first
laws of equivalence and refinement without assuming either property; checked
symmetry and transitivity preserve the explicit premises of their input
evidence. The resulting module predicates compose with context-quantified
observational equivalence through a checked adapter. Keeping `same_runs` distinct from
contextual equivalence prevents a closed run-graph claim from silently standing
in for linking-context indistinguishability, while the existing individual-function
replacement theorems apply to any selected may, must, or never behavior. This
layer constructs checked syntax only and neither executes Wasm nor creates
theorem facts.

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

The current parameterized lowering establishes checked versions of these
claims conditional on the complete SpecTec theory and explicit grounding laws.
In particular, the full pinned-document audit constructs structural `TRUE` and
`FALSE` modules, derives `callsAssert(TRUE)` and
`not callsAssert(FALSE)`, and derives their contextual inequivalence. Closing
the theorem premises produces a premise-free HOL implication from those exact
laws to the inequivalence; it does not silently turn them into axioms.

The result is not yet an unconditional theorem of the parameterized theory.
Structural constructors, sequences, records, literals, and primitive
operations remain free HOL interpretation symbols. The complete theory
constrains SpecTec declaration predicates, but does not by itself require those
symbols to be a faithful algebraic representation. A permitted interpretation
could still map the structural `TRUE` and `FALSE` module terms to the same HOL
value. Distinguishing them therefore necessarily depends on checked
representation laws or a concrete faithful interpretation.

`StructuralValueAlgebra` is the generic syntax boundary for those laws. Given
an erased value classifier, Boolean classifier, and checked curried
constructors, it constructs arbitrary-arity injectivity and pairwise
disjointness propositions. `SpecTecValueBuilder::structural_constructor`
resolves the exact recorded lowering operation into that schema. Neither API
creates evidence: until a concrete interpretation proves the propositions,
they remain explicit premises suitable for `ParameterizedDocument`'s evidence
scope. The record tests exercise this path for the pinned empty-list and module
constructors.

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

The exact-byte side is separately represented by `covalence-data-wasm`. It
recognizes resource-bounded Wasm 3.0 modules while retaining every input byte,
section range, and a raw SHA-256 CID. A borrowed module can be promoted to an
immutable `Arc`-backed artifact, and `parse_shared` retains an existing
`Arc<[u8]>` allocation for concurrent proof-package workflows. Neither form
claims that the bytes denote a particular HOL term; that still requires the
checked decoding evidence above.

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

Positive reachability has an executable checked proof interface:
`AssertionReachability::prove_calls_assert` accepts the three concrete witness
facts (`starts`, `Steps`, and the pre-host-call observation) and introduces the
two existential states. The pinned audit now derives the `instantiate`,
`store`, and `invoke` graph facts through retained SpecTec definition
productions and checked equation transport. It also exposes each remaining
production condition instead of assuming those graph facts wholesale. The
initialization `Steps` fact is derived from the retained SpecTec reflexivity
rule and checked equality transport; the exact equalities relating its
structural source and target to the instantiation configurations remain
grounding premises. The final reflexive `Steps` fact is derived the same way,
leaving only its two structural equalities as premises. Export selection
remains an explicit grounding premise. The host-call observer is an immutable
structural predicate equating its configuration with the exact retained
`$invoke` production result; its concrete fact is discharged by checked beta
reduction and equality reflexivity. Interpreter traces cannot be passed in
place of theorem handles.

For `FALSE`, the negative proof opens the concrete exported-function predicate
and reduces non-reachability to two independent laws: every export list exposed
by instantiating the empty module equals the structural empty list, and that
list has no members. Export projection is a relational view of the exact
nine-field module-instance constructor, while membership is the exact
`expression:Membership` operation recorded by the lowering. These laws are
still premises; they are no longer aliases for `not callsAssert(FALSE)`.

Individual-function equivalence is contextual observational equivalence: it
quantifies every function-hole replacement context and then every outer
module-observation context. It requires both sides to agree whether each
context is admissible and, when admissible, to agree on the observation. Thus
contextual rejection is observable and the relation is transitive. Checked
reflexivity, symmetry, and transitivity theorems establish the equivalence
laws, and a checked discriminator refutes equivalence when one side alone is
admissible. Equivalence is relative to the observation predicate supplied by
the caller; a complete Wasm observation suite belongs in that parameter. The
checked replacement rule specializes supplied function-equivalence evidence,
and the closed replacement-soundness theorem proves directly that function
equivalence implies equivalence of the replaced modules. The latter theorem
is structural and premise-free; neither result depends on an evaluator or on
the pending concrete representation laws.
