# SpecTec kernel frontend

`covalence-nucleus-spectec` is the semi-trusted boundary between an untrusted
SpecTec elaboration and a checked HOL kernel. A compiler records an exhaustive
mapping from every SpecTec IL declaration to checked kernel rows. Finishing is
impossible while a declaration is unaccounted for.

The portable output is an ATProto DRISL object linking the exact source bundle
and exact kernel CBOR bytes. The mapping is provenance and audit data, not
theorem authority: only facts present in the linked arena and accepted through
the checked kernel boundary are trusted.

`AddSlicePlan` is the closed coverage IR for the first parameter-only add
theorem. It classifies every elaborated declaration, nested clause, and nested
rule by structural selector as one translation case or an explicit rejection.
Selected cases carry pinned raw-source line mappings. The plan assigns no HOL
meaning and cannot create facts.

The underlying `Coverage`, `CoverageDisposition`, `CoveragePlan`, and
`CoverageArtifact` types are generic schema APIs. Other slices can compose the
same exact-input links and declaration/clause/rule shape with their own case,
rejection, and source vocabularies; the add-specific aliases, builder, and
closed codec are only one policy instance.

`AddSliceArtifact` encodes that plan as a closed ATProto-profile DRISL record
linked to the exact bundle and elaborated-AST CIDs. Its SHA-256 DRISL CID is the
translation CID; it remains provenance rather than theorem authority.
Decoding rechecks the closed schema, CID profiles, selector and case uniqueness,
and translate/reject invariants. Source verification then rebuilds the plan from
the linked elaborated document and requires exact coverage equality.

`SelectedCompiler<Case>` is the generic checked dispatch boundary. It derives
the exact required case set from a coverage plan, ignores only explicit
rejections, applies each selected case transactionally once, and refuses to
finish while any selected declaration, clause, or rule lacks resident roots.

`parameterized_document_with` supports incremental semantic grounding through
an immutable map from overload-safe `InterpretationSignature` values to HOL
terms. Supplied implementations are classifier-checked; missing operations
remain inspectable as categorized grounding obligations. Supplying every
operation does not itself close a theory, because supplied terms may retain
free variables and the resulting theory is still syntax until used by checked
proof rules.

`Proposition<Atom>` is an immutable, `Arc`-shared schema for small program-
logic experiments. Its `CallsAssert<Program>` atom denotes the open claim that
some permitted invocation and imported-I/O behavior reaches a named assertion
import. `AssertCombinator<Leaf>` is explicitly Boolean scaffolding, not
WebAssembly syntax: it gives `TRUE`, `FALSE`, `AND`, and `OR` propositions a
compositional mapping to that schema. Closed examples lower to HOL and produce
positive or negative kernel-checked theorems. They exercise the composition API
without treating an interpreter as theorem authority. A future semantic
interpretation must relate open leaves and exact program bytes to the complete
`SpecTec` theory before these examples establish WebAssembly behavior. See
[`GROUNDING.md`](GROUNDING.md) for that acceptance boundary.

`Evidence` composes checked positive or negative conclusions while retaining
all theorem premises, which is the expected shape for early semantic results
conditional on the complete `SpecTec` theory and explicit representation laws.
`Established` is reserved for the stronger premise-free case; conversion to it
rechecks that no assumptions remain.

`ParameterizedDocument::evidence_scope` enforces that boundary mechanically.
It accepts only unit premises naming the exact complete theory, one of its
source-indexed declaration constraints, or a caller-enumerated grounding law.
In particular, an interpreter observation or the desired goal cannot be
silently smuggled into a purported semantic proof.

`HolTheory::derive_constraint` is the first checked bridge from the complete
theory term into usable theorem evidence. It derives any source-indexed
declaration equation from the exact stored conjunction spine, leaving the
complete theory as its single visible premise. The full pinned-document audit
uses it to derive the Wasm `Steps` equation and validates that theorem through
the evidence scope.

`spectec_execution` extracts the exact lowered `instantiate`, `invoke`, and
`Steps` declarations from the pinned source vocabulary. It adapts SpecTec's
tuple-argument `Steps` relation to the curried predicate consumed by
`AssertionReachability`; construction is classifier-checked and creates no
theorem fact.

`SpecTecValueBuilder` is the corresponding generic structural API. It composes
recorded list, optional, tuple, and tagged-case operations immutably and
transactionally; `empty_wasm_module` is deliberately only a thin composition
of those operations. Missing constructor arities are explicit failures rather
than newly invented semantics.
