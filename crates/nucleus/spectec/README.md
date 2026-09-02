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
