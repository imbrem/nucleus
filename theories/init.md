# `init.json` bootstrap theory specification

Status: proposed version 0 specification for `nucleus.hol.init.array-v0`.

This document specifies the source manifest in [`init.json`](init.json). The
manifest is the first standard library presented to a Nucleus HOL kernel. It is
human-reviewable JSON, not the trusted representation and not itself a content
address. A deterministic importer resolves it into checked, content-addressed
kernel objects. See [`kernel-content-addressing.md`](kernel-content-addressing.md)
for the importer and storage plan.

## Goals

The bootstrap theory must:

1. use only the primitive type-family HOL kernel plus an explicit initial
   signature;
2. define the logical vocabulary and ordinary algebraic datatypes needed by
   later libraries;
3. record every definition and theorem as a dependency-ordered declaration;
4. distinguish definitions, primitive signature entries, proved theorems, and
   unfinished proof obligations;
5. elaborate to one canonical object graph independent of JSON whitespace,
   object-key order, comments, and local implementation details;
6. reject ambiguity, shadowing, ill-kinded families, ill-typed terms, malformed
   proofs, forward references, and undeclared primitives before changing a
   kernel environment; and
7. be reproducibly importable: two conforming importers given the same
   manifest and parent theory address must produce the same root address.

The bootstrap is not a new trusted axiom schema. A `definition` is accepted
only after its body checks. A `theorem` is accepted only after its proof checks.
A deferred declaration is useful design metadata but is not exported into a
checked theory and cannot be referenced by later checked declarations.

## The three representations

The design deliberately separates three layers:

| Layer | Purpose | Names/references | Trusted? |
| --- | --- | --- | --- |
| `init.json` | reviewable source manifest | UTF-8 names and prior declarations | no |
| checked arena | bounded parsing, scope/sort/type/proof checking | backward row indices | transient |
| CAS object graph | identity, sharing, transport, imports | 256-bit child addresses | yes, after checking |

Names are presentation and environment lookup keys. They are not the identity
of an expression. Bound term and type variables use de Bruijn indices, so
alpha-renaming cannot change an expression address. Declaration names do affect
the address of the theory map that exports them, but do not affect the address
of their type, body, or proof objects.

## Top-level object

The top-level value has exactly these fields:

```json
{
  "format": "nucleus.hol.init.array-v0",
  "status": "design-sketch",
  "encoding": { "...": "self-description for readers" },
  "declarations": []
}
```

- `format` is exactly `nucleus.hol.init.array-v0`. Any incompatible change uses
  a new format string.
- `status` is one of:
  - `design-sketch`: may contain deferred bodies/proofs or surface macros not
    yet implemented by the importer;
  - `checked`: every exported declaration elaborates and checks, although the
    library inventory may still be incomplete;
  - `complete`: every required declaration in this specification is exported
    and the conformance tests pass.
- `encoding` is descriptive and must agree with the constants constrained by
  [`init.schema.json`](init.schema.json). It does not alter decoding.
- `declarations` is an ordered array. Order is semantically significant for
  name resolution and permits a streaming importer.

Unknown top-level fields are rejected. JSON is decoded as UTF-8. Duplicate
object keys, non-integer numbers, invalid Unicode, and trailing data are
rejected. The source file need not have canonical whitespace because it is not
hashed directly.

## Declaration rows

Every declaration is a six-element array:

```text
[class, name, parameters, type-or-kind, body, properties]
```

### `class`

The classes are:

- `section`: a non-semantic heading. Parameters are empty and the type and body
  are null. It creates no name and is excluded from the canonical theory.
- `type-family`: introduces a type or type family. `type-or-kind` is its kind.
- `constant`: introduces a primitive signature term. Its body is null and its
  type is checked. This is the only declaration class that can extend term
  syntax without a definition.
- `definition`: introduces a transparent constant or family abbreviation.
  Its body must check at the declared type or kind.
- `theorem`: introduces a proposition together with a proof certificate. The
  `type-or-kind` field is the proposition and the body is its proof.

A checked bootstrap should have no primitive `constant` except entries that
are intentionally part of the initial signature, such as the infinite type
and its certified structure. Equality, application, lambda, choice, subtype
abstraction, and subtype representation are kernel syntax, not constants.

### `name`

Names are nonempty NFC-normalized UTF-8 strings. Version 0 uses the conservative
grammar `[A-Za-z][A-Za-z0-9_.?-]*`. Names are unique across all semantic
declarations. A section heading may repeat a semantic name because it is not
entered into the environment, although unique section names are recommended.

Resolution is exact and case-sensitive. A name resolves only to an earlier
semantic declaration or to an entry in the fixed kernel vocabulary. There is
no implicit namespace opening, overloading, or priority-based resolution.

### `parameters`

Parameters are pairs `[name, classifier]`, ordered outermost to innermost.

- A family parameter is classified by a kind, for example
  `["A", ["kind.star"]]` or
  `["F", ["kind.arr", ["kind.star"], ["kind.star"]]]`.
- A term parameter is classified by a type expression, for example
  `["n", "nat"]`.

Parameter names must be unique within a declaration and may shadow global
names only inside that declaration. Elaboration replaces parameter names with
de Bruijn indices. A declaration with parameters denotes iterated family
lambda or term lambda at the storage layer; parameters are not stored as names.

### `type-or-kind`

For `type-family`, this is a kind. For `constant` and `definition`, it is a
type. For `theorem`, it is a closed Boolean term. It is null only for `section`.

Version 0 kinds are:

```text
Kind ::= ["kind.star"]
       | ["kind.arr", Kind, Kind]
```

Arrows associate to the right. The string `bool` is surface sugar for
`["ty.bool"]`; `A->B` and applications such as `list A` are permitted only in
the design sketch. The checked importer accepts array expressions exclusively,
or first expands these strings with a separately specified surface parser.
Canonical objects never contain these strings.

### `body`

- A `definition` body is an expression.
- A `theorem` body is a proof certificate.
- A primitive `constant` has a null body.
- A `type-family` has either a defining family expression or a null body when
  it is an initial-signature primitive.
- A `section` has a null body.

During `design-sketch`, a null theorem body records a deferred obligation. It
does not enter the checked environment. The same applies to any explicitly
deferred definition. The importer reports all deferred declarations and then
rejects a request to produce a `checked` or `complete` root.

### `properties`

`properties` is an ordered list of theorem names promised by a datatype or
definition. It is an inventory and documentation aid, not proof evidence.
Every property in a `complete` manifest must occur later as a theorem
declaration. A property must not be treated as an axiom merely because its name
appears here.

## Core expression language

After surface expansion, every expression is either a prior declaration
reference or a tagged array. Core tags correspond exactly to
`Nucleus.Hol.FamilySub.Json.Tag`:

| Tag | Operands | Result |
| --- | --- | --- |
| `ty.bool` | none | type `bool : *` |
| `ty.arr` | domain, codomain | type `domain -> codomain : *` |
| `ty.app` | domain kind, codomain kind, family, argument | family application |
| `ty.lam` | domain kind, codomain kind, body | type-family lambda |
| `ty.bv` | kind, de Bruijn index | bound type-family variable |
| `ty.sub` | carrier, one-bound-variable predicate | guarded subtype |
| `sig.fam` | declared signature family symbol | primitive family |
| `tm.bv` | de Bruijn index | bound term variable |
| `tm.fv` | numeric identity, type | typed free term variable |
| `tm.app` | function, argument | application |
| `tm.lam` | domain, body | lambda |
| `tm.bool` | JSON Boolean | primitive Boolean term |
| `tm.eq` | type, left, right | typed equality proposition |
| `tm.eps` | type, predicate | Hilbert choice |
| `tm.abs` | carrier, predicate, value | guarded subtype abstraction |
| `tm.rep` | carrier, predicate, value | guarded subtype representation |
| `sig.tm` | declared signature term symbol | primitive term |

The source tree form nests operands. The importer hash-conses the tree into the
positional arena described by `FamilySub.Json.Row`; each row can refer only to
strictly earlier rows. The checked arena validates references, expected sorts,
type-variable kinds, and bound-term scopes before expressions reach the proof
checker.

`tm.fv` is allowed in reusable theorem objects and signatures but no exported
bootstrap definition or theorem may have an unabstracted free variable.

## Surface macros

Names such as `family.product`, `initial-algebra`, and `graph.recursor` in the
current design sketch are macros, not kernel constructors. Each macro must have:

1. a versioned name;
2. an arity and operand-sort declaration;
3. a deterministic expansion into core expressions and proof certificates;
4. no access to network, time, randomness, filesystem ordering, or mutable
   global state; and
5. golden expansion tests.

Macros are eliminated before hashing. Consequently a macro implementation may
be optimized without changing addresses only when it produces byte-identical
canonical core objects. A changed expansion is a new library version and
normally yields new addresses.

Required version 0 macro families are:

- derived logic: `true`, `false`, `not`, `and`, `or`, `imp`, `exists`, `forall`;
- guarded subtype packaging and its `abs`/`rep` laws;
- Church/guarded encodings for unit, product, and coproduct;
- option as `unit + A`;
- nonempty finite types as iterated `unit + _` (HOL types are inhabited, so
  the base family is `Fin (n+1)`, not an empty `Fin 0`);
- natural numbers as the inductive intersection subtype of `ind`;
- graph-based recursion and uniqueness;
- lists as the least closed subtype for `1 + A × X`;
- canonical representatives for integer and rational quotient relations; and
- Dedekind cuts for reals.

## Proof certificates

The proof object vocabulary mirrors all constructors of
`FamilySub.Proves` and `FamilySub.EqTm`. It must include:

- hypothesis, truth, false elimination, and Boolean cases;
- equality reflexivity, symmetry/transitivity through `EqTm`, congruence,
  equality modus ponens, and conversion;
- beta and eta conversion;
- Hilbert choice;
- generalization and bound/hypothesis weakening;
- propositional antisymmetry; and
- guarded-subtype `abs`/`rep`, witness predicate, congruence, and injectivity
  rules exposed by the kernel.

Every proof node records child addresses and the minimum annotations required
for deterministic checking. Types inferable uniquely from checked children are
not duplicated. If type inference is unavailable or non-unique for the active
signature, the certificate carries the expected type address explicitly.

The kernel checks proofs; it never trusts a theorem tag or a property list.

## Required bootstrap inventory

The following inventory defines “all basic datatypes” for version 0. Entries
marked derived must be definitions, not new axioms.

### Logic and predicates

- truth and falsehood;
- negation, conjunction, disjunction, implication, iff;
- existential and universal term quantification;
- predicate membership, subset, empty/full set, union, intersection, and
  complement as functions into `bool`;
- identity and function composition.

### Finite algebraic data

- `unit`, its inhabitant, and uniqueness;
- binary product with pair, projections, beta, eta, extensionality, and
  constructor injectivity;
- binary coproduct with injections, eliminator, beta, injectivity,
  disjointness, and exhaustiveness;
- option with `none`, `some`, cases, injectivity, and disjointness;
- nonempty finite ordinals `finSucc n` with zero, successor/cast, cases,
  injectivity, and cardinality;
- tuples as right-associated products and records as named presentation only.

There is intentionally no empty HOL type in the base logic. An “empty” syntax
extension must either use a guarded encoding whose carrier remains inhabited or
belong to a different logic.

### Recursive data

- natural numbers, zero, successor, induction, recursion, no-confusion;
- addition, multiplication, exponentiation, truncated subtraction, comparison,
  minimum, maximum, and their defining laws;
- lists with nil, cons, recursion, induction, no-confusion, append, map, fold,
  length, reverse, membership, all/any, head/tail as options, take, and drop;
- nonempty lists as `A × list A`;
- vectors as the guarded subtype of lists of length `n`;
- binary trees with leaf/node recursion and induction.

The recursive encodings may use least closed subtypes and graph-defined
recursors. `NaturalRecursorExistence` (and analogous datatype certificates)
must ultimately be proved by finite compatible graphs before the manifest can
be marked complete.

### Numbers

- integers as canonical representatives of pairs of naturals;
- rationals as canonical reduced signed fractions with nonzero denominator;
- reals as Dedekind cuts over rationals;
- embeddings `nat -> int -> rat -> real` and preservation of zero, one,
  addition, multiplication, order, and injectivity;
- the expected ordered-ring/field laws and real completeness theorem.

Only the natural-number layer is needed for the first loader milestone. Integer,
rational, and real declarations remain in the same specification so their
dependencies and eventual proof obligations are visible.

## Dependency and acceptance rules

The importer processes declarations left-to-right. For each semantic row it:

1. validates row shape and local parameter uniqueness;
2. resolves names only against the parent theory, kernel vocabulary, local
   parameters, and earlier accepted rows;
3. expands surface macros;
4. checks family kinding or term typing;
5. checks the definition body or proof certificate;
6. verifies declared closure (no escaping bound variables; no unabstracted
   free variables for bootstrap exports);
7. stores canonical expression/proof/declaration objects; and
8. extends a tentative immutable environment.

Failure is atomic: no theory root is published unless every non-deferred row
requested for the import succeeds. Duplicate names are always errors. Cycles
must be represented through a justified recursive construction, never through
forward declaration references.

## Canonical theory result

A successful import produces:

- an ordered declaration-log object, preserving dependency order;
- a canonical name-map object, sorted by UTF-8 name bytes;
- the parent theory address;
- the format and kernel-semantics version addresses; and
- a theory root addressing those objects.

The declaration log makes auditing and incremental replay straightforward. The
sorted map makes name lookup independent of insertion-map implementation. The
theory root, not the source JSON byte hash, is the identity imported by later
theories.

## Conformance tests

A version 0 importer is conforming when it passes all of these tests:

1. JSON schema and semantic validator accept the checked fixture.
2. Reformatting or reordering top-level object keys leaves the theory address
   unchanged.
3. Renaming bound parameters leaves expression and theory addresses unchanged.
4. Renaming an exported declaration changes the name-map/theory address but
   not the body expression address.
5. Repeated equal subexpressions yield one expression address.
6. A changed child changes every ancestor address.
7. A wrong fetched byte sequence is rejected against its requested address.
8. Forward arena references, cycles, bad scope, bad kinds, bad types, and bad
   proofs are rejected.
9. A deferred theorem cannot be referenced by a checked declaration.
10. Importing the checked `init.json` twice into empty stores yields the same
    theory root and identical reachable object sets.
11. Fetching all objects reachable from only the theory root into a fresh store
    permits independent revalidation and lookup of representative declarations
    (`unit`, `product`, `option`, `nat`, and `list`).
12. Lean model tests and the executable kernel agree on the accepted roots and
    calculated addresses for the golden fixture.

## Versioning

There are three independent versions:

- source manifest format (`array-v0`);
- canonical object encoding;
- kernel semantics/proof-rule set.

All three are domain-separated in stored objects. A source-compatible importer
may target a newer object encoding, but it must report that target and produce a
different theory root. Kernel semantics cannot silently change beneath an
existing theory address.
