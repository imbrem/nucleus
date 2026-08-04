# HOL-omega table MVP

Status: proposed API and representation direction. The kind slice is ready to
implement. The complete type/term constructor vocabulary is blocked on one
small formal-specification mismatch described below.

## Goals

The first HOL-omega implementation should be easy to inspect, hard to misuse,
and replaceable behind a stable operation-oriented API. SQLite stores immutable
canonical syntax and accepted judgements. Short Rust functions perform kinding,
typing, and LCF inference. SQL constraints defend structural invariants but do
not become a second implementation of the logic.

The MVP should provide:

- integer IDs for admitted kinds, types, terms, and assumption contexts;
- direct kind/type/rank and local-closure queries;
- exact free and unbound variable queries;
- user-owned metadata in satellite tables;
- immutable finite sets of closed Boolean assumptions;
- append-only proved judgements;
- protocol policy checks around every trusted read, insertion, and rule;
- one physical representation, while leaving room for future namespaces and
  imported representations.

## Formal audit

The current reference is the `inventing-the-universe` branch of
`/home/tekne/projects/tekne.dev`, especially:

- `lean/ProjectBeth/ProjectBeth/Defs/HOLOmega/Syntax.lean`;
- `lean/ProjectBeth/ProjectBeth/Defs/HOLOmega/Substitution.lean`;
- `lean/ProjectBeth/ProjectBeth/Defs/HOLOmega/Kernel.lean`;
- `lean/ProjectBeth/ProjectBeth/Defs/HOL/Contexts.lean`.

This material is active work, not yet a versioned Nucleus specification. The
last file was untracked during the audit and `Kernel.lean` was changing.

The committed extrinsic syntax currently has:

```text
Kind = star | arrow Kind Kind

Type = base | bound | lambda | application | bool | arrow | subtype

Term = bound | application | lambda | type-application | type-lambda
     | bool | equality | epsilon | abstraction | representation
```

There are several important consequences:

1. Type and term syntax are mutually recursive because a subtype contains a
   term predicate.
2. Term binders and type binders use separate de Bruijn depths.
3. A subtype predicate is checked under a fresh singleton term environment
   containing its carrier type, not the ambient term environment.
4. The ordered typing environment called `Gamma` in Lean is not a logical
   context of Boolean assumptions.
5. The draft contexts work separately compares finite sets of assumptions,
   binary assumption trees, and one conjunction term.
6. Semantic universes such as the power tower are model carriers, not syntax
   annotations. Universe levels do not belong in the first tables.

The active shallow kernel now distinguishes type-operator `lambda/application`
from polymorphic `all/instantiation`, while the committed extrinsic syntax
still overloads `lambda/application` for term type abstraction/application.
The project must settle that tiny normative calculus before freezing type and
term constructor tags or proof rules.

## Stable public shape

The API should stabilize operation families and typed IDs before it stabilizes
the physical schema. IDs are database-local integers with distinct Rust
newtypes:

```rust
pub struct KindId(i64);
pub struct TypeId(i64);
pub struct TermId(i64);
pub struct ContextId(i64);

impl<P: HolPolicy> Connection<Hol<P>> {
    pub fn insert_kind(&mut self, kind: &Kind) -> Result<KindId>;
    pub fn insert_type(&mut self, ty: &ClosedType) -> Result<TypeId>;
    pub fn insert_term(&mut self, term: &ClosedTerm) -> Result<TermId>;

    pub fn kind(&mut self, id: KindId) -> Result<KindView>;
    pub fn kind_rank(&mut self, id: KindId) -> Result<u32>;
    pub fn type_kind(&mut self, id: TypeId) -> Result<KindId>;
    pub fn term_type(&mut self, id: TermId) -> Result<TypeId>;

    pub fn type_is_locally_closed(&mut self, id: TypeId) -> Result<bool>;
    pub fn term_is_locally_closed(&mut self, id: TermId) -> Result<bool>;
    pub fn type_free_variables(&mut self, id: TypeId) -> Result<Vec<TypeVarId>>;
    pub fn term_free_variables(&mut self, id: TermId) -> Result<FreeVariables>;
    pub fn type_unbound_variables(&mut self, id: TypeId) -> Result<Vec<UnboundTypeVar>>;
    pub fn term_unbound_variables(&mut self, id: TermId) -> Result<UnboundVariables>;

    pub fn define_context(&mut self, members: impl IntoIterator<Item = TermId>)
        -> Result<ContextId>;
    pub fn context_members(&mut self, id: ContextId) -> Result<Vec<TermId>>;
}
```

The first insertion methods admit closed roots. A later explicitly named API
may admit open roots under supplied type- and term-binder environments. Never
make an implicit "possibly open" insertion operation part of the trusted API.

Proof API methods should correspond to individual rules and run inside a
generative session which borrows one connection. The session can hold several
theorem capabilities for compositional rules, but its invariant brand cannot
escape or cross connections:

```rust
pub struct ProofSession<'brand, P> {
    connection: &'brand mut Connection<Hol<P>>,
    brand: PhantomData<fn(&'brand ()) -> &'brand ()>,
}

pub struct Theorem<'brand> {
    context: ContextId,
    conclusion: TermId,
    brand: PhantomData<fn(&'brand ()) -> &'brand ()>,
}
```

Only trusted session rule methods construct `Theorem`. Persisted local
judgements may be loaded only through a session after policy and structural
checks. There is no public `insert_theorem(context, term)` escape hatch, and
detached structural validation alone cannot mint theorem capabilities.

The exact AST and rule enums should carry an explicit calculus/schema version
until the `all/instantiation` issue is reconciled. Constructor additions must
not silently change the meaning of an existing database.

## Binding representation

Persisted syntax should refine the raw Lean representation in one useful way:
distinguish bound occurrences from content-addressed free symbols.

```text
Bound(index, declared kind or type)
Free(symbol ID, declared kind or type)
```

Every term row stores its admitted type and every type row stores its admitted
kind. Bound occurrences also record their expected annotation. This makes an
interned lambda body or other open subterm independently queryable through the
required API.

Two cached nonnegative depths make local closure constant time:

- `required_type_depth` for free de Bruijn type indices;
- `required_term_depth` for free de Bruijn term indices.

For a bound occurrence at index `i`, the requirement is `i + 1`. Ordinary
constructors take the maximum child requirement. A binder subtracts one from
its body's corresponding requirement, saturating at zero. A subtype predicate
is validated under its special singleton term environment.

Exact free-symbol and unbound-index queries initially use recursive CTEs. The
CTE carries both depths because a shared DAG node may occur under different
numbers of binders. Materialized variable tables are rebuildable optimizations,
not logical authority.

## Physical representation

Use separate object tables for kinds, types, and terms, plus one narrow table
per constructor. This is more verbose than a wide tagged row, but each table
has one meaning, imports are easier to diagnose, and future constructor changes
do not add more nullable columns to every node.

### Kinds

```sql
CREATE TABLE hol_kind (
    kind_id INTEGER PRIMARY KEY,
    rank INTEGER NOT NULL CHECK (rank >= 0)
) STRICT;

CREATE TABLE hol_kind_star (
    kind_id INTEGER PRIMARY KEY REFERENCES hol_kind
) STRICT;

CREATE TABLE hol_kind_arrow (
    kind_id INTEGER PRIMARY KEY REFERENCES hol_kind,
    domain_id INTEGER NOT NULL REFERENCES hol_kind,
    codomain_id INTEGER NOT NULL REFERENCES hol_kind,
    UNIQUE(domain_id, codomain_id)
) STRICT;
```

Seed one canonical `star`. Define rank normatively as:

```text
rank(star) = 0
rank(K -> L) = max(rank(K) + 1, rank(L))
```

This is the order convention, not plain syntax-tree height. The Lean work does
not currently define kind rank, so Nucleus must state and test this convention.

The schema-level invariant that every object has exactly one constructor row
is enforced on trusted writes and rechecked when admitting an imported
database.

### Types and terms

The common headers are stable even while constructor tags remain versioned:

```sql
CREATE TABLE hol_type (
    type_id INTEGER PRIMARY KEY,
    kind_id INTEGER NOT NULL REFERENCES hol_kind,
    required_type_depth INTEGER NOT NULL CHECK (required_type_depth >= 0)
) STRICT;

CREATE TABLE hol_term (
    term_id INTEGER PRIMARY KEY,
    type_id INTEGER NOT NULL REFERENCES hol_type,
    required_type_depth INTEGER NOT NULL CHECK (required_type_depth >= 0),
    required_term_depth INTEGER NOT NULL CHECK (required_term_depth >= 0)
) STRICT;
```

Constructor tables contain the object ID, immutable child IDs, and immediate
annotations. A uniqueness constraint over the complete constructor payload
provides hash-consing. Children must already exist, so ordinary trusted
insertion builds an acyclic DAG even though type and term tables refer to one
another. Import admission still performs an explicit cycle check.

### Why not a tagged wide table?

A tagged wide table gives shorter traversal queries and fewer tables. It is a
credible alternative and should be benchmarked. Its nullable columns and
tag-dependent checks make malformed imports less obvious, however, and a new
constructor changes the shared table. For a first auditable TCB, constructor
tables win narrowly.

### Why not one universal syntax table?

A universal table simplifies generic DAG traversal and future base-logic
namespaces, but SQLite cannot express child-sort constraints cleanly. It would
prematurely merge kind, type, and term identity spaces. Keep it as a possible
interchange or base-logic representation.

### Why not canonical blobs?

Canonical blobs are excellent export/CAS encodings. They make the required
kind, type, closure, and variable queries decoder-dependent and move canonical
decoding into the TCB. Use them later behind another validated representation,
not as the first operational tables.

## Validation and insertion

One trusted insertion transaction performs:

1. policy admission for the requested operation;
2. lookup of every already-admitted child and cached annotation;
3. one short Rust kinding or typing rule;
4. computation of rank, type, kind, and required binder depths;
5. reuse of an existing canonical constructor row, or atomic allocation of an
   object row plus exactly one constructor row;
6. optional protocol-specific metadata writes;
7. commit only after every invariant holds.

SQLite enforces strict storage, foreign keys, elementary ranges, and canonical
constructor uniqueness. Rust enforces the calculus. Avoid triggers for typing
and inference: they enlarge and obscure the TCB without eliminating the Rust
checker.

An untrusted imported database is admitted through a separate validator that
recomputes all cached fields, checks constructor exclusivity, checks acyclicity,
and applies the same rule functions. A normal trusted connection never exposes
raw SQL.

## Metadata

User metadata does not participate in canonical syntax identity. Protocols own
satellite tables with real typed columns and indexes:

```sql
CREATE TABLE my_term_metadata (
    term_id INTEGER PRIMARY KEY REFERENCES hol_term,
    source_span TEXT,
    display_name TEXT
) STRICT;
```

The protocol may write metadata in the same insertion transaction. HOL kinding,
typing, and proof code never consults it. A generic EAV table may help a UI but
must not replace user-defined relational metadata.

## Logical contexts

Keep binder environments and assumption contexts separate in names and types.
A logical context is an immutable finite set of locally closed Boolean terms:

```sql
CREATE TABLE hol_context (
    context_id INTEGER PRIMARY KEY,
    member_count INTEGER NOT NULL CHECK (member_count >= 0)
) STRICT;

CREATE TABLE hol_context_member (
    context_id INTEGER NOT NULL REFERENCES hol_context,
    term_id INTEGER NOT NULL REFERENCES hol_term,
    PRIMARY KEY(context_id, term_id)
) STRICT, WITHOUT ROWID;

CREATE TABLE hol_judgement (
    context_id INTEGER NOT NULL REFERENCES hol_context,
    term_id INTEGER NOT NULL REFERENCES hol_term,
    PRIMARY KEY(context_id, term_id)
) STRICT, WITHOUT ROWID;

CREATE TABLE hol_proof_event (
    event_id INTEGER PRIMARY KEY,
    context_id INTEGER NOT NULL,
    term_id INTEGER NOT NULL,
    rule TEXT NOT NULL
) STRICT;
```

Reserve context zero for the empty set. Once a judgement mentions a context
ID, changing its members would change the judgement's meaning. Therefore
context construction is atomic and there is no member mutation API.

The v1 store assigns one canonical ID to each extensional member set. This is
an identity convention and optimization, not an additional logical rule.

`hol_judgement` is the sole authoritative proposition set. Proof-event rows
are optional observational provenance: rule strings are not proof evidence,
multiple events may name one judgement, and deleting events does not change
the logical state.

The proposed directed union relation is valuable but is not the same thing as
the extensional member table. It can represent an opaque compositional context
equivalent to a binary union. Add it after the exact set semantics and proof
rules are fixed.

## Additional judgement tables

Context implication, equivalence, union, and typed term equality should begin
as append-only proved edges with provenance. Do not make a destructive
union-find the authoritative database:

- union-find discards which accepted rule established an edge;
- term equality depends on context and type;
- context equivalence is two implication directions;
- signed snapshots should retain their accepted claims.

Rust or TEMP-table union-find and transitive-closure indexes may accelerate
queries and can be rebuilt from the append-only edges. Deleting those caches
must not delete logical authority.

## Policy and TCB

Use a protocol state such as `Hol<P>` where `P: HolPolicy` decides whether each
operation is allowed and may record it. Policy checks distinguish at least:

- read syntax;
- intern syntax;
- define contexts;
- read judgements;
- apply each inference rule;
- persist a judgement;
- read or write a named metadata extension.

This supports a static allowlist, a dynamic proof-footprint recorder, or a
signature/VFS admission policy without changing rule code.

The trusted surface is limited to schema admission, constructor validation,
cache recomputation, typed ID minting, rule functions, and policy checks.
Proof traces, tactics, metadata, recursive-query accelerators, and UI rendering
remain outside it.

## Namespaces and multiple representations

The public typed-ID API should not promise one physical representation forever,
but the first implementation should have one. Do not add a store ID to every
inner primary key yet.

Treat each validated attached database/schema as a distinct store. The later
namespace layer maps database hashes and exported IDs to names or local opaque
terms. Cross-store or cross-representation equality is an explicit proved
relation, never an accidental integer comparison.

Do not use negative IDs as an implicit namespace in the first schema. Do not
put dynamic table names in trusted prepared statements until representation
admission exists.

## Staged implementation

1. Implement canonical kinds, the stated rank convention, typed IDs, policy
   hooks, and corruption tests.
2. Freeze a one-page normative HOL-omega type/term calculus resolving
   `lambda/application` versus `all/instantiation`.
3. Implement canonical types, two-sorted closure data, and kind queries.
4. Implement terms, type queries, and recursive free/unbound variable queries.
5. Add atomic immutable contexts and the empty context.
6. Add the smallest LCF proof object and rule set, then persist theorem rows.
7. Add an independent validator for untrusted attached stores.
8. Prototype append-only implication, union, and typed equality edges with
   rebuildable in-memory or TEMP-table accelerators.
9. Add namespaces, canonical blob exports, and alternative representations
   only after the single-store API is exercised.

Property tests compare every cached rank/depth and recursive variable query
against a small pure Rust reference walk. Mutation tests corrupt each redundant
field and child relationship and require import admission to fail. Policy tests
prove each operation touches only its declared table footprint.

## Open decisions

Before the type/term slice, settle:

- explicit `all/instantiation` versus overloaded type lambda/application;
- exact syntactic type equality versus beta-eta definitional equality;
- whether free symbols are primitive variables or signature constants;
- the exact Boolean theorem calculus versus typed equality judgement;
- whether subtype constructors remain in the first executable kernel.

These decisions version constructors and rules. They do not change the stable
outer API of typed insertion, structural queries, immutable contexts, and
connection-branded theorems.
