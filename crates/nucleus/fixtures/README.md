# Local proposition fixtures

The versioned TSV files form a language-neutral conformance corpus. They use
only UTF-8 records, tabs, signed decimal integers, commas, and a dot for an
empty value. Consumers must reject unknown record types or outcome names.

`local_prop_v1.tsv` groups physical rows into cases:

```text
case  outcome  premise  source  conclusion  reason
```

The outcomes distinguish `accept`, `reject-storage`, `reject-cycle`, and
`reject-empty`. Rows use signed decimal literals, source `0`, reason `0` for a
definition, and a positive reason for a theorem. A case is one atomic table:
every row must be accepted together or none of it is. Cycles follow atom
dependencies, so the sign of a conclusion does not break a cycle.
An empty definition is represented by its premise and reason zero with a dot
in the conclusion column; it is an attempted group operation, not a physical
row and not an assertion that an empty database is invalid.

`local_prop_queries_v1.tsv` specifies direct, classification-aware query
answers for accepted cases. `definition` returns only reason-zero conclusions;
`implied-by` and `implying` return only positive-reason theorem candidates.
Results use SQLite primary-key order, with candidates encoded as
`premise>conclusion`. Reasons classify stored rows but are deliberately not
exposed as logical query authority.

`local_prop_deletion_v1.tsv` is the minimal arbitrary-row-deletion
counterexample. Under its valuation, the complete definition `1 := 2 and 3` is
false while the partial group left after deleting `1 -> 3` is true. Consumers
must therefore replace or delete a definition as one complete atomic group.

Rust tests load all three fixtures through the checked schema and semantic
validator. `Nucleus.PropTable.Fixture` embeds and parses those same files as a
Lean build input without depending on SQLite or Rust. Agreement is
differential evidence, not a refinement proof.

Demo-facing SAT integration belongs above this authority layer. Its seam is:
list/get/show named problems; select canonical DIMACS; verify a model or binary
LRAT artifact; admit only resulting checked `Fact`s; inspect judgement and
certificate metadata separately. Initial host fixtures should include a small
bitblasted AND family. ASCII LRAT is an explicit pretty-print mode only.
