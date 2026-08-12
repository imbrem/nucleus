# Local proposition fixtures

`local_prop_v1.tsv` is a language-neutral ordered row corpus:

```text
premise  source  conclusion  reason
```

It uses signed decimal literals, source `0`, reason `0` for definitions, and
positive reasons for proved rows. Rust tests load it through the checked schema.
SQLite can load the non-comment rows into `prop_row` with tab-separated import;
a later Lean conformance test can parse the same four integers. Passing these
tests is differential evidence, not a refinement proof.

Demo-facing SAT integration belongs above this authority layer. Its seam is:
list/get/show named problems; select canonical DIMACS; verify a model or binary
LRAT artifact; admit only resulting checked `Fact`s; inspect judgement and
certificate metadata separately. Initial host fixtures should include a small
bitblasted AND family. ASCII LRAT is an explicit pretty-print mode only.
