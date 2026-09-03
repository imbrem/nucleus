# Metamath

The public `trace` API reports exact transitive dependencies and `$a` leaves,
and classifies leaves as logical axioms, conventional definitions, syntax
constructors, or unclassified assertions. `AxiomIndex` computes deterministic
whole-database answers in one forward pass. This is untrusted provenance
metadata: verify the database separately before treating the report as evidence
of a valid proof. See
[`docs/metamath-axiom-audit.md`](../../../docs/metamath-axiom-audit.md) for the
formal axiom-set, soundness, and conservativity results and their scope.

This crate parses and validates Metamath databases. It supports comments,
scopes, every declaration form, recursive `$[ file $]` inclusion, normal
proofs, and compressed proofs (including `Z` saves and heap references).

It is deliberately **not** part of the Nucleus TCB. `DatabaseSink` lets the
same parser drive a future in-HOL validator, whose kernel results—not this
checker—will carry authority.

Because the whole database is parsed before anything is checked, the checker
re-imposes by position what a read-as-you-go verifier gets for free: a proof may
cite only labels declared **strictly earlier** than the theorem it proves
(`MmError::ForwardReference`), and may cite only active `$f`/`$e` hypotheses
(`MmError::InactiveHypothesis`). Databases that relied on either being
unchecked—a theorem citing itself, or another block's hypothesis—no longer
validate.

```rust
use covalence_logic_metamath::{parse, verify_all};

let database = parse(source)?;
let theorem_count = verify_all(&database)?;
```

The deep Metamath-to-HOL-omega claim, its shallow-bridge boundary, and the
signed-corpus provenance mapping are specified in
[`docs/metamath-hol-embedding.md`](../../../docs/metamath-hol-embedding.md).
The worked Lean slice is `Nucleus.Metamath.Embedding`.

## Deviations from the spec

Comment text is not held to the spec's character repertoire. §4.1 restricts a
database to printable ASCII plus whitespace, but prose comments in real
databases — this crate's own `demo0.mm` fixture included — carry typographic
characters such as an em-dash, and rejecting them buys nothing: comments are
stripped before anything is interpreted. **Tokens** are checked in full, so a
label, math symbol, or keyword may not smuggle in a non-ASCII or control
character.

## Upstream corpus

The corpus is not a Git submodule: it is large, changes frequently, and is not
required to build this repository. Corpus tests instead use a normal checkout
pinned by the caller. The benchmark recorded for this initial port uses
`metamath/set.mm` revision `b263d6e45b460ace961dea8839c953be7034adb4`.

```sh
git clone https://github.com/metamath/set.mm.git /tmp/set.mm
git -C /tmp/set.mm checkout b263d6e45b460ace961dea8839c953be7034adb4
NUCLEUS_METAMATH_CORPUS=/tmp/set.mm \
  cargo test -p covalence-logic-metamath --release --test corpus -- --ignored

cargo run -p covalence-logic-metamath --release --example validate -- \
  /tmp/set.mm/{demo0,miu,peano,big-unifier,hol,ql,nf,iset,set}.mm
```
