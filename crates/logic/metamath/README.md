# Metamath

This crate parses and validates Metamath databases. It supports comments,
scopes, every declaration form, recursive `$[ file $]` inclusion, normal
proofs, and compressed proofs (including `Z` saves and heap references).

It is deliberately **not** part of the Nucleus TCB. `DatabaseSink` lets the
same parser drive a future in-HOL validator, whose kernel results—not this
checker—will carry authority.

```rust
use covalence_logic_metamath::{parse, verify_all};

let database = parse(source)?;
let theorem_count = verify_all(&database)?;
```

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
