# Rust–Lean syntax correspondence

The normative Rust syntax is in `src/lib.rs`; its direct formal counterpart is
`lean/Nucleus/Nucleus/HolSurface.lean`. Both are parameterized by the same seven
representation indices:

| Rust `Repr` | Lean `Repr` | Meaning |
|---|---|---|
| `Kind`, `Ty`, `Tm` | `Kind`, `Ty`, `Tm` | Child indices of each syntactic sort |
| `Var`, `Ctx` | `Var`, `Ctx` | Variables and premise contexts |
| `Link` | `Link` | Abstract imported-object reference |
| `Prim` | `Prim` | Backend primitive |

Lean intentionally imposes no structure on `Link`. The default Rust
representation chooses `Arc<(O256, Format)>`: the enum stores one shared pointer
while the allocation contains the full hash and serialization format. A type
link carries a kind; a term link carries a type. Kind links are intentionally
absent.

Links always resolve to closed checked objects. Rust expresses this through
`LinkResolver::{ClosedType, ClosedTerm}` and the `ClosedTyI`/`ClosedTmI` marker
interfaces. Lean's `EmptyDesugar.LinkResolver` is stronger still: its result is
respectively `FamK [] kind` or `Term (Ctx.empty : Ctx [] 0) A`, so closedness
and the kinding/typing certificate are present by construction. Resolution
must reject a target that disagrees with the annotation stored in the link
node.

`Context::{Empty, And}` corresponds to Lean `Context.{empty, and}`. Contexts
are ordered conjunction spines rather than name maps: stacking the infinity
assumption is `And(TM_INF, rest)`, and the spine lowers to nested `TM_AND`.

The high-level forms `TM_AND`, `TM_INF`, `TM_NAT`, `TM_ZERO`, `TM_SUCC`, and
`TM_LIT_NAT` are definitions. Their canonical checked expansions live in
`Nucleus.HolE.EmptyNatural`; none extends the trusted HolE syntax.

Each row below is an exact constructor and wire-tag correspondence.

| Rust | Lean | Canonical tag | ID |
|---|---|---:|---:|
| `Kind::Star` | `Kind.star` | `KIND_STAR` | 0 |
| `Kind::Arr` | `Kind.arr` | `KIND_ARR` | 1 |
| `Ty::Bool` | `Ty.bool` | `TY_BOOL` | 2 |
| `Ty::Arr` | `Ty.arr` | `TY_ARR` | 3 |
| `Ty::App` | `Ty.app` | `TY_APP` | 4 |
| `Ty::Abs` | `Ty.abs` | `TY_LAM` | 5 |
| `Ty::Bv` | `Ty.bv` | `TY_BV` | 6 |
| `Ty::Sub` | `Ty.sub` | `TY_SUB` | 7 |
| `Tm::Exists` | `Tm.tyExists` | `TY_EXISTS` | 8 |
| `Ty::Model` | `Ty.model` | `TY_MODEL` | 9 |
| `Ty::Prim` | `Ty.prim` | `TY_PRIM` | 10 |
| `Ty::Link` | `Ty.link` | `TY_LINK` | 11 |
| `Tm::Prim` | `Tm.prim` | `TM_PRIM` | 12 |
| `Tm::Bv` | `Tm.bv` | `TM_BV` | 13 |
| `Tm::Fv` | `Tm.fv` | `TM_FV` | 14 |
| `Tm::App` | `Tm.app` | `TM_APP` | 15 |
| `Tm::Lam` | `Tm.lam` | `TM_LAM` | 16 |
| `Tm::Bool` | `Tm.bool` | `TM_BOOL` | 17 |
| `Tm::Eq` | `Tm.eq` | `TM_EQ` | 18 |
| `Tm::Eps` | `Tm.eps` | `TM_EPS` | 19 |
| `Tm::Abs` | `Tm.abs` | `TM_ABS` | 20 |
| `Tm::Rep` | `Tm.rep` | `TM_REP` | 21 |
| `Tm::Link` | `Tm.link` | `TM_LINK` | 22 |
| `Tm::Imp` | `Tm.imp` | `TM_IMP` | 64 |
| `Tm::And` | `Tm.and` | `TM_AND` | 65 |
| `Tm::Inf` | `Tm.inf` | `TM_INF` | 66 |
| `Ty::Nat` | `Ty.nat` | `TM_NAT` | 67 |
| `Tm::Zero` | `Tm.zero` | `TM_ZERO` | 68 |
| `Tm::Succ` | `Tm.succ` | `TM_SUCC` | 69 |
| `Tm::Nat` | `Tm.nat` | `TM_LIT_NAT` | 70 |

Rust `AnyExpr::{Kind, Ty, Tm}` corresponds to Lean
`AnyExpr.{kind, ty, tm}`. It is only the explicit heterogeneous-storage wrapper;
the kernel and formal syntax retain the three sorts. Rust `ArcRepr` is a concrete
sharing strategy and therefore has no formal counterpart.
