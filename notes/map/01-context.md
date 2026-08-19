# Map: current context

State of the project on 2026-08-19, `main` at `ae39f6a` [v:1].
Markers are defined in [`00-index.md`](./00-index.md).

## Lean: the specification

148 files, 32,515 lines. Zero `sorry`, zero `admit`, zero `axiom`
declarations [v:2].

| Area                   | Lines | Contents                                                                                                                     |
| ---------------------- | ----- | ---------------------------------------------------------------------------------------------------------------------------- |
| `Hol/`                 | 8,373 | signature-parametric HOL: `Signature`, `Typing`, `Intrinsic`, `Soundness`, `FamilySub`, `Nat`                                |
| `HolE/`                | 7,422 | type-variable-scoped HOL with subtype families; classical kernel laws, `Semantics`, `Soundness`, `Consistency`, `Empty*` API |
| `SExpr/`               | 5,036 | models, parser, printers, canonical form                                                                                     |
| `HolLN/`               | 4,481 | monomorphic locally nameless HOL, plus `Array` (arena) and `Json`                                                            |
| `Json/`                | 4,288 | RFC parser, I-JSON, IPLD, CAS                                                                                                |
| `Cbor/`                | 1,415 | data model, deterministic encoding, DAG and CAS layers                                                                       |
| `Encoding/`, `Number/` | 464   |                                                                                                                              |

[v:3]

Three things worth flagging.

- The plan notes from 2026-08-17 describe `Nucleus.Hol` as 8.6k unmerged lines
  in PR #700→#701 and put the Lean total at 14.3k
  [n:notes/plans/2026-08-hol-kernel-mvp.md]. Both figures have moved.
- **`Nucleus/Hol/` is in the trunk, but #701 did not put it there.** 30 files,
  8,373 lines on `main`. It arrived through the HolE merges #728 and #729;
  #701's tip is not an ancestor of `main`, though the directory's contents are
  currently identical on both [v:17]. Whether that counts as the HOL kernel
  having landed is a question about what "landed" means here, not about the
  files [?1.A].
- **The named HolE syntax landed on 2026-08-19**, after the first draft of these
  notes, in #749 and #751:
  `HolE/Named/{Syntax,Typing,Lower,FV,Alpha,Equivalence,Kernel,Quote,Semantics,Unsorted}.lean`,
  1,869 lines [v:18]. It carries the alpha quotient equivalence, typed
  free-variable substitution, and an unsorted variant whose `check`/`infer` pair
  is the arena's situation exactly. This is what
  [`07-format-v0.md`](./07-format-v0.md) now builds on.

`HolE.lean` declares independent locally nameless scopes for type and term
variables [v:7]; `HolE/Named/` is the named surface above it [v:18]. Concretely [v:13]: term bound variables are `bv : Fin depth`,
scoped and untyped, so no dangling index is representable and `depth = 0` means
locally closed; free variables are `fv (name : Nat) (type)`, numeric levels
carrying their type; `lam` carries the binder's domain. Type variables are
kind-indexed de Bruijn, so they are already intrinsically typed. The asymmetry
between the two levels is what `03-arena.md` §8 is about.

## Rust: the implementation

No HOL kernel on `main`. `crates/logic/` holds `lrat` and `sat` only [v:5].

| Crate           | Lines |
| --------------- | ----- |
| `lib/sqlite`    | 3,842 |
| `lib/hash`      | 2,089 |
| `repl`          | 1,810 |
| `neutron`       | 1,744 |
| `ffi/python`    | 1,370 |
| `bin/cas-shell` | 827   |
| `logic/lrat`    | 629   |
| `data/num`      | 535   |
| `nucleus`       | 530   |
| `data/cas`      | 498   |
| `data/cbor`     | 211   |

[v:8]

`data/cbor` is the immutable CBOR value model merged 2026-08-19 in #730, #731,
#732 [v:1]. `data/num` is the `Num`/`Int` foundation from #27 [v:1].

## The Rust arena spike

Lives at `crates/logic/hol/` on a stack of `hol-*` branches. The widest version
is `hol-e-full-surface`; `hol-arena-v0` adds relations and sequents;
`hol-syntax-arena-v0` (PR #746) is the trimmed syntax-only cut aimed at `main`
[v:5]. Shape, as implemented:

- `Ix` — nonzero, at most `i32::MAX` [v:5].
- `Expr` — one node per index; children in constructor order; `var` payload on
  variable leaves only. Wire form `ExprWire` is separate from `Expr`, with a
  `TryFrom` in between. Same for `SegmentWire`/`Segment` and `ArenaWire`/`Arena`
  [v:5]. The POD-plus-validation split the dump asks for [d] is already the
  spike's habit.
- `Link { addr: O256, format: Format, kind: ObjectKind }`, with
  `Format ∈ {Blob, CborDense, CborSparse}` and
  `ObjectKind ∈ {Bytes, ImportTable, Arena, Sequent}`. Format and class sit at
  the reference site, never behind the hash [v:5].
- `Segment { start, end, link, source_start }`, sorted and disjoint. Plus a
  `local_base` for where local definitions begin [v:5].
- `Relations` — sparse `BTreeMap<(SRef, SRef), (premise mask, conclusion mask)>`
  over eight relations: `SynEq`, `ConvEq`, `TyEq`, `HasTy`, `Imp`, `Eq`,
  `HasKind`, `Ne` [v:5].
- `SRef` — a signed endpoint. Sign carries polarity; the intended reading is not
  documented in the code [?1.B].
- `Seq` — premises and conclusions over one arena and import table, projected
  out as two `Ctx` values [v:5]. This is the object the dump calls complicated
  [d]; PR #744 ("Simplify HolE sequents to plain contexts") is already pulling
  the same direction.
- Surface tags: 24 assigned, `KIND_STAR` through `TM_CAST`, with `TM_BV` and
  `TM_FV` both present — locally nameless, matching Lean [v:10].

`SYNTAX.md` on that branch already states the non-canonical rule the dump
restates: distinct byte strings, and therefore distinct addresses, may decode to
the same logical value; an address identifies the exact stored bytes [v:5].

## Covalence: what carries over

Read-only clone, 942 Rust files, 389,841 lines, last commit 2026-07-22 [v:9].
It is a research repo with many overlapping experiments; the notes below are
individual experiments, not a settled architecture.

- **Binder discipline.** `TermKind::Bound(u32)` plus `Free(Var)` where
  `Var = (name, type)` [v:11]. Locally nameless, with free variables carrying
  their type in their identity. Same answer as HolLN and as the Rust spike, from
  a separate line of work.
- **Two representations, one meaning** [c:notes/vibes/kernel/substrate-expressions.md].
  A dynamic tree that validates itself, serializes canonically and is the audit
  reference; a typed Rust façade above it for construction, lowered into the
  dynamic tree and differentially tested. Explicitly: the façade's type
  machinery must not define the persisted semantics. This is the same split the
  dump proposes [d], reached independently.
- **Four equality levels** [c:notes/vibes/kernel/type-hierarchy.md]: pointer,
  structural, checked, derived. With the claim that decidability and
  universality are separate axes. Relevant to the `syn_eq` / `conv_eq` / `eq`
  column split.
- **Fail-closed decoding** [c:notes/vibes/kernel/substrate-expressions.md]: a row
  that cannot decode produces no theorem; a trusted batch transition rejects if
  any relevant row fails; untrusted imports keep a rejection report.
- **Table facts as quantified propositions**: `All`, `Any`, `NotAll`, `NotAny`
  over a table interpretation, with the warning not to read absence as negative
  information without completeness evidence [c:same].
- **Kernel shape**: HOL Light's ten rules as primitives, plus derived rules
  admitted as primitives for ergonomics, plus per-family computation
  certificates for closed-literal arithmetic [c:notes/vibes/kernel/kernel-design.md].
  TCB stated as ~3 KLoC.

## Design principles in force

From the author, 2026-08-19 [d]:

1. Canonical encodings are not required. The requirement is that a hash decodes
   to at most one object. Many encodings of one object is fine.
2. Hash raw bytes in whatever format, not data structures.
3. Many formalizations and much experimental userspace code are fine. The TCB
   must stay small, coherent, and audited.

From `AGENTS.md` [n:AGENTS.md, open in PR #712]:

4. Lean specifies, Rust transcribes; Lean wins disputes.
5. Merging is the risky act; an open spike is the safe one.
6. Never deserialize a checked term, equality, or theorem. Signed statements are
   the one exception, and there both codec directions are TCB.
