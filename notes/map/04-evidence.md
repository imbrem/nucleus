# Map: evidence

Commands run on 2026-08-19 in a clean checkout, and what they returned. Cited as
`[v:N]` from the other documents. Output is abbreviated where it was long; the
command is exact so it can be re-run.

## v:1 — `main` tip and recent merges

```
$ git log --oneline -1 main
ae39f6a Merge pull request #732 from imbrem/cbor-python-conversion

$ git log --oneline --merges -25 main
#732 cbor-python-conversion · #731 cbor-python · #730 cbor-data · #27 codex/issue-21-num
#729 hole-defeq-opening · #728 hole-type-exists · #714 python-sat-order-hash
#713 forsp-formalization · #706 sexpr-lisp · #704 sexpr-memory · #702 sexpr-pointer-tables
#699 sexpr-atom-classes · #697 sexpr-pretty · #695 sexpr-literals · #694 sexpr-theory
#696 python-lib-hash · #679 better-o256-serde · #693 typed-free-vars · #692 hol-evar
#690 cbor-wire-format · #689 dag-codec-correspondences · #691 untyped-hol-syntax
#678 cbor-data-model · #673 codex/hol-ln-array
```

## v:2 — Lean size and proof hygiene

```
$ find lean -name '*.lean' | wc -l                                  → 148
$ find lean -name '*.lean' -exec cat {} + | wc -l                    → 32515
$ grep -rn --include=*.lean -E '(^|[^a-zA-Z_])(sorry|admit)([^a-zA-Z_]|$)' lean | wc -l   → 0
$ grep -rn --include=*.lean -E '^axiom ' lean | wc -l                → 0
```

Caveat: this counts declarations, it does not run `lake build` or
`#print axioms`. Those gates are what `AGENTS.md` actually requires; they were
not run here.

## v:3 — Lean lines per area

```
$ for d in lean/Nucleus/Nucleus/*/; do ...; done | sort -rn
8373 Hol/ · 7422 HolE/ · 5036 SExpr/ · 4481 HolLN/ · 4288 Json/ · 1415 Cbor/
350 Encoding/ · 114 Number/
```

## v:4 — `notes/` is not on `main`

```
$ ls /home/user/nucleus            → no notes/ directory
$ git diff --stat main...origin/claude/hol-kernel-mvp-roadmap-wgzbpb
AGENTS.md 182+ · CLAUDE.md 1+ · notes/design/repl-core-sketches.md 403+
notes/design/repl-language.md 484+ · notes/plans/2026-08-17-eight-hour-mvp.md 325+
notes/plans/2026-08-hol-kernel-mvp.md 412+ · notes/plans/v0-mvp.md 342+
notes/spikes/README.md 51+ · notes/vision/ladder.md 211+      (9 files, 2411 insertions)
```

## v:5 — the Rust arena spike

```
$ git diff --stat main...origin/hol-arena-v0
crates/logic/hol/src/arena.rs 743+ · cbor.rs 85+ · lib.rs 399+ · relations.rs 437+
tag.rs 113+ · theorem.rs 302+ · lean/.../HolSurface.lean 369+ · HolSurface/Cbor.lean 586+
```

Read from `git show origin/hol-arena-v0:crates/logic/hol/src/{arena,relations,theorem}.rs`
and `git show origin/hol-syntax-arena-v0:crates/logic/hol/SYNTAX.md`:

- `MAX_INDEX = i32::MAX`; `Ix(NonZeroU32)`.
- `enum Format { Blob, CborDense, CborSparse }`;
  `enum ObjectKind { Bytes, ImportTable, Arena, Sequent }`.
- `struct Link { addr: O256, format: Format, kind: ObjectKind }` and
  `struct LinkRef { import: u32, format, kind }`, with the comment "Format and
  object kind are stored at the reference site, never behind the content hash."
- `struct Segment { start, end, link, source_start }` with
  `add_segment` / `set_local_base`.
- `struct ExprWire { ix, var, ... }` with `TryFrom<ExprWire> for Expr`; likewise
  `SegmentWire`, `ArenaWire`.
- `enum Relation { SynEq, ConvEq, TyEq, HasTy, Imp, Eq, HasKind, Ne }`, eight
  variants, five symmetric.
- `struct Relations { pairs: BTreeMap<(SRef, SRef), (RelationFlags, RelationFlags)> }`
  — the pair is (premise mask, conclusion mask).
- `struct SRef(i32)` with `pos`, `neg`, `NULL`, and `SRefView { Null, Pos, Neg }`.
  No doc comment on what `Neg` means.
- `struct Seq { ... }` with `premises()`, `conclusion()`, `assume(LinkRef)`,
  `conclude(LinkRef)`.
- `SYNTAX.md`: "distinct CBOR byte strings and therefore distinct addresses may
  decode to the same logical value. An address identifies the exact bytes stored
  under it."

`crates/logic/` on `main` contains `lrat` and `sat` only, so none of this is on
the trunk.

## v:6 — open issue count

`mcp__github__list_issues(state=OPEN)` → `pageInfo.totalCount = 260`.

## v:7 — Lean HolE binder discipline

`lean/Nucleus/Nucleus/HolE.lean`, header comment: "HOL syntax with independent
locally nameless scopes for type and term variables." `TyVar` is a kind-indexed
de Bruijn variable over `List Kind`.

## v:8 — Rust lines per crate

```
$ for d in $(find crates -name src -type d); do ...; done | sort -rn
3842 lib/sqlite · 2089 lib/hash · 1810 repl · 1744 neutron · 1370 ffi/python
827 bin/cas-shell · 629 logic/lrat · 535 data/num · 530 nucleus · 498 data/cas
392 browser · 229 data/cas-http · 211 data/cbor · 201 lib/python · 188 logic/sat
148 data/container · 103 bin/nucleus · 59 bin/cas-serve · then stubs under 45
```

## v:9 — covalence size

```
$ git -C /workspace/imbrem/covalence log -1 --format='%h %ad %s' --date=short
0122507 2026-07-22 fix(hol): align inductive graph proofs under beta

$ find crates -name '*.rs' | wc -l        → 942
$ find crates -name '*.rs' -exec cat {} + | wc -l   → 389841
```

Shallow clone, read-only. GitHub API access to covalence issues and PRs was
refused in this session, so nothing here is sourced from them.

## v:10 — surface tag table

`git show origin/hol-e-full-surface:crates/logic/hol/src/tag.rs` — 24 tags:
`KIND_STAR`, `KIND_ARR`, `TY_BOOL`, `TY_ARR`, `TY_APP`, `TY_LAM`, `TY_BV`,
`TY_SUB`, `TY_EXISTS`, `TY_MODEL`, `TY_LINK`, `TM_BV`, `TM_FV`, `TM_APP`,
`TM_LAM`, `TM_BOOL`, `TM_EQ`, `TM_EPS`, `TM_ABS`, `TM_REP`, `TM_LINK`,
`TM_CAST`. Integer IDs 10 and 12 are reserved.

## v:11 — covalence binder discipline

`crates/kernel/hol/core/src/term/term.rs`: `pub struct Var` at line 567,
`Bound(u32)` at 608, `Free(Var)` at 610. The design note
`notes/vibes/kernel/kernel-design.md` states `Var = (name, type)` and that free
variables carry their type in their identity.

## v:12 — open PR count

`mcp__github__list_pull_requests(state=open, perPage=100)` over four pages:
100 + 100 + 100 + 40 = **340**. Page 4 ends at #25.

## What was not verified

- `lake build`, zero-`sorry` via the actual Lean gates, `#print axioms`.
- Whether `cargo test` passes anywhere.
- Any claim about covalence issues or PRs (no API access).
- The relationship between `lean/.../Hol/` on `main` and open PR #701 [?1.A].
- Whether the spike branches build; only their contents were read.
