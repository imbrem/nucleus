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

## v:13 — Lean HolE term constructors

`lean/Nucleus/Nucleus/HolE.lean`, `inductive Expr (Sig) : List Kind → HolSort → Nat → Type`:

```
| tyBv (v : TyVar types kind)                             -- kind-indexed de Bruijn
| bv   {depth} (index : Fin depth)                        -- scoped, untyped
| fv   {depth} (name : Nat) (type : Expr ... (.kind .star) 0)
| lam  {depth} (domain : Expr ... (.kind .star) 0)
       (body : Expr ... .tm (depth + 1))
| sub  (carrier) (predicate : Expr ... .tm 1)             -- binds one term variable
| abs  / rep (carrier) (predicate : Expr ... .tm 1) (value)
```

So the term level is scoped de Bruijn with untyped `bv` and typed numeric-level
`fv`; the type level is intrinsically kinded de Bruijn.

## v:14 — freshness, closing, and alpha in Lean

```
$ grep -rn "def close\|def open\|def abstract\|def instantiate" lean/Nucleus/Nucleus/{Hol,HolE}/*.lean
HolE/EmptySyntax.lean:132  def openBound
HolE/EmptySyntax.lean:136  def openType
HolE/Substitution.lean:29  def instantiate
HolE/Substitution.lean:42  def openBound
HolE/Substitution.lean:46  def instantiateOne
Hol/Substitution.lean:29   def instantiate
Hol/Substitution.lean:42   def openBound
Hol/Substitution.lean:46   def instantiateOne
Hol/FamilySub.lean:105,133,414
```

No `close` and no `abstract`. Opening exists, closing does not.

```
$ grep -rln -i "alpha" lean/Nucleus/Nucleus/          → no matches
$ grep -rn "freeVars\|def free" lean/.../{HolE,HolLN}/*.lean  → no matches
$ grep -rn "fresh\|Fresh" lean/Nucleus/Nucleus/{Hol,HolE}/*.lean
Hol/Kernel.lean:24         | eta (name : Nat) (fresh : Fresh name f)
HolE/Kernel.lean:34        | eta (name : Nat) (fresh : Fresh name f)
HolE/EmptyRules.lean:63    (fresh : Fresh name function.raw)
plus soundness cases in Hol/Soundness.lean, HolE/Classical{Soundness,EqTmSoundness,EtaKernelLaw}.lean
```

So `Fresh name t` is already a spec-level predicate used by the `eta` rule,
while a set-valued `freeVars` function does not exist.

## v:15 — keyed hashing in `crates/lib/hash`

`crates/lib/hash/src/lib.rs`:

```
pub trait KeyedNamespace<K: ?Sized>: Namespace + Sized {
    fn keyed(key: &K, bytes: impl AsRef<[u8]>) -> Obj<Self>;
    fn keyed_from_reader(key: &K, reader: impl std::io::Read) -> std::io::Result<Obj<Self>>;
}

impl<N: Namespace> Obj<N> {
    pub fn with_key<K: ?Sized>(key: &K, bytes: impl AsRef<[u8]>) -> Self
    where N: KeyedNamespace<K>;
}
```

So a derivation kind is a namespace type and domain separation sits in the type.
The crate also carries multiformats (`from_multihash`, `from_raw_cid`) and a
`git.rs`. Not checked: whether the BLAKE3 implementation behind
`KeyedNamespace` uses BLAKE3's keyed mode or a prefix construction.

## v:16 — signed literals in the SAT crate

`crates/logic/sat/src/lib.rs`: `pub struct Literal(i64)` with `impl Neg`,
rejecting zero and `i64::MIN` — "CNF literal must be nonzero and negatable".
So a signed integer meaning "this reference, negated" is an existing convention
in the tree, which is what a negative `SRef` is: the logical negation of the
positive reference as an endpoint of the implication relation `A ⇒ B` [d].

## v:17 — how `Nucleus/Hol/` reached `main`

```
$ git ls-tree -r --name-only main lean/Nucleus/Nucleus/Hol/ | wc -l   → 30
$ git merge-base --is-ancestor origin/hol-signatures main             → NO
$ git log --oneline --diff-filter=A -- lean/.../Hol/Signature.lean    → f23a204 (2026-08-17)
$ git log --oneline --merges --ancestry-path f23a204..main | tail -2
  1eee983 Merge pull request #729 from imbrem/hole-defeq-opening
  068a92a Merge pull request #728 from imbrem/hole-type-exists
$ git diff --stat main origin/hol-signatures -- lean/.../Hol/         → (empty)
```

So the directory is on `main`, it arrived via the HolE branches rather than via
#701, #701's tip is not an ancestor of `main`, and the directory's contents are
identical on both at present.

`Hol/Signature.lean` imports `Nucleus.HolLN.Syntax` and declares "sorted,
intrinsically scoped, but extrinsically typed HOL syntax".

## v:18 — the named HolE syntax landed 2026-08-19

```
$ git log --oneline ae39f6a..origin/main
01e2d07 Merge pull request #751 from imbrem/hol-e-unsorted
04ebebc lean: add unsorted named HolE syntax
d447bf4 Merge pull request #749 from imbrem/hol-e-named
6cde69a lean: prove named HolE alpha quotient equivalence
9da7e32 lean: parameterize named HolE variable names
53c37c9 lean: give named HolE lowering semantics
6e0d8cb lean: pull back HolE judgments to named syntax
390cc02 lean: add typed free-variable substitution
99620ea lean: extract fresh natural Finset utility
462ebda lean: add HolE free-variable indices and quotation
e277b3d lean: add named HolE syntax and lowering
92fadf4 lean: add typed free-variable support views
                                        (17 files, 1869 insertions)
```

From `HolE/Named/Syntax.lean`:

```lean
structure Decl (S : Type v) (Name : Type := Nat) where
  name : Name
  sort : S
inductive Expr (Sig : Signature) (Name : Type := Nat) : HolSort → Type (max u 1)
  | lam   (name : Name) (domain : Expr Sig Name (.kind .star)) (body : Expr Sig Name .tm)
  | tmFv  (name : Name) (type : Expr Sig Name (.kind .star))
  | sub   (carrier) (name : Name) (predicate)
  | abs / rep (carrier) (name : Name) (predicate) (value)
  | tyLam (name : Name) (body) ;  tyFv (name : Name) (kind : Kind)
```

Header: "A binder captures only an occurrence with the same name and the same
syntactic sort. Type conversion is not part of name resolution."

`Named/Unsorted.lean`: "erases the result sort while retaining the kind
annotations needed to reconstruct type application, type abstraction, type
variables, and signature primitives. `check` validates a caller-supplied sort.
`infer` determines the result sort from the outer constructor."

`Named/Alpha.lean` has `Alpha.refl/symm/trans`, `Alpha.lower_eq`,
`ScopedExpr.lowered_eq_of_alpha`; `Named/Equivalence.lean` has
`ClosedFamQuotient.ofLN_toLN` and `ClosedTmQuotient.ofLN_toLN`.

## What was not verified

- `lake build`, zero-`sorry` via the actual Lean gates, `#print axioms`.
- Whether `cargo test` passes anywhere.
- Any claim about covalence issues or PRs (no API access).
- The relationship between `lean/.../Hol/` on `main` and open PR #701 [?1.A].
- Whether the spike branches build; only their contents were read.
