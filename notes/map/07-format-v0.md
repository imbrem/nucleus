# Map: the minimal dense arena, v0

The smallest thing worth formalizing. Everything in
[`03-arena.md`](./03-arena.md) is an extension of this; nothing here depends on
anything there.

**The loop is formalization → Rust → Python → iterate** [d]. Each turn of it may
change the last three. Old formalizations stay, interlinked, as grounding: a
second model that agrees is evidence the symbols mean what they are meant to
(principle 5, and adequacy in `05-pointers.md` §5).

## The format

```
{
  "tag":  "arena.dense",
  "elem": "hol",
  "defs": [ node, node, ... ]
}

node = { "tag": string, "ix": [nat], "var": nat }     -- ix and var per tag
```

That is all of it. No links, no parent, no segments, no facts, no `ctx`, no
`eq`, no `ty`, no metadata, no schema.

### Nodes

Six tags, which is enough to write a typed term and say two things are equal:

| tag           | `ix`               | `var` |
| ------------- | ------------------ | ----- |
| `hol.ty.bool` | —                  | —     |
| `hol.ty.arr`  | domain, codomain   | —     |
| `hol.tm.var`  | type               | name  |
| `hol.tm.lam`  | domain, body       | name  |
| `hol.tm.app`  | function, argument | —     |
| `hol.tm.eq`   | type, left, right  | —     |

The lambda carries its name and its domain, matching the spec, which landed on
`main` on 2026-08-19 as `HolE/Named/Syntax.lean` [v:18]:

```lean
| lam   (name : Name) (domain : Expr Sig Name (.kind .star)) (body : Expr Sig Name .tm)
| tmFv  (name : Name) (type : Expr Sig Name (.kind .star))
```

That settles question 1.R in favour of name-plus-domain over a pointer to a
variable node.

Two details from the same file worth carrying into the arena. Names are a type
_parameter_ defaulting to `Nat`, so the arena picking naturals is an
instantiation rather than a commitment. And a variable's identity is its name
paired with its syntactic sort: "a binder captures only an occurrence with the
same name and the same syntactic sort. Type conversion is not part of name
resolution" [v:18]. So variable equality in the arena is name equality plus
_syntactic_ type equality, and never up to conversion.

### Validity

For `defs[i]`:

1. `tag` is one of the six.
2. `ix` has exactly the arity the tag requires; `var` is present exactly when
   the tag requires it.
3. every `j` in `ix` satisfies `j < i`.
   Three conditions, one pass, no fetches. Sorts are not checked here: whether
   `hol.tm.app`'s function is a term rather than a type is a _sorting_ question,
   and `Named.Unsorted` already separates it — see the Lean section.

### Worked example

`λx:bool. x` and the proposition `(λx:bool. x) = (λx:bool. x)`:

```json
{
  "tag": "arena.dense",
  "elem": "hol",
  "defs": [
    { "tag": "hol.ty.bool" },
    { "tag": "hol.tm.var", "var": 0, "ix": [0] },
    { "tag": "hol.tm.lam", "var": 0, "ix": [0, 1] },
    { "tag": "hol.ty.arr", "ix": [0, 0] },
    { "tag": "hol.tm.eq", "ix": [3, 2, 2] }
  ]
}
```

## Field names, and why

| Name   | Holds                              | Why this name                                                                                                      |
| ------ | ---------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| `tag`  | what the object or node is         | already the spike's name [v:5], and the dump's rule is to tag everything                                           |
| `elem` | what an index denotes, `"hol"`     | keeps the arena reusable for non-HOL element types later, and one string is a cheap guard against format confusion |
| `defs` | the nodes, in index order          | the spike's name [v:5]                                                                                             |
| `ix`   | child indices in constructor order | the spike's name [v:5]; `children` is clearer in isolation and longer everywhere it appears                        |
| `var`  | a variable's name, a natural       | the spike's name [v:5]                                                                                             |

Two decisions worth arguing rather than inheriting:

**Indices are 0-based, and there is no null index.** The spike uses `NonZeroU32`
with 0 reserved [v:5]. Zero-based makes the Lean side `Fin defs.size` with no
offset arithmetic anywhere, which is most of the proof burden in an indexed
representation. If a hole is wanted later it should be an explicit
`hol.undef` _value_, not a reserved _index_ — a null value can be reasoned
about, a null index has to be excluded at every use.

**Tags are strings, matched exactly.** No splitting on `.` in the decoder, so
the TCB has no path parser. The dotted structure is for humans and for userspace
prefix dispatch. Integer tags later are a second codec over the same vocabulary,
not a version of this one.

## Lean

This is a **flattening of a type that now exists**, not a new model.
`HolE/Named/Unsorted.lean` landed on `main` on 2026-08-19 and is the arena's
situation exactly: the result sort is erased, kind annotations are retained,
`check` validates a caller-supplied sort, and `infer` derives the sort from the
outer constructor [v:18].

So the arena is `Named.Unsorted.Expr` with its subterms replaced by indices:

```lean
inductive Node where
  | tyBool
  | tyArr (dom cod : Nat)
  | var   (name ty : Nat)
  | lam   (name dom body : Nat)
  | app   (fn arg : Nat)
  | eq    (ty lhs rhs : Nat)

structure Arena where
  defs : Array Node

def Node.children : Node → List Nat
def Arena.Valid (a : Arena) : Prop           -- the three conditions above
def Arena.expand : (a : Arena) → Valid a → Fin a.defs.size → Unsorted.Expr
```

Three theorems, in order of how much they buy:

- `decode (encode a) = some a` — round trip, from which injectivity of `encode`
  follows.
- `Valid a → ∀ i, (a.expand h i)` is defined — a valid arena expands at every
  index. Structural recursion on the validated prefix, which is why condition 3
  is `j < i` rather than merely `j < size`.
- Composition with what is already proven: `Unsorted.infer` for sorting,
  `Named.Lower` for the locally nameless image, and
  `ClosedTmQuotient.ofLN_toLN` for the named/nameless correspondence up to
  alpha [v:18]. The arena adds indexing; it does not re-litigate any of that.

`HolLN/Array.lean` also has an arena, `validate` and `elaborate`
[n:notes/plans/2026-08-hol-kernel-mvp.md]. Read both before writing [?1.F].

## Rust

```
crates/logic/hol/src/
  wire.rs    Node, Arena — serde only, no invariants
  check.rs   wire -> mem, total, typed errors        (TCB)
  mem.rs     the live arena
```

Transcribe the Lean, function for function, error for error. Reuse #746, which
is already this shape [v:5].

## Python

Construct, encode, decode, print. Enough to build the worked example by hand and
look at the bytes. This is the iteration surface and it should exist within a
day of the Rust.

## What is deliberately missing

Parent arenas, links, segments, facts, `ctx`, `eq`, `ty`, variable windows,
derived addresses, metadata, schema addresses, kinds, literals, and every HOL
constructor beyond the six. Each is additive over this format, and each has a
section in [`03-arena.md`](./03-arena.md) waiting for it.

The reason to start here rather than one step further out: this is small enough
that the Lean, the Rust and the Python can all be wrong in a way that is visible
in an afternoon.
