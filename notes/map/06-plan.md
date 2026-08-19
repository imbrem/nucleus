# Map: implementation order

Concrete ordering for the design in [`03-arena.md`](./03-arena.md), written to
start now. Markers per [`00-index.md`](./00-index.md).

## What blocks what

Two things are in flight: Iroh-style hash array APIs, and the named syntax
formalization [d].

- **S1 is blocked by neither.** A parentless dense arena has no links and no
  imports, so it needs no hash arrays; and the Rust wire shape needs only the
  constructor list, not the proofs.
- **S1's Lean side waits on the named syntax.** Do Rust first, Lean when it
  lands. The wire shape is what the Lean model consumes, so writing it first
  costs nothing.
- **S2 wants the hash arrays.** `links.flat` _is_ the Iroh-style hash array, so
  the parent step lands on top of that merge rather than duplicating it.

## S0 — freeze the vocabulary

Half a day, and it is the one thing that is expensive to skip: every fixture
written before the tag list settles has to be regenerated.

One file, one list, generating the Rust table and the Lean table. This is issue
#745; string tags make it cheaper than the integer version that issue assumes.

**Naming rules** for the dotted tags [d]:

1. The first segment is the **family**: `arena`, `links`, `seg`, `hol`.
2. The remaining segments are a path whose meaning the family declares. For
   container families it is the representation — `arena.dense`, `arena.segment`,
   `links.flat`. For `hol` it is sort then constructor — `hol.tm.app`,
   `hol.ty.arr`, `hol.kind.star`.
3. **Prefix-closed.** Every proper prefix names something, even if it is not
   itself a usable tag. `hol.tm` is a sort, which is what lets userspace have a
   `Tm` type whose members are exactly the tags under `hol.tm.`, and lets a
   checker dispatch on prefix.
4. **Tags are opaque strings on the wire.** The decoder matches them exactly
   against a table and never splits on `.` at runtime. The dots are for humans
   and for userspace dispatch. Otherwise the format has smuggled in a path
   parser, and the TCB has to contain it.
5. Adding or renaming a tag changes the **schema** address. Integer tags later
   are a different _format_ over the same _class_, so they arrive as a second
   codec rather than as a version flag.

## S1 — dense arena, no parent

The whole first slice. Everything after it is additive.

### Shape

```
{
  "tag":  "arena.dense",
  "base": 1,
  "defs": [ def, ... ],
  "eq":   { ... }        -- optional, see below
}
```

`base` is the first local index; with no parent it is 1. It is in the wire from
the start so that S2 does not renumber anything.

A def is `{tag, ix?, var?}`:

```
{"tag": "hol.kind.star"}
{"tag": "hol.ty.bool"}
{"tag": "hol.ty.arr", "ix": [1, 1]}
{"tag": "hol.tm.var", "var": 0, "ix": [1]}      -- variable 0, of type #1
{"tag": "hol.tm.app", "ix": [3, 5]}
{"tag": "hol.tm.lam", "ix": [2, 6]}             -- binds the variable at #2
```

**A variable is `(name, type)`, both on the node.** No variable table. Lean's
`fv (name : Nat) (type)` [v:13] and covalence's `Var = (name, type)` [v:11] both
do this, and it is better than a table: two occurrences that disagree on the
type are simply two different variables, so the fold has no agreement condition
and no failure mode. `var 3 : bool` and `var 3 : nat` coexist.

Variable equality is name equality plus type equality. Type equality is
structural, so it is decidable within an arena, and the type indices being
ordered below their use makes the identity well founded even when a type
mentions variables.

### Worked example

`λx:bool. x`, with its type:

```
#1  {"tag": "hol.ty.bool"}
#2  {"tag": "hol.tm.var", "var": 0, "ix": [1]}
#3  {"tag": "hol.tm.lam", "ix": [2, 2]}
#4  {"tag": "hol.ty.arr", "ix": [1, 1]}
```

`fvs[2] = {(0, #1)}`, `fvs[3] = {}`, everything else empty. The lambda binds the
variable node at `#2` and its body is that same node.

### Rust

```
crates/logic/hol/src/
  wire.rs     Def, Arena — POD, serde only, no invariants
  check.rs    wire -> mem, total, typed errors        (TCB)
  mem.rs      the live arena
  tag.rs      generated from the S0 manifest
```

Reuse #746 rather than starting fresh: `ExprWire`/`Expr` and `ArenaWire`/`Arena`
are already this shape [v:5], and the changes are the tag type, the named
variable node, and dropping what S1 does not have.

### Validator

One pass, in index order:

1. tag known; `ix` arity and `var` presence match the tag.
2. every child index is in `[base, i)`.
3. the `fvs` fold, which is also what computes binder structure.
4. the `eq` forest, if present: `eq[i] ≤ i` and `eq[eq[i]] = eq[i]`, plus
   `fvs[i] = fvs[eq[i]]`.

No fetches, no fixed point, no allocation beyond the fold's own tables.

**Include the `eq` column in S1**, even with nothing to check its claims
against. It is two lines of validator and putting it in now means the wire and
the Lean model do not change when the e-graph arrives.

**Do not include a `ty` column in S1.** With named variables the type is a fold,
so store nothing. It becomes a stored claim only when unresolved imports arrive
and the fold cannot run — S2 at the earliest. This also sidesteps question 1.E.

One thing to know before writing the fold: **type synthesis produces types that
may not exist in the arena.** `ty(λx:bool. x)` is `bool → bool` whether or not
anything wrote it down. So the checker needs scratch space to build types in,
and cannot assume the answer is an index. That is a reason the `ty` column is a
claim rather than a cache.

### Lean

When the named syntax lands: the wire shape as a Lean structure, `validate` as a
predicate, `elaborate` into the named syntax, and

```
validate a = ok  →  elaborate a  is well formed
```

`HolLN/Array.lean` already has an arena, `validate` and `elaborate`
[n:notes/plans/2026-08-hol-kernel-mvp.md], so check whether this is a port
before writing it [?1.F].

### Tests

- Round-trip a corpus of small arenas, Rust and Lean agreeing on the bytes.
- Adversarial decode: cycles, out-of-range children, unknown tags, wrong arity,
  `var` on a node that takes none, duplicate map keys, non-preferred integer
  encodings. Every one a typed error, no panic. Fuzz it.
- The JSON projection as snapshot tests, since it is the debugging surface.

### Not in S1

Parent, links, segments, facts, sequents, stages, `ty` column, derived
addresses, substitutions, signing. Each is additive over this.

**Done when** the worked example round-trips through CBOR and through JSON, and
the adversarial corpus produces errors rather than panics.

## S1.5 — thin Python, immediately

Build, encode, decode, print. Perhaps an afternoon, and it is the surface you
will actually iterate on — a Rust test does not tell you whether the object
model is pleasant to hold. Do it before S2, not after.

## S2 — parent

The delta is small because S1 left room for it.

```
"links":  {"tag": "links.flat", "addrs": [O256, ...]}
        | {"tag": "links.link", "link": O256}
"parent": 0,          -- index into links; absent means none
"base":   14,         -- parent supplies [1, 14)
"var_base": 9         -- parent supplies variables [0, 9)
```

Links go in a table rather than inline, as decided [d]: shared tables cache
well, and the parent then needs no privileged name — it is a link index, so a
sequent can refer to it the same way it refers to anything else. Tagging both
forms rather than discriminating on CBOR major type keeps it self-describing and
JSON-clean, consistent with tagging everything else.

Write `resolve` as `Ix -> Local(i) | Import(link, source_ix)` from the start.
That is the same signature segments need, so S4 changes its body and not its
callers.

`var_base` is the degenerate one-window case of §9. Nothing about it changes in
S4; segments just get their own windows.

## S3 — Python API, and e-graph play

Full construction and inspection. E-graphs enter here as userspace over the
loaded arena, projecting back to the `eq` column. Resist specializing the wire
to whatever the first e-graph wants — issue #739 is the standing argument for
keeping congruence closure out of the format.

## S4 — segments

Segments over any arena kind, with `var_start`/`var_count` windows and the
overlap check. This is where the freshness interval test starts paying, so it is
also where the first tactic that needs it should be written.

## S5 — userspace

Basic tactics in Rust; the init arena for naturals and infinity that everything
imports; groundwork for nat and int literals. Issues #707–#710 are this, and
they are gated on polymorphism, so check that gate before starting.

## S6 — facts and sequents

Deliberately last. Until it exists, arenas make claims about nothing and stage 0
is the only stage, which keeps the TCB at "decode and validate" while the
representation settles. §6 and §7 are the design; PR #744 is already moving the
existing spike this way.

## If you want it faster

Cut S1 to: no `eq` column, no JSON projection, no fuzzing, three tags
(`hol.ty.bool`, `hol.tm.var`, `hol.tm.lam`). That is a day, and the object model
becomes something you can hold in Python by the end of the next one. Add the
rest back in S1's own follow-ups rather than blocking the first round trip on
them.
