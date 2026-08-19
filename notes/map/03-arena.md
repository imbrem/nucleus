# Map: the arena design

Proposal for the arena format and the plan to build it. Sources: the author's
2026-08-19 dump [d], the spike stack #734–#747 [v:5], issue #739, and the
covalence substrate notes [c]. Markers defined in [`00-index.md`](./00-index.md).

Hypotheses are labelled **H**. They are arguments, not results.

## 1. What an arena is

An indexed pile of HOL definitions, plus imports that supply some of the
indices, plus claims about those indices. It is the unit of serialization, the
unit of import, and the unit a worker hands to another worker.

Two things it is not. It is not canonical: many byte strings may decode to the
same arena, and each address names exactly one byte string [v:5][d]. It is not
the in-memory kernel state: the live structure may normalize, index, and cache
whatever it likes, provided it projects back to a wire arena.

## 2. Principles carried in

1. Decode is a partial function from bytes to objects. Injectivity in the other
   direction is not required and not wanted [d].
2. Hash raw bytes [d]. `Link` therefore addresses a byte string and carries its
   format and class at the reference site, which the spike already does [v:5].
3. TCB small and audited; userspace plural [d]. This sets the layering in §9.
4. Lean specifies; Rust transcribes [n:AGENTS.md].

## 3. Wire shape

```
arena = {
  tag:      "arena",
  elem:     "hol",                  -- what an index denotes
  schema?:  O256,                   -- drawn from links; identifies this vocabulary
  links:    [O256],                 -- flat address table, no logical content
  base:     u32,                    -- first local index
  segments: [seg],                  -- sorted, disjoint, inside [1, base)
  defs:     [def],                  -- indices base .. base + len
  ctx?:     Ix,                     -- default context for dense semantic columns
  premises:    [fact],
  conclusions: [fact],
  meta?:    { ... }
}

seg = { start, end, link, source_start }        -- as in the spike [v:5]
def = { tag, ix: [Ix], var?, data?, <columns>, meta? }
```

Field names are provisional [?1.C].

Three deliberate choices:

- **One arena class, not two.** The dump considers `arena.dense` and
  `arena.segment` as separate classes [d]. A dense arena is the case
  `segments = [{1, base, parent, 1}]`; an empty arena is `base = 1, segments =
  []`. Keeping one wire class keeps one decoder and one Lean model; the dense
  and overlay fast paths are in-memory specializations, which cost nothing given
  §9. Split the wire class later if a segment map needs to be shared by many
  overlays without copying — the dump's own workaround (build an arena of
  segments, import it as one segment) covers that case first [d].
- **Indices stay unsigned.** The dump floats negative indices for imports [d].
  The sign bit is already spent: `SRef` uses it for relation endpoint polarity
  [v:5]. One integer space with two sign conventions is a bug source, and it
  halves range.
- **Segments carry no logical content**, as the dump requires [d]. Claims about
  an imported arena go in the fact lists (§5), never on the segment.

## 4. Nodes and columns

A node is `tag`, children, optional payload, optional claim columns, optional
metadata. Claim columns are the dump's "arena is an E-graph by default": absent
column means absent claim, so an arena with no equalities pays nothing [d].

Two columns are worth having dense from the start:

- `ty : Ix` — the type of this index. Cheap, wanted by almost every consumer.
- `eq : Ix` — semantic equality, read under `ctx` (§6).

Everything else stays sparse in the fact lists until a workload demands a
column. Adding a column later is additive; removing one is not.

## 5. `eq` as a decreasing forest

**Proposal.** `eq` is an optional per-node index with `eq[i] ≤ i`. The
equivalence class of `i` is the fibre of the map. Normalized form: `eq[i]` is
the least index in `i`'s class, which makes `eq[eq[i]] = eq[i]`.

Validation is then one linear scan checking two conditions:

```
eq[i] ≤ i
eq[eq[i]] = eq[i]
```

No union-find, no path compression, no fixed point, no congruence closure at
decode time. Any finite equivalence relation on the index set is representable
this way, so nothing is lost. Normalization on load is a second scan.

**H1.** This is the whole of what an E-graph needs on the wire. Congruence
closure, E-matching, and hash-consing are derived indexes, rebuilt by whoever
wants them, exactly the position issue #739 takes. The wire records which
classes were claimed; it does not record how anyone arrived at them.

**H2 (merge restriction).** `eq` may only relate nodes with the same escaping
context. A node containing a bound variable that escapes it denotes something
only relative to a binder path, so two nodes escaping different contexts are not
comparable. §8 defines the per-index demand map `dem[i]` that makes this
checkable; the condition is `dem[i] = dem[eq[i]]`, and the common case is both
empty, meaning both locally closed. H2 is not yet checked against the Lean
semantics [?1.D].

`ty` gets the same treatment minus the forest condition: `ty[i]` is an index,
`ty[i] ≠ i`, and whether `ty[i] < i` should be forced is [?1.E].

## 6. Facts, and where the context goes

The dump works through a real tension and lands on needing `syn_ctx` beside
`sem_ctx` [d]. The tension is that

```
Der(Γ) ⊢ Der(P)        -- meta-level: if Γ is derivable then P is
Der(Γ ⊢ P)             -- one derivation, premises inside the turnstile
```

are different statements. The second gives the first by cut. The first does not
give the second: it holds vacuously whenever Γ is not derivable.

**Proposal.** One fact type, with the context inside the derivability former.

```
fact ::= Syn(rel, a, b)      -- syn_eq, conv_eq, ty_eq, has_ty, has_kind, ne, ...
       | Der(ctx, i)         -- i is derivable in HOL under context index ctx
       | Claims(link, stage) -- everything the linked object claims up to stage
```

Premises and conclusions are then two lists of the same type, and the sequent is
metalogical throughout. Object-level implication does not appear in the sequent;
it appears as a bigger `ctx`. That removes the need for a second sequent, a
`sem_ctx` field, and the syntactic/semantic split at the top level. Dense
columns desugar: `eq[i] = j` is `Der(ctx, EQ(i, j))`, `ty[i] = t` is
`Syn(HasTy, i, t)`.

The three import modes the dump names [d] fall out. Ignore an imported arena's
claims by mentioning no `Claims` fact; assume them with a premise; take
responsibility for them with a conclusion. Both directions are needed:
premises may be added freely and conclusions dropped freely, which is the
weakening the dump wants.

**H3.** `Der` is a modality over an unspecified derivability relation and need
not be decidable. Every `Syn` relation currently is decidable, but nothing in the
format should assume it.

## 7. Stages

A stage is a number saying how far an object has been checked. Each fact former
declares the stage at which it is checked.

| Stage | Meaning |
| --- | --- |
| absent | nothing claimed |
| 0 | decodes; structurally well formed; indices in range |
| 1 | `Syn` facts checked |
| 2 | `Der` facts checked |

Stage is orthogonal to fact former. A stage says how far; a former says what
shape. The dump considers collapsing the syntactic/semantic distinction into
staging [d]; §6 says the distinction was never the right axis in the first
place, and once contexts sit inside `Der` there is nothing left to collapse.
Higher stages are free for later conventions, and `Claims(link, stage)` lets an
importer say which level of an import it is relying on.

Validation at stage n implies validation at every stage below it. An arena
carrying no facts is valid at every stage vacuously.

## 8. Binder discipline

The arena constrains this more than a tree does, because an arena **shares
subterms**. One index may be reached from two different binder paths. Sharing an
open node across two incompatible contexts is unsound, so whichever discipline
is chosen, validation needs a per-index summary of what escapes that node. Call
it `dem[i]`, the demand map.

That reframes the choice. The cost of tracking locally-closed-versus-not is not
a cost of de Bruijn; it is a cost of sharing, and it is owed under every option.

### What Lean does today

Term level: `bv : Fin depth` — scoped and **untyped**, so no dangling index is
representable and `depth = 0` means locally closed. `fv (name : Nat) (type)` —
free variables are numeric levels carrying their type. `lam (domain) (body)`
carries the binder's domain on the binder [v:13]. Type level: `TyVar` is a
kind-indexed de Bruijn variable, so type variables are already intrinsically
typed [v:7].

The consequence, and the objection that prompted this section: a `bv` gets its
type from the enclosing `lam`, so `ty` cannot be a per-index column. Typing a
lambda means either opening the body against a fresh variable, or walking with a
binder-type stack and accepting that the cached type of a shared open node is
only valid under one stack.

### Three options

| | named levels | typed de Bruijn | untyped de Bruijn (today) |
| --- | --- | --- | --- |
| type of a lambda body | local | local | needs the binder stack, or an open |
| `dem[i]` is | a set of free names | a map depth → type | a map depth → type, discovered by walking |
| alpha equivalence | not structural | structural | structural |
| shifting | none | at every binder | at every binder |
| substitution | capture-avoiding; freshness trivial if names are levels | shift and subst | shift and subst |
| effect on the Lean spec | changes `lam`'s shape; pushes freshness side conditions into the rules | none: the annotation erases | none |
| wire cost | binder stores a variable index; `bv` nodes disappear | one extra index per `bv` node | nil |

### Proposal: typed de Bruijn in the arena, erased on elaboration

`TM_BV(k, α)` carries the type index `α`. Elaboration to Lean drops it, so the
arena stays a surface for the existing spec rather than a change to it. For a
valid arena the annotation is determined by the enclosing binder, so it adds no
expressiveness — only locality.

Checking becomes one bottom-up fold computing `(ty[i], dem[i])`:

```
TM_BV(k, α)        ty = α                        dem = {k ↦ α}
TM_FV(x, α)        ty = α                        dem = {}
TM_APP(f, a)       ty = codomain of ty[f]        dem = dem[f] ⊔ dem[a]
TM_LAM(α, b)       ty = α → ty[b]                dem = shift(dem[b] ∖ {0})
                   requires dem[b][0] = α or absent
```

`⊔` is union with agreement required on shared depths; disagreement is a decode
error. `dem` is bounded by binder depth and is empty for the overwhelming
majority of nodes.

Three things fall out:

- `ty` becomes a genuine per-index column, cacheable and shareable, which is
  what the arena wanted.
- `dem[i] = ∅` is exactly "locally closed", so H2 needs no separate machinery,
  and its relaxed form — merge whenever `dem` agrees — is available for free.
- Sharing is checked rather than assumed. Two use sites of one open node must
  agree on the escaping context, which is what the `⊔` at every node enforces.

**H5.** Annotation erasure is total and the annotated arena is in bijection with
the Lean term up to sharing, so no soundness argument changes. Unverified
[?1.K].

Names remain the fallback if the annotation bookkeeping turns out worse in
practice than it reads here. In that case use levels rather than user strings,
since freshness and capture-avoidance become trivial, and accept that
alpha-equivalent terms occupy different classes until something proves them
equal — which is admissible, since `eq` is a claim rather than a definition.
Covalence went the named-free route with `Var = (name, type)` [v:11], so there
is prior experience to draw on either way.

## 9. Layering

```
crates/logic/hol/src/
  wire/    POD structs, serde only, no invariants, no methods that can fail
  check/   wire -> mem. Total. Typed errors. In the TCB.
  mem/     live structures. Plural. Not in the TCB.
```

Only `wire` and `check` are mirrored in Lean and read line by line. `mem` may
hold a dense `Vec` arena, a static-slice arena, a SQLite-backed arena, or an
E-graph with congruence closure, provided each projects back to a `wire` arena.
The spike already splits `ExprWire`/`Expr`, `SegmentWire`/`Segment`,
`ArenaWire`/`Arena` [v:5]; this makes the habit a rule and names the layers.

Covalence reached the same split and added a warning worth keeping: the typed
façade's type machinery must not define the persisted semantics, and the two
evaluators must be differentially tested
[c:notes/vibes/kernel/substrate-expressions.md].

## 10. Links, formats, classes, schemas

Keep the spike's `Link { addr, format, class }` [v:5]. Format is the byte-level
codec; class is the logical object. Both at the reference site, never behind the
hash.

Add one optional field: `schema: O256`, drawn from `links`. A new vocabulary
gets a new address, so version confusion becomes a hash mismatch rather than a
misparse, and there are no sequential version numbers to keep in sync.

Prior art, since the dump asks [d] [x]:

- **IPLD CID** is `(multicodec, multihash)` — the same `(format, addr)` pair,
  with class folded into the codec. The repo already has multiformats in
  `crates/lib/hash`.
- **Unison** addresses definitions by hash and keeps names as metadata, which is
  the dump's "namespace maps a string to a link".
- **Nix content-addressed derivations** and **Bazel's action cache** are both
  "hash of a deterministic computation → result", the generalized CAS the dump
  sketches. Both are worth reading for what goes wrong: mostly non-determinism
  and cache poisoning.
- **CDDL** for schema description over CBOR; **Arrow** and **FlatBuffers** for
  dense typed ranges over a buffer, which is what a segment over an array of
  10M floats becomes.
- **CLOS / the metaobject protocol** for the object-system-with-refinements idea.
  A single-inheritance class tree plus a DAG of refinements that unlock
  interfaces is close to CLOS with `deftype` predicates.

## 11. Data payloads

Start with `bytes` and small unsigned integers, matching ladder level 0A
[n:notes/vision/ladder.md]. Bignat and bigint decode from bytes or arithmetic
expressions in HOL. CBOR bignum tags are a portability hazard across
implementations and are not needed for the first slice [d].

Keep string map keys throughout v0. Integer keys buy compactness and cost
readability and JSON compatibility; if wanted, they belong in a separate schema
O256, not a flag.

## 12. Validation, in one pass

Every check below is linear, allocation-bounded, and independent of any fixed
point:

1. tag known; arity and payload shape match the tag.
2. every child index either `< i` locally, or inside a declared segment.
3. segments sorted, disjoint, inside `[1, base)`; translated source ranges stay
   in index space.
4. the `(ty, dem)` fold of §8; binder agreement discharged at every binder.
5. `eq` forest conditions; `ty` conditions.
6. facts: endpoints in range, `ctx` in range, relation known.

Nothing here fetches an import. Resolving a segment is a separate, later,
fallible step. Fail closed: a node that does not decode yields no arena, no
partial arena, and no theorem — covalence's rule [c:notes/vibes/kernel/substrate-expressions.md].

## 13. Not building yet

Named so they are not smuggled in: the general object system and class tree;
namespaces and string-keyed links; sparse arenas; 64-bit arenas; WASM-defined
segment formats; Amazon Ion; signatures and PKI on arenas; persistent E-graphs
as their own `(format, class)`. Each is a natural extension point of §3 and none
is needed to get the first slice used.

Ion is worth revisiting when either the CBOR bignum situation or the
self-describing-symbol-table pressure actually bites; writing our own reader
would put it in the TCB, which is the reason to wait.

## 14. Plan

Each step is a spike branch off `main`, kept open, with a note in
`notes/spikes/` when it has been used [n:AGENTS.md §2].

**P0 — tag manifest.** One file generating the Rust tag table and the Lean tag
table. Closes issue #745. *Done when* adding a constructor in one place fails
the build everywhere it is not handled.

**P1 — `wire` + `check`.** The §3 shape, the §12 validator, no logic. Round-trip
and adversarial-input fuzzing. Reuse #746 as the starting point rather than
starting fresh. *Done when* a corpus of arenas round-trips and every malformed
input yields a typed error instead of a panic.

**P2 — facts, stage 1.** The §6 fact type, both lists, the `Syn` checker.
Replaces `Seq`/`Ctx`/`Relations` from #735 with one list type; PR #744 is
already moving that way. *Done when* an arena with `has_ty` and `syn_eq`
conclusions checks at stage 1, and a wrong claim is rejected.

**P3 — `Der` and the LCF boundary.** Rule methods that mint conclusions. No
constructor for a `Der` conclusion outside a rule. Ties into #727. *Done when*
a small theorem is proved through the rule API and lands in an arena's
conclusion list.

**P4 — derived E-graph index.** Userspace. Congruence closure over a loaded
arena, projecting back to `eq` columns. Benchmarks against the sparse
representation. This is issue #739. *Done when* the projection round-trips and
the benchmark exists, whatever it says.

**P5 — Python.** Mirror the `wire` objects, not the `mem` ones. Follows #747 and
#742.

Lean work runs beside P1–P3: the `wire` shape and the §12 validation predicate,
with the theorem that a validated wire arena elaborates to the intended HolE
object. `HolLN/Array.lean` already has an arena, `validate`, and `elaborate`
[n:notes/plans/2026-08-hol-kernel-mvp.md], so this is closer to porting than to
inventing [?1.F].

## 15. Open points

Collected in [`questions/round-1.md`](./questions/round-1.md): 1.A–1.K.
