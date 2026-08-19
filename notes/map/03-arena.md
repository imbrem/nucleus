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
3. TCB small and audited; userspace plural [d]. This sets the layering in §10.
4. Lean specifies; Rust transcribes [n:AGENTS.md].
5. **Grounding by consilience.** Several equivalent syntaxes and proof systems,
   with maps between them, are worth having for their own sake. They are
   evidence that the thing formalized is the thing intended, which internal
   consistency alone cannot give: a system can be consistent while its symbols
   mean something subtly other than what was meant. The condition is that
   exactly one surface is _normative_ — the one the arena implements — and that
   the others are labelled as grounding rather than mistaken for it [d].

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

seg = { start, end, link, source_start,
        var_start, var_count }                  -- §8; the first four are the spike's [v:5]
def = { tag, ix: [Ix], var?, data?, <columns>, meta? }

A variable is `(name, type)`, both carried on the node — `{tag: "hol.tm.var",
var: n, ix: [type]}` — as in Lean's `fv (name : Nat) (type)` [v:13] and
covalence's `Var = (name, type)` [v:11]. There is no variable table. Two
occurrences that disagree on the type denote two different variables, so
gathering free variables has no agreement condition and cannot fail.
```

Field names are provisional [?1.C].

Three deliberate choices:

- **One arena class, not two.** The dump considers `arena.dense` and
  `arena.segment` as separate classes [d]. A dense arena is the case
  `segments = [{1, base, parent, 1}]`; an empty arena is `base = 1, segments =
[]`. Keeping one wire class keeps one decoder and one Lean model; the dense
  and overlay fast paths are in-memory specializations, which cost nothing given
  §10. Split the wire class later if a segment map needs to be shared by many
  overlays without copying — the dump's own workaround (build an arena of
  segments, import it as one segment) covers that case first [d].
- **Indices stay unsigned.** The dump floats negative indices for imports [d].
  The sign bit is already spent: in the spike a negative `SRef` is the logical
  negation of the positive reference, as an endpoint of the implication relation
  `A ⇒ B` [d], matching the signed-literal convention in `crates/logic/sat`
  where `Literal(i64)` is negatable and zero is rejected [v:16]. One integer
  space with two sign conventions is a bug source, and it halves range.
- **Segments carry no logical content**, as the dump requires [d]. Claims about
  an imported arena go in the fact lists (§5), never on the segment.

## 4. Nodes and columns

A node is `tag`, children, optional payload, optional claim columns, optional
metadata. Claim columns are the dump's "arena is an E-graph by default": absent
column means absent claim, so an arena with no equalities pays nothing [d].

Two columns are worth having dense from the start:

- `ty : Ix` — the type of this index. Cheap, wanted by almost every consumer.
- `eq : Ix` — semantic equality, read under `ctx` (§6).

A third is derived rather than stored: `fvs[i]`, the free variable set (§7).
It is a fold over local nodes, so putting it on the wire would only cache it.

Note what `ty` is and is not. **Only a node's child indices are syntax.** A type
is a predicate attached to an index afterwards, so the `ty` column carries no
ordering or well-foundedness obligation and `ty[i]` may point anywhere [d]. The
child indices are the only thing the structural validator constrains.

Everything else stays sparse in the fact lists until a workload demands a
column. Adding a column later is additive; removing one is not.

**Derived for local nodes, claimed for imported ones.** `ty`, `fvs` and `dem`
are all folds, and a fold cannot run over an index that has not been fetched. So
for any index supplied by an unresolved segment, each of them has to arrive as a
fact instead — `Syn(HasTy, i, t)`, and the analogous formers for free variables
and escaping context. That is what makes a side condition dischargeable without
resolving the import, and it is the same shape as the classified links of #726,
where `TM_LINK` carries its declared type. Issues #715 and #718 are the same
question from the import side. §8 gives the variable case a cheaper answer
than a fact: an interval.

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

**H2 (what context-freedom costs).** The point of keeping `eq` on the wire this
way is that an E-class carries no context: a class is a set of indices and
nothing else, so two arenas' classes can be compared without carrying a context
around [d].

The price is paid at use rather than at merge. An `eq` claim is read under the
arena's `ctx`, so a class over indices whose free variables include `x` is only
usable under a binder for `x` when `x` does not occur in the context
assumptions. Otherwise the class was justified by hypotheses about `x` that the
binder has just discharged.

That side condition is `x ∉ fvs(ctx)`, which is the freshness test §8 makes an
interval comparison when the context is imported. So context-freedom of E-class
identity is bought with a freshness obligation on the consumer, and the
obligation is cheap.

Nothing in the validator enforces it: a stage-0 validator checks the forest
shape, and whoever _uses_ a class under a binder checks the freshness. Recorded
because it is easy to forget and unsound to skip [?1.D].

`ty` gets no such condition. **A type is not syntax** — only a node's child
indices are. `ty` is a predicate attached after the fact, so `ty[i]` is
unconstrained: it may point anywhere, before or after `i` [d]. Only the child
indices carry the ordering invariant.

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
       | Claims(link)        -- everything the linked object claims
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

**What an absent `ctx` means.** Absent is the empty context. Since a context
here is an index denoting a proposition, the empty context is `⊤`, so absent and
`ctx: ⊤` agree and writing `⊤` explicitly is the unambiguous form [d].

`ctx: ⊥` is worth having for the opposite reason. Everything is derivable from
`⊥`, so an arena whose context is `⊥` makes semantically vacuous claims — its
`Der` facts hold trivially and carry no information. That is a sound way to
write "these facts are not semantically checked" without a mode, a flag, or a
special case in the checker: the marker is a value, and the ordinary reading of
it is already the intended meaning. Well-formedness is still required, so `⊥`
buys vacuity, not permission to write nonsense.

**H3.** `Der` is a modality over an unspecified derivability relation and need
not be decidable. Every `Syn` relation currently is decidable, but nothing in the
format should assume it.

## 7. Binder discipline

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

|                           | named levels                                                                     | typed de Bruijn               | untyped de Bruijn (today)                 |
| ------------------------- | -------------------------------------------------------------------------------- | ----------------------------- | ----------------------------------------- |
| type of a lambda body     | local                                                                            | local                         | needs the binder stack, or an open        |
| `dem[i]` is               | a set of free names                                                              | a map depth → type            | a map depth → type, discovered by walking |
| alpha equivalence         | not structural                                                                   | structural                    | structural                                |
| shifting                  | none                                                                             | at every binder               | at every binder                           |
| substitution              | capture-avoiding; freshness trivial if names are levels                          | shift and subst               | shift and subst                           |
| freshness side conditions | an `fvs` column (§4)                                                             | an `fvs` column (§4)          | an `fvs` column (§4)                      |
| effect on the Lean spec   | needs `close`, an alpha relation, and the quotient in every correspondence lemma | none: the annotation erases   | none                                      |
| wire cost                 | binder stores a variable index; `bv` nodes disappear                             | one extra index per `bv` node | nil                                       |

### Freshness is a column, not a per-rule burden

An earlier draft of this section counted freshness side conditions against the
named option. That was wrong. "Term `t` has free variable set `S`" is a
meta-fact of the same standing as "term `t` has type `α`", so it is a column
computed by a fold, and the rules read it:

```
fvs(TM_FV x)      = {x}
fvs(TM_APP f a)   = fvs[f] ∪ fvs[a]
fvs(TM_LAM x b)   = fvs[b] ∖ {x}          -- named binders
fvs(binder b)     = fvs[b]                -- de Bruijn binders
```

The fold is **total**: unlike `dem`, it has no agreement condition and no failure
mode. The spec already has the predicate this computes — `Fresh name f` is a
hypothesis of the `eta` rule in `Hol/Kernel.lean` and `HolE/Kernel.lean` [v:14] —
so `fvs` is its computational form, and there is no `freeVars` function in Lean
yet to conflict with [v:14].

Take the column regardless of which binder discipline wins. HOL's side
conditions are about _free_ variables, which are named under every option here,
so `fvs` is owed either way. §4 lists it.

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

### What is left of the argument against names

As of 2026-08-19 the author is formalizing a named syntax in Lean that lowers
into the nameless one [d]. It is wanted under either outcome here — it is
grounding under principle 5, and the arena's choice does not bear on whether it
is worth having. It does, incidentally, fire the flip condition stated in the
previous draft of this section.

The argument against names was never about the implementation. It was that named
binders introduce an alpha quotient which then rides along in every
correspondence lemma, and that the spec has no reason to carry one: Lean today
has `openBound`, `instantiate` and `instantiateOne`, no `close` or `abstract`,
no `freeVars`, and zero occurrences of "alpha" in `lean/Nucleus` [v:14]. Once
`close` and the lowering exist and are proven, that cost is paid for other
reasons — under principle 5 it is not a cost at all, it is the grounding — and
the arena's elaboration becomes an instance of a map that already has a Lean
counterpart.

What names then have going for them, collected:

- `fvs` is a total fold. `dem` is a fold with an agreement condition that can
  fail.
- Sharing of open nodes is unconditional. There is no merge restriction, so H2
  disappears rather than relaxing.
- No shifting anywhere.
- No annotations, so no H5 erasure obligation.
- Alpha-variants occupying distinct indices is not a new kind of problem. It is
  principle 1 again: many encodings, one meaning, and the requirement is only
  that each encoding decodes to at most one term.

What they cost:

- `syn_eq` stays structural, so alpha-equivalence needs a rule or belongs to
  `conv_eq`, which already does beta and eta.
- Congruence closure wants alpha-canonical keys. Canonical renaming is
  well defined bottom-up for closed nodes, so it can be a load-time
  normalization in userspace rather than a validity condition. Open nodes stay
  as written.
- Free variable identity has to survive imports and overlays, and under names
  that identity sits under binders as well as at leaves [?1.M]. This is the one
  that is genuinely unsolved.

### Recommendation

**Start named**, with numeric levels [d]. §8 adds the argument that decided it
in practice: with integer names and per-segment variable windows, freshness
against an entire import is an interval test. Typed de Bruijn stays fully specified
above as the fallback, and is what to reach for if free-variable identity across
imports turns out to want anonymous binders [?1.M].

Starting named is cheap to reverse, which is most of why it is the right place
to start. Both surfaces lower to the same Lean term, so a later move to typed de
Bruijn changes the arena's node set and its validator, and changes nothing about
the theorems underneath.

Two consequences worth stating, since principle 5 turns on being clear which
surface is normative:

- The **named surface is the implemented one**. The nameless syntax is the
  spec's core and the lowering's target.
- The **lowering is TCB**, because the checker's meaning for an arena is the
  term it lowers to. The reverse map, nameless back to named for display, is
  not TCB — it is in the same semi-trusted position as the REPL's
  prettyprinter [n:notes/vision/ladder.md].

This reverses the recommendation two paragraphs of this document earlier held.
The ground moved twice: freshness side conditions turned out to be a column
rather than a per-rule burden, and the alpha quotient turned out to be
deliberate work rather than a tax. Both were flip conditions written down in
advance, which is the only reason to trust the reversal.

The `dem` fold is still worth writing even under names, as the thing that would
have to exist if 1.M forces the fallback. Both folds are around forty lines
[?1.L].

## 8. Variables across arenas

Free variables are integers [v:13]. Two arenas built independently will use the
same integer for different variables. Inside one arena, whether two indices
mention the same variable is a comparison; across arenas it is undecidable
without a convention.

**Rejected: a per-arena variable namespace.** It works — an arena's variables
cannot leak into its parents, since cycles are forbidden, and parents may
contain parent variables. The problem is that mutating an arena changes its
variable signature, so loading a parent and extending it silently refreshes
every variable [d]. Identity that changes under append is not worth the
disjointness it buys.

**Proposal: variable translation is index translation.** A segment already
carries `source_start` and translates the source's indices into the importer's
index space. Give it two more fields and let it do the same to variables:

```
seg = { start, end, link, source_start, var_start, var_count }
```

Imported variable `k < var_count` denotes `var_start + k` locally. `k ≥
var_count` is out of range [?1.N]. The validator checks that the windows
`[var_start, var_start + var_count)` of distinct segments do not overlap and
that the arena's own variables sit above all of them. Disjointness then holds by
construction rather than by convention, and nothing is renamed: translation is
virtual, exactly as it already is for indices.

Three things follow.

- **Freshness against a whole import is an interval test.** The free variables
  of any imported index lie in that segment's window, so `x ∉ fvs(t)` for an
  entire imported term or context reduces to `x ∉ [var_start, var_start +
var_count)`. Constant time, and no fetch. This is the fast discharge the dump
  asks for [d], and it is the strongest practical argument for integer-named
  free variables.
- **Append-only mutation preserves identity.** Adding definitions allocates new
  variables above the existing windows and renumbers nothing, which is the
  property the per-arena namespace loses.
- **`super.k` is a display convention**, not a mechanism. A parent's variable
  `k` is `parent_var_start + k`, and the prettyprinter may render it however it
  likes.

`var_count` is a claim about the source until the import is resolved. Before
resolution it belongs in the premise list; on resolution it is checked. That is
the same treatment §4 gives to `ty` and `fvs` for unresolved indices.

The general form is a substitution per segment rather than an offset, or a
separate variable arena that definitions draw from, with a segment arena of
those for extensibility [d]. A window is the affine degenerate case of both.
Start with windows; the wire cost is two integers per segment and the checker
cost is an overlap scan.

## 9. Derived addresses

Give every term a name of its own, fast, by keyed hashing:

```
at(base, kind, payload) = keyed_hash(key = base, tag(kind) ‖ payload)

term    at(arena_addr, IX,     u64le(index))
symbol  at(base,       SYM,    utf8)
member  at(iface,      MEMBER, member_addr)        -- e.g. Add.add
```

`crates/lib/hash` already has the shape: `Obj::<N>::with_key(key, bytes)` where
`N: KeyedNamespace<K>`, so each derivation kind is a namespace type and the
domain separation is in the type rather than in a byte the caller must remember
[v:15]. The payload encoding has to be injective, which fixed-width and
whole-remainder encodings give.

Properties, stated plainly because they decide how the thing can be used:

- **Not canonical.** Two encodings of the same arena give different arena
  addresses and therefore different term names, and a term imported from
  elsewhere gets a different name again. Principle 1 already accepts this: what
  matters is that each name denotes at most one term.
- **Situated, and that is the point.** `at(H, IX, i)` names a term _as it sits
  in a particular theory in a particular DAG of parents_. That carries real
  information — the reals presented over Dedekind cuts are a different name from
  the reals presented otherwise. The Git analogy is close enough to be useful:
  the plumbing is content and parent pointers, and the naming conventions on top
  are porcelain [d].
- **One-way.** Given a bare derived address you cannot recover the base or the
  key, so resolving one needs a directory. Given the preimage anyone can check
  it.

That last property sets a rule: **never store a bare derived address; store the
derivation and compute it.** Then every use is checkable without a lookup, and
derived addresses stay an export and interchange concern rather than an internal
one.

**Pointwise term imports.** A term named by a derived address enters an arena as
a segment of length one whose link is that address. No new fact former is
needed: facts stay index-to-index, and a HOL equation about two individually
named terms is an ordinary fact between two one-element segments. That also
answers what the dump wanted from single-definition segment formats [d].

**Reconciling pointwise and range imports.** If a segment imports `3..25` from
`H` and another imports the single term `at(H, IX, 10)`, whether the two
indices denote the same term is decidable by arithmetic on the segment table.
Recompute the derived address from the range segment's `(link, source_start)`
and compare. Neither import has to be resolved. This is the near-term payoff and
worth building early [?1.O].

Symbols and interface members use the same operator and are otherwise deferred.
Prior art for the operator itself: BLAKE3's `derive_key` mode, HKDF's info
label, and capability derivation in Tahoe-LAFS all do exactly this, and all of
them insist on domain separation for the same reason [x].

## 10. Layering

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

## 11. Links, formats, classes, schemas

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

## 12. Data payloads

Start with `bytes` and small unsigned integers, matching ladder level 0A
[n:notes/vision/ladder.md]. Bignat and bigint decode from bytes or arithmetic
expressions in HOL. CBOR bignum tags are a portability hazard across
implementations and are not needed for the first slice [d].

Keep string map keys throughout v0. Integer keys buy compactness and cost
readability and JSON compatibility; if wanted, they belong in a separate schema
O256, not a flag.

## 13. Validation, in one pass

Every check below is linear, allocation-bounded, and independent of any fixed
point:

1. tag known; arity and payload shape match the tag.
2. every child index either `< i` locally, or inside a declared segment.
3. segments sorted, disjoint, inside `[1, base)`; translated source ranges stay
   in index space.
4. the `(ty, dem)` fold of §7; binder agreement discharged at every binder.
5. `eq` forest conditions; `ty` conditions.
6. facts: endpoints in range, `ctx` in range, relation known.

Nothing here fetches an import. Resolving a segment is a separate, later,
fallible step. Fail closed: a node that does not decode yields no arena, no
partial arena, and no theorem — covalence's rule [c:notes/vibes/kernel/substrate-expressions.md].

## 14. Not building yet

Options considered and set aside are in
[`08-alternatives.md`](./08-alternatives.md) rather than deleted: staged
validity levels, first-class substitutions, typed de Bruijn, per-arena variable
namespaces.

Named so they are not smuggled in: the general object system and class tree;
namespaces and string-keyed links; sparse arenas; 64-bit arenas; WASM-defined
segment formats; Amazon Ion; signatures and PKI on arenas; persistent E-graphs
as their own `(format, class)`. Each is a natural extension point of §3 and none
is needed to get the first slice used.

Ion is worth revisiting when either the CBOR bignum situation or the
self-describing-symbol-table pressure actually bites; writing our own reader
would put it in the TCB, which is the reason to wait.

## 15. Plan

Each step is a spike branch off `main`, kept open, with a note in
`notes/spikes/` when it has been used [n:AGENTS.md §2].

**P0 — tag manifest.** One file generating the Rust tag table and the Lean tag
table. Closes issue #745. _Done when_ adding a constructor in one place fails
the build everywhere it is not handled.

**P1 — `wire` + `check`.** The §3 shape with named binders (§7), the §13
validator, the `fvs` fold, no logic. Round-trip
and adversarial-input fuzzing. Reuse #746 as the starting point rather than
starting fresh. _Done when_ a corpus of arenas round-trips and every malformed
input yields a typed error instead of a panic.

**P2 — facts.** The §6 fact type, both lists, the `Syn` checker.
Replaces `Seq`/`Ctx`/`Relations` from #735 with one list type; PR #744 is
already moving that way. _Done when_ an arena with `has_ty` and `syn_eq`
conclusions checks at stage 1, and a wrong claim is rejected.

**P3 — `Der` and the LCF boundary.** Rule methods that mint conclusions. No
constructor for a `Der` conclusion outside a rule. Ties into #727. _Done when_
a small theorem is proved through the rule API and lands in an arena's
conclusion list.

**P4 — derived E-graph index.** Userspace. Congruence closure over a loaded
arena, projecting back to `eq` columns. Benchmarks against the sparse
representation. This is issue #739. _Done when_ the projection round-trips and
the benchmark exists, whatever it says.

**P4a — derived addresses.** The `at` operator, one-element segments, and the
pointwise-versus-range reconciliation of §9. Small, and it is what makes HOL
equations about individual O256s possible.

**P5 — Python.** Mirror the `wire` objects, not the `mem` ones. Follows #747 and
#742.

Lean work runs beside P1–P3: the named syntax and its lowering, then the `wire`
shape and the §13 validation predicate, with the theorem that a validated wire
arena elaborates through the lowering to the intended HolE object. `HolLN/Array.lean` already has an arena, `validate`, and `elaborate`
[n:notes/plans/2026-08-hol-kernel-mvp.md], so this is closer to porting than to
inventing [?1.F].

## 16. Open points

Collected in [`questions/round-1.md`](./questions/round-1.md): 1.A–1.R.
Implementation order in [`06-plan.md`](./06-plan.md). The minimal first
format is [`07-format-v0.md`](./07-format-v0.md). Parked options are in
[`08-alternatives.md`](./08-alternatives.md).
Literature in [`05-pointers.md`](./05-pointers.md).
