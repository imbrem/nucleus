# Questions, round 1

Opened 2026-08-19. Cited elsewhere as `[?1.A]` and so on. Write answers under
each question; this file is the log, so nothing gets deleted.

---

## 1.A — What landed of `Nucleus.Hol`, and by which route?

`lean/Nucleus/Nucleus/Hol/` is on `main` at 8,373 lines with `Signature.lean`,
`Soundness.lean`, `Intrinsic.lean` [v:3]. PR #701, described as the
signature-parametric kernel, is still open [v:6]. The 2026-08-17 plan treats
landing #701 as the Day-0 decision [n:notes/plans/2026-08-hol-kernel-mvp.md].

Matters because: that plan's critical path may already be done, which would
change what the next fortnight is for.

**Answer:**

---

## 1.B — What does a negative `SRef` mean?

`SRef::neg` exists with no doc comment [v:5]. The dump mentions "the variant
with SAT style negative indices" [d], which reads as polarity.

Matters because: §3 of `03-arena.md` rejects negative indices for imports on the
grounds that the sign is already spent. If `neg` means something else, or is
vestigial, that argument changes.

**Answer:**

---

## 1.C — Field names

`03-arena.md` §3 uses `tag, elem, schema, links, base, segments, defs, ctx,
premises, conclusions, meta`. The dump floats `imports`/`links`, `offset`/`count`
versus `start`/`end`, `class` versus `kind` [d]. The spike uses `kind` in
`Link` and `start`/`end` in `Segment` [v:5].

Matters because: renaming after fixtures exist is annoying, and the JSON
projection makes these user-facing.

**Answer:**

---

## 1.D — Is the merge restriction right?

**H2** in `03-arena.md` says `eq` may relate two nodes only when their demand
maps agree, `dem[i] = dem[eq[i]]`. The strict form is both empty, meaning both
locally closed. The relaxed form allows merging two open nodes that escape the
same context — a subterm under a binder during rewriting, for instance.

Matters because: strict is one comparison and is hard to relax later without a
format change; relaxed makes the escaping context part of E-class identity,
which is the "context key in E-class identity" question in issue #739.

**Answer:**

---

## 1.E — Must `ty[i] < i`?

Forcing it means a type always precedes the term it types, so the whole arena
stays a DAG in index order. Allowing `ty[i] > i` allows types to be added to an
arena after the fact, in an overlay.

Matters because: the overlay story wants late additions; the single-scan
validator wants monotone indices.

**Answer:**

---

## 1.F — Does `HolLN/Array.lean` port to the HolE arena?

It has an arena, `validate`, `elaborate`, and a JSON codec for rows
[n:notes/plans/2026-08-hol-kernel-mvp.md]. Not read in detail this session.

Matters because: it decides whether the Lean side of P1 is a port or a new
model.

**Answer:**

---

## 1.G — What does an absent `ctx` mean?

Empty context, or "this arena makes no derivability claims"? And is one default
context per arena enough, or does each dense column need its own?

Matters because: it sets whether `eq` columns are usable in an arena that never
declares a context.

**Answer:**

---

## 1.H — Where does this land, and when?

The arena work is a spike stack. Is the goal to get #746 or a successor onto
`main` in this push, or to keep iterating off-trunk until the design has been
used? `AGENTS.md` sets a high bar for merging and says the decision is human
[n:AGENTS.md §2].

Matters because: it decides whether P1 in the plan targets a merge or another
spike.

**Answer:**

---

## 1.I — Is `elem` needed in v0?

The only value is `"hol"`. It is one string per arena and it makes format
confusion between arena kinds impossible later.

**Answer:**

---

## 1.J — Should `Claims(link, stage)` carry a stage?

Alternative: `Claims(link)` means everything the linked object claims, and the
importer takes it or leaves it.

Matters because: a stage argument lets an importer assume only the syntactic
half of an import, which is the cheap half to check.

**Answer:**

---

## 1.K — Is annotation erasure really free?

**H5** in `03-arena.md` §8 claims `TM_BV(k, α)` erases to Lean's `bv k`, that
the annotation is determined by the enclosing binder in any valid arena, and
that no soundness argument therefore changes.

Two things to check. First, whether the `(ty, dem)` fold really discharges every
obligation the binder-stack walk would, including for `sub`, `abs` and `rep`,
which bind a term variable in their predicate at `depth 1` [v:13]. Second,
whether the elaboration in `HolSurface/RustMapping.lean` can absorb the extra
field without restructuring.

Matters because: if erasure is not free, typed de Bruijn stops being a surface
convenience and becomes a change to the spec, at which point named levels are
the cheaper option.

**Answer:**
