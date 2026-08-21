# Map: PR, issue, and docs status

As of 2026-08-19. Counts are exact [v:6][v:12].

## Counts

- **340 open pull requests** (100 + 100 + 100 + 40 across four pages) [v:12].
- **260 open issues** [v:6].
- `AGENTS.md`, written 2026-08-17, says "~50 open PRs and ~247 open issues"
  [n:AGENTS.md]. The issue figure has drifted a little; the PR figure is off by
  about 290. The prose around it still holds — the count is a breadth metric,
  not a health metric — but any plan quoting "~50" is quoting a stale number.

Open PRs are spikes and stay open by policy [n:AGENTS.md §2]. Nothing below is
a cleanup proposal.

## Recently merged to `main`

Newest first [v:1]:

| PR                                       | Subject                                                             |
| ---------------------------------------- | ------------------------------------------------------------------- |
| #732, #731, #730                         | CBOR: shared data model, immutable Python API, recursive conversion |
| #27                                      | foundational `Num` and `Int`                                        |
| #729, #728                               | HolE: hole/defeq opening, `TY_EXISTS`                               |
| #714, #696                               | Python: SAT order hash, lib hash                                    |
| #713                                     | forsp formalization                                                 |
| #706, #704, #702, #699, #697, #695, #694 | the S-expression stack, including the Lisp evaluator                |
| #693, #692, #691                         | typed free variables, HOL evars, untyped HOL syntax                 |
| #690, #689, #678                         | CBOR wire format, DAG codec correspondences, CBOR data model        |
| #673                                     | HolLN array representation                                          |

The CBOR half of the ladder's L1 is landing steadily. The Rust HOL kernel is
still absent from `main` [v:5].

## The current arena stack

The live design conversation. All open [v:6].

```
main
 ├── #734  hol-single-index          checked HolE surface syntax and CBOR values
 ├── #746  hol-syntax-arena-v0       indexed HolE syntax arena          ← narrowest cut at main
 │    └── #747  hol-syntax-python-v0   Python exposure
 │         └── #735  hol-arena-v0       sparse sequents and relations
 │              ├── #736 → #737 → #738  full surface, literals, init arena  (draft)
 │              └── #744  hol-mvp-arena-v2  simplify sequents to plain contexts
 │                   └── #741 → #743 → #740 → #742  surface, literals, init, Python
 └── #733  logic-bdd                 userspace BDDs
 └── #727  hol-rust                  backend-neutral HOL LCF boundary
```

Reading of the stack: #746 is the syntax-only floor, #735 adds the relation and
sequent layer, #744 is the first simplification pass over that layer. The v2
lineage (#740–#744) and the v0 lineage (#736–#738) are two cuts at the same
question, kept side by side.

## Other open lineages

| Band                                           | Theme                                                                        |
| ---------------------------------------------- | ---------------------------------------------------------------------------- |
| #587–#593, #396–#399, #455                     | two earlier Rust HOL kernel stacks, both draft                               |
| #606, #607, #627, #643, #646, #649, #650, #652 | propositional / SAT / LRAT / CaDiCaL                                         |
| #625, #626, #647, #648, #651, #674             | proposition tables, JSON interchange, REPL demo                              |
| #700, #701, #705, #711                         | Lean signature-parametric HOL, finite semantics, content-addressed bootstrap |
| #675, #672                                     | indexed HOL equivalence classes; linked HOL JSON imports                     |
| #605, #632                                     | `covalence-data-json`                                                        |
| #418, #419, #456, #474, #481                   | SQLite wrapper, flat hash arrays, BLAKE3 constants                           |
| #231–#355                                      | the signed-artifact, REPL-guest and above-LCF-library lineage                |
| #115–#230                                      | older substrate and kernel spikes                                            |

## Issues that bear on the arena design

| Issue           | Subject                                                                            | Bearing                                                                                                                                                                                                                               |
| --------------- | ---------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| #739            | derived E-graph indexes over HolE arenas                                           | states the position that congruence closure is a derived index, not wire format; asks which relations get separate graphs, how context keys into E-class identity, and whether a persistent E-graph is another `(format, class)` pair |
| #745            | one manifest generating Rust/Lean constructor correspondence                       | the tag-table single-source problem                                                                                                                                                                                                   |
| #726            | execution plan: Python/Rust/Lean HolLN kernel with swappable HolE backend          | the surrounding milestone; fixes the LCF boundary and the eager/classified link split                                                                                                                                                 |
| #725            | tracking: in-memory HolE CBOR_TREE prototype                                       | parent of #716–#724                                                                                                                                                                                                                   |
| #715            | total typed imports over HolE                                                      | import typing                                                                                                                                                                                                                         |
| #717, #718      | canonical CBOR_TREE serialization; in-memory CAS with lazy classified imports      |                                                                                                                                                                                                                                       |
| #723, #724      | CBOR macro tags and canonical lowering; cross-language conformance tests           |                                                                                                                                                                                                                                       |
| #721, #722      | Lean formalization of surface syntax, elaboration, link filling, import resolution |                                                                                                                                                                                                                                       |
| #664, #611–#663 | proposition tables and the SAT/LRAT boundary                                       | the other consumer of a fact representation                                                                                                                                                                                           |
| #680–#688       | HOL variants, reusable interfaces, evars, representation equivalences              | binder and representation questions                                                                                                                                                                                                   |
| #707–#710       | bootstrap from `init.json`; nat/int/rat/real                                       | needs polymorphism, so downstream of the signature kernel                                                                                                                                                                             |

## Docs status

- `main` has no `notes/` tree [v:4]. Everything below is on the PR #712 branch
  `claude/hol-kernel-mvp-roadmap-wgzbpb`:
  `AGENTS.md`, `CLAUDE.md`, `notes/vision/ladder.md`,
  `notes/plans/{v0-mvp,2026-08-hol-kernel-mvp,2026-08-17-eight-hour-mvp}.md`,
  `notes/design/{repl-language,repl-core-sketches}.md`, `notes/spikes/README.md`
  [v:4].
- `notes/spikes/` has a README and no spike notes. The retrospectives the README
  asks for have not been written, so the comparison the spikes exist to enable
  cannot be made from the repo alone [n:notes/spikes/README.md].
- This `notes/map/` set is on `claude/arena-design-planning-vuzcdd` and does not
  depend on #712 landing. If #712 lands first, `notes/map/` sits beside
  `notes/vision/` and `notes/plans/` without collision.
- Covalence keeps a tiered notes corpus with an authorship policy and a
  generated TODO index [c:notes/README.md, c:README.md]. Worth copying later;
  out of scope now.

## Suggested next docs

Not written yet, listed so they are not re-derived:

1. `notes/spikes/hol-arena-rust.md` — retrospective on the #734–#747 stack, once
   the design in `03-arena.md` has been used.
2. `notes/spikes/hol-kernel-rust.md` — retrospective on #587–#593 and #396–#399,
   the two earlier kernel stacks. Neither has a note [n:notes/spikes/README.md].
