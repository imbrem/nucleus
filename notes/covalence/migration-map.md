---
title: Covalence migration map
status: research
issues: [503, 511, 551, 552, 553, 561, 562, 570]
reviewed: 2026-08-11
source-revision: 01225078f58260d3527f05bd3aa62ffa521e0eb6
summary: Source-by-source decision table — preserve, adapt, defer, research, or reject.
---

The decision table asked for by
[#570](https://github.com/imbrem/nucleus/issues/570). Read
[the Covalence context](README.md) for the trust architecture and the
claim-labelling convention, and [kernel lessons](kernel-lessons.md) for the
reasoning behind the kernel rows.

All sources are pinned to
[`0122507`](https://github.com/imbrem/covalence/commit/01225078f58260d3527f05bd3aa62ffa521e0eb6).
Actions mean:

| Action       | Meaning                                                                     |
| ------------ | --------------------------------------------------------------------------- |
| **preserve** | Keep the invariant. The reasoning transfers whatever the representation is. |
| **adapt**    | The idea is right, the mechanism needs rebuilding for a JSON-first kernel.  |
| **defer**    | Real value, wrong time. Revisit when a concrete requirement forces it.      |
| **research** | Not understood well enough to decide. Named so it is not decided by drift.  |
| **reject**   | Do not bring across.                                                        |

## Representation and syntax

| Concern                    | Covalence source                                                                                                                            | Observed lesson                                                                                      | Nucleus action | Tracking                                             |
| -------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------- | -------------- | ---------------------------------------------------- |
| Locally nameless terms     | [`term/term.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/core/src/term/term.rs) | De Bruijn for bound, named-and-typed for free. Matches the Lean reference closely enough to compare. | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553) |
| Anonymous binders          | same                                                                                                                                        | No display label on `Abs` ⇒ structural equality **is** α-equivalence ⇒ rules use `==`.               | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553) |
| Free variables carry types | same (`Var`)                                                                                                                                | Makes typing context-free, which is what makes any type caching sound.                               | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553) |
| Two logical primitives     | [`lib.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/core/src/lib.rs)             | Only `=` and `ε`; `T`/`F` are literals; every connective is a defined constant.                      | **adapt**      | [#553](https://github.com/imbrem/nucleus/issues/553) |
| Cached per-node typing     | `TermInfo` in `term/term.rs`                                                                                                                | Cache only for closed nodes. A cache that can be wrong is an axiom — see hazard 2.                   | **adapt**      | [#561](https://github.com/imbrem/nucleus/issues/561) |
| Bloom + fingerprint        | same                                                                                                                                        | One-sided guarantees: a miss degrades to slow, never to wrong.                                       | **defer**      | [#561](https://github.com/imbrem/nucleus/issues/561) |
| Kernel literal leaves      | `TermKind::{Nat,Int,SmallInt,Blob,Bool}`                                                                                                    | _[in-flight]_ Covalence is removing them; they pull computation into the kernel's commitments.       | **reject**     | [#553](https://github.com/imbrem/nucleus/issues/553) |
| Intrinsic scoping in types | Lean `Nucleus.HolLN`, versus Covalence's untyped index                                                                                      | The Lean reference is stronger. Whether Rust should mirror it is genuinely open.                     | **research**   | [#561](https://github.com/imbrem/nucleus/issues/561) |

## Theorems, rules, and trust

| Concern                        | Covalence source                                                                                                                                | Observed lesson                                                                                                       | Nucleus action | Tracking                                                                                                   |
| ------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------- | -------------- | ---------------------------------------------------------------------------------------------------------- |
| Opaque theorem values          | [`thm/mod.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/core/src/thm/mod.rs)         | Only rule methods construct it. Everything else follows from this.                                                    | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| Opaque hypothesis context      | [`ctx.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/core/src/ctx.rs)                 | Set equality, order documented as non-meaningful.                                                                     | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| Rules derive conclusions       | [`thm/rules.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/core/src/thm/rules.rs)     | No rule takes a conclusion. Soundness reduces to which rule ids are admitted.                                         | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| One well-typedness floor       | `check_sequent` / `seq` in `thm/rules.rs`                                                                                                       | Every rule and every landing constructor calls the same nine lines.                                                   | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| Generated rule manifest        | `docs/deps/core-manifest.txt`, the `core_rules!` macro                                                                                          | Catalogue, `admits`, and manifest emitted from one list "so they can never drift".                                    | **adapt**      | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| Measured TCB with a ratchet    | `docs/deps/{tcb.json,tcb-audit.json,purge-ratchet.json}`                                                                                        | The trusted surface has a generated number and a CI gate that stops it growing.                                       | **adapt**      | [#564](https://github.com/imbrem/nucleus/issues/564)                                                       |
| Trust tiers in the type        | [`seam.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/core/src/seam.rs)               | `Thm<CoreLang>` vs `Thm<CoreEval>` — the type parameter declares which axioms were used. Elegant, and heavy.          | **defer**      | [#503](https://github.com/imbrem/nucleus/issues/503)                                                       |
| Symbolic conclusions           | `Thm::from_pure_sym`, `notes/vibes/literal-endgame-design.md`                                                                                   | Avoids materializing large numerals — and carries a documented "WIDENED TRUST OBLIGATION" because it cannot re-floor. | **reject**     | —                                                                                                          |
| Freshness allocated in-rule    | [`thm/typedef.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/core/src/thm/typedef.rs) | Identity minted inside `decide`, never an input, "so an adversary cannot force a collision".                          | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| `Arc` pointers as identity     | `Def` in `term/term.rs`; `FreshId` in `term/fresh.rs`                                                                                           | Right for one process, unserialisable, and it collides under content hashing. See hazard 4.                           | **reject**     | [#551](https://github.com/imbrem/nucleus/issues/551), [#552](https://github.com/imbrem/nucleus/issues/552) |
| Checked untrusted construction | [`term/cons.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/core/src/term/cons.rs)     | Sealed trusted trait, public untrusted mirror, `Checked` adapter restoring the guarantee by verification.             | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| Hash-consing as policy         | same                                                                                                                                            | Safe to make pluggable _because_ equality is structural — establish that property first.                              | **adapt**      | [#561](https://github.com/imbrem/nucleus/issues/561)                                                       |

## Computation and evaluation

| Concern                         | Covalence source                                                                                                                             | Observed lesson                                                                                              | Nucleus action          | Tracking                                             |
| ------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------ | ----------------------- | ---------------------------------------------------- |
| Computation certificates        | [`eval/src/certs.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/eval/src/certs.rs) | Native computation as gated rules that refuse rather than guess: "a refusal, never a wrong equation".        | **defer**               | [#553](https://github.com/imbrem/nucleus/issues/553) |
| Certificate/definition coupling | `notes/vibes/kernel/kernel-design.md` §9; `eval/tests/audit_reduce.rs`                                                                       | **The confirmed soundness bug.** `nat.mod n 0` derived `⊢ 0 = 5`. Two paths to one fact need a differential. | **preserve** (the test) | [#553](https://github.com/imbrem/nucleus/issues/553) |
| `defs/` derived catalogue       | `core/src/defs/`, 22 modules                                                                                                                 | Semi-trusted by construction, and the source of the coupling above. 165 coupling points at the eval tier.    | **reject**              | —                                                    |
| Definition-vs-native units      | `eval/tests/pure_hol_units.rs`                                                                                                               | Derive the same equation from definitions and from the native path, assert conclusion equality.              | **adapt**               | [#553](https://github.com/imbrem/nucleus/issues/553) |
| Evaluation tiers generally      | `covalence-hol-eval`                                                                                                                         | Doubles TCB lines (6,951 → 13,281) for computation Nucleus does not yet need.                                | **defer**               | [#503](https://github.com/imbrem/nucleus/issues/503) |

## Serialization, imports, and replay

| Concern                        | Covalence source                                                                                                                                                | Observed lesson                                                                                      | Nucleus action | Tracking                                                                                                   |
| ------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------- | -------------- | ---------------------------------------------------------------------------------------------------------- |
| Theorems serialize one-way     | [`init/src/sexp.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/init/src/sexp.rs)                      | Theorems print but do not parse. Importers reconstruct.                                              | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| Construct, don't trust         | [`metalogic/mm_replay.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/init/src/metalogic/mm_replay.rs) | A verified external proof is a hint; every step is re-derived. Land in derivability, not denotation. | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| Host selection isn't authority | [`api/src/wasm.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/api/src/wasm.rs)                        | "Host-side selection of a rule is not proof authority." One sentence worth copying.                  | **preserve**   | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| Content hashing                | [`init/src/hash.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/init/src/hash.rs)                      | Domain-separated BLAKE3, outside the TCB, tags explicitly unstable and saying so in the source.      | **adapt**      | [#551](https://github.com/imbrem/nucleus/issues/551), [#552](https://github.com/imbrem/nucleus/issues/552) |
| Import graph and ordering      | [`init/src/project.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/init/src/project.rs)                | Edges read from the sources, graph built, topologically ordered, each unit checked. Nothing trusted. | **adapt**      | [#553](https://github.com/imbrem/nucleus/issues/553)                                                       |
| Hand-wired dependency order    | the `library_env` match arms `project.rs` replaces                                                                                                              | The predecessor: order implicit in the Rust call graph and `LazyLock` forcing. It needed replacing.  | **reject**     | —                                                                                                          |
| Lazy namespaces and resolvers  | [`script/env.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/kernel/hol/init/src/script/env.rs)                   | Persistent maps, uniformly lazy bindings, one namespace absorbing catalogue churn.                   | **defer**      | —                                                                                                          |

## Interfaces, storage, and the rest

| Concern                      | Covalence source                                                                                                                              | Observed lesson                                                                                     | Nucleus action | Tracking                                             |
| ---------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------- | -------------- | ---------------------------------------------------- |
| Store WIT interface          | [`wit/store.wit`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/lib/wasm/core/wit/store.wit)       | Store as a resource with pure reads; `none` collapses absent/failure so richer errors can layer on. | **adapt**      | —                                                    |
| Kernel WIT interface         | [`wit/kernel.wit`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/lib/wasm/core/wit/kernel.wit)     | Modules, components, containers as validated resources; proving instantiates a nested scope.        | **research**   | —                                                    |
| Git-compatible objects       | `crates/vcs/object/`                                                                                                                          | Git tree/commit encodings alongside a native `Dir`, with a hash mapping between them.               | **defer**      | [#552](https://github.com/imbrem/nucleus/issues/552) |
| Proof-format bridge traits   | `crates/proof/{alethe,egglog}`                                                                                                                | One trait per external calculus, a driver walking the DAG in dependency order.                      | **defer**      | —                                                    |
| E-graphs                     | [`proof/egglog/src/lib.rs`](https://github.com/imbrem/covalence/blob/01225078f58260d3527f05bd3aa62ffa521e0eb6/crates/proof/egglog/src/lib.rs) | Marked "⚠️ Status: skeleton" and currently disabled. There is no working precedent here.            | **research**   | [#511](https://github.com/imbrem/nucleus/issues/511) |
| Script/theory/model language | `init/src/script/`                                                                                                                            | Signatures, theories, models, tactics, a surface compiler. Enormous, and downstream of everything.  | **defer**      | —                                                    |
| `docs/` vs `notes/` split    | `docs/README.md`, `notes/README.md`                                                                                                           | "Everything in here must be _true_" versus explicitly aspirational. Already adopted by #569.        | **preserve**   | [#569](https://github.com/imbrem/nucleus/issues/569) |
| Note metadata database       | `bun run notes`, SQLite graph over note front matter                                                                                          | Justified at Covalence's corpus size. Nucleus has three notes.                                      | **defer**      | [#569](https://github.com/imbrem/nucleus/issues/569) |

## Open questions

Named so they are decided deliberately rather than by whichever code lands
first.

1. **What replaces `Arc` identity?** Nucleus is content-addressed, so defined
   constants and typedef freshness need identity that is data. A hash of the
   defining equation is the obvious candidate and has an obvious problem: two
   definitions with the same body would collide, which is exactly what
   Covalence's `define` promises cannot happen. Resolve before writing `define`.
2. **Does the Rust kernel mirror the Lean development's intrinsic scoping?**
   Covalence answers no by construction. The Lean reference answers yes. The
   correspondence argument is easier if they agree and the Rust is harder to
   write if they do.
3. **Where does computation live, if anywhere?** Covalence's answer — a separate
   tier with its own admitted rules — is good, and it doubled the TCB. Nucleus
   can defer the question entirely for now, but not silently.
4. **What is the JSON analogue of the sequent floor?** Deserialization produces
   syntax, not theorems, and the floor is what stops that syntax becoming a
   fact. The single-entrance property is the thing to design for.
