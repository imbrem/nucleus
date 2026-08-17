# The Nucleus ladder

The long-range design intent, captured so it does not have to be re-derived.
This is the *destination*; the plans under `notes/plans/` are the routes.

Each ladder is ordered by dependency, not by priority. Levels annotated with
their state as of 2026-08-17.

**Reading the annotations:** `✔` landed · `◐` formalized in Lean, absent in Rust ·
`○` neither · `⌛` in an open PR.

---

## Core kernel — the TCB

Everything here is read line by line by a human. Nothing else in the repository is.

| L | Contents | State |
| --- | --- | --- |
| **0** | In-memory syntax trees for types, terms, kinds; typing rules | ◐ `HolLN` complete in Lean incl. soundness + consistency; ⌛ signature-parametric `Nucleus.Hol` in #700→#701; ○ in Rust |
| **0A** | *Optional but default* acceleration for bytestrings + small unsigned integers — everything needed to write parsers, and later for WASM acceleration | ○ |
| **0B** | *Optional* acceleration for bignat, bigint, string, char, list, set, map, indexmap as built-in types. Possibly eventually a table type over SQLite | ○ |
| **1** | Serialization to **CBOR**. Chosen over JSON because it has byte strings natively; JSON + IPLD conventions then serve as a user-facing prettyprint and as an alternative format that can exploit SQLite JSONB — at the cost of some TCB growth | ◐ Lean `Cbor` has the data model, deterministic encoding with a uniqueness theorem, wire parser, DAG and CAS layers |
| **1** | PKI for loading trusted proofs: a set of trusted keys plus derivations in SQLite, stored by hash | ◐ partial — `crates/nucleus/src/snapshot/signing.rs` |
| **2** | Content-addressed links inside CBOR-HOL terms, rules fully formalized | ⌛ spec in #711; Lean `Cbor.Cas` + `Json.IpldStore` exist |
| **3** | SQLite + LRAT logical reasoning over contexts-as-formulas, and over formulas generally; CBOR + JSON ser/de of formulas to and from SQLite | ◐ Lean `Lrat`; ✔ `crates/logic/lrat`; the propositional PR stacks target this |
| **4** | Interconversion between tree format and array format, rules fully formalized | ◐ `HolLN/Array.lean` has the arena, validation, elaboration |
| **5** | E-graph over the array format, rules fully formalized. **This stabilizes kernel v1** — v2 is v1 plus WASM acceleration | ○ |

### Why L3 is shaped the way it is

The SAT solver is **untrusted**: it reasons about contexts, and its output is
checked. SMT then arrives via an untrusted Alethe frontend. That makes the whole
thing a toolkit for *build your own SMT without worrying about soundness*.

The target application is **domain-specific SMT autoresearch**: do SAT fast on
contexts, do whatever theory you want in HOL, and combine the two either
directly or through E-graphs. So the three core data structures across the
ladder are **syntax + derivation trees** (L0–L2), **implication graphs** (L3),
and **E-graphs** (L5).

---

## UI/UX

| L | Contents | State |
| --- | --- | --- |
| **0** | S-expression REPL: prettyprinter and parser, targeting both CBOR and in-memory so round-trips are testable | ◐ Lean `SExpr` has models, parser, printers *with soundness theorems*, Rivest canonical form; ✔ a reader exists in `crates/repl/src/sexpr.rs` |
| **1** | The same REPL used for querying the kernel DB, general SQLite ops, general CAS ops, and as a small programming language with real Lean semantics | ⌛ Lean Lisp evaluator in #706; ✔ the SQLite/CAS half already works |

**Content addressing in the REPL** arrives two ways: *eager*, which needs only
L0 and fetches during parse; and *lazy*, which needs L1 and puts the hash into
the parsed structure for the kernel to fetch on demand.

The REPL is **semi-trusted**. It cannot affect soundness, but what it prints
must be accurate — otherwise it can display something false as proved when the
underlying theorem is something true but different. So it is formalized in Lean
as a Scheme dialect, which also buys macros on the REPL.

S-expressions need their own CBOR format, so libraries can be saved and
content-addressed.

Eventually the same Scheme can be reasoned about *inside* a covalence-scheme
model in the prover as well as outside — which matters most for WASM
compilation. The dialect is oriented towards functional programming: cons cells
are immutable.

Later this becomes the compile/link/run path for WASM components, including
dynamically generated ones and ones with content-addressed components — replacing
the older "magic imports" approach, which accumulates special cases quickly. The
existing CAS-SQLite work becomes a special case of this.

---

## Persistence and distribution

| L | Contents | State |
| --- | --- | --- |
| **0** | Proofs saved as Scheme programs, in CBOR, in the CAS | ○ |
| **1** | Proofs saved as WASM/Scheme amalgamations — the first step toward a Scheme/WASM API | ○ |

---

## System integration

| L | Contents | State |
| --- | --- | --- |
| **0** | OpenTheory import; `init.json` aligned with standard theories, e.g. natural numbers | ○ — **requires polymorphism**, so it is gated on the signature-parametric kernel |
| **1** | Metamath import — `set.mm` support as in covalence. Extended with SQLite metadata tables mapping theorem names to HOL objects and code | ○ |
| **2** | Alethe import — use cvc5 to prove theorems | ○ |
| **3** | Specific bitblaster support — verify simple circuits: adders, multipliers, and so on | ○ |

---

## CAS

| L | Contents | State |
| --- | --- | --- |
| **0** | Ultra-basic in-memory CAS | ✔ `crates/data/cas` |
| **1** | SQLite-backed CAS | ✔ `crates/neutron` (CAS VFS + SQL) |
| **2** | HTTPS CAS; static variant plus S3 support. Basic CAS composition via Scheme, later Scheme+WASM scripts | ◐ `crates/data/cas-http` partial |
| **3** | CAS with transforms and compression — gzip/bzip/zstd and/or delta compression to start. Uses the general composition architecture | ○ |
| **4** | Rosetta CAS: SHA-256 and Git hash ⟷ BLAKE3. Git repositories, Nix stores, and OCI stores as CAS sources | ○ — `crates/lib/hash` already has multiformats |

---

## WASM

| L | Contents |
| --- | --- |
| **0** | Basic Scheme API for linking, instantiating, and running WASM: modules, components, individual functions |
| **1** | Scheme composing components — especially to *build* WASI implementations, e.g. a VFS, eventually the SQLite shell |
| **2** | WIT from Scheme, and Scheme via WIT |
| **3** | WIT WASM-builder API for general dynamic component construction; eventually implementing important component families — hashmaps, btreemaps, indexmaps, SQLite itself |

All `○`. `wit/kernel/kernel.wit` defines the component ABI today.

---

## Applications

| L | Contents |
| --- | --- |
| **0** | The Scheme REPL (see UI/UX) |
| **1** | A VSCode extension for covalence-scheme. As simple as possible to start, but must work in the browser and support the CAS. A good playground for a VFS explorer, and a useful toolkit for WASM and CBOR |
| **2** | An MCP protocol for covalence, so AI agents can build, link, and query proof databases and the CAS |

**The L2 demo** is using AI to solve hard problems by decomposing them and
shelling out to SAT, SMT, E-graph saturation, and tactics — eventually doing SMT
autoresearch.

**AI-backed CAS resolution** is a strange but compelling side demo: hand it a
hash and a pile of link databases, and let it go find where the object lives
when the original link has rotted.

---

## Tactics

| L | Contents |
| --- | --- |
| **0** | Basic tactics: rewriter, simplifier, tauto |
| **1** | E-graph saturation. Probably wants kernel L4; can be done earlier through an interface, which is then a good test of that interface |
| **2** | SMT-integration tactics: omega, ring solver, bitblaster |
| **3** | Scheme tactics, then Scheme/WASM tactics and a WIT tactic API — which also gives a CAS graph of tactics |
| **4** | Induction tactics, in several advanced variants |

---

## Metalogic

| L | Contents |
| --- | --- |
| **0** | Metamath, deep embedding |
| **1** | Internal HOL; prove it equivalent to Metamath's `hol.mm`. Opens up staged-HOL and template-HOL metatheory later |
| **2** | ACL2, deep embedding — should be provable sound |
| **3** | Edinburgh LF / Dedukti |
| **4** | Use the above to do Lean; bonus points for Rocq. May try Lean directly instead. Medium-term goal: **Lean-NDJSON ⟹ "this is provable in Lean"** as a metatheorem |
| **5** | K-framework |

---

## PL metatheory

| L | Contents |
| --- | --- |
| **0** | Minimal LISP and variants, e.g. Sector Lisp |
| **1** | Covalence Scheme without WASM |
| **2** | WASM from SpecTec |
| **3** | Covalence Scheme/WASM |
| **4** | Basic lambda-iter, SSA per the thesis |
| **5** | Basic MLIR, and its equivalence to thesis-SSA |

Much of L4–L5 already exists as formalization in `debruijn-ssa`.

---

## Mathematics

- **Basic analysis** — follow Spivak's *Calculus*, then perhaps *Calculus on
  Manifolds*. Demo: "the MAT157 game", in the spirit of the natural numbers
  game but following the UofT MAT157 course, which derives analysis from the 13
  axioms of the real numbers — starting by showing the Dedekind cuts are a model.
- **Basic algebra** — groups, rings, fields.
- **Advanced linear algebra** — important later for acceleration lore, and
  combinable with analysis for numerical analysis lore.
- **Showpiece theorems** — a few that are both useful and impressive.

---

## How the pieces relate

`nucleus` exposes the high-level API and, eventually, all of the above. The
`covalence` repo then sits on top and implements an extensive standard library,
naturally scoped at *everything you need to develop and prove WASM extensions to
covalence, and to import existing developments from e.g. Lean*.

The long-run shape of a request: drive the nucleus API over MCP to produce a
WASM/Scheme module **plus a proof that loading it yields a conservative
extension** — for instance, to support CTL\* model checking.

Much of this ladder already exists as vibe-coded work in `covalence`, or as
formalization in `debruijn-ssa`. Reaching a level often means *porting and
proving* rather than inventing.
