# Map: pointers

Literature and systems worth reading against the design in
[`03-arena.md`](./03-arena.md). Organized by the question each answers.

**Caveat.** These are from memory and were **not checked against sources in this
session**. Titles are reliable, years and venues may be off by one, and any
claim about what a paper proves should be confirmed before it is leaned on.
Everything here is `[x]` under the convention in [`00-index.md`](./00-index.md).

---

## 1. Substitutions as first-class syntax

The λσ line, which is what "a substitution arena" joins.

- **Abadi, Cardelli, Curien, Lévy, "Explicit Substitutions"** (POPL 1990, JFP
  1991). λσ. Substitutions become terms; composition is a syntactic operation.
  The monoid structure is in the calculus rather than in the metatheory.
- **Melliès, "Typed λ-calculi with explicit substitutions may not terminate"**
  (TLCA 1995). The known hazard: λσ with composition breaks strong
  normalization for well-typed terms. Read this before deciding how much
  composition to admit as syntax.
- **Lescanne, λυ** (POPL 1994) and **Kesner, "A theory of explicit substitutions
  with safe and full composition"** (LMCS 2009). The repairs, and what they cost.

The practical reading: an object-level substitution that is _applied_ is safe;
an object-level substitution that is _composed lazily inside terms_ is where the
metatheory gets hard. §11 keeps application in the kernel and composition in
userspace, which lands on the safe side by accident. Worth making deliberate.

## 2. Where the monoid laws come from

- **Dybjer, "Internal Type Theory"** (TYPES 1995) — categories with families.
  Contexts are objects, substitutions are the morphisms, so identity,
  composition and the substitution lemma are the category axioms rather than
  separate theorems. This is the cleanest formal home for "substitutions as
  first-class objects with a monoid structure".
- **Cartmell, "Generalised algebraic theories and contextual categories"**
  (APAL 1986). The older presentation, closer to syntax.
- **Fiore, Plotkin, Turi, "Abstract Syntax and Variable Binding"** (LICS 1999).
  Substitution as a monoid in a presheaf category. The precise version of "terms
  form a monoid under substitution".
- **Altenkirch, Chapman, Uustalu, "Monads need not be endofunctors"** (FoSSaCS
  2010). Syntax with binding as a relative monad; the well-scoped version of the
  same statement.
- **Theory interpretations as morphisms**: **Farmer, Guttman, Thayer, "Little
  Theories"** (CADE 1992), **Rabe and Kohlhase, "A Scalable Module System"**
  (Information and Computation, 2013) for MMT, **Ballarin, "Locales: A Module
  System for Mathematical Theories"** (JAR 2014). MMT is the closest existing
  system to the arena's ambitions: theory graphs, views as first-class
  morphisms, and a URI for every declaration — which is §10's derived addresses
  with a different naming function.
- **Metamath.** The extreme case where substitution _is_ the proof step. Useful
  as a lower bound on how small the machinery can be.

## 3. `eq` as a decreasing forest is a solved form

§5 and §11's "index normalization" are unification, not binding.

- **Baader and Snyder, "Unification Theory"** (Handbook of Automated Reasoning,
  2001). Triangular versus idempotent substitutions and solved forms. A
  union-find in triangular form with strictly decreasing parents is exactly §5's
  invariant, and the idempotent form is what you get by applying it to itself —
  the normalization pass.
- **Martelli and Montanari, "An Efficient Unification Algorithm"** (TOPLAS
  1982). The solved-form transformation.
- **Nelson and Oppen, "Fast decision procedures based on congruence closure"**
  (JACM 1980), and **Nieuwenhuis and Oliveras, "Proof-Producing Congruence
  Closure"** (RTA 2005). The second matters for LCF: congruence closure that
  emits a proof is what lets an untrusted e-graph feed a trusted kernel.

## 4. E-graphs

- **Willsey et al., "egg: Fast and Extensible Equality Saturation"** (POPL 2021).
  Deferred rebuilding, and e-class ids as a union-find.
- **Zhang et al., "Relational E-matching"** (POPL 2022) and **"Better Together:
  Unifying Datalog and Equality Saturation"** (PLDI 2023, egglog). The
  e-graph-as-database view, which is the one to steal given the SQLite substrate
  already in the tree.

The representative-per-class reading in §11 is standard here: canonicalization
is a section of the quotient map, and "which representative" is a policy, not a
semantics.

## 5. Naming open terms

- **Sekar, Ramakrishnan, Voronkov, "Term Indexing"** (Handbook of Automated
  Reasoning, 2001). Discrimination trees and substitution trees key open terms by
  variable-normalized form: rename free variables in first-occurrence order.
  That is §11's first option, with decades of practice behind it.
- **Filliâtre and Conchon, "Type-Safe Modular Hash-Consing"** (ML Workshop 2006).
  Maximal sharing, and why identity-by-construction is easier than
  identity-by-comparison.
- **Harper, Honsell, Plotkin, "A Framework for Defining Logics"** (JACM 1993).
  Adequacy — the theorem that an encoding denotes what it is meant to. This is
  principle 5's grounding argument stated as a proof obligation, and it is the
  right word to use for it.

## 6. Hygiene, which is what §9 is

- **Flatt, "Binding as Sets of Scopes"** (POPL 2016). Identifiers carry scope
  sets; resolution is a subset test. §9's per-segment variable windows are a
  degenerate, interval-shaped version of the same idea, and the payoff is the
  same: name coincidence becomes intentional rather than accidental. Doubly
  relevant given the Scheme metalanguage on the ladder.
- **Kohlbecker, Friedman, Felleisen, Duba, "Hygienic Macro Expansion"** (LFP 1986) and **Dybvig, Hieb, Bruggeman, "Syntactic Abstraction in Scheme"**
  (LSC 1992). The original problem and the renaming-based answer.
- **Gabbay and Pitts, "A New Approach to Abstract Syntax with Variable Binding"**
  (FAC 2002) and **Pitts, "Nominal Sets"** (2013). Freshness as a first-class
  relation `a # x`, which is `fvs` as a fact rather than a computation, and the
  formal setting where that is the primitive.

## 7. Derived and situated names

- **BLAKE3's `derive_key` mode**, and **HKDF's info label** (RFC 5869). Both are
  `at(base, label)` with domain separation, for the same reason §10 needs it.
- **Unison.** Definitions addressed by hash, names as metadata. The closest
  system to "an integer ID that refers to exactly one thing".
- **Nix content-addressed derivations** and **Bazel's action cache**. Hash of a
  deterministic computation to its result, which is the generalized CAS in the
  original dump. Read them for the failure modes: non-determinism and cache
  poisoning.
- **IPLD CIDs.** `(multicodec, multihash)`, already in `crates/lib/hash`.

## 8. Not read, but probably should be

- Autexier, Hutter, Mossakowski on **development graphs** — theory morphisms
  managed as a graph with change propagation, which is what a DAG of arenas with
  claims becomes once anything is edited.
- Isabelle's **`interpretation`/`sublocale`** implementation, for what goes wrong
  at scale with theory morphisms.
- The **λ-calculus with names and levels** implementations in NbE — for the
  fresh-name-as-counter discipline §8 assumes.
