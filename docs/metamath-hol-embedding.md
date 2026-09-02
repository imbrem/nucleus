# Metamath in HOL-omega

This document fixes the boundary between a verified Metamath corpus and the
HOL-omega objects produced from it. The first target is a deep embedding: a HOL
theorem says that a Metamath frame is derivable. It does not silently identify
the frame's conclusion with a native HOL proposition.

Executable evidence for the metalogic is in
`lean/Nucleus/Nucleus/Metamath/Embedding.lean`. The Rust parser and differential
checker remain untrusted userspace in `crates/logic/metamath`.

## Claim and trust boundary

For corpus database `C`, source position `i`, and assertion `a`, replay produces
the closed claim

```text
mm_derivable (prefix C i) (context a) (conclusion a)
```

where `prefix C i` contains only earlier assertions. `mm_derivable e` is encoded
impredicatively as membership of `e` in every expression predicate closed under
active hypotheses, substitution-based assertion application, and the
distinct-variable side condition. `provable_iff_holDerivable` proves this
higher-order formula equivalent to the executable inductive specification. A
`$a` row enters the
embedded database as data; it is not asserted as a native HOL proposition.
Consequently a malformed importer can at worst fail to construct this claim or
construct a claim about different data. Only checked HOL rules create the
theorem.

This adds no kernel rule or parser trust. The existing HOL infinity capability
is the one explicit logical assumption needed by a concrete object-language
encoding of finite symbol strings; it supplies the natural-number/list package.
The Lean executable specification uses inductive data directly and therefore
does not hide this runtime representation dependency.

## Embedded data

The object language represents the following values. Products, finite lists,
options, booleans, and natural numbers are ordinary derived HOL libraries, not
kernel constructors.

| Metamath object      | HOL representation                                                  |
| -------------------- | ------------------------------------------------------------------- |
| symbol or label      | natural number interned by exact source bytes                       |
| expression           | `(typecode, body : list symbol)`                                    |
| substitution         | finite association list `variable -> list symbol`                   |
| floating hypothesis  | `(label, typecode, variable)`                                       |
| essential hypothesis | `(label, expression)`                                               |
| frame                | ordered float list, ordered essential list, unordered `$d` pair set |
| assertion            | label, conclusion, mandatory frame, full active context             |
| database prefix      | source-ordered list of assertions                                   |

Interning is injective over the corpus symbol table and is attested by the
corpus database. The embedded theorem concerns the natural-number codes, so a
bridge from source bytes must also prove or check the table entries it uses.
Names are never kernel identities.

Substitution preserves the expression typecode and splices the image of each
variable into the flat body. This is deliberately string-level Metamath
substitution; no grammar or abstract-syntax interpretation participates in the
deep theorem.

## Rules

`mm_derivable db ctx expression` is closed under exactly three constructors:

1. an active `$f` pushes its one-symbol expression;
2. an active `$e` supplies its expression;
3. an earlier assertion may be instantiated when every substituted mandatory
   hypothesis is derivable and every substituted `$d` pair is distinct and
   declared in the caller's active context.

The assertion application rule consumes the mandatory frame but proof replay
uses the complete active context. In particular, active non-mandatory floats
for dummy variables are legal; earlier floats from closed scopes are not. This
is the same distinction represented by Rust `frame`, `scope_floats`, and
`scope_disjoints`, and by Lean `Assertion.frame` and `Assertion.context`.

Normal and compressed proof encodings are outside the proposition. They are two
untrusted programs for constructing the same derivation. Heap entries in a
compressed proof share theorem construction but add no logical rule.

## Worked slice

The executable slice uses the Metamath-book `demo0` assertion `th1`. Lean builds
the source-ordered database value, evaluates its normal RPN proof, and proves
that successful checking yields `Provable` for `th1` from the strict database
prefix, then converts it to the impredicative `HolDerivable` claim. This
exercises floats, nested assertion applications, essential hypotheses,
substitution, and the source-order condition. The theorem exported by the
embedding module packages that checked derivation with its corpus provenance.

The runtime replay guest should reproduce the same construction through the
checked HOL API. It must not import the Lean proof, trust the Rust verifier, or
assert the result via an axiom capability.

## Shallow bridges

A shallow bridge is a separate derived theorem of the form

```text
mm_derivable db ctx encoded_frame -> native_hol_statement
```

and states all interpretation assumptions in its antecedent. Different source
theories may have different bridges. HOL alpha-equivalence does not erase
Metamath's byte-level variable discipline: the bridge starts only after the
deep theorem has checked string substitution and `$d` obligations. No shallow
bridge is part of this first slice.

## Provenance

The replay output carries a satellite relation with one row per exported deep
theorem:

```sql
CREATE TABLE metamath_theorem_provenance (
  theorem_id       INTEGER NOT NULL,
  corpus_db_hash   BLOB NOT NULL CHECK (length(corpus_db_hash) = 32),
  statement_index  INTEGER NOT NULL CHECK (statement_index >= 0),
  label_bytes      BLOB NOT NULL,
  PRIMARY KEY (theorem_id),
  UNIQUE (corpus_db_hash, statement_index),
  UNIQUE (corpus_db_hash, label_bytes)
);
```

`theorem_id` is only a local navigation handle. Authority remains the checked
theorem row, and provenance is attested because this table and the theorem live
in the same signed whole-image output database. `corpus_db_hash` addresses the
exact signed corpus image; `(statement_index, label_bytes)` must match its
attested statement table before publication. Using both fields catches label
renaming and ordering mistakes without pretending that a label is a content
address.

Mutable search indexes, embeddings, and statistics do not belong in either
signed image. They live in sidecar databases keyed by the signed image hash.

## Correspondence obligations

The replay guest is complete for this design only when executable tests show:

- its symbol-code table agrees with exact corpus bytes;
- its decoded frame, full active context, conclusion, and source prefix agree
  with the signed corpus row;
- normal and compressed replays construct the same embedded claim;
- an out-of-scope `$f`, an out-of-scope `$e`, a forward citation, and a missing
  `$d` condition all fail without publishing provenance;
- an active non-mandatory dummy float succeeds;
- the published provenance row resolves back to the exact corpus assertion;
- replaying the worked slice from the same signed inputs reproduces a checked
  theorem with the same statement, whether or not physical row IDs are stable.

These checks establish correspondence. They do not move parsing, importing,
interning policy, naming, or provenance into the TCB.
