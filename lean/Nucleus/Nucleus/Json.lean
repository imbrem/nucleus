import Nucleus.Json.Raw
import Nucleus.Json.Extensional
import Nucleus.Json.Ordered
import Nucleus.Json.Validate
import Nucleus.Json.Equiv
import Nucleus.Json.Alternatives
import Nucleus.Json.IJson

/-!
# Scalar-parametric JSON trees

Core JSON inductives parametric over **scalar values only**, with object keys
fixed to `String` (issue #541; the parent RFC-8259 formalization effort is
issue #530).  Three related forms:

1. `RawJson Scalar` — raw ordered syntax.  Objects are ordered member
   sequences that may contain duplicate names, exactly as RFC 8259 object
   syntax allows; equality observes order and duplicates.  This is what a
   parser produces.  It is the value sort of the three-sorted indexed family
   `RawSyn` (values, array tails, object tails), so every operation recurses
   structurally; the tail sorts are isomorphic to lists
   (`RawSyn.arrEquivList`, `RawSyn.objEquivList`).
2. `Json Scalar` — the extensional value.  Arrays are finite indexed families
   `Fin n → Json Scalar`; objects are value families over a `Finset String`.
   Object equality ignores member ordering by construction, and duplicate keys
   are unrepresentable.
3. `OrderedJson Scalar` — sorted duplicate-free syntax, the canonical data
   representative of an extensional value: `jsonEquivOrdered : Json Scalar ≃
   OrderedJson Scalar`.

Conversions: `RawJson.validate` (explicit duplicate-key rejection — building
`Json` never silently chooses first-wins or last-wins semantics),
`Json.toOrdered`, `OrderedJson.toJson`, `OrderedJson.toRaw`, and the
supporting `Σ n, Fin n → A ≃ List A` (`sigmaFinEquivList`).

## Why scalars remain generic

Scalar genericity isolates the genuinely unsettled parts of JSON semantics:
null/Boolean representation, decoded Unicode strings versus preserved raw
lexemes, number lexemes versus exact `(sign, coefficient, exponent)` values,
rational/integer views, profile restrictions, and extension atoms.  A strict
RFC specialization can later fix these, e.g.

```
inductive JsonScalar
  | null
  | bool (value : Bool)
  | number (value : JsonNumber)
  | string (value : String)

abbrev RfcJson := Json JsonScalar
```

keeping `JsonNumber` explicit so #530 can settle exact numeral semantics
without touching arrays and maps.  Object keys being `String` is independent
of how string *values* are represented inside `Scalar`.

The first such specialization is the I-JSON profile (RFC 7493):
`IJson := Json IJsonScalar` with binary64-representable numbers; see
`Nucleus.Json.IJson`.

## Later key/container generalization

If a struct/schema use case ever needs non-string field positions, the
documented route is a generic

```
KeyedJson Scalar Key
```

(or a free tree over a container/polynomial signature whose shapes describe
arrays, maps, structs, tuples, and list-only trees), introduced *behind* the
current surface:

```
abbrev Json Scalar := KeyedJson Scalar String
```

Nothing in the present API leaks the key type, so the migration preserves the
`Json Scalar` surface: constructors, `size`/`depth`/`scalars`, `get?`,
`mapScalar`, and the equivalences specialize verbatim.  The generic type is
deliberately **not** exposed now — the initial parser, schema, Serde, and HOL
APIs should not carry a second parameter.

## Equality and hashing

- `RawJson` equality observes member order and duplicate keys.
- `Json` object equality ignores member ordering by construction.
- `OrderedJson` is one chosen data representative of an extensional value,
  useful for proofs, comparison, pretty-printing, and optional deduplication.
- Encoded bytes may preserve raw syntax or use the ordered representative;
  content hashes always identify the exact chosen bytes.  The isomorphisms
  here are data-level only: equal extensional JSON values (or equal HOL
  denotations) are **not** required to have equal byte encodings or content
  hashes, and nothing in this hierarchy is a project-wide content-addressing
  requirement.

See `Nucleus.Json.Alternatives` for the prototype comparison of ordered-form
designs (indexed grammar versus proof-carrying sorted lists versus the chosen
subtype).
-/

namespace Nucleus

universe u

variable {Scalar : Type u}

/-- The canonical raw representative validates back to its extensional value:
round-tripping through raw syntax loses nothing. -/
theorem Json.validate_toRaw (j : Json Scalar) : j.toRaw.validate = .ok j := by
  rw [RawSyn.validate_ok_of_wellFormed j.toRaw_sortedKeys.wellFormed, Json.toJson_toRaw]

/-- Ordered trees validate to their extensional value. -/
theorem OrderedJson.validate_toRaw (o : OrderedJson Scalar) :
    o.toRaw.validate = .ok o.toJson :=
  RawSyn.validate_ok_of_wellFormed o.2.wellFormed

end Nucleus
