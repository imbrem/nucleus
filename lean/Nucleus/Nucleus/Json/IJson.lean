import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Nucleus.Json.Equiv
import Nucleus.Json.Validate

/-!
# I-JSON (RFC 7493) as JSON over an I-JSON scalar type

I-JSON ("Internet JSON", [RFC 7493](https://www.rfc-editor.org/rfc/rfc7493))
is the interoperable profile of RFC 8259 JSON.  Because the core trees are
parametric over scalars, the profile is obtained by instantiation:
`IJson := Json IJsonScalar`, where `IJsonScalar` fixes null, Booleans,
binary64-representable numbers, and strings.

How each normative requirement of RFC 7493 is accounted for:

- **UTF-8 encoding (§2.1, MUST)** — a byte-level concern that arises with the
  parser (#530); the tree layers here start above bytes.
- **No surrogates in strings (§2.1, MUST)** — holds by construction: Lean
  `Char`s are Unicode scalar values and can never be surrogates
  (`char_not_surrogate`).
- **No noncharacters in strings (§2.1, MUST)** — captured by the
  `IJson.Interoperable` predicate over whole values, since it constrains
  object member *names* as well as string scalars, and member names live in
  the tree structure rather than the scalar type.  (Enforcing it inside a
  string type would still not cover keys without the `KeyedJson`
  generalization documented in `Nucleus.Json`.)
- **Numbers within IEEE 754 binary64 (§2.2, SHOULD)** — enforced by
  construction: `IJsonNumber` carries exactly the rationals representable as
  finite binary64 values.  The RFC's interoperable integer range
  `[-(2^53 - 1), 2^53 - 1]` is covered by `binary64Representable_intCast`,
  and larger values are RECOMMENDED to travel as string scalars, which
  `IJsonScalar.string` supports unchanged.
- **No duplicate member names (§2.3, MUST)** — holds by construction in
  `IJson` and `OrderedIJson`; raw trees (`RawIJson`) can still express
  duplicates, and `RawSyn.validate` rejects them explicitly.
- **Member ordering carries no meaning (§2.3)** — the extensional form
  ignores ordering by construction.
- **Top-level SHOULD be an object or array (§4.1)** — the `IJson.IsMessage`
  predicate.

The equivalences and the validator specialize definitionally:
`iJsonEquivOrdered : IJson ≃ OrderedIJson`.
-/

namespace Nucleus

/-! ## Binary64-representable numbers -/

/-- A rational is exactly representable as a finite IEEE 754 binary64 value:
`q = m * 2 ^ e` with `|m| < 2 ^ 53` and `-1074 ≤ e ≤ 971`.  This is the value
set behind RFC 7493 §2.2's interoperable numbers; no floating-point
arithmetic is involved. -/
def Binary64Representable (q : ℚ) : Prop :=
  ∃ (m e : ℤ), m.natAbs < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ q = (m : ℚ) * 2 ^ e

/-- An I-JSON number: a rational exactly representable in binary64. -/
def IJsonNumber : Type := {q : ℚ // Binary64Representable q}

namespace IJsonNumber

instance : DecidableEq IJsonNumber :=
  inferInstanceAs (DecidableEq {q : ℚ // Binary64Representable q})

/-- The exact rational value of an I-JSON number. -/
def toRat (n : IJsonNumber) : ℚ := n.1

/-- I-JSON numbers are their exact rational values. -/
theorem toRat_injective : Function.Injective toRat :=
  Subtype.coe_injective

end IJsonNumber

/-- Integers of magnitude below `2 ^ 53` are binary64-representable; this is
RFC 7493 §2.2's interoperable integer range `[-(2^53 - 1), 2^53 - 1]`
(`9007199254740991 = 2^53 - 1`). -/
theorem binary64Representable_intCast {n : ℤ} (h : n.natAbs < 2 ^ 53) :
    Binary64Representable (n : ℚ) :=
  ⟨n, 0, h, by norm_num, by norm_num, by norm_num⟩

/-- Binary64-representable numbers are closed under negation. -/
theorem Binary64Representable.neg {q : ℚ} (h : Binary64Representable q) :
    Binary64Representable (-q) := by
  obtain ⟨m, e, hm, he₁, he₂, rfl⟩ := h
  exact ⟨-m, e, by simpa using hm, he₁, he₂, by push_cast; ring⟩

/-- The upper end of the interoperable integer range, exactly. -/
example : ((2 : ℤ) ^ 53 - 1) = 9007199254740991 := by norm_num

/-! ## The I-JSON scalar type and profile -/

/-- Scalars of the I-JSON profile: null, Booleans, binary64-representable
numbers, and strings.  Object member names are `String` in the tree layer and
are unaffected by this choice. -/
inductive IJsonScalar : Type where
  /-- The JSON `null` literal. -/
  | null
  /-- A JSON Boolean. -/
  | bool (value : Bool)
  /-- A number within binary64 magnitude and precision (RFC 7493 §2.2). -/
  | number (value : IJsonNumber)
  /-- A decoded Unicode string.  Surrogates are unrepresentable; freedom from
  noncharacters is tracked by `IJson.Interoperable`. -/
  | string (value : String)
  deriving DecidableEq

/-- Extensional I-JSON values: duplicate member names are unrepresentable
(RFC 7493 §2.3) and member ordering carries no meaning. -/
abbrev IJson := Json IJsonScalar

/-- Raw I-JSON syntax: member order preserved, duplicates expressible;
`RawSyn.validate` applies the profile's duplicate rejection. -/
abbrev RawIJson := RawJson IJsonScalar

/-- The canonical sorted representative of an extensional I-JSON value. -/
abbrev OrderedIJson := OrderedJson IJsonScalar

/-- I-JSON values and their sorted representatives are equivalent, by
specializing `jsonEquivOrdered`. -/
def iJsonEquivOrdered : IJson ≃ OrderedIJson := jsonEquivOrdered IJsonScalar

/-! ## String obligations -/

/-- RFC 7493 §2.1's surrogate exclusion holds by construction: every Lean
`Char` is a Unicode scalar value, so its code point is never in the surrogate
range `U+D800`–`U+DFFF`. -/
theorem char_not_surrogate (c : Char) : c.toNat < 0xD800 ∨ 0xDFFF < c.toNat := by
  rcases c.valid with h | ⟨h₁, _⟩
  · exact Or.inl h
  · exact Or.inr h₁

/-- Unicode noncharacters: `U+FDD0`–`U+FDEF` and the last two code points of
every plane. -/
def isNoncharacter (c : Char) : Prop :=
  (0xFDD0 ≤ c.toNat ∧ c.toNat ≤ 0xFDEF)
    ∨ c.toNat % 0x10000 = 0xFFFE ∨ c.toNat % 0x10000 = 0xFFFF

instance : DecidablePred isNoncharacter := fun c => by
  unfold isNoncharacter
  infer_instance

/-- A string containing no Unicode noncharacters (RFC 7493 §2.1). -/
def NoncharacterFree (s : String) : Prop :=
  ∀ c ∈ s.toList, ¬ isNoncharacter c

instance : DecidablePred NoncharacterFree := fun s => by
  unfold NoncharacterFree
  infer_instance

/-- The string obligations of RFC 7493 §2.1 that the types do not enforce:
every string scalar and every object member name is free of noncharacters.
Stated over whole values because member names live in the tree, not in the
scalar type. -/
def IJson.Interoperable : IJson → Prop
  | .scalar (.string s) => NoncharacterFree s
  | .scalar _ => True
  | .list _n elems => ∀ i, IJson.Interoperable (elems i)
  | .map keys vals =>
      (∀ k ∈ keys, NoncharacterFree k) ∧ ∀ k, IJson.Interoperable (vals k)

/-- RFC 7493 §4.1: top-level values SHOULD be objects or arrays. -/
def IJson.IsMessage : IJson → Prop
  | .scalar _ => False
  | .list _ _ => True
  | .map _ _ => True

end Nucleus
