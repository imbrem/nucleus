import Nucleus.Cbor.General

/-!
# CBOR structural profiles

The complete CBOR grammar is refined by orthogonal capabilities rather than
copied into many nearly identical inductives. `KeysSatisfy` constrains map
keys recursively and `TagNumbersSatisfy` constrains tags. Their conjunctions
describe the requested string-key, integer-label, arbitrary-key, and tagged
variants while full `Cbor` remains the total final model.
-/

namespace Nucleus

namespace CborSyn

/-- Every map key in a tree satisfies `accept`; values are checked recursively
because they may contain more maps. -/
def KeysSatisfy (accept : Cbor → Prop) : {i : CborIx} → CborSyn i → Prop
  | _, .primitive _ => True
  | _, .array items => items.KeysSatisfy accept
  | _, .map entries => entries.KeysSatisfy accept
  | _, .tag _ content => content.KeysSatisfy accept
  | _, .arrayNil => True
  | _, .arrayCons head tail => head.KeysSatisfy accept ∧ tail.KeysSatisfy accept
  | _, .mapNil => True
  | _, .mapCons key value tail =>
      accept key ∧ key.KeysSatisfy accept ∧ value.KeysSatisfy accept ∧
        tail.KeysSatisfy accept

/-- Every tag in a tree satisfies `accept`. -/
def TagNumbersSatisfy (accept : UInt64 → Prop) : {i : CborIx} → CborSyn i → Prop
  | _, .primitive _ => True
  | _, .array items => items.TagNumbersSatisfy accept
  | _, .map entries => entries.TagNumbersSatisfy accept
  | _, .tag number content => accept number ∧ content.TagNumbersSatisfy accept
  | _, .arrayNil => True
  | _, .arrayCons head tail =>
      head.TagNumbersSatisfy accept ∧ tail.TagNumbersSatisfy accept
  | _, .mapNil => True
  | _, .mapCons key value tail =>
      key.TagNumbersSatisfy accept ∧ value.TagNumbersSatisfy accept ∧
        tail.TagNumbersSatisfy accept

/-- No semantic tags occur. -/
abbrev TagFree (value : Cbor) := value.TagNumbersSatisfy fun _ => False

/-- A key is a text string. -/
def IsTextKey : Cbor → Prop
  | .primitive (.text _) => True
  | _ => False

/-- A key is a text string or CBOR integer. -/
def IsLabelKey : Cbor → Prop
  | .primitive (.text _) | .primitive (.integer _) => True
  | _ => False

/-- The tag-free string-key profile underlying `StringKeyCbor`. -/
def IsStringKeyProfile (value : Cbor) : Prop :=
  value.KeysSatisfy IsTextKey ∧ value.TagFree

/-- The tag-free string-or-integer-key profile underlying `LabelledCbor`. -/
def IsLabelledProfile (value : Cbor) : Prop :=
  value.KeysSatisfy IsLabelKey ∧ value.TagFree

/-- Tagged CBOR restricted to string keys. -/
def IsTaggedStringKeyProfile (value : Cbor) : Prop :=
  value.KeysSatisfy IsTextKey

/-- Tagged CBOR restricted to text or integer labels. This is a useful host
for COSE structures; COSE schemas impose additional constraints. -/
def IsCoseHostProfile (value : Cbor) : Prop :=
  value.KeysSatisfy IsLabelKey

/-- Tag-free CBOR with arbitrary values as keys. -/
def IsUntaggedProfile (value : Cbor) : Prop := value.TagFree

/-- Tags plus arbitrary keys is exactly unrestricted CBOR. -/
abbrev TaggedArbitraryKeyCbor := Cbor

end CborSyn

end Nucleus
