import Nucleus.Json.Rfc

/-!
# Integer IPLD-style JSON

The base format is RFC-shaped JSON restricted to decoded strings, Booleans and
signed 64-bit integers.  Floating point is intentionally absent.  A second form
recognizes the conventional singleton object `{ "/": "..." }` as a link.
-/

namespace Nucleus

/-- Non-null scalar values in the integer-only IPLD profile. -/
inductive IpldJsonAtom where
  | bool (value : Bool)
  | string (decoded : String)
  | int (value : Int64)
  deriving DecidableEq, Repr

/-- `none` is JSON null, not missing information. -/
abbrev IpldJsonScalar := Option IpldJsonAtom

/-- Integer-only JSON before recognizing links. -/
abbrev IpldJson := Json IpldJsonScalar

/-- Leaves of linked IPLD data. -/
inductive IpldLinkedScalar (Name : Type) where
  | value (value : IpldJsonScalar)
  | link (name : Name)
  deriving DecidableEq, Repr

/-- Integer-only linked data, whose links have been recognized structurally. -/
abbrev IpldLinkedJson (Name : Type) := Json (IpldLinkedScalar Name)

namespace IpldJson

private def int64Min : Int := -9223372036854775808
private def int64Max : Int := 9223372036854775807

/-- Parse an RFC number lexeme as a signed 64-bit integer.  Decimal fractions,
exponents, malformed lexemes, and out-of-range integers are rejected. -/
def parseInt64? (literal : String) : Option Int64 := do
  let value ← literal.toInt?
  if int64Min ≤ value ∧ value ≤ int64Max then
    some (Int64.ofInt value)
  else
    none

/-- Convert an RFC scalar to the integer-only profile. Failure means invalid for
this profile, rather than JSON null. -/
def ofRfcScalar? : RfcJsonScalar → Option IpldJsonScalar
  | none => some none
  | some (.bool b) => some (some (.bool b))
  | some (.string s) => some (some (.string s))
  | some (.number literal) =>
      match parseInt64? literal with
      | some i => some (some (.int i))
      | none => none

/-- Convert an RFC tree to integer-only JSON, rejecting any non-integral or
out-of-range number. -/
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def ofRfc? : RfcJson → Option IpldJson
  | .scalar s => .scalar <$> ofRfcScalar? s
  | .list n elems =>
      if h : ∀ i, ∃ child, ofRfc? (elems i) = some child then
        some (.list n fun i => Classical.choose (h i))
      else none
  | .map keys vals =>
      if h : ∀ k, ∃ child, ofRfc? (vals k) = some child then
        some (.map keys fun k => Classical.choose (h k))
      else none

@[simp] theorem ofRfc?_scalar (s : RfcJsonScalar) :
    ofRfc? (.scalar s) = (.scalar <$> ofRfcScalar? s) := rfl

@[simp] theorem ofRfc?_null : ofRfc? (.scalar none) = some (.scalar none) := rfl

/-- Forget the integer restriction, choosing ordinary decimal notation for ints. -/
def toRfc : IpldJson → RfcJson := Json.mapScalar fun
  | none => none
  | some (.bool b) => some (.bool b)
  | some (.string s) => some (.string s)
  | some (.int i) => some (.number (toString i.toInt))

@[simp] theorem toRfc_null : toRfc (.scalar none) = .scalar none := rfl

end IpldJson

namespace IpldLinkedJson

variable {Name : Type}

/-- A JSON object is link syntax exactly when it is a singleton `/` object whose
value is a string. -/
def slashName? [DecidableEq String] : IpldJson → Option String
  | .map keys vals =>
      if hkeys : keys = {"/"} then
        match vals ⟨"/", hkeys.symm ▸ Finset.mem_singleton_self "/"⟩ with
        | .scalar (some (.string name)) => some name
        | _ => none
      else none
  | _ => none

/-- Recognize slash-object links recursively. `parseName` validates and decodes
the textual link payload. Invalid link-looking objects are left as ordinary maps. -/
def ofIpld (parseName : String → Option Name) : IpldJson → IpldLinkedJson Name
  | .scalar s => .scalar (.value s)
  | .list n elems => .list n fun i => ofIpld parseName (elems i)
  | j@(.map keys vals) =>
      match slashName? j >>= parseName with
      | some name => .scalar (.link name)
      | none => .map keys fun k => ofIpld parseName (vals k)

@[simp] theorem ofIpld_scalar (parseName : String → Option Name) (s : IpldJsonScalar) :
    ofIpld parseName (.scalar s) = .scalar (.value s) := rfl

theorem ofIpld_eq_link_of_slashName {parseName : String → Option Name}
    {j : IpldJson} {text : String} {name : Name}
    (hj : slashName? j = some text) (hn : parseName text = some name) :
    ofIpld parseName j = .scalar (.link name) := by
  cases j with
  | scalar s => simp [slashName?] at hj
  | list n elems => simp [slashName?] at hj
  | map keys vals => simp only [ofIpld]; rw [hj]; simp [hn]

/-- Parse RFC JSON into linked integer IPLD data. Failure is precisely failure
of the integer-only conversion; slash recognition itself is total. -/
noncomputable def ofRfc? (parseName : String → Option Name) (j : RfcJson) :
    Option (IpldLinkedJson Name) :=
  ofIpld parseName <$> IpldJson.ofRfc? j

end IpldLinkedJson

end Nucleus
