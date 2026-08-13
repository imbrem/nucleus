import Nucleus.Cbor.Dag
import Nucleus.Json.RfcCanonical

/-!
# DAG-JSON and its common IPLD model

DAG-JSON and DAG-CBOR are codecs for the same IPLD data model. Consequently
their semantic values are definitionally shared; codec conversion is the
identity, while their text/byte representations differ.
-/

namespace Nucleus

/-- A link name has canonical injective textual and binary spellings, with
partial decoders. CIDs can later instantiate this class with CIDv0/CIDv1 text
and raw binary CID rules; arbitrary strings and bytes need not be valid links. -/
class LinkString (Name : Type) where
  toString : Name ↪ String
  ofString? : String → Option Name
  ofString_toString : ∀ name, ofString? (toString name) = some name
  toBytes : Name ↪ Bytes
  ofBytes? : Bytes → Option Name
  ofBytes_toBytes : ∀ name, ofBytes? (toBytes name) = some name

namespace LinkString

variable {Name : Type}

def print [LinkString Name] (name : Name) : String := LinkString.toString name
def parse? [LinkString Name] (text : String) : Option Name := LinkString.ofString? text
def bytes [LinkString Name] (name : Name) : Bytes := LinkString.toBytes name
def parseBytes? [LinkString Name] (value : Bytes) : Option Name := LinkString.ofBytes? value

@[simp] theorem parse_print [LinkString Name] (name : Name) :
    parse? (print name) = some name := LinkString.ofString_toString name

@[simp] theorem parseBytes_bytes [LinkString Name] (name : Name) :
    parseBytes? (bytes name) = some name := LinkString.ofBytes_toBytes name

end LinkString

/-- Semantic DAG-JSON. Bytes and links are semantic leaves; only its RFC JSON
serialization uses reserved slash objects. -/
abbrev DagJson (Name : Type) := DagCbor Name

/-- DAG-CBOR and DAG-JSON are losslessly interconvertible because both are
representations of the same IPLD value, not competing tree models. -/
def dagCborEquivDagJson (Name : Type) : DagCbor Name ≃ DagJson Name := Equiv.refl _

namespace DagJson

variable {Name : Type}

/-- RFC DAG-JSON spelling of a link: `{ "/": "name" }`. -/
def linkText [DecidableEq String] [LinkString Name] (name : Name) : RfcJson :=
  .map {"/"} fun _ => .scalar (.string (LinkString.print name))

/-- Recognize exactly a singleton slash object containing a string. This
captures the link portion of DAG-JSON's reserved namespace. -/
def parseLinkText? [DecidableEq String] [LinkString Name] : RfcJson → Option Name
  | .map keys values =>
      if h : keys = {"/"} then
        match values ⟨"/", h.symm ▸ Finset.mem_singleton_self "/"⟩ with
        | .scalar (some (.string text)) => LinkString.parse? text
        | _ => none
      else none
  | _ => none

@[simp] theorem parseLinkText_linkText [DecidableEq String] [LinkString Name]
    (name : Name) : parseLinkText? (linkText name) = some name := by
  simp [parseLinkText?, linkText, RfcJsonScalar.string, LinkString.parse_print]

/-- Canonical compact RFC JSON text for a link object. The general canonical
printer supplies key sorting and whitespace removal. -/
noncomputable def canonicalLinkText? [DecidableEq String] [LinkString Name]
    (name : Name) : Option String := RfcJson.canonical? (linkText name)

end DagJson

end Nucleus
