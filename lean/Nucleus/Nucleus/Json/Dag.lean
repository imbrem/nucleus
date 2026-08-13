import Nucleus.Cbor.Dag
import Nucleus.Json.RfcCanonical

/-!
# DAG-JSON and its common IPLD model

DAG-JSON and DAG-CBOR are codecs for the same IPLD data model. Consequently
their semantic values are definitionally shared; codec conversion is the
identity, while their text/byte representations differ.
-/

namespace Nucleus

/-- A link name has a canonical textual spelling and parser. CIDs can later
instantiate this class with their CIDv0/CIDv1 textual rules. -/
class LinkString (Name : Type) where
  equiv : Name ≃ String

namespace LinkString

variable {Name : Type}

def print [LinkString Name] (name : Name) : String := LinkString.equiv name
def parse [LinkString Name] (text : String) : Name := LinkString.equiv.symm text

@[simp] theorem parse_print [LinkString Name] (name : Name) : parse (print name) = name :=
  LinkString.equiv.left_inv name

@[simp] theorem print_parse [LinkString Name] (text : String) : print (parse text : Name) = text :=
  LinkString.equiv.right_inv text

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
        | .scalar (some (.string text)) => some (LinkString.parse text)
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
