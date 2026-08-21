/-!
# Amber rows

`Amber` is the first named representation of Ethane.  Representation names are
short material names: they identify a complete embedding without making its
current storage choices part of the Ethane dialect's name.

A forest row has three observable parts.  Its tag identifies the operation,
its children are forest edges, and its extra elements are non-recursive data.
Only the tag and children belong to the forest shape.  Extra elements remain
available to codecs and relation rows such as `has_ty` and `eq`.
-/

namespace Nucleus.Hol.Ethane.Amber

universe u v w x
set_option relaxedAutoImplicit true

/-- Interface implemented by datatypes that can be stored as forest rows.

The output parameters make the projections unambiguous once the concrete row
type is known. -/
class Row (R : Type u) (Tag : outParam (Type v))
    (Ref : outParam (Type w)) (Extra : outParam (Type x)) where
  tag : R → Tag
  children : R → List Ref
  extra : R → List Extra

namespace Row

/-- The part of a row which affects forest topology. -/
structure Shape (Tag : Type v) (Ref : Type w) where
  tag : Tag
  children : List Ref
  deriving DecidableEq

/-- A canonical, fully exposed row representation. -/
structure View (Tag : Type v) (Ref : Type w) (Extra : Type x) where
  tag : Tag
  children : List Ref
  extra : List Extra
  deriving DecidableEq

instance : Row (View Tag Ref Extra) Tag Ref Extra where
  tag := View.tag
  children := View.children
  extra := View.extra

/-- Project any row implementation to the canonical representation. -/
def view [Row R Tag Ref Extra] (row : R) : View Tag Ref Extra :=
  ⟨Row.tag row, Row.children row, Row.extra row⟩

/-- Forget the non-recursive data fields of a row. -/
def shape [Row R Tag Ref Extra] (row : R) : Shape Tag Ref :=
  ⟨Row.tag row, Row.children row⟩

/-- Rows have the same forest meaning when their tags and edges agree.
Their extra data may still encode different relations or scalar payloads. -/
def SameShape [Row R Tag Ref Extra] (left right : R) : Prop :=
  shape left = shape right

/-- Change every recursive reference in a canonical row. -/
def View.mapChildren (f : Ref → Ref') (row : View Tag Ref Extra) :
    View Tag Ref' Extra :=
  ⟨row.tag, row.children.map f, row.extra⟩

/-- Change every non-recursive field in a canonical row. -/
def View.mapExtra (f : Extra → Extra') (row : View Tag Ref Extra) :
    View Tag Ref Extra' :=
  ⟨row.tag, row.children, row.extra.map f⟩

@[simp] theorem view_tag [Row R Tag Ref Extra] (row : R) :
    (view row).tag = Row.tag row := rfl

@[simp] theorem view_children [Row R Tag Ref Extra] (row : R) :
    (view row).children = Row.children row := rfl

@[simp] theorem view_extra [Row R Tag Ref Extra] (row : R) :
    (view row).extra = Row.extra row := rfl

@[simp] theorem shape_view (row : View Tag Ref Extra) :
    shape row = ⟨row.tag, row.children⟩ := rfl

@[simp] theorem mapChildren_tag (f : Ref → Ref') (row : View Tag Ref Extra) :
    (row.mapChildren f).tag = row.tag := rfl

@[simp] theorem mapChildren_children (f : Ref → Ref')
    (row : View Tag Ref Extra) :
    (row.mapChildren f).children = row.children.map f := rfl

@[simp] theorem mapChildren_extra (f : Ref → Ref') (row : View Tag Ref Extra) :
    (row.mapChildren f).extra = row.extra := rfl

end Row

end Nucleus.Hol.Ethane.Amber
