import Nucleus.Hol.FamilySub
import Nucleus.Json.Raw

/-!
# JSON wire syntax for type-family HOL

This is the current storage vocabulary for `FamilySub.Expr`.  Unlike the
legacy `HolLN.Json` format, extension symbols are explicit sorted primitives
and type-family abstraction and bound type variables are first-class.

The compact representation is an arena of positional rows.  Child positions
are natural-number backward references; checking that property and elaborating
the rows into intrinsically scoped syntax are deliberately separate steps.
-/

namespace Nucleus.Hol.FamilySub.Json

universe u v

/-- Scalar leaves used by the generic logical codec.  A concrete RFC JSON
profile supplies textual encodings for kinds and signature symbols. -/
inductive Scalar (Sig : Signature.{u}) where
  | string (value : String)
  | nat (value : Nat)
  | bool (value : Bool)
  | kind (value : Kind)
  | famSymbol {familyKind : Kind} (value : Sig (.kind familyKind))
  | tmSymbol (value : Sig .tm)

abbrev Tree (Sig : Signature.{u}) := RawJson (Scalar Sig)

/-- Stable core and extension row tags. -/
inductive Tag where
  | tyBool | tyArr | tyApp | tyLam | tyBv | tySub | sigFam
  | tmBv | tmFv | tmApp | tmLam | tmBool | tmEq | tmEps | tmAbs | tmRep | sigTm
  deriving DecidableEq, Repr

def Tag.name : Tag → String
  | .tyBool => "ty.bool"
  | .tyArr => "ty.arr"
  | .tyApp => "ty.app"
  | .tyLam => "ty.lam"
  | .tyBv => "ty.bv"
  | .tySub => "ty.sub"
  | .sigFam => "sig.fam"
  | .tmBv => "tm.bv"
  | .tmFv => "tm.fv"
  | .tmApp => "tm.app"
  | .tmLam => "tm.lam"
  | .tmBool => "tm.bool"
  | .tmEq => "tm.eq"
  | .tmEps => "tm.eps"
  | .tmAbs => "tm.abs"
  | .tmRep => "tm.rep"
  | .sigTm => "sig.tm"

theorem Tag.name_injective : Function.Injective Tag.name := by
  intro left right equality
  cases left <;> cases right <;> simp_all [Tag.name]

/-- One compact arena row.  `Ref` selects untrusted indices or checked
backward references. -/
inductive Row (Sig : Signature.{u}) (Ref : Type v) : Type (max u v) where
  | tyBool
  | tyArr (domain codomain : Ref)
  | tyApp (domain codomain : Kind) (function argument : Ref)
  | tyLam (domain codomain : Kind) (body : Ref)
  | tyBv (kind : Kind) (index : Nat)
  | tySub (carrier predicate : Ref)
  | sigFam {kind : Kind} (symbol : Sig (.kind kind))
  | tmBv (index : Nat)
  | tmFv (name : Nat) (type : Ref)
  | tmApp (function argument : Ref)
  | tmLam (domain body : Ref)
  | tmBool (value : Bool)
  | tmEq (type left right : Ref)
  | tmEps (type predicate : Ref)
  | tmAbs (carrier predicate value : Ref)
  | tmRep (carrier predicate value : Ref)
  | sigTm (symbol : Sig .tm)

abbrev RawArena (Sig : Signature.{u}) := Array (Row Sig Nat)

private def string {Sig : Signature.{u}} (value : String) : Tree Sig :=
  .scalar (.string value)

private def nat {Sig : Signature.{u}} (value : Nat) : Tree Sig :=
  .scalar (.nat value)

private def bool {Sig : Signature.{u}} (value : Bool) : Tree Sig :=
  .scalar (.bool value)

private def kind {Sig : Signature.{u}} (value : Kind) : Tree Sig :=
  .scalar (.kind value)

private def array {Sig : Signature.{u}} (values : List (Tree Sig)) : Tree Sig :=
  .list (RawSyn.ofList values)

/-- Canonical positional encoding of one arena row. -/
def encodeRow {Sig : Signature.{u}} : Row Sig Nat → Tree Sig
  | .tyBool => array [string Tag.tyBool.name]
  | .tyArr domain codomain => array [string Tag.tyArr.name, nat domain, nat codomain]
  | .tyApp domain codomain function argument =>
      array [string Tag.tyApp.name, kind domain, kind codomain, nat function, nat argument]
  | .tyLam domain codomain body =>
      array [string Tag.tyLam.name, kind domain, kind codomain, nat body]
  | .tyBv familyKind index => array [string Tag.tyBv.name, kind familyKind, nat index]
  | .tySub carrier predicate => array [string Tag.tySub.name, nat carrier, nat predicate]
  | @Row.sigFam _ _ familyKind symbol =>
      array [string Tag.sigFam.name, .scalar (.famSymbol (familyKind := familyKind) symbol)]
  | .tmBv index => array [string Tag.tmBv.name, nat index]
  | .tmFv name type => array [string Tag.tmFv.name, nat name, nat type]
  | .tmApp function argument => array [string Tag.tmApp.name, nat function, nat argument]
  | .tmLam domain body => array [string Tag.tmLam.name, nat domain, nat body]
  | .tmBool value => array [string Tag.tmBool.name, bool value]
  | .tmEq type left right => array [string Tag.tmEq.name, nat type, nat left, nat right]
  | .tmEps type predicate => array [string Tag.tmEps.name, nat type, nat predicate]
  | .tmAbs carrier predicate value =>
      array [string Tag.tmAbs.name, nat carrier, nat predicate, nat value]
  | .tmRep carrier predicate value =>
      array [string Tag.tmRep.name, nat carrier, nat predicate, nat value]
  | .sigTm symbol => array [string Tag.sigTm.name, .scalar (.tmSymbol symbol)]

/-- Parse exactly the canonical positional form of one arena row. -/
def decodeRow {Sig : Signature.{u}} : Tree Sig → Option (Row Sig Nat)
  | .list values =>
      match values.toList with
      | [.scalar (.string "ty.bool")] => some .tyBool
      | [.scalar (.string "ty.arr"), .scalar (.nat domain), .scalar (.nat codomain)] =>
          some (.tyArr domain codomain)
      | [.scalar (.string "ty.app"), .scalar (.kind domain), .scalar (.kind codomain),
          .scalar (.nat function), .scalar (.nat argument)] =>
          some (.tyApp domain codomain function argument)
      | [.scalar (.string "ty.lam"), .scalar (.kind domain), .scalar (.kind codomain),
          .scalar (.nat body)] => some (.tyLam domain codomain body)
      | [.scalar (.string "ty.bv"), .scalar (.kind familyKind), .scalar (.nat index)] =>
          some (.tyBv familyKind index)
      | [.scalar (.string "ty.sub"), .scalar (.nat carrier), .scalar (.nat predicate)] =>
          some (.tySub carrier predicate)
      | [.scalar (.string "sig.fam"), .scalar (.famSymbol symbol)] => some (.sigFam symbol)
      | [.scalar (.string "tm.bv"), .scalar (.nat index)] => some (.tmBv index)
      | [.scalar (.string "tm.fv"), .scalar (.nat name), .scalar (.nat type)] =>
          some (.tmFv name type)
      | [.scalar (.string "tm.app"), .scalar (.nat function), .scalar (.nat argument)] =>
          some (.tmApp function argument)
      | [.scalar (.string "tm.lam"), .scalar (.nat domain), .scalar (.nat body)] =>
          some (.tmLam domain body)
      | [.scalar (.string "tm.bool"), .scalar (.bool value)] => some (.tmBool value)
      | [.scalar (.string "tm.eq"), .scalar (.nat type), .scalar (.nat left),
          .scalar (.nat right)] => some (.tmEq type left right)
      | [.scalar (.string "tm.eps"), .scalar (.nat type), .scalar (.nat predicate)] =>
          some (.tmEps type predicate)
      | [.scalar (.string "tm.abs"), .scalar (.nat carrier), .scalar (.nat predicate),
          .scalar (.nat value)] => some (.tmAbs carrier predicate value)
      | [.scalar (.string "tm.rep"), .scalar (.nat carrier), .scalar (.nat predicate),
          .scalar (.nat value)] => some (.tmRep carrier predicate value)
      | [.scalar (.string "sig.tm"), .scalar (.tmSymbol symbol)] => some (.sigTm symbol)
      | _ => none
  | _ => none

private def decodeRows {Sig : Signature.{u}} : List (Tree Sig) → Option (List (Row Sig Nat))
  | [] => some []
  | value :: values => return (← decodeRow value) :: (← decodeRows values)

/-- Encode a complete compact arena as an outer JSON array. -/
def encodeArena {Sig : Signature.{u}} (rows : RawArena Sig) : Tree Sig :=
  array (rows.toList.map encodeRow)

/-- Parse row shapes without yet trusting their references or sorts. -/
def decodeArena {Sig : Signature.{u}} : Tree Sig → Option (RawArena Sig)
  | .list values => return (← decodeRows values.toList).toArray
  | _ => none

end Nucleus.Hol.FamilySub.Json
