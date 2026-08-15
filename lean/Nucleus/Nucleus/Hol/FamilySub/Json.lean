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

universe u v w

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

def TyVar.index {types : List Kind} {kind : Kind} : TyVar types kind → Nat
  | .zero => 0
  | .succ v => TyVar.index v + 1

namespace Object

private def string {Sig : Signature.{u}} (value : String) : Tree Sig :=
  .scalar (.string value)

private def nat {Sig : Signature.{u}} (value : Nat) : Tree Sig :=
  .scalar (.nat value)

private def bool {Sig : Signature.{u}} (value : Bool) : Tree Sig :=
  .scalar (.bool value)

private def kind {Sig : Signature.{u}} (value : Kind) : Tree Sig :=
  .scalar (.kind value)

private def field {Sig : Signature.{u}} (key : String) (value : Tree Sig)
    (tail : RawSyn String (Scalar Sig) .obj) : RawSyn String (Scalar Sig) .obj :=
  .objCons key value tail

private def tagged {Sig : Signature.{u}} (tag : Tag)
    (fields : RawSyn String (Scalar Sig) .obj := .objNil) : Tree Sig :=
  .map (.objCons "tag" (string tag.name) fields)

/-- Named-field encoding of the active type-family HOL syntax.  The positional
arena codec below uses the same tag vocabulary. -/
def encode {Sig : Signature.{u}} : {types : List Kind} → {sort : HolSort} →
    {depth : Nat} → Expr Sig types sort depth → Tree Sig
  | _, _, _, .boolTy => tagged .tyBool
  | _, _, _, .arr domain codomain =>
      tagged .tyArr (field "domain" (encode domain)
        (field "codomain" (encode codomain) .objNil))
  | _, .kind _, _, @Expr.tyApp _ _ domain codomain function argument =>
      tagged .tyApp (field "domainKind" (kind domain)
        (field "codomainKind" (kind codomain)
          (field "function" (encode function) (field "argument" (encode argument) .objNil))))
  | _, .kind _, _, @Expr.tyLam _ _ domain codomain body =>
      tagged .tyLam (field "domainKind" (kind domain)
        (field "codomainKind" (kind codomain) (field "body" (encode body) .objNil)))
  | _, .kind _, _, @Expr.tyBv _ _ familyKind v =>
      tagged .tyBv (field "kind" (kind familyKind)
        (field "index" (nat (TyVar.index v)) .objNil))
  | _, _, _, .sub carrier predicate =>
      tagged .tySub (field "carrier" (encode carrier)
        (field "predicate" (encode predicate) .objNil))
  | _, .kind _, _, @Expr.primFam _ _ familyKind symbol =>
      tagged .sigFam (field "symbol" (.scalar (.famSymbol (familyKind := familyKind) symbol))
        .objNil)
  | _, .tm, _, .primTm symbol =>
      tagged .sigTm (field "symbol" (.scalar (.tmSymbol symbol)) .objNil)
  | _, _, _, .bv index => tagged .tmBv (field "index" (nat index) .objNil)
  | _, _, _, .fv name type =>
      tagged .tmFv (field "name" (nat name) (field "type" (encode type) .objNil))
  | _, _, _, .app function argument =>
      tagged .tmApp (field "function" (encode function)
        (field "argument" (encode argument) .objNil))
  | _, _, _, .lam domain body =>
      tagged .tmLam (field "domain" (encode domain) (field "body" (encode body) .objNil))
  | _, _, _, .bool value => tagged .tmBool (field "value" (bool value) .objNil)
  | _, _, _, .eq type left right =>
      tagged .tmEq (field "type" (encode type)
        (field "left" (encode left) (field "right" (encode right) .objNil)))
  | _, _, _, .eps type predicate =>
      tagged .tmEps (field "type" (encode type)
        (field "predicate" (encode predicate) .objNil))
  | _, _, _, .abs carrier predicate value =>
      tagged .tmAbs (field "carrier" (encode carrier)
        (field "predicate" (encode predicate) (field "value" (encode value) .objNil)))
  | _, _, _, .rep carrier predicate value =>
      tagged .tmRep (field "carrier" (encode carrier)
        (field "predicate" (encode predicate) (field "value" (encode value) .objNil)))

end Object

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

/-- Apply a representation change uniformly to every child reference. -/
def Row.map {Sig : Signature.{u}} {R : Type v} {S : Type w} (f : R → S) :
    Row Sig R → Row Sig S
  | .tyBool => .tyBool
  | .tyArr domain codomain => .tyArr (f domain) (f codomain)
  | .tyApp domain codomain function argument =>
      .tyApp domain codomain (f function) (f argument)
  | .tyLam domain codomain body => .tyLam domain codomain (f body)
  | .tyBv kind index => .tyBv kind index
  | .tySub carrier predicate => .tySub (f carrier) (f predicate)
  | .sigFam symbol => .sigFam symbol
  | .tmBv index => .tmBv index
  | .tmFv name type => .tmFv name (f type)
  | .tmApp function argument => .tmApp (f function) (f argument)
  | .tmLam domain body => .tmLam (f domain) (f body)
  | .tmBool value => .tmBool value
  | .tmEq type left right => .tmEq (f type) (f left) (f right)
  | .tmEps type predicate => .tmEps (f type) (f predicate)
  | .tmAbs carrier predicate value => .tmAbs (f carrier) (f predicate) (f value)
  | .tmRep carrier predicate value => .tmRep (f carrier) (f predicate) (f value)
  | .sigTm symbol => .sigTm symbol

/-- Child references in their canonical constructor order. -/
def Row.children {Sig : Signature.{u}} {Ref : Type v} : Row Sig Ref → List Ref
  | .tyBool | .tyBv _ _ | .sigFam _ | .tmBv _ | .tmBool _ | .sigTm _ => []
  | .tyLam _ _ body => [body]
  | .tmFv _ type => [type]
  | .tyArr left right | .tySub left right | .tmApp left right |
      .tmLam left right | .tmEps left right => [left, right]
  | .tyApp _ _ function argument => [function, argument]
  | .tmEq type left right | .tmAbs type left right | .tmRep type left right =>
      [type, left, right]

@[simp] theorem Row.children_map {Sig : Signature.{u}} {R : Type v} {S : Type w}
    (f : R → S) (row : Row Sig R) :
    (row.map f).children = row.children.map f := by
  cases row <;> rfl

abbrev RawArena (Sig : Signature.{u}) := Array (Row.{u, 0} Sig Nat)

/-- A backward reference lifted to the signature's universe. -/
abbrev BackRef (n : Nat) := ULift.{u} (Fin n)

/-- A validated arena whose rows can only refer to strict prefixes. -/
inductive Arena (Sig : Signature.{u}) : Nat → Type u where
  | nil : Arena Sig 0
  | snoc {n : Nat} (prior : Arena Sig n) (row : Row Sig (BackRef.{u} n)) :
      Arena Sig (n + 1)

/-- Existential package for a dynamically sized validated arena. -/
structure SomeArena (Sig : Signature.{u}) where
  size : Nat
  arena : Arena Sig size

private def validateRow {Sig : Signature.{u}} (n : Nat) :
    Row.{u, 0} Sig Nat → Option (Row Sig (BackRef.{u} n))
  | .tyBool => some .tyBool
  | .tyArr domain codomain => return .tyArr (← ref domain) (← ref codomain)
  | .tyApp domain codomain function argument =>
      return .tyApp domain codomain (← ref function) (← ref argument)
  | .tyLam domain codomain body => return .tyLam domain codomain (← ref body)
  | .tyBv kind index => some (.tyBv kind index)
  | .tySub carrier predicate => return .tySub (← ref carrier) (← ref predicate)
  | .sigFam symbol => some (.sigFam symbol)
  | .tmBv index => some (.tmBv index)
  | .tmFv name type => return .tmFv name (← ref type)
  | .tmApp function argument => return .tmApp (← ref function) (← ref argument)
  | .tmLam domain body => return .tmLam (← ref domain) (← ref body)
  | .tmBool value => some (.tmBool value)
  | .tmEq type left right => return .tmEq (← ref type) (← ref left) (← ref right)
  | .tmEps type predicate => return .tmEps (← ref type) (← ref predicate)
  | .tmAbs carrier predicate value =>
      return .tmAbs (← ref carrier) (← ref predicate) (← ref value)
  | .tmRep carrier predicate value =>
      return .tmRep (← ref carrier) (← ref predicate) (← ref value)
  | .sigTm symbol => some (.sigTm symbol)
where
  ref (child : Nat) : Option (BackRef.{u} n) :=
    if h : child < n then some ⟨⟨child, h⟩⟩ else none

private def validateList {Sig : Signature.{u}} :
    (rows : List (Row.{u, 0} Sig Nat)) → {n : Nat} → Arena Sig n →
      Option (SomeArena Sig)
  | [], n, prior => some ⟨n, prior⟩
  | row :: rows, _, prior => do
      let checked ← validateRow _ row
      validateList rows (.snoc prior checked)

/-- Validate every raw reference in one left-to-right pass. This rejects
forward references and cycles before any sort or scope elaboration occurs. -/
def RawArena.validate {Sig : Signature.{u}} (rows : RawArena Sig) :
    Option (SomeArena Sig) :=
  validateList rows.toList .nil

private abbrev EmptySignature : Signature := fun _ => Empty

example : (RawArena.validate (Sig := EmptySignature)
    #[.tyBool, .tmBool true, .tmEq 0 1 1]).isSome = true := by
  decide

example : (RawArena.validate (Sig := EmptySignature) #[.tyArr 0 0]).isSome = false := by
  decide

example : (RawArena.validate (Sig := EmptySignature)
    #[.tyBool, .tmApp 2 0, .tmBool true]).isSome = false := by
  decide

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
