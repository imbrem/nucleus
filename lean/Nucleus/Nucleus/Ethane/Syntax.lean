import Nucleus.HolE.Named.Unsorted

/-!
# Ethane syntax

Ethane is the named, model-only HOL flavor.  Its core syntax has type choice
through `model`, but no primitive subtype, abstraction, or representation
constructors.  Subtypes are intended to be library definitions built from a
single subtype-package existence axiom.

`Syn` is the serialization-facing syntax: it admits sort errors.  `Expr` carries
only the syntactic sort.  Typing and proof certificates live in later layers.
-/

namespace Nucleus.Ethane

universe u

abbrev Kind := Nucleus.HolE.Kind
abbrev HolSort := Nucleus.HolE.HolSort
abbrev Signature := Nucleus.HolE.Signature

/-- Completely unsorted, fully named Ethane syntax. -/
inductive Syn (Sig : Signature.{u}) (Name : Type := Nat) : Type (max u 1) where
  | boolTy
  | arr (domain codomain : Syn Sig Name)
  | tyApp (domain codomain : Kind) (function argument : Syn Sig Name)
  | tyLam (domain codomain : Kind) (name : Name) (body : Syn Sig Name)
  | tyFv (name : Name) (kind : Kind)
  | tyExists (name : Name) (predicate : Syn Sig Name)
  | model (name : Name) (predicate : Syn Sig Name)
  | primFam (kind : Kind) (symbol : Sig (.kind kind))
  | primTm (symbol : Sig .tm)
  | tmFv (name : Name) (type : Syn Sig Name)
  | app (function argument : Syn Sig Name)
  | lam (name : Name) (domain body : Syn Sig Name)
  | bool (value : Bool)
  | eq (type left right : Syn Sig Name)
  | eps (type predicate : Syn Sig Name)

/-- Named Ethane syntax indexed by its syntactic sort. -/
inductive Expr (Sig : Signature.{u}) (Name : Type := Nat) : HolSort → Type (max u 1) where
  | boolTy : Expr Sig Name (.kind .star)
  | arr (domain codomain : Expr Sig Name (.kind .star)) : Expr Sig Name (.kind .star)
  | tyApp {domain codomain : Kind}
      (function : Expr Sig Name (.kind (.arr domain codomain)))
      (argument : Expr Sig Name (.kind domain)) : Expr Sig Name (.kind codomain)
  | tyLam {domain codomain : Kind} (name : Name)
      (body : Expr Sig Name (.kind codomain)) :
      Expr Sig Name (.kind (.arr domain codomain))
  | tyFv (name : Name) (kind : Kind) : Expr Sig Name (.kind kind)
  | tyExists (name : Name) (predicate : Expr Sig Name .tm) : Expr Sig Name .tm
  | model (name : Name) (predicate : Expr Sig Name .tm) : Expr Sig Name (.kind .star)
  | primFam {kind : Kind} (symbol : Sig (.kind kind)) : Expr Sig Name (.kind kind)
  | primTm (symbol : Sig .tm) : Expr Sig Name .tm
  | tmFv (name : Name) (type : Expr Sig Name (.kind .star)) : Expr Sig Name .tm
  | app (function argument : Expr Sig Name .tm) : Expr Sig Name .tm
  | lam (name : Name) (domain : Expr Sig Name (.kind .star))
      (body : Expr Sig Name .tm) : Expr Sig Name .tm
  | bool (value : Bool) : Expr Sig Name .tm
  | eq (type : Expr Sig Name (.kind .star))
      (left right : Expr Sig Name .tm) : Expr Sig Name .tm
  | eps (type : Expr Sig Name (.kind .star))
      (predicate : Expr Sig Name .tm) : Expr Sig Name .tm

abbrev Fam (Sig : Signature) (kind : Kind) (Name : Type := Nat) :=
  Expr Sig Name (.kind kind)

abbrev Ty (Sig : Signature) (Name : Type := Nat) := Fam Sig .star Name

abbrev Tm (Sig : Signature) (Name : Type := Nat) := Expr Sig Name .tm

/-- A sorted expression carrying its sort as data. -/
structure AnyExpr (Sig : Signature.{u}) (Name : Type := Nat) where
  sort : HolSort
  expression : Expr Sig Name sort

namespace Syn

/-- The result sort suggested by the root constructor. -/
def rootSort : Syn Sig Name → HolSort
  | .boolTy | .arr .. | .model .. => .kind .star
  | .tyApp _ codomain .. => .kind codomain
  | .tyLam domain codomain .. => .kind (.arr domain codomain)
  | .tyFv _ kind | .primFam kind _ => .kind kind
  | .tyExists .. | .primTm .. | .tmFv .. | .app .. | .lam .. | .bool .. |
      .eq .. | .eps .. => .tm

/-- Check an unsorted expression against a caller-supplied syntactic sort. -/
def check : (sort : HolSort) → Syn Sig Name → Option (Expr Sig Name sort)
  | .kind expected, .boolTy =>
      if equality : expected = .star then equality ▸ some .boolTy else none
  | .kind expected, .arr domain codomain =>
      if equality : expected = .star then by
        subst expected
        exact do return .arr (← check (.kind .star) domain) (← check (.kind .star) codomain)
      else none
  | .kind expected, .tyApp domain codomain function argument =>
      if equality : expected = codomain then by
        subst expected
        exact do
          return .tyApp (← check (.kind (.arr domain codomain)) function)
            (← check (.kind domain) argument)
      else none
  | .kind expected, .tyLam domain codomain name body =>
      if equality : expected = .arr domain codomain then by
        subst expected
        exact do return .tyLam name (← check (.kind codomain) body)
      else none
  | .kind expected, .tyFv name actual =>
      if equality : expected = actual then equality ▸ some (.tyFv name actual) else none
  | .kind expected, .model name predicate =>
      if equality : expected = .star then by
        subst expected
        exact do return .model name (← check .tm predicate)
      else none
  | .kind expected, .primFam actual symbol =>
      if equality : expected = actual then equality ▸ some (.primFam symbol) else none
  | .tm, .tyExists name predicate => return .tyExists name (← check .tm predicate)
  | .tm, .primTm symbol => some (.primTm symbol)
  | .tm, .tmFv name type => return .tmFv name (← check (.kind .star) type)
  | .tm, .app function argument => return .app (← check .tm function) (← check .tm argument)
  | .tm, .lam name domain body =>
      return .lam name (← check (.kind .star) domain) (← check .tm body)
  | .tm, .bool value => some (.bool value)
  | .tm, .eq type left right =>
      return .eq (← check (.kind .star) type) (← check .tm left) (← check .tm right)
  | .tm, .eps type predicate =>
      return .eps (← check (.kind .star) type) (← check .tm predicate)
  | _, _ => none

/-- Infer the root sort and validate all child sorts. -/
def infer (expression : Syn Sig Name) : Option (AnyExpr Sig Name) := do
  let sort := rootSort expression
  return ⟨sort, ← check sort expression⟩

/-- Embed Ethane syntax into the existing unsorted named HolE syntax. -/
def toHolE : Syn Sig Name → Nucleus.HolE.Named.Unsorted.Expr Sig Name
  | .boolTy => .boolTy
  | .arr A B => .arr A.toHolE B.toHolE
  | .tyApp domain codomain F A => .tyApp domain codomain F.toHolE A.toHolE
  | .tyLam domain codomain name body => .tyLam domain codomain name body.toHolE
  | .tyFv name kind => .tyFv name kind
  | .tyExists name predicate => .tyExists name predicate.toHolE
  | .model name predicate => .model name predicate.toHolE
  | .primFam kind symbol => .primFam kind symbol
  | .primTm symbol => .primTm symbol
  | .tmFv name A => .tmFv name A.toHolE
  | .app function argument => .app function.toHolE argument.toHolE
  | .lam name A body => .lam name A.toHolE body.toHolE
  | .bool value => .bool value
  | .eq A left right => .eq A.toHolE left.toHolE right.toHolE
  | .eps A predicate => .eps A.toHolE predicate.toHolE

/-- Recover Ethane syntax exactly on the model-only HolE fragment. -/
def ofHolE : Nucleus.HolE.Named.Unsorted.Expr Sig Name → Option (Syn Sig Name)
  | .boolTy => some .boolTy
  | .arr A B => return .arr (← ofHolE A) (← ofHolE B)
  | .tyApp domain codomain F A => return .tyApp domain codomain (← ofHolE F) (← ofHolE A)
  | .tyLam domain codomain name body =>
      return .tyLam domain codomain name (← ofHolE body)
  | .tyFv name kind => some (.tyFv name kind)
  | .sub .. => none
  | .tyExists name predicate => return .tyExists name (← ofHolE predicate)
  | .model name predicate => return .model name (← ofHolE predicate)
  | .primFam kind symbol => some (.primFam kind symbol)
  | .primTm symbol => some (.primTm symbol)
  | .tmFv name A => return .tmFv name (← ofHolE A)
  | .app function argument => return .app (← ofHolE function) (← ofHolE argument)
  | .lam name A body => return .lam name (← ofHolE A) (← ofHolE body)
  | .bool value => some (.bool value)
  | .eq A left right => return .eq (← ofHolE A) (← ofHolE left) (← ofHolE right)
  | .eps A predicate => return .eps (← ofHolE A) (← ofHolE predicate)
  | .abs .. | .rep .. => none

@[simp] theorem ofHolE_toHolE (expression : Syn Sig Name) :
    ofHolE expression.toHolE = some expression := by
  induction expression <;> simp_all [toHolE, ofHolE]

end Syn

namespace Expr

/-- Erase only the syntactic sort index. -/
def erase : {sort : HolSort} → Expr Sig Name sort → Syn Sig Name
  | _, .boolTy => .boolTy
  | _, .arr A B => .arr A.erase B.erase
  | .kind codomain, @Expr.tyApp _ _ domain _ F A =>
      .tyApp domain codomain F.erase A.erase
  | .kind (.arr domain codomain), .tyLam name body =>
      .tyLam domain codomain name body.erase
  | .kind kind, .tyFv name _ => .tyFv name kind
  | _, .tyExists name predicate => .tyExists name predicate.erase
  | _, .model name predicate => .model name predicate.erase
  | .kind kind, .primFam symbol => .primFam kind symbol
  | _, .primTm symbol => .primTm symbol
  | _, .tmFv name A => .tmFv name A.erase
  | _, .app function argument => .app function.erase argument.erase
  | _, .lam name A body => .lam name A.erase body.erase
  | _, .bool value => .bool value
  | _, .eq A left right => .eq A.erase left.erase right.erase
  | _, .eps A predicate => .eps A.erase predicate.erase

/-- Embed sorted Ethane syntax into sorted named HolE. -/
def toHolE : {sort : HolSort} → Expr Sig Name sort → Nucleus.HolE.Named.Expr Sig Name sort
  | _, .boolTy => .boolTy
  | _, .arr A B => .arr A.toHolE B.toHolE
  | _, .tyApp F A => .tyApp F.toHolE A.toHolE
  | _, .tyLam name body => .tyLam name body.toHolE
  | _, .tyFv name kind => .tyFv name kind
  | _, .tyExists name predicate => .tyExists name predicate.toHolE
  | _, .model name predicate => .model name predicate.toHolE
  | _, .primFam symbol => .primFam symbol
  | _, .primTm symbol => .primTm symbol
  | _, .tmFv name A => .tmFv name A.toHolE
  | _, .app function argument => .app function.toHolE argument.toHolE
  | _, .lam name A body => .lam name A.toHolE body.toHolE
  | _, .bool value => .bool value
  | _, .eq A left right => .eq A.toHolE left.toHolE right.toHolE
  | _, .eps A predicate => .eps A.toHolE predicate.toHolE

/-- Recover sorted Ethane syntax exactly on the model-only HolE fragment. -/
def ofHolE : {sort : HolSort} → Nucleus.HolE.Named.Expr Sig Name sort → Option (Expr Sig Name sort)
  | _, .boolTy => some .boolTy
  | _, .arr A B => return .arr (← ofHolE A) (← ofHolE B)
  | _, .tyApp F A => return .tyApp (← ofHolE F) (← ofHolE A)
  | _, .tyLam name body => return .tyLam name (← ofHolE body)
  | _, .tyFv name kind => some (.tyFv name kind)
  | _, .sub .. => none
  | _, .tyExists name predicate => return .tyExists name (← ofHolE predicate)
  | _, .model name predicate => return .model name (← ofHolE predicate)
  | _, .primFam symbol => some (.primFam symbol)
  | _, .primTm symbol => some (.primTm symbol)
  | _, .tmFv name A => return .tmFv name (← ofHolE A)
  | _, .app function argument => return .app (← ofHolE function) (← ofHolE argument)
  | _, .lam name A body => return .lam name (← ofHolE A) (← ofHolE body)
  | _, .bool value => some (.bool value)
  | _, .eq A left right => return .eq (← ofHolE A) (← ofHolE left) (← ofHolE right)
  | _, .eps A predicate => return .eps (← ofHolE A) (← ofHolE predicate)
  | _, .abs .. | _, .rep .. => none

@[simp] theorem ofHolE_toHolE (expression : Expr Sig Name sort) :
    ofHolE expression.toHolE = some expression := by
  induction expression <;> simp_all [toHolE, ofHolE]

@[simp] theorem check_erase (expression : Expr Sig Name sort) :
    Syn.check sort expression.erase = some expression := by
  induction expression <;> simp_all [erase, Syn.check]

@[simp] theorem syn_toHolE_erase (expression : Expr Sig Name sort) :
    expression.erase.toHolE = Nucleus.HolE.Named.Unsorted.erase expression.toHolE := by
  induction expression <;> simp_all [erase, toHolE, Syn.toHolE,
    Nucleus.HolE.Named.Unsorted.erase]

end Expr

end Nucleus.Ethane
