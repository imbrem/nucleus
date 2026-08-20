import Nucleus.HolE.Named.Unsorted.Macros

/-!
# Well-sorted unsorted named syntax

`WellSorted sort` is the checked view of the unindexed wire syntax.  It stores
the corresponding sorted named expression; erasure is its public projection.
This layer checks only syntactic sorts.  Object-language typing is represented
separately in `Rules`.
-/

namespace Nucleus.HolE.Named.Unsorted

universe u
set_option relaxedAutoImplicit true

/-- Unsorted syntax certified to have one specified syntactic sort. -/
structure WellSorted (Sig : Signature.{u}) (sort : HolSort) where
  sorted : Named.Expr Sig Nat sort

namespace WellSorted

/-- Forget the sort certificate. -/
def raw (expression : WellSorted Sig sort) : Expr Sig Nat :=
  erase expression.sorted

/-- Check raw syntax at a requested sort. -/
def ofRaw (sort : HolSort) (expression : Expr Sig Nat) : Option (WellSorted Sig sort) :=
  (check sort expression).map WellSorted.mk

/-- Embed already sorted syntax. -/
def ofSorted (expression : Named.Expr Sig Nat sort) : WellSorted Sig sort :=
  ⟨expression⟩

@[simp] theorem raw_ofSorted (expression : Named.Expr Sig Nat sort) :
    (ofSorted expression).raw = erase expression := rfl

@[simp] theorem ofRaw_raw (expression : WellSorted Sig sort) :
    ofRaw sort expression.raw = some expression := by
  cases expression
  simp [ofRaw, raw]

/-- Sort erasure is injective at a fixed sort. -/
theorem raw_injective : Function.Injective (@raw Sig sort) := by
  intro left right equality
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      congr
      change erase left = erase right at equality
      have leftCheck := check_erase left
      have rightCheck := check_erase right
      rw [equality] at leftCheck
      exact Option.some.inj (leftCheck.symm.trans rightCheck)

@[ext] theorem ext {left right : WellSorted Sig sort}
    (equality : left.raw = right.raw) : left = right :=
  raw_injective equality

def boolTy : WellSorted Sig (.kind .star) := ⟨.boolTy⟩

def arr (domain codomain : WellSorted Sig (.kind .star)) :
    WellSorted Sig (.kind .star) :=
  ⟨.arr domain.sorted codomain.sorted⟩

def tyApp {domain codomain : Kind}
    (function : WellSorted Sig (.kind (.arr domain codomain)))
    (argument : WellSorted Sig (.kind domain)) : WellSorted Sig (.kind codomain) :=
  ⟨.tyApp function.sorted argument.sorted⟩

def tyLam {domain codomain : Kind} (name : Nat)
    (body : WellSorted Sig (.kind codomain)) :
    WellSorted Sig (.kind (.arr domain codomain)) :=
  ⟨.tyLam name body.sorted⟩

def tyFv (name : Nat) (kind : Kind) : WellSorted Sig (.kind kind) :=
  ⟨.tyFv name kind⟩

def sub (carrier : WellSorted Sig (.kind .star)) (name : Nat)
    (predicate : WellSorted Sig .tm) : WellSorted Sig (.kind .star) :=
  ⟨.sub carrier.sorted name predicate.sorted⟩

def tyExists (name : Nat) (predicate : WellSorted Sig .tm) : WellSorted Sig .tm :=
  ⟨.tyExists name predicate.sorted⟩

def model (name : Nat) (predicate : WellSorted Sig .tm) :
    WellSorted Sig (.kind .star) :=
  ⟨.model name predicate.sorted⟩

def primFam {kind : Kind} (symbol : Sig (.kind kind)) : WellSorted Sig (.kind kind) :=
  ⟨.primFam symbol⟩

def primTm (symbol : Sig .tm) : WellSorted Sig .tm := ⟨.primTm symbol⟩

def tmFv (name : Nat) (type : WellSorted Sig (.kind .star)) : WellSorted Sig .tm :=
  ⟨.tmFv name type.sorted⟩

def app (function argument : WellSorted Sig .tm) : WellSorted Sig .tm :=
  ⟨.app function.sorted argument.sorted⟩

def lam (name : Nat) (domain : WellSorted Sig (.kind .star))
    (body : WellSorted Sig .tm) : WellSorted Sig .tm :=
  ⟨.lam name domain.sorted body.sorted⟩

def bool (value : Bool) : WellSorted Sig .tm := ⟨.bool value⟩

def eq (type : WellSorted Sig (.kind .star)) (left right : WellSorted Sig .tm) :
    WellSorted Sig .tm :=
  ⟨.eq type.sorted left.sorted right.sorted⟩

def eps (type : WellSorted Sig (.kind .star)) (predicate : WellSorted Sig .tm) :
    WellSorted Sig .tm :=
  ⟨.eps type.sorted predicate.sorted⟩

def abs (carrier : WellSorted Sig (.kind .star)) (name : Nat)
    (predicate value : WellSorted Sig .tm) : WellSorted Sig .tm :=
  ⟨.abs carrier.sorted name predicate.sorted value.sorted⟩

def rep (carrier : WellSorted Sig (.kind .star)) (name : Nat)
    (predicate value : WellSorted Sig .tm) : WellSorted Sig .tm :=
  ⟨.rep carrier.sorted name predicate.sorted value.sorted⟩

/-- Checked let syntax. -/
def letTm (name : Nat) (type : WellSorted Sig (.kind .star))
    (value body : WellSorted Sig .tm) : WellSorted Sig .tm :=
  app (lam name type body) value

def truth : WellSorted Sig .tm := bool true
def falsehood : WellSorted Sig .tm := bool false
def not (proposition : WellSorted Sig .tm) : WellSorted Sig .tm :=
  eq boolTy proposition falsehood

/-- The same hygienic equality-only conjunction as the raw macro. -/
def and (left right : WellSorted Sig .tm) : WellSorted Sig .tm :=
  let functionType := arr boolTy (arr boolTy boolTy)
  let name := Unsorted.freshName left.raw right.raw
  let function := tmFv name functionType
  let lhs := lam name functionType (app (app function left) right)
  let rhs := lam name functionType (app (app function truth) truth)
  eq (arr functionType boolTy) lhs rhs

def or (left right : WellSorted Sig .tm) : WellSorted Sig .tm :=
  not (and (not left) (not right))

def imp (left right : WellSorted Sig .tm) : WellSorted Sig .tm :=
  eq boolTy (and left right) left

@[simp] theorem raw_boolTy : (boolTy (Sig := Sig)).raw = .boolTy := rfl
@[simp] theorem raw_arr (A B : WellSorted Sig (.kind .star)) :
    (arr A B).raw = .arr A.raw B.raw := rfl
@[simp] theorem raw_app (f x : WellSorted Sig .tm) :
    (app f x).raw = .app f.raw x.raw := rfl
@[simp] theorem raw_lam (name : Nat) (A : WellSorted Sig (.kind .star))
    (body : WellSorted Sig .tm) :
    (lam name A body).raw = .lam name A.raw body.raw := rfl
@[simp] theorem raw_letTm (name : Nat) (A : WellSorted Sig (.kind .star))
    (value body : WellSorted Sig .tm) :
    (letTm name A value body).raw = Unsorted.letTm name A.raw value.raw body.raw := rfl
@[simp] theorem raw_not (p : WellSorted Sig .tm) :
    (not p).raw = Unsorted.not p.raw := rfl
@[simp] theorem raw_and (p q : WellSorted Sig .tm) :
    (and p q).raw = Unsorted.and p.raw q.raw := rfl
@[simp] theorem raw_or (p q : WellSorted Sig .tm) :
    (or p q).raw = Unsorted.or p.raw q.raw := rfl
@[simp] theorem raw_imp (p q : WellSorted Sig .tm) :
    (imp p q).raw = Unsorted.imp p.raw q.raw := rfl

end WellSorted

/-- A well-sorted expression carrying its result sort at runtime. -/
structure SomeWellSorted (Sig : Signature.{u}) where
  sort : HolSort
  expression : WellSorted Sig sort

namespace SomeWellSorted

def raw (expression : SomeWellSorted Sig) : Expr Sig Nat := expression.expression.raw

/-- Infer and validate the result sort of raw syntax. -/
def ofRaw (expression : Expr Sig Nat) : Option (SomeWellSorted Sig) := do
  let checked ← infer expression
  return ⟨checked.sort, ⟨checked.expression⟩⟩

@[simp] theorem ofRaw_raw (expression : SomeWellSorted Sig) :
    ofRaw expression.raw = some expression := by
  cases expression with
  | mk sort expression =>
    cases expression with
    | mk sorted => simp [ofRaw, raw, WellSorted.raw]

/-- The erased syntax determines its syntactic result sort. -/
theorem raw_injective : Function.Injective (@raw Sig) := by
  intro left right equality
  cases left with
  | mk leftSort left =>
    cases right with
    | mk rightSort right =>
      have sortEquality : leftSort = rightSort := by
        rw [← rootSort_erase left.sorted, ← rootSort_erase right.sorted]
        exact congrArg rootSort equality
      subst rightSort
      congr
      exact WellSorted.raw_injective equality

@[ext] theorem ext {left right : SomeWellSorted Sig}
    (equality : left.raw = right.raw) : left = right :=
  raw_injective equality

/-- Apply raw syntax construction and reject any argument-sort mismatch. -/
def mapRaw (constructor : List (Expr Sig Nat) → Expr Sig Nat)
    (arguments : List (SomeWellSorted Sig)) : Option (SomeWellSorted Sig) :=
  ofRaw (constructor (arguments.map raw))

def boolTy : SomeWellSorted Sig := ⟨.kind .star, WellSorted.boolTy⟩
def bool (value : Bool) : SomeWellSorted Sig := ⟨.tm, WellSorted.bool value⟩
def arr (domain codomain : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.arr domain.raw codomain.raw)
def tyApp (domain codomain : Kind) (function argument : SomeWellSorted Sig) :
    Option (SomeWellSorted Sig) :=
  ofRaw (.tyApp domain codomain function.raw argument.raw)
def tyLam (domain codomain : Kind) (name : Nat) (body : SomeWellSorted Sig) :
    Option (SomeWellSorted Sig) :=
  ofRaw (.tyLam domain codomain name body.raw)
def tyFv (name : Nat) (kind : Kind) : SomeWellSorted Sig :=
  ⟨.kind kind, WellSorted.tyFv name kind⟩
def sub (carrier : SomeWellSorted Sig) (name : Nat) (predicate : SomeWellSorted Sig) :
    Option (SomeWellSorted Sig) :=
  ofRaw (.sub carrier.raw name predicate.raw)
def tyExists (name : Nat) (predicate : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.tyExists name predicate.raw)
def model (name : Nat) (predicate : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.model name predicate.raw)
def primFam {kind : Kind} (symbol : Sig (.kind kind)) : SomeWellSorted Sig :=
  ⟨.kind kind, WellSorted.primFam symbol⟩
def primTm (symbol : Sig .tm) : SomeWellSorted Sig := ⟨.tm, WellSorted.primTm symbol⟩
def tmFv (name : Nat) (type : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.tmFv name type.raw)
def app (function argument : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.app function.raw argument.raw)
def lam (name : Nat) (domain body : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.lam name domain.raw body.raw)
def eq (type left right : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.eq type.raw left.raw right.raw)
def eps (type predicate : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.eps type.raw predicate.raw)
def abs (carrier : SomeWellSorted Sig) (name : Nat)
    (predicate value : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.abs carrier.raw name predicate.raw value.raw)
def rep (carrier : SomeWellSorted Sig) (name : Nat)
    (predicate value : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (.rep carrier.raw name predicate.raw value.raw)
def letTm (name : Nat) (type value body : SomeWellSorted Sig) :
    Option (SomeWellSorted Sig) :=
  ofRaw (Unsorted.letTm name type.raw value.raw body.raw)
def not (proposition : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (Unsorted.not proposition.raw)
def and (left right : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (Unsorted.and left.raw right.raw)
def or (left right : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (Unsorted.or left.raw right.raw)
def imp (left right : SomeWellSorted Sig) : Option (SomeWellSorted Sig) :=
  ofRaw (Unsorted.imp left.raw right.raw)

end SomeWellSorted

end Nucleus.HolE.Named.Unsorted
