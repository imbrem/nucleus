import Nucleus.HolE.Named.Unsorted.Checked

/-!
# Syntax-directed constructors for checked named HolE

This file is the implementation of the small structures in `Checked`.  Its
public declarations mirror every constructor of core `HolE.Checks`; lowering
bookkeeping remains in the bodies below.
-/

namespace Nucleus.HolE.Named.Unsorted

set_option relaxedAutoImplicit true

namespace Family

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]

def boolTy (typeScope : Named.TyScope types) : Family Sig typeScope .star :=
  ⟨WellSorted.boolTy, .boolTy, by simp [WellSorted.boolTy, Named.lowerFam], .boolTy⟩

def arr (domain codomain : Family Sig typeScope .star) : Family Sig typeScope .star :=
  ⟨WellSorted.arr domain.expression codomain.expression,
    .arr domain.lowered codomain.lowered,
    by simp [WellSorted.arr, Named.lowerFam, domain.lowering, codomain.lowering],
    .arr domain.kinding codomain.kinding⟩

def app {domain codomain : Kind}
    (function : Family Sig typeScope (.arr domain codomain))
    (argument : Family Sig typeScope domain) : Family Sig typeScope codomain :=
  ⟨WellSorted.tyApp function.expression argument.expression,
    .tyApp function.lowered argument.lowered,
    by simp [WellSorted.tyApp, Named.lowerFam, function.lowering, argument.lowering],
    .tyApp function.kinding argument.kinding⟩

def lam {domain codomain : Kind} (name : Nat)
    (body : Family Sig (.cons (kind := domain) name typeScope) codomain) :
    Family Sig typeScope (.arr domain codomain) :=
  ⟨WellSorted.tyLam name body.expression, .tyLam body.lowered,
    by simp [WellSorted.tyLam, Named.lowerFam, body.lowering], .tyLam body.kinding⟩

def tyFv (name : Nat) (kind : Kind) (v : Nucleus.HolE.TyVar types kind)
    (lookup : Named.lookupTy ⟨name, kind⟩ typeScope = some v) :
    Family Sig typeScope kind :=
  ⟨WellSorted.tyFv name kind, .tyBv v,
    by simp [WellSorted.tyFv, Named.lowerFam, lookup], .tyBv v⟩

def prim {kind : Kind} (symbol : Sig (.kind kind))
    (typeScope : Named.TyScope types) : Family Sig typeScope kind :=
  ⟨WellSorted.primFam symbol, .primFam symbol,
    by simp [WellSorted.primFam, Named.lowerFam], .primFam symbol⟩

end Family

namespace Term

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]

def primitive (symbol : Sig .tm) (type : Family Sig typeScope .star)
    (rule : Nucleus.HolE.SigTyping.HasType symbol type.lowered) :
    Term Sig typeScope termScope Γ type :=
  ⟨WellSorted.primTm symbol, .primTm symbol,
    by simp [WellSorted.primTm, Named.lowerTm], .primTm type.kinding rule⟩

/-- A named occurrence resolved by the current term scope. -/
def boundVariable (name : Nat) (type : Family Sig typeScope .star)
    (index : Fin depth)
    (scopeLookup : Named.lookupTm ⟨name, type.expression.sorted⟩ termScope = some index)
    (contextLookup : Γ index = type.lowered) :
    Term Sig typeScope termScope Γ type :=
  ⟨WellSorted.tmFv name type.expression, .bv index,
    by simp [WellSorted.tmFv, Named.lowerTm, scopeLookup],
    .bv type.kinding contextLookup⟩

/-- A named occurrence not captured by the current term scope. -/
def freeVariable (name : Nat) (type : Family Sig typeScope .star)
    (fresh : Named.lookupTm ⟨name, type.expression.sorted⟩ termScope = none) :
    Term Sig typeScope termScope Γ type :=
  ⟨WellSorted.tmFv name type.expression, .fv name type.lowered,
    by simp [WellSorted.tmFv, Named.lowerTm, fresh, type.lowering],
    .fv name type.kinding⟩

def app (function : Term Sig typeScope termScope Γ (Family.arr domain codomain))
    (argument : Term Sig typeScope termScope Γ domain) :
    Term Sig typeScope termScope Γ codomain :=
  ⟨WellSorted.app function.expression argument.expression,
    .app function.lowered argument.lowered,
    by simp [WellSorted.app, Named.lowerTm, function.lowering, argument.lowering],
    by simpa [Family.arr] using Nucleus.HolE.Checks.app function.typing argument.typing⟩

def lam (name : Nat) (domain codomain : Family Sig typeScope .star)
    (body : Term Sig typeScope
      (.cons ⟨name, domain.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound domain.lowered Γ) codomain) :
    Term Sig typeScope termScope Γ (Family.arr domain codomain) :=
  ⟨WellSorted.lam name domain.expression body.expression,
    .lam domain.lowered body.lowered,
    by simp [WellSorted.lam, Named.lowerTm, domain.lowering, body.lowering],
    by simpa [Family.arr] using
      Nucleus.HolE.Checks.lam body.lowered domain.kinding body.typing⟩

def bool (value : Bool) :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope) :=
  ⟨WellSorted.bool value, .bool value,
    by simp [WellSorted.bool, Named.lowerTm],
    by simpa [Family.boolTy] using (Nucleus.HolE.Checks.bool (Sig := Sig) value)⟩

def eq (type : Family Sig typeScope .star)
    (left right : Term Sig typeScope termScope Γ type) :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope) :=
  ⟨WellSorted.eq type.expression left.expression right.expression,
    .eq type.lowered left.lowered right.lowered,
    by simp [WellSorted.eq, Named.lowerTm, type.lowering, left.lowering, right.lowering],
    by simpa [Family.boolTy] using
      Nucleus.HolE.Checks.eq type.kinding left.typing right.typing⟩

def eps (type : Family Sig typeScope .star)
    (predicate : Term Sig typeScope termScope Γ
      (Family.arr type (Family.boolTy typeScope))) :
    Term Sig typeScope termScope Γ type :=
  ⟨WellSorted.eps type.expression predicate.expression,
    .eps type.lowered predicate.lowered,
    by simp [WellSorted.eps, Named.lowerTm, type.lowering, predicate.lowering],
    by simpa [Family.arr, Family.boolTy] using
      Nucleus.HolE.Checks.eps type.kinding predicate.typing⟩

def sub (carrier : Family Sig typeScope .star) (name : Nat)
    (predicate : Term Sig typeScope
      (.cons ⟨name, carrier.expression.sorted⟩ .nil)
      (Nucleus.HolE.extendBound carrier.lowered Nucleus.HolE.emptyBound)
      (Family.boolTy typeScope)) : Family Sig typeScope .star :=
  ⟨WellSorted.sub carrier.expression name predicate.expression,
    .sub carrier.lowered predicate.lowered,
    by simp [WellSorted.sub, Named.lowerFam, carrier.lowering, predicate.lowering],
    by simpa [Family.boolTy] using
      Nucleus.HolE.Checks.sub carrier.kinding predicate.typing⟩

def abs (carrier : Family Sig typeScope .star) (name : Nat)
    (predicate : Term Sig typeScope
      (.cons ⟨name, carrier.expression.sorted⟩ .nil)
      (Nucleus.HolE.extendBound carrier.lowered Nucleus.HolE.emptyBound)
      (Family.boolTy typeScope))
    (value : Term Sig typeScope termScope Γ carrier) :
    Term Sig typeScope termScope Γ (sub carrier name predicate) :=
  ⟨WellSorted.abs carrier.expression name predicate.expression value.expression,
    .abs carrier.lowered predicate.lowered value.lowered,
    by simp [WellSorted.abs, Named.lowerTm, carrier.lowering, predicate.lowering,
      value.lowering],
    by simpa [sub, Family.boolTy] using
      Nucleus.HolE.Checks.abs carrier.kinding predicate.typing value.typing⟩

def rep (carrier : Family Sig typeScope .star) (name : Nat)
    (predicate : Term Sig typeScope
      (.cons ⟨name, carrier.expression.sorted⟩ .nil)
      (Nucleus.HolE.extendBound carrier.lowered Nucleus.HolE.emptyBound)
      (Family.boolTy typeScope))
    (value : Term Sig typeScope termScope Γ (sub carrier name predicate)) :
    Term Sig typeScope termScope Γ carrier :=
  ⟨WellSorted.rep carrier.expression name predicate.expression value.expression,
    .rep carrier.lowered predicate.lowered value.lowered,
    by simp [WellSorted.rep, Named.lowerTm, carrier.lowering, predicate.lowering,
      value.lowering],
    by simpa [sub, Family.boolTy] using
      Nucleus.HolE.Checks.rep carrier.kinding predicate.typing value.typing⟩

def tyExists (name : Nat)
    (predicate : Term Sig (.cons (kind := .star) name typeScope) .nil
      Nucleus.HolE.emptyBound (Family.boolTy (.cons name typeScope))) :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope) :=
  ⟨WellSorted.tyExists name predicate.expression, .tyExists predicate.lowered,
    by simp [WellSorted.tyExists, Named.lowerTm, predicate.lowering],
    by simpa [Family.boolTy] using Nucleus.HolE.Checks.tyExists predicate.typing⟩

end Term

namespace Family

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]

def model (name : Nat)
    (predicate : Term Sig (.cons (kind := .star) name typeScope) .nil
      Nucleus.HolE.emptyBound (boolTy (.cons name typeScope))) :
    Family Sig typeScope .star :=
  ⟨WellSorted.model name predicate.expression, .model predicate.lowered,
    by simp [WellSorted.model, Named.lowerFam, predicate.lowering],
    by simpa [boolTy] using Nucleus.HolE.Checks.model predicate.typing⟩

end Family

namespace Term

variable {Sig : Signature} [Nucleus.HolE.SigTyping Sig]

def truth : Term Sig typeScope termScope Γ (Family.boolTy typeScope) := bool true
def falsehood : Term Sig typeScope termScope Γ (Family.boolTy typeScope) := bool false

/-- Checked let-binding; its typing is inherited from lambda and application. -/
def letTm (name : Nat) (domain codomain : Family Sig typeScope .star)
    (value : Term Sig typeScope termScope Γ domain)
    (body : Term Sig typeScope
      (.cons ⟨name, domain.expression.sorted⟩ termScope)
      (Nucleus.HolE.extendBound domain.lowered Γ) codomain) :
    Term Sig typeScope termScope Γ codomain :=
  app (lam name domain codomain body) value

def not (proposition : Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope) :=
  eq (Family.boolTy typeScope) proposition falsehood

/-- Partial checked conjunction.  The raw macro is hygienic; this façade keeps
the operation partial until named weakening is available as an executable
checker theorem. -/
noncomputable def and? (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Option (Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :=
  ofRaw (Family.boolTy typeScope) (Unsorted.and left.raw right.raw)

noncomputable def or? (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Option (Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :=
  ofRaw (Family.boolTy typeScope) (Unsorted.or left.raw right.raw)

noncomputable def imp? (left right :
    Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :
    Option (Term Sig typeScope termScope Γ (Family.boolTy typeScope)) :=
  ofRaw (Family.boolTy typeScope) (Unsorted.imp left.raw right.raw)

end Term

end Nucleus.HolE.Named.Unsorted
