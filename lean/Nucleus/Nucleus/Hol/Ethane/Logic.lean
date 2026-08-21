import Nucleus.Hol.Ethane.Syntax

/-!
# Derived Ethane logical syntax

These are macros, not core constructors.  Binder-taking definitions expose the
binder name so callers can arrange freshness.  The subtype package uses a
tagged name type and is therefore hygienic by construction.
-/

namespace Nucleus.Hol.Ethane.Expr

set_option relaxedAutoImplicit true

def letTm (name : Name) (type : Ty Sig Name) (value body : Tm Sig Name) :
    Tm Sig Name :=
  .app (.lam name type body) value

def truth : Tm Sig Name := .bool true

def falsehood : Tm Sig Name := .bool false

def not (proposition : Tm Sig Name) : Tm Sig Name :=
  .eq .boolTy proposition falsehood

/-- Universal quantification as equality with the constantly true function. -/
def forallTm (name : Name) (type : Ty Sig Name) (body : Tm Sig Name) : Tm Sig Name :=
  .eq (.arr type .boolTy) (.lam name type body) (.lam name type truth)

/-- Existential quantification by Hilbert choice. -/
def existsTm (name : Name) (type : Ty Sig Name) (body : Tm Sig Name) : Tm Sig Name :=
  let predicate := .lam name type body
  .app predicate (.eps type predicate)

/-- The standard equality-only HOL definition of conjunction.

`functionName` binds only variables carrying the displayed binary Boolean
function type.  Callers which do not already control freshness should first
embed their names into the right side of a sum and use a left-side name here. -/
def and (functionName : Name) (left right : Tm Sig Name) : Tm Sig Name :=
  let functionType : Ty Sig Name := .arr .boolTy (.arr .boolTy .boolTy)
  let function : Tm Sig Name := .tmFv functionName functionType
  let lhsBody := .app (.app function left) right
  let lhs := .lam functionName functionType lhsBody
  let rhsBody := .app (.app function truth) truth
  let rhs := .lam functionName functionType rhsBody
  .eq (.arr functionType .boolTy) lhs rhs

def or (functionName : Name) (left right : Tm Sig Name) : Tm Sig Name :=
  not (and functionName (not left) (not right))

def imp (functionName : Name) (left right : Tm Sig Name) : Tm Sig Name :=
  not (and functionName left (not right))

end Nucleus.Hol.Ethane.Expr
