import Nucleus.HolE.FreeVariables
import Nucleus.HolE.Named.Lower

/-!
# Quoting locally nameless HolE as named syntax

Quotation chooses binder names above every source free-variable index.  It
therefore cannot capture an existing free variable.  Names may be reused in
separate branches; nested binders receive successive indices.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

/-- Names aligned with a heterogeneous locally nameless type context. -/
abbrev TyNames (types : List Kind) :=
  {kind : Kind} → Nucleus.HolE.TyVar types kind → Nat

def emptyTyNames : TyNames [] := fun item => nomatch item

def extendTyNames (name : Nat) (names : TyNames types) :
    TyNames (kind :: types)
  | _, .zero => name
  | _, .succ item => names item

/-- Named declarations aligned with a de Bruijn term scope. -/
abbrev TmNames (Sig : Signature) (depth : Nat) := Fin depth → TmDecl Sig

def emptyTmNames : TmNames Sig 0 := Fin.elim0

def extendTmNames (declaration : TmDecl Sig) (names : TmNames Sig depth) :
    TmNames Sig (depth + 1) :=
  Fin.cases declaration names

/-- Quote locally nameless syntax using the supplied names for open binders. -/
noncomputable def quote (next : Nat) (typeNames : TyNames types)
    (termNames : TmNames Sig depth) :
    Nucleus.HolE.Expr Sig types sort depth → Expr Sig Nat sort
  | .boolTy => .boolTy
  | .arr A B => .arr (quote next typeNames emptyTmNames A)
      (quote next typeNames emptyTmNames B)
  | .tyApp F A => .tyApp (quote next typeNames emptyTmNames F)
      (quote next typeNames emptyTmNames A)
  | @Nucleus.HolE.Expr.tyLam _ _ domain _ body =>
      .tyLam next (quote (next + 1) (extendTyNames next typeNames) emptyTmNames body)
  | @Nucleus.HolE.Expr.tyBv _ _ kind item =>
      .tyFv (typeNames item) kind
  | .sub A predicate =>
      let namedA := quote next typeNames emptyTmNames A
      .sub namedA next
        (quote (next + 1) typeNames (extendTmNames ⟨next, namedA⟩ emptyTmNames) predicate)
  -- Only the type names grow across a type binder; the term names carry
  -- through, mirroring `lowerTm`.
  | .tyExists predicate =>
      .tyExists next
        (quote (next + 1) (extendTyNames next typeNames) termNames predicate)
  -- Only the type names grow across a type binder; the term names carry
  -- through, mirroring `lowerTm`.
  | .tyForall predicate =>
      .tyForall next
        (quote (next + 1) (extendTyNames next typeNames) termNames predicate)
  | .model predicate =>
      .model next
        (quote (next + 1) (extendTyNames next typeNames) emptyTmNames predicate)
  | .primFam symbol => .primFam symbol
  | .primTm symbol => .primTm symbol
  | .bv index => .tmFv (termNames index).name (termNames index).sort
  | .fv name A => .tmFv name (quote next typeNames emptyTmNames A)
  | .app function argument => .app (quote next typeNames termNames function)
      (quote next typeNames termNames argument)
  | .lam A body =>
      let namedA := quote next typeNames emptyTmNames A
      .lam next namedA
        (quote (next + 1) typeNames (extendTmNames ⟨next, namedA⟩ termNames) body)
  | .bool value => .bool value
  | .eq A left right => .eq (quote next typeNames emptyTmNames A)
      (quote next typeNames termNames left) (quote next typeNames termNames right)
  | .eps A predicate => .eps (quote next typeNames emptyTmNames A)
      (quote next typeNames termNames predicate)
  | .abs A predicate value =>
      let namedA := quote next typeNames emptyTmNames A
      .abs namedA next
        (quote (next + 1) typeNames (extendTmNames ⟨next, namedA⟩ emptyTmNames) predicate)
        (quote next typeNames termNames value)
  | .rep A predicate value =>
      let namedA := quote next typeNames emptyTmNames A
      .rep namedA next
        (quote (next + 1) typeNames (extendTmNames ⟨next, namedA⟩ emptyTmNames) predicate)
        (quote next typeNames termNames value)

/-- Quote a closed locally nameless expression without caller-supplied names. -/
noncomputable def quoteClosed (expression : Nucleus.HolE.Expr Sig [] sort 0) :
    Expr Sig Nat sort :=
  quote (Nucleus.HolE.freshIndex expression) emptyTyNames emptyTmNames expression

end Nucleus.HolE.Named
