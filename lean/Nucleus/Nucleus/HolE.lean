import Nucleus.Hol.Signature

/-!
# Type-variable-scoped HOL and pointwise subtype families

This is the experimental syntax layer for the question left deliberately out
of the first signature kernel: using ordinary HOL subtypes to construct whole
type families.  Type-variable scope is separate from term-variable scope.
-/

namespace Nucleus.HolE

universe u
set_option relaxedAutoImplicit true

abbrev Kind := Nucleus.Hol.Kind
abbrev HolSort := Nucleus.Hol.HolSort
abbrev Signature := Nucleus.Hol.Signature

/-- A kind-indexed de Bruijn variable in a heterogeneous type context. -/
inductive TyVar : List Kind → Kind → Type where
  | zero : TyVar (kind :: context) kind
  | succ : TyVar context kind → TyVar (other :: context) kind

abbrev TyRen (source target : List Kind) :=
  {kind : Kind} → TyVar source kind → TyVar target kind

def liftTyRen (ρ : TyRen source target) :
    TyRen (kind :: source) (kind :: target)
  | _, .zero => .zero
  | _, .succ v => .succ (ρ v)

/-- HOL syntax with independent locally nameless scopes for type and term
variables.  `tyLam` is only type-family abstraction; it does not add impredicative
type quantification to the object logic. -/
inductive Expr (Sig : Signature) : List Kind → HolSort → Nat → Type u where
  | boolTy : Expr Sig types (.kind .star) 0
  | arr (domain codomain : Expr Sig types (.kind .star) 0) :
      Expr Sig types (.kind .star) 0
  | tyApp {domain codomain : Kind}
      (function : Expr Sig types (.kind (.arr domain codomain)) 0)
      (argument : Expr Sig types (.kind domain) 0) : Expr Sig types (.kind codomain) 0
  | tyLam {domain codomain : Kind}
      (body : Expr Sig (domain :: types) (.kind codomain) 0) :
      Expr Sig types (.kind (.arr domain codomain)) 0
  | tyBv {kind : Kind} (v : TyVar types kind) : Expr Sig types (.kind kind) 0
  | sub (carrier : Expr Sig types (.kind .star) 0)
      (predicate : Expr Sig types .tm 1) : Expr Sig types (.kind .star) 0
  | tyExists {depth : Nat} (predicate : Expr Sig (.star :: types) .tm 0) :
      Expr Sig types .tm depth
  | model (predicate : Expr Sig (.star :: types) .tm 0) :
      Expr Sig types (.kind .star) 0
  | primFam {kind : Kind} (symbol : Sig (.kind kind)) : Expr Sig types (.kind kind) 0
  | primTm {depth : Nat} (symbol : Sig .tm) : Expr Sig types .tm depth
  | bv {depth : Nat} (index : Fin depth) : Expr Sig types .tm depth
  | fv {depth : Nat} (name : Nat) (type : Expr Sig types (.kind .star) 0) :
      Expr Sig types .tm depth
  | app {depth : Nat} (function argument : Expr Sig types .tm depth) :
      Expr Sig types .tm depth
  | lam {depth : Nat} (domain : Expr Sig types (.kind .star) 0)
      (body : Expr Sig types .tm (depth + 1)) : Expr Sig types .tm depth
  | bool {depth : Nat} (value : Bool) : Expr Sig types .tm depth
  | eq {depth : Nat} (type : Expr Sig types (.kind .star) 0)
      (left right : Expr Sig types .tm depth) : Expr Sig types .tm depth
  | eps {depth : Nat} (type : Expr Sig types (.kind .star) 0)
      (predicate : Expr Sig types .tm depth) : Expr Sig types .tm depth
  | abs {depth : Nat} (carrier : Expr Sig types (.kind .star) 0)
      (predicate : Expr Sig types .tm 1) (value : Expr Sig types .tm depth) :
      Expr Sig types .tm depth
  | rep {depth : Nat} (carrier : Expr Sig types (.kind .star) 0)
      (predicate : Expr Sig types .tm 1) (value : Expr Sig types .tm depth) :
      Expr Sig types .tm depth

abbrev Fam (Sig : Signature) (types : List Kind) (kind : Kind) :=
  Expr Sig types (.kind kind) 0
abbrev Ty (Sig : Signature) (types : List Kind) := Fam Sig types .star
abbrev Tm (Sig : Signature) (types : List Kind) (depth : Nat) := Expr Sig types .tm depth

abbrev TySub (Sig : Signature) (source target : List Kind) :=
  {kind : Kind} → TyVar source kind → Fam Sig target kind

def renameTypes (ρ : TyRen source target) :
    Expr Sig source sort depth → Expr Sig target sort depth
  | .boolTy => .boolTy
  | .arr A B => .arr (renameTypes ρ A) (renameTypes ρ B)
  | .tyApp F A => .tyApp (renameTypes ρ F) (renameTypes ρ A)
  | .tyLam body => .tyLam (renameTypes (liftTyRen ρ) body)
  | .tyBv v => .tyBv (ρ v)
  | .sub A p => .sub (renameTypes ρ A) (renameTypes ρ p)
  | .tyExists p => .tyExists (renameTypes (liftTyRen ρ) p)
  | .model p => .model (renameTypes (liftTyRen ρ) p)
  | .primFam symbol => .primFam symbol
  | .primTm symbol => .primTm symbol
  | .bv index => .bv index
  | .fv name A => .fv name (renameTypes ρ A)
  | .app f x => .app (renameTypes ρ f) (renameTypes ρ x)
  | .lam A body => .lam (renameTypes ρ A) (renameTypes ρ body)
  | .bool value => .bool value
  | .eq A x y => .eq (renameTypes ρ A) (renameTypes ρ x) (renameTypes ρ y)
  | .eps A p => .eps (renameTypes ρ A) (renameTypes ρ p)
  | .abs A p x => .abs (renameTypes ρ A) (renameTypes ρ p) (renameTypes ρ x)
  | .rep A p x => .rep (renameTypes ρ A) (renameTypes ρ p) (renameTypes ρ x)

def weakenTypes (expression : Expr Sig types sort depth) :
    Expr Sig (kind :: types) sort depth :=
  renameTypes (fun v => .succ v) expression

def liftTySub (σ : TySub Sig source target) :
    TySub Sig (kind :: source) (kind :: target)
  | _, .zero => .tyBv .zero
  | _, .succ v => weakenTypes (σ v)

/-- Capture-avoiding simultaneous substitution of type variables throughout
types and terms. -/
def instantiateTypes (σ : TySub Sig source target) :
    Expr Sig source sort depth → Expr Sig target sort depth
  | .boolTy => .boolTy
  | .arr A B => .arr (instantiateTypes σ A) (instantiateTypes σ B)
  | .tyApp F A => .tyApp (instantiateTypes σ F) (instantiateTypes σ A)
  | .tyLam body => .tyLam (instantiateTypes (liftTySub σ) body)
  | .tyBv v => σ v
  | .sub A p => .sub (instantiateTypes σ A) (instantiateTypes σ p)
  | .tyExists p => .tyExists (instantiateTypes (liftTySub σ) p)
  | .model p => .model (instantiateTypes (liftTySub σ) p)
  | .primFam symbol => .primFam symbol
  | .primTm symbol => .primTm symbol
  | .bv index => .bv index
  | .fv name A => .fv name (instantiateTypes σ A)
  | .app f x => .app (instantiateTypes σ f) (instantiateTypes σ x)
  | .lam A body => .lam (instantiateTypes σ A) (instantiateTypes σ body)
  | .bool value => .bool value
  | .eq A x y => .eq (instantiateTypes σ A) (instantiateTypes σ x)
      (instantiateTypes σ y)
  | .eps A p => .eps (instantiateTypes σ A) (instantiateTypes σ p)
  | .abs A p x => .abs (instantiateTypes σ A) (instantiateTypes σ p)
      (instantiateTypes σ x)
  | .rep A p x => .rep (instantiateTypes σ A) (instantiateTypes σ p)
      (instantiateTypes σ x)

def headTySub (replacement : Fam Sig types kind) :
    TySub Sig (kind :: types) types
  | _, .zero => replacement
  | _, .succ v => .tyBv v

def openType (body : Expr Sig (kind :: types) sort depth)
    (replacement : Fam Sig types kind) : Expr Sig types sort depth :=
  instantiateTypes (headTySub replacement) body

@[simp] theorem openType_bv_zero (replacement : Fam Sig types kind) :
    openType (.tyBv .zero) replacement = replacement := rfl

@[simp] theorem openType_bv_succ (v : TyVar types otherKind)
    (replacement : Fam Sig types kind) :
    openType (.tyBv (.succ v)) replacement = .tyBv v := rfl

theorem instantiateTypes_renameTypes_cancel
    (expression : Expr Sig source sort depth) (ρ : TyRen source middle)
    (σ : TySub Sig middle source)
    (cancel : ∀ {variableKind} (v : TyVar source variableKind),
      σ (ρ v) = .tyBv v) :
    instantiateTypes σ (renameTypes ρ expression) = expression := by
  induction expression generalizing middle with
  | boolTy | primFam | primTm | bv | bool => rfl
  | arr A B ihA ihB | tyApp A B ihA ihB | app A B ihA ihB =>
      simp only [renameTypes, instantiateTypes]
      rw [ihA ρ σ cancel, ihB ρ σ cancel]
  | tyLam body ih =>
      simp only [renameTypes, instantiateTypes]
      congr 1
      apply ih (liftTyRen ρ) (liftTySub σ)
      intro variableKind v
      cases v with
      | zero => rfl
      | succ v => simp [liftTyRen, liftTySub, cancel v, weakenTypes, renameTypes]
  | tyExists body ih | model body ih =>
      simp only [renameTypes, instantiateTypes]
      congr 1
      apply ih (liftTyRen ρ) (liftTySub σ)
      intro variableKind v
      cases v with
      | zero => rfl
      | succ v => simp [liftTyRen, liftTySub, cancel v, weakenTypes, renameTypes]
  | tyBv v => exact cancel v
  | sub A p ihA ihp | lam A p ihA ihp | eps A p ihA ihp =>
      simp only [renameTypes, instantiateTypes]
      rw [ihA ρ σ cancel, ihp ρ σ cancel]
  | fv name A ih =>
      simp only [renameTypes, instantiateTypes]
      rw [ih ρ σ cancel]
  | eq A x y ihA ihx ihy | abs A x y ihA ihx ihy | rep A x y ihA ihx ihy =>
      simp only [renameTypes, instantiateTypes]
      rw [ihA ρ σ cancel, ihx ρ σ cancel, ihy ρ σ cancel]

@[simp] theorem openType_weakenTypes
    (expression : Expr Sig types sort depth) (replacement : Fam Sig types kind) :
    openType (weakenTypes (kind := kind) expression) replacement = expression := by
  apply instantiateTypes_renameTypes_cancel expression (fun v => .succ v)
    (headTySub replacement)
  intro variableKind v
  rfl

@[simp] theorem instantiateTypes_head_weakenTypes
    (expression : Expr Sig types sort depth) (replacement : Fam Sig types kind) :
    instantiateTypes (headTySub replacement) (weakenTypes (kind := kind) expression) =
      expression := openType_weakenTypes expression replacement

/-- Type-family beta reduction is computation of locally nameless opening. -/
@[simp] theorem openType_tyLam_beta
    (body : Fam Sig (kind :: types) codomain) (argument : Fam Sig types kind) :
    openType body argument = instantiateTypes (headTySub argument) body := rfl

/-- Pointwise subtype-family formation, defined solely from type-family lambda,
application, and ordinary `Sub`.  Its predicate receives one term whose type is
`carrier α`, where `α` is the freshly bound type variable. -/
def subFam {kind : Kind} (carrier : Fam Sig types (.arr kind .star))
    (predicate : Tm Sig (kind :: types) 1) : Fam Sig types (.arr kind .star) :=
  .tyLam (.sub (.tyApp (weakenTypes carrier) (.tyBv .zero)) predicate)

abbrev BoundCtx (Sig : Signature) (types : List Kind) (depth : Nat) :=
  Fin depth → Ty Sig types

def emptyBound : BoundCtx Sig types 0 := Fin.elim0

def extendBound (A : Ty Sig types) (context : BoundCtx Sig types depth) :
    BoundCtx Sig types (depth + 1) := Fin.cases A context

/-- Signature-provided primitive family equalities.  An implementation may
obtain these certificates by fetching content-addressed definitions or by
running a computation; the kernel only consumes the resulting rule value. -/
class SigFamilyEquality (Sig : Signature.{u}) where
  Rule : {types : List Kind} → {kind : Kind} →
    Fam Sig types kind → Fam Sig types kind → Type u

/-- Definitional equality for type families.  In particular, family lambda is
computational: applying it opens its body. -/
inductive FamEq (Sig : Signature.{u}) [rules : SigFamilyEquality Sig] :
    {types : List Kind} → {kind : Kind} →
    Fam Sig types kind → Fam Sig types kind → Type (u + 1) where
  | refl : FamEq Sig A A
  | symm : FamEq Sig A B → FamEq Sig B A
  | trans : FamEq Sig A B → FamEq Sig B C → FamEq Sig A C
  | arr : FamEq Sig A A' → FamEq Sig B B' → FamEq Sig (.arr A B) (.arr A' B')
  | app : FamEq Sig F F' → FamEq Sig A A' → FamEq Sig (.tyApp F A) (.tyApp F' A')
  | lam : FamEq Sig body body' → FamEq Sig (.tyLam body) (.tyLam body')
  | sub : FamEq Sig A B → p = q → FamEq Sig (.sub A p) (.sub B q)
  | model : p = q → FamEq Sig (.model p) (.model q)
  | beta (body : Fam Sig (domain :: types) codomain) (argument : Fam Sig types domain) :
      FamEq Sig (.tyApp (.tyLam body) argument) (openType body argument)
  | rename {source target : List Kind} {kind : Kind}
      {A B : Fam Sig source kind} (equality : FamEq Sig A B)
      (ρ : TyRen source target) :
      FamEq Sig (renameTypes ρ A) (renameTypes ρ B)
  | instantiate {source target : List Kind} {kind : Kind}
      {A B : Fam Sig source kind} (equality : FamEq Sig A B)
      (σ : TySub Sig source target) :
      FamEq Sig (instantiateTypes σ A) (instantiateTypes σ B)
  | signature (certificate : rules.Rule A B) : FamEq Sig A B

/-- First-class equality certificates for ordinary HOL types.  Equality for
higher-kinded families is `FamEq`; this is its `★` fragment. -/
abbrev EqTy (Sig : Signature) [SigFamilyEquality Sig]
    {types : List Kind} (A B : Ty Sig types) :=
  FamEq Sig A B

class SigTyping (Sig : Signature) where
  HasType : {types : List Kind} → Sig .tm → Ty Sig types → Prop
  rename {source target : List Kind} {symbol : Sig .tm} {A : Ty Sig source}
    (ρ : TyRen source target) : HasType symbol A → HasType symbol (renameTypes ρ A)
  instantiate {source target : List Kind} {symbol : Sig .tm} {A : Ty Sig source}
    (σ : TySub Sig source target) :
    HasType symbol A → HasType symbol (instantiateTypes σ A)

inductive Classification (Sig : Signature) (types : List Kind) : HolSort → Type u where
  | kind {kind : Kind} : Classification Sig types (.kind kind)
  | tm (type : Ty Sig types) : Classification Sig types .tm

inductive Checks {Sig : Signature} [SigTyping Sig] : {types : List Kind} →
    {sort : HolSort} → {depth : Nat} → BoundCtx Sig types depth →
    Expr Sig types sort depth → Classification Sig types sort → Prop where
  | boolTy : Checks emptyBound .boolTy .kind
  | arr : Checks emptyBound A .kind → Checks emptyBound B .kind →
      Checks emptyBound (.arr A B) .kind
  | tyApp : Checks emptyBound F .kind → Checks emptyBound A .kind →
      Checks emptyBound (.tyApp F A) .kind
  | tyLam : Checks (types := kind :: types) emptyBound body .kind →
      Checks (types := types) emptyBound (.tyLam body) .kind
  | tyBv (v : TyVar types kind) : Checks emptyBound (.tyBv v) .kind
  | sub : Checks emptyBound A .kind →
      Checks (extendBound A emptyBound) p (.tm .boolTy) →
      Checks emptyBound (.sub A p) .kind
  | tyExists : Checks (types := .star :: types) emptyBound p (.tm .boolTy) →
      Checks (types := types) Γ (.tyExists p) (.tm .boolTy)
  | model : Checks (types := .star :: types) emptyBound p (.tm .boolTy) →
      Checks (types := types) emptyBound (.model p) .kind
  | primFam (symbol : Sig (.kind kind)) : Checks emptyBound (.primFam symbol) .kind
  | primTm (rule : SigTyping.HasType symbol A) :
      Checks Γ (.primTm symbol) (.tm A)
  | bv (hA : Checks emptyBound A .kind) (lookup : Γ i = A) :
      Checks Γ (.bv i) (.tm A)
  | fv (name : Nat) (hA : Checks emptyBound A .kind) : Checks Γ (.fv name A) (.tm A)
  | app : Checks Γ f (.tm (.arr A B)) → Checks Γ x (.tm A) →
      Checks Γ (.app f x) (.tm B)
  | lam (body : Tm Sig types (depth + 1)) (hA : Checks emptyBound A .kind) :
      Checks (extendBound A Γ) body (.tm B) → Checks Γ (.lam A body) (.tm (.arr A B))
  | bool (value : Bool) : Checks Γ (.bool value) (.tm .boolTy)
  | eq (hA : Checks emptyBound A .kind) : Checks Γ x (.tm A) → Checks Γ y (.tm A) →
      Checks Γ (.eq A x y) (.tm .boolTy)
  | eps (hA : Checks emptyBound A .kind) : Checks Γ p (.tm (.arr A .boolTy)) →
      Checks Γ (.eps A p) (.tm A)
  | abs (hA : Checks emptyBound A .kind)
      (hp : Checks (extendBound A emptyBound) p (.tm .boolTy)) :
      Checks Γ x (.tm A) → Checks Γ (.abs A p x) (.tm (.sub A p))
  | rep (hA : Checks emptyBound A .kind)
      (hp : Checks (extendBound A emptyBound) p (.tm .boolTy)) :
      Checks Γ x (.tm (.sub A p)) → Checks Γ (.rep A p x) (.tm A)

abbrev Kinded {Sig : Signature} [SigTyping Sig] (A : Fam Sig types kind) : Prop :=
  Checks emptyBound A .kind

abbrev HasType {Sig : Signature} [SigTyping Sig] (Γ : BoundCtx Sig types depth)
    (term : Tm Sig types depth) (A : Ty Sig types) : Prop := Checks Γ term (.tm A)

/-- Typing modulo type-family definitional equality.  `HasType` remains the
syntax-directed judgment used by the checker; this is its conversion closure. -/
inductive HasTypeDefEq {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig] :
    {types : List Kind} →
    {depth : Nat} → BoundCtx Sig types depth → Tm Sig types depth → Ty Sig types → Prop where
  | exact (typing : HasType Γ term A) : HasTypeDefEq Γ term A
  | app : HasTypeDefEq Γ f (.arr A B) → HasTypeDefEq Γ x A →
      HasTypeDefEq Γ (.app f x) B
  | lam (body : Tm Sig types (depth + 1)) (hA : Kinded A) :
      HasTypeDefEq (extendBound A Γ) body B →
      HasTypeDefEq Γ (.lam A body) (.arr A B)
  | eq (hA : Kinded A) : HasTypeDefEq Γ x A → HasTypeDefEq Γ y A →
      HasTypeDefEq Γ (.eq A x y) .boolTy
  | eps (hA : Kinded A) : HasTypeDefEq Γ p (.arr A .boolTy) →
      HasTypeDefEq Γ (.eps A p) A
  | abs (hA : Kinded A) (hp : HasType (extendBound A emptyBound) p .boolTy) :
      HasTypeDefEq Γ x A → HasTypeDefEq Γ (.abs A p x) (.sub A p)
  | rep (hA : Kinded A) (hp : HasType (extendBound A emptyBound) p .boolTy) :
      HasTypeDefEq Γ x (.sub A p) → HasTypeDefEq Γ (.rep A p x) A
  | tyExists : HasTypeDefEq (types := .star :: types) emptyBound p .boolTy →
      HasTypeDefEq (types := types) Γ (.tyExists p) .boolTy
  | conv (typing : HasTypeDefEq Γ term A) (hB : Kinded B)
      (conversion : FamEq Sig A B) : HasTypeDefEq Γ term B

namespace HasTypeDefEq

variable {Sig : Signature} [SigTyping Sig] [SigFamilyEquality Sig]
  {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {term : Tm Sig types depth} {A B : Ty Sig types}

theorem ofHasType (typing : HasType Γ term A) : HasTypeDefEq Γ term A := .exact typing

theorem convert (typing : HasTypeDefEq Γ term A) (hB : Kinded B)
    (conversion : FamEq Sig A B) : HasTypeDefEq Γ term B := .conv typing hB conversion

end HasTypeDefEq

def renameBoundCtx (ρ : TyRen source target) (Γ : BoundCtx Sig source depth) :
    BoundCtx Sig target depth := fun i => renameTypes ρ (Γ i)

@[simp] theorem renameBoundCtx_empty (ρ : TyRen source target) :
    renameBoundCtx (Sig := Sig) ρ (emptyBound : BoundCtx Sig source 0) =
      (emptyBound : BoundCtx Sig target 0) :=
  by
    funext i
    exact Fin.elim0 i

@[simp] theorem renameBoundCtx_extend (ρ : TyRen source target)
    (A : Ty Sig source) (Γ : BoundCtx Sig source depth) :
    renameBoundCtx ρ (extendBound A Γ) =
      extendBound (renameTypes ρ A) (renameBoundCtx ρ Γ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def Classification.rename (ρ : TyRen source target) :
    Classification Sig source sort → Classification Sig target sort
  | .kind => .kind
  | .tm A => .tm (renameTypes ρ A)

attribute [simp] renameTypes Classification.rename

def FamEq.renameTypes [SigFamilyEquality Sig] {A B : Fam Sig source kind}
    (equality : FamEq Sig A B) (ρ : TyRen source target) :
    FamEq Sig (renameTypes ρ A) (renameTypes ρ B) := .rename equality ρ

theorem Checks.renameTypes {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig source depth} {expression : Expr Sig source sort depth}
    {classification : Classification Sig source sort}
    (checking : Checks Γ expression classification) (ρ : TyRen source target) :
    Checks (renameBoundCtx ρ Γ) (HolE.renameTypes ρ expression)
      (classification.rename ρ) := by
  induction checking generalizing target with
  | boolTy =>
      simpa [Classification.rename] using (Checks.boolTy (Sig := Sig))
  | arr _ _ ihA ihB => simpa [Classification.rename] using
      (Checks.arr (by simpa using ihA ρ) (by simpa using ihB ρ))
  | tyApp _ _ ihF ihA => simpa [Classification.rename] using
      (Checks.tyApp (by simpa using ihF ρ) (by simpa using ihA ρ))
  | tyLam body ih => simpa [Classification.rename] using
      (Checks.tyLam (by simpa using ih (liftTyRen ρ)))
  | tyBv v => simpa [Classification.rename] using
      (Checks.tyBv (Sig := Sig) (ρ v))
  | sub _ _ ihA ihp => simpa [Classification.rename, extendBound] using
      (Checks.sub (by simpa using ihA ρ) (by simpa using ihp ρ))
  | tyExists hp ihp =>
      simpa [Classification.rename] using
        (Checks.tyExists (by simpa using (ihp (liftTyRen ρ))))
  | model hp ihp => simpa [Classification.rename] using
      (Checks.model (by simpa using ihp (liftTyRen ρ)))
  | primFam symbol =>
      simpa [Classification.rename] using (Checks.primFam (Sig := Sig) symbol)
  | primTm rule => exact .primTm (SigTyping.rename ρ rule)
  | bv hA lookup ihA =>
      exact .bv (by simpa using ihA ρ)
        (congrArg (HolE.renameTypes ρ) lookup)
  | fv name hA ihA => exact .fv name (by simpa using ihA ρ)
  | app hf hx ihf ihx => exact .app (ihf ρ) (ihx ρ)
  | lam body hA hb ihA ihb =>
      exact .lam _ (by simpa using ihA ρ) (by simpa using ihb ρ)
  | bool value => exact .bool value
  | eq hA hx hy ihA ihx ihy => exact .eq (by simpa using ihA ρ) (ihx ρ) (ihy ρ)
  | eps hA hp ihA ihp => exact .eps (by simpa using ihA ρ) (ihp ρ)
  | abs hA hp hx ihA ihp ihx =>
      exact .abs (by simpa using ihA ρ) (by simpa using ihp ρ) (ihx ρ)
  | rep hA hp hx ihA ihp ihx =>
      exact .rep (by simpa using ihA ρ) (by simpa using ihp ρ) (ihx ρ)

theorem Kinded.weakenTypes {Sig : Signature} [SigTyping Sig]
    {A : Fam Sig types familyKind} (checking : Kinded A) :
    Kinded (weakenTypes (kind := kind) A) := by
  let ρ : TyRen types (kind :: types) := fun v => .succ v
  change Kinded (renameTypes ρ A)
  simpa only [renameBoundCtx_empty, Classification.rename] using checking.renameTypes ρ

def WellFormedTySub {Sig : Signature} [SigTyping Sig]
    (σ : TySub Sig source target) : Prop :=
  ∀ {kind} (v : TyVar source kind), Kinded (σ v)

theorem WellFormedTySub.lift {Sig : Signature} [SigTyping Sig]
    {σ : TySub Sig source target} (wellFormed : WellFormedTySub σ) :
    WellFormedTySub (liftTySub (kind := kind) σ) := by
  intro resultKind v
  cases v with
  | zero => exact .tyBv .zero
  | succ v => exact (wellFormed v).weakenTypes

def instantiateBoundCtx (σ : TySub Sig source target) (Γ : BoundCtx Sig source depth) :
    BoundCtx Sig target depth := fun i => instantiateTypes σ (Γ i)

@[simp] theorem instantiateBoundCtx_empty (σ : TySub Sig source target) :
    instantiateBoundCtx (Sig := Sig) σ (emptyBound : BoundCtx Sig source 0) =
      (emptyBound : BoundCtx Sig target 0) := by
  funext i
  exact Fin.elim0 i

@[simp] theorem instantiateBoundCtx_extend (σ : TySub Sig source target)
    (A : Ty Sig source) (Γ : BoundCtx Sig source depth) :
    instantiateBoundCtx σ (extendBound A Γ) =
      extendBound (instantiateTypes σ A) (instantiateBoundCtx σ Γ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def Classification.instantiate (σ : TySub Sig source target) :
    Classification Sig source sort → Classification Sig target sort
  | .kind => .kind
  | .tm A => .tm (instantiateTypes σ A)

attribute [simp] instantiateTypes Classification.instantiate

def FamEq.instantiateTypes [SigFamilyEquality Sig] {A B : Fam Sig source kind}
    (equality : FamEq Sig A B)
    (σ : TySub Sig source target) :
    FamEq Sig (instantiateTypes σ A) (instantiateTypes σ B) := .instantiate equality σ

theorem Checks.instantiateTypes {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig source depth} {expression : Expr Sig source sort depth}
    {classification : Classification Sig source sort}
    (checking : Checks Γ expression classification) {σ : TySub Sig source target}
    (wellFormed : WellFormedTySub σ) :
    Checks (instantiateBoundCtx σ Γ) (HolE.instantiateTypes σ expression)
      (classification.instantiate σ) := by
  induction checking generalizing target with
  | boolTy => simpa using (Checks.boolTy (Sig := Sig))
  | arr _ _ ihA ihB => simpa using (.arr (by simpa using ihA wellFormed)
      (by simpa using ihB wellFormed))
  | tyApp _ _ ihF ihA => simpa using (.tyApp (by simpa using ihF wellFormed)
      (by simpa using ihA wellFormed))
  | tyLam body ih => simpa using (.tyLam (by simpa using ih wellFormed.lift))
  | tyBv v => simpa using wellFormed v
  | sub _ _ ihA ihp => simpa using (.sub (by simpa using ihA wellFormed)
      (by simpa using ihp wellFormed))
  | tyExists hp ihp =>
      simpa using (Checks.tyExists (by simpa using (ihp wellFormed.lift)))
  | model hp ihp => simpa using (.model (by simpa using ihp wellFormed.lift))
  | primFam symbol => simpa using (Checks.primFam (Sig := Sig) symbol)
  | primTm rule => exact .primTm (SigTyping.instantiate σ rule)
  | bv hA lookup ihA => exact (.bv (by simpa using ihA wellFormed)
      (congrArg (HolE.instantiateTypes σ) lookup))
  | fv name hA ihA => exact .fv name (by simpa using ihA wellFormed)
  | app hf hx ihf ihx => exact .app (ihf wellFormed) (ihx wellFormed)
  | lam body hA hb ihA ihb => exact (.lam _ (by simpa using ihA wellFormed)
      (by simpa using ihb wellFormed))
  | bool value => exact .bool value
  | eq hA hx hy ihA ihx ihy => exact (.eq (by simpa using ihA wellFormed)
      (ihx wellFormed) (ihy wellFormed))
  | eps hA hp ihA ihp => exact .eps (by simpa using ihA wellFormed) (ihp wellFormed)
  | abs hA hp hx ihA ihp ihx => exact (.abs (by simpa using ihA wellFormed)
      (by simpa using ihp wellFormed) (ihx wellFormed))
  | rep hA hp hx ihA ihp ihx => exact (.rep (by simpa using ihA wellFormed)
      (by simpa using ihp wellFormed) (ihx wellFormed))

theorem Kinded.openType {Sig : Signature} [SigTyping Sig]
    {body : Fam Sig (kind :: types) resultKind} (bodyKinded : Kinded body)
    {argument : Fam Sig types kind} (argumentKinded : Kinded argument) :
    Kinded (openType body argument) := by
  let σ : TySub Sig (kind :: types) types := headTySub argument
  change Kinded (instantiateTypes σ body)
  have wellFormed : WellFormedTySub σ := by
    intro variableKind v
    cases v with
    | zero => exact argumentKinded
    | succ v => exact .tyBv v
  simpa using bodyKinded.instantiateTypes wellFormed

/-- The crucial admissible construction: ordinary subtype formation under a
type-family lambda yields a well-kinded family. -/
theorem subFam_kinded {Sig : Signature} [SigTyping Sig] {kind : Kind}
    {carrier : Fam Sig types (.arr kind .star)}
    {predicate : Tm Sig (kind :: types) 1}
    (carrierKinded : Kinded carrier)
    (predicateTyped : HasType
      (extendBound (.tyApp (weakenTypes (kind := kind) carrier) (.tyBv .zero)) emptyBound)
      predicate .boolTy) :
    Kinded (subFam carrier predicate) := by
  exact .tyLam (.sub (.tyApp carrierKinded.weakenTypes (.tyBv .zero)) predicateTyped)

/-! ## Embedding of the closed signature kernel -/

def embed : {sort : HolSort} → {depth : Nat} → Nucleus.Hol.Expr Sig sort depth →
    Expr Sig [] sort depth
  | _, _, .boolTy => .boolTy
  | _, _, .arr A B => .arr (embed A) (embed B)
  | _, _, .tyApp F A => .tyApp (embed F) (embed A)
  | _, _, .sub A p => .sub (embed A) (embed p)
  | _, _, .primFam symbol => .primFam symbol
  | _, _, .primTm symbol => .primTm symbol
  | _, _, .bv index => .bv index
  | _, _, .fv name A => .fv name (embed A)
  | _, _, .app f x => .app (embed f) (embed x)
  | _, _, .lam A body => .lam (embed A) (embed body)
  | _, _, .bool value => .bool value
  | _, _, .eq A x y => .eq (embed A) (embed x) (embed y)
  | _, _, .eps A p => .eps (embed A) (embed p)
  | _, _, .abs A p x => .abs (embed A) (embed p) (embed x)
  | _, _, .rep A p x => .rep (embed A) (embed p) (embed x)

def embedBoundCtx (Γ : Nucleus.Hol.BoundCtx Sig depth) : BoundCtx Sig [] depth :=
  fun i => embed (Γ i)

end Nucleus.HolE
