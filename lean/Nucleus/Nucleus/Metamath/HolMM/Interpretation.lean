import Nucleus.Hol.Soundness

/-!
# Interpreting `hol.mm` into the pointed-set HOL semantics

`hol.mm` is Metamath's own formalisation of higher-order logic. This file gives
the *interpretation* half of a soundness argument for it: a translation of
`hol.mm`'s type and term grammar into `Nucleus.Hol`'s intrinsically scoped
syntax, together with the one substantive semantic lemma the translation needs.
`Nucleus.Metamath.HolMM.Axioms` then checks `hol.mm`'s axioms against it.

## What is being interpreted, and what is not

`hol.mm` terms are *flat symbol strings*; `Nucleus.Metamath.Expr` models them
faithfully. This file starts one level up, from an **abstract syntax tree**
(`Term`), and does not model parsing. Bridging the two needs unique readability
for `hol.mm`'s grammar — that every derivable `term`-typecode expression is the
printing of exactly one `Term` — which is *not* proved here. See the module
documentation of `Nucleus.Metamath.HolMM` for the precise statement of that gap.

Two deliberate departures from the surface syntax are recorded in `Term`:

* `hol.mm`'s `=` (`ke`) and `@` (`tat`) are *polymorphic constants*: `ax-weq`
  gives `|- = : ( al -> ( al -> bool ) )` for every type `al`. `Nucleus.Hol` has
  no polymorphism, so `Term.eq` and `Term.choose` carry the type they are used
  at. Equivalently, the interpretation is defined on typing derivations rather
  than on raw terms. This is what makes `Typ` recoverable from a `Term`
  (`elabTm_type_unique`), and it is exactly the hypothesis `ax-eqtypi` needs.
* Variables are identified by the pair *(name, type)*, matching every standard
  presentation of HOL. `hol.mm` writes the type at each occurrence (`tv`), so
  this is the reading its syntax suggests — but it is *not* the reading
  `ax-hbl1` demands. See `Nucleus.Metamath.HolMM.Axioms` for the counterexample.

## The shape of the interpretation

`elabTm ctx t` walks a `Term` under a list of binders `ctx`, returning the
`hol.mm` type it synthesises together with a `Nucleus.Hol` term of that type.
Occurrences bound by `ctx` become de Bruijn indices; the rest become
`Nucleus.Hol` free variables `.fv name type`. So a `hol.mm` judgment
`|- A : al` becomes `elabTm [] A = some (al, a)`, and a sequent `|- R |= A`
becomes semantic entailment between the interpretations of `R` and `A`.

`elabEval_iff` is the technical heart: the value of an interpreted term does not
depend on *which* binders were used to reach it, only on the environment. It is
what makes `ax-beta`, `ax-17`, `ax-distrc`, `ax-distrl` and `ax-leq` provable,
and it is stated over two elaboration contexts and two free environments at once
precisely because those axioms compare a term elaborated under a binder with the
same term elaborated without it.

This file leaves nothing unproved.
-/

namespace Nucleus.Metamath.HolMM

open Nucleus.Hol

/-! ## The target signature -/

/-- The `Nucleus.Hol` signature `hol.mm` is interpreted into: one primitive type
family, `ind`. `bool` and `->` are already primitive in `Nucleus.Hol`. -/
inductive IndSig : HolSort → Type where
  /-- The type of individuals. -/
  | ind : IndSig (.kind .star)

instance : SigTyping IndSig where
  HasType symbol := nomatch symbol

/-- The signature has no term symbols, so its primitive typing is vacuously
functional. -/
private theorem indSig_hasType_iff {symbol : IndSig .tm} {A : Ty IndSig} :
    SigTyping.HasType symbol A ↔ A = (nomatch symbol : Ty IndSig) := nomatch symbol

instance : FunctionalSigTyping IndSig where
  typeOf symbol := nomatch symbol
  hasType_iff := indSig_hasType_iff

/-- `ind` denotes the natural numbers, pointed at zero. Any infinite pointed set
would do; `Nat` is chosen so that `ax-inf` is at least *true* in this model, even
though it is not proved here. -/
instance : FamilyModel IndSig where
  denote symbol := match symbol with | .ind => ⟨Nat, 0⟩

instance : TermModel IndSig where
  denote symbol := nomatch symbol

/-- `Nucleus.Hol` types over the interpretation's signature. -/
abbrev HTy := Nucleus.Hol.Ty IndSig

/-- `Nucleus.Hol` terms over the interpretation's signature. -/
abbrev HTm (depth : Nat) := Nucleus.Hol.Tm IndSig depth

/-! ## `hol.mm` abstract syntax -/

/-- A ground `hol.mm` type: `bool`, `ind`, and function types. Type *variables*
(`al`, `be`, …) are metavariables of the Metamath schema, so a soundness
statement quantifies over `Typ` rather than representing them. -/
inductive Typ where
  /-- `bool`. -/
  | bool
  /-- `ind`. -/
  | ind
  /-- `( al -> be )`. -/
  | arr (domain codomain : Typ)
  deriving DecidableEq, Repr

/-- The `Nucleus.Hol` type a `hol.mm` type denotes. -/
def Typ.denote : Typ → HTy
  | .bool => .boolTy
  | .ind => .primFam .ind
  | .arr domain codomain => .arr domain.denote codomain.denote

/-- Every interpreted type is a well-formed `Nucleus.Hol` type. -/
theorem Typ.denote_kinded : (τ : Typ) → Kinded τ.denote
  | .bool => .boolTy
  | .ind => .primFam _
  | .arr domain codomain => .arr domain.denote_kinded codomain.denote_kinded

/-- Distinct `hol.mm` types denote distinct `Nucleus.Hol` types. Variable
identity is by (name, type) pair, so this is what keeps distinct variables
distinct. -/
theorem Typ.denote_injective : Function.Injective Typ.denote := by
  intro σ τ equal
  induction σ generalizing τ with
  | bool => cases τ <;> first | rfl | simp [Typ.denote] at equal
  | ind => cases τ <;> first | rfl | simp [Typ.denote] at equal
  | arr domain codomain ihDomain ihCodomain =>
      cases τ with
      | bool => simp [Typ.denote] at equal
      | ind => simp [Typ.denote] at equal
      | arr domain' codomain' =>
          simp only [Typ.denote, Expr.arr.injEq] at equal
          rw [ihDomain equal.1, ihCodomain equal.2]

/-- A ground `hol.mm` term.

`br` is `hol.mm`'s infix form `[ A F B ]` (`kbr`), and `ctx` is its context
comma `( A , B )` (`kct`). Both are kept as separate constructors so that
`df-ov` and the context axioms are statements about *this* syntax rather than
about a paraphrase of it. -/
inductive Term where
  /-- `x : al`, a typed variable occurrence (`tv`). -/
  | var (name : Nat) (type : Typ)
  /-- `( F T )`, a combination (`kc`). -/
  | app (function argument : Term)
  /-- `\ x : al . T`, a lambda abstraction (`kl`). -/
  | lam (name : Nat) (type : Typ) (body : Term)
  /-- `=` (`ke`), annotated with the type it is used at. -/
  | eq (type : Typ)
  /-- `T.` (`kt`). -/
  | tru
  /-- `( A , B )`, the context comma (`kct`). -/
  | ctx (left right : Term)
  /-- `[ A F B ]`, the infix form (`kbr`). -/
  | br (left oper right : Term)
  /-- `@` (`tat`), annotated with the type it is used at. -/
  | choose (type : Typ)
  deriving DecidableEq, Repr

/-- The (name, type) pairs occurring free in a term.

Metamath's `$d x A` is *stronger* than `x` not occurring free: it forbids `x`
from occurring in the symbol string of `A` at all, bound occurrences included.
Every theorem below that needs a `$d` assumes only the weaker
`∀ τ, (x, τ) ∉ freeVars A`, so the theorems are stronger than `hol.mm` needs. -/
def freeVars : Term → List (Nat × Typ)
  | .var name type => [(name, type)]
  | .app function argument => freeVars function ++ freeVars argument
  | .lam name type body => (freeVars body).filter (fun p => p ≠ (name, type))
  | .eq _ | .tru | .choose _ => []
  | .ctx left right => freeVars left ++ freeVars right
  | .br left oper right => freeVars left ++ freeVars oper ++ freeVars right

/-! ## Encoded constants

`Nucleus.Hol` has no conjunction and no polymorphic equality, so `hol.mm`'s
context comma and its `=` and `@` constants are interpreted by encodings.
-/

/-- `bool -> bool -> bool`, the type of the selector used to encode conjunction. -/
def pairTy : HTy := .arr .boolTy (.arr .boolTy .boolTy)

/-- `pairTy` is a well-formed type. -/
theorem pairTy_kinded : Kinded pairTy := .arr .boolTy (.arr .boolTy .boolTy)

/-- Conjunction, encoded as `(λ f. f p q) = (λ f. f ⊤ ⊤)`.

This is the standard Church encoding, and it is forced: over `bool` the only
operations `Nucleus.Hol` supplies without going to a higher type are equality
and the constants, and those generate exactly the affine Boolean functions,
which do not include conjunction. -/
def conj {depth : Nat} (p q : HTm depth) : HTm depth :=
  .eq (.arr pairTy .boolTy)
    (.lam pairTy (.app (.app (.bv 0) (weaken p)) (weaken q)))
    (.lam pairTy (.app (.app (.bv 0) (.bool true)) (.bool true)))

/-- `hol.mm`'s polymorphic `=` at a fixed type: `λ x y. x = y`. -/
def eqFun (τ : Typ) (depth : Nat) : HTm depth :=
  .lam τ.denote (.lam τ.denote (.eq τ.denote (.bv (Fin.succ 0)) (.bv 0)))

/-- `hol.mm`'s indefinite descriptor `@` at a fixed type, interpreted by
`Nucleus.Hol`'s choice operator: `λ p. ε p`. -/
def chooseFun (τ : Typ) (depth : Nat) : HTm depth :=
  .lam (.arr τ.denote .boolTy) (.eps τ.denote (.bv 0))

/-! ## Elaboration -/

/-- A list of binders in scope, innermost first. -/
abbrev ElabCtx := List (Nat × Typ)

/-- The `Nucleus.Hol` bound context an elaboration context denotes. -/
def ctxTypes : (ctx : ElabCtx) → BoundCtx IndSig ctx.length
  | [] => emptyBound
  | (_, τ) :: rest => extendBound τ.denote (ctxTypes rest)

/-- The de Bruijn index of the innermost binder for `(name, type)`, if any. -/
def ctxLookup : (ctx : ElabCtx) → Nat → Typ → Option (Fin ctx.length)
  | [], _, _ => none
  | (m, ρ) :: rest, name, type =>
      if m = name ∧ ρ = type then some 0 else (ctxLookup rest name type).map Fin.succ

/-- A looked-up binder really does carry the type it was looked up at. -/
theorem ctxLookup_types {ctx : ElabCtx} {name : Nat} {type : Typ} {i : Fin ctx.length}
    (found : ctxLookup ctx name type = some i) : ctxTypes ctx i = type.denote := by
  induction ctx with
  | nil => simp [ctxLookup] at found
  | cons head rest ih =>
      obtain ⟨m, ρ⟩ := head
      simp only [ctxLookup] at found
      split at found
      · rename_i hit
        rw [← Option.some.inj found]
        simp only [ctxTypes, extendBound, Fin.cases_zero]
        exact congrArg Typ.denote hit.2
      · obtain ⟨j, hj, hij⟩ := Option.map_eq_some_iff.mp found
        subst hij
        simpa [ctxTypes, extendBound] using ih hj

/-- The interpretation of a variable occurrence: a de Bruijn index if the
occurrence is bound by `ctx`, and a `Nucleus.Hol` free variable otherwise. -/
def varTm (ctx : ElabCtx) (name : Nat) (type : Typ) : HTm ctx.length :=
  match ctxLookup ctx name type with
  | some i => .bv i
  | none => .fv name type.denote

/-- Elaborate a `hol.mm` term under a list of binders, synthesising its type.

`none` means the term is not well typed at all, which for a `hol.mm` term means
no `|- A : al` is derivable for it. -/
def elabTm : (ctx : ElabCtx) → Term → Option (Typ × HTm ctx.length)
  | ctx, .var name type => some (type, varTm ctx name type)
  | _, .tru => some (.bool, .bool true)
  | ctx, .eq type => some (.arr type (.arr type .bool), eqFun type ctx.length)
  | ctx, .choose type => some (.arr (.arr type .bool) type, chooseFun type ctx.length)
  | ctx, .app function argument =>
      (elabTm ctx function).bind fun f => (elabTm ctx argument).bind fun a =>
        match f.1 with
        | .arr domain codomain =>
            if domain = a.1 then some (codomain, .app f.2 a.2) else none
        | _ => none
  | ctx, .lam name type body =>
      (elabTm ((name, type) :: ctx) body).map fun b => (.arr type b.1, .lam type.denote b.2)
  | ctx, .ctx left right =>
      (elabTm ctx left).bind fun l => (elabTm ctx right).bind fun r =>
        if l.1 = .bool ∧ r.1 = .bool then some (.bool, conj l.2 r.2) else none
  | ctx, .br left oper right =>
      (elabTm ctx oper).bind fun f => (elabTm ctx left).bind fun l =>
        (elabTm ctx right).bind fun r =>
          match f.1 with
          | .arr domain (.arr domain' codomain) =>
              if domain = l.1 ∧ domain' = r.1 then
                some (codomain, .app (.app f.2 l.2) r.2)
              else none
          | _ => none

/-! ### Elaboration: introduction and inversion -/

/-- Elaboration of a variable occurrence. -/
theorem elabTm_var {ctx : ElabCtx} {name : Nat} {type : Typ} :
    elabTm ctx (.var name type) = some (type, varTm ctx name type) := rfl

/-- Inversion for the elaboration of a variable occurrence. -/
theorem elabTm_var_inv {ctx : ElabCtx} {name : Nat} {type σ : Typ} {t : HTm ctx.length}
    (h : elabTm ctx (.var name type) = some (σ, t)) : σ = type ∧ t = varTm ctx name type := by
  simp only [elabTm, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- Elaboration of a combination. -/
theorem elabTm_app {ctx : ElabCtx} {function argument : Term} {α σ : Typ}
    {f a : HTm ctx.length}
    (hf : elabTm ctx function = some (.arr α σ, f))
    (ha : elabTm ctx argument = some (α, a)) :
    elabTm ctx (.app function argument) = some (σ, .app f a) := by
  simp [elabTm, hf, ha]

/-- Inversion for the elaboration of a combination. -/
theorem elabTm_app_inv {ctx : ElabCtx} {function argument : Term} {σ : Typ}
    {t : HTm ctx.length} (h : elabTm ctx (.app function argument) = some (σ, t)) :
    ∃ (α : Typ) (f a : HTm ctx.length),
      elabTm ctx function = some (.arr α σ, f) ∧ elabTm ctx argument = some (α, a) ∧
        t = .app f a := by
  simp only [elabTm, Option.bind_eq_some_iff] at h
  obtain ⟨fp, hf, ap, ha, hrest⟩ := h
  obtain ⟨φ, f⟩ := fp
  obtain ⟨α, a⟩ := ap
  cases φ with
  | bool => simp at hrest
  | ind => simp at hrest
  | arr domain codomain =>
      simp only at hrest
      split at hrest
      · rename_i equal
        subst equal
        simp only [Option.some.injEq, Prod.mk.injEq] at hrest
        exact ⟨domain, f, a, hrest.1 ▸ hf, ha, hrest.2.symm⟩
      · simp at hrest

/-- Elaboration of a lambda abstraction. -/
theorem elabTm_lam {ctx : ElabCtx} {name : Nat} {type σ : Typ} {body : Term}
    {b : HTm ((name, type) :: ctx).length}
    (hb : elabTm ((name, type) :: ctx) body = some (σ, b)) :
    elabTm ctx (.lam name type body) = some (.arr type σ, .lam type.denote b) := by
  simp [elabTm, hb]

/-- Inversion for the elaboration of a lambda abstraction. -/
theorem elabTm_lam_inv {ctx : ElabCtx} {name : Nat} {type : Typ} {body : Term} {σ : Typ}
    {t : HTm ctx.length} (h : elabTm ctx (.lam name type body) = some (σ, t)) :
    ∃ (τ : Typ) (b : HTm ((name, type) :: ctx).length),
      elabTm ((name, type) :: ctx) body = some (τ, b) ∧ σ = .arr type τ ∧
        t = .lam type.denote b := by
  simp only [elabTm, Option.map_eq_some_iff] at h
  obtain ⟨⟨τ, b⟩, hb, hrest⟩ := h
  simp only [Prod.mk.injEq] at hrest
  exact ⟨τ, b, hb, hrest.1.symm, hrest.2.symm⟩

/-- Elaboration of a context comma. -/
theorem elabTm_ctx {ctx : ElabCtx} {left right : Term} {l r : HTm ctx.length}
    (hl : elabTm ctx left = some (.bool, l)) (hr : elabTm ctx right = some (.bool, r)) :
    elabTm ctx (.ctx left right) = some (.bool, conj l r) := by
  simp [elabTm, hl, hr]

/-- Inversion for the elaboration of a context comma. -/
theorem elabTm_ctx_inv {ctx : ElabCtx} {left right : Term} {σ : Typ} {t : HTm ctx.length}
    (h : elabTm ctx (.ctx left right) = some (σ, t)) :
    ∃ l r : HTm ctx.length, elabTm ctx left = some (.bool, l) ∧
      elabTm ctx right = some (.bool, r) ∧ σ = .bool ∧ t = conj l r := by
  simp only [elabTm, Option.bind_eq_some_iff] at h
  obtain ⟨⟨σ₁, l⟩, hl, ⟨σ₂, r⟩, hr, hrest⟩ := h
  split at hrest
  · rename_i both
    simp only at both
    obtain ⟨rfl, rfl⟩ := both
    simp only [Option.some.injEq, Prod.mk.injEq] at hrest
    exact ⟨l, r, hl, hr, hrest.1.symm, hrest.2.symm⟩
  · simp at hrest

/-- Elaboration of the infix form: it is exactly the elaboration of the
corresponding curried application, which is what `df-ov` asserts. -/
theorem elabTm_br {ctx : ElabCtx} {left oper right : Term} {α β σ : Typ}
    {l f r : HTm ctx.length}
    (hf : elabTm ctx oper = some (.arr α (.arr β σ), f))
    (hl : elabTm ctx left = some (α, l)) (hr : elabTm ctx right = some (β, r)) :
    elabTm ctx (.br left oper right) = some (σ, .app (.app f l) r) := by
  simp [elabTm, hf, hl, hr]

/-- Inversion for the elaboration of the infix form. -/
theorem elabTm_br_inv {ctx : ElabCtx} {left oper right : Term} {σ : Typ}
    {t : HTm ctx.length} (h : elabTm ctx (.br left oper right) = some (σ, t)) :
    ∃ (α β : Typ) (l f r : HTm ctx.length),
      elabTm ctx oper = some (.arr α (.arr β σ), f) ∧ elabTm ctx left = some (α, l) ∧
        elabTm ctx right = some (β, r) ∧ t = .app (.app f l) r := by
  simp only [elabTm, Option.bind_eq_some_iff] at h
  obtain ⟨⟨φ, f⟩, hf, ⟨α, l⟩, hl, ⟨β, r⟩, hr, hrest⟩ := h
  cases φ with
  | bool => simp at hrest
  | ind => simp at hrest
  | arr domain codomain =>
      cases codomain with
      | bool => simp at hrest
      | ind => simp at hrest
      | arr domain' codomain' =>
          simp only at hrest
          split at hrest
          · rename_i both
            obtain ⟨rfl, rfl⟩ := both
            simp only [Option.some.injEq, Prod.mk.injEq] at hrest
            exact ⟨domain, domain', l, f, r, hrest.1 ▸ hf, hl, hr, hrest.2.symm⟩
          · simp at hrest

/-! ### Elaboration produces well-typed terms -/

/-- Weakening for typing, obtained from the semantics rather than by a separate
induction: a well-typed term evaluates, evaluation is stable under renaming, and
evaluation implies typing. -/
theorem hasType_weaken {depth : Nat} {Γ : BoundCtx IndSig depth} {t : HTm depth}
    {A B : HTy} (typing : HasType Γ t A) : HasType (extendBound B Γ) (weaken t) A := by
  obtain ⟨value, evaluation⟩ := typing.eval_exists defaultFreeEnv (fun _ C _ => defaultValue C)
  exact (evaluation.rename (Γ' := extendBound B Γ) (ρ := Fin.succ)
    (target := fun _ C _ => defaultValue C) (fun _ => rfl) (by intro i C lookup; rfl)).typing

/-- The interpretation of a variable occurrence is well typed. -/
theorem varTm_hasType (ctx : ElabCtx) (name : Nat) (type : Typ) :
    HasType (ctxTypes ctx) (varTm ctx name type) type.denote := by
  unfold varTm
  split
  · rename_i i found
    exact .bv type.denote_kinded (ctxLookup_types found)
  · exact .fv name type.denote_kinded

/-- The interpretation of `=` is well typed. -/
theorem eqFun_hasType (τ : Typ) {depth : Nat} (Γ : BoundCtx IndSig depth) :
    HasType Γ (eqFun τ depth) (.arr τ.denote (.arr τ.denote .boolTy)) := by
  refine .lam _ τ.denote_kinded (.lam _ τ.denote_kinded
    (.eq τ.denote_kinded (.bv τ.denote_kinded ?_) (.bv τ.denote_kinded ?_)))
  · simp only [extendBound, Fin.cases_succ, Fin.cases_zero]
  · simp only [extendBound, Fin.cases_zero]

/-- The interpretation of `@` is well typed. -/
theorem chooseFun_hasType (τ : Typ) {depth : Nat} (Γ : BoundCtx IndSig depth) :
    HasType Γ (chooseFun τ depth) (.arr (.arr τ.denote .boolTy) τ.denote) := by
  refine .lam _ (.arr τ.denote_kinded .boolTy)
    (.eps τ.denote_kinded (.bv (.arr τ.denote_kinded .boolTy) ?_))
  simp [extendBound]

/-- The encoded conjunction is well typed. -/
theorem conj_hasType {depth : Nat} {Γ : BoundCtx IndSig depth} {p q : HTm depth}
    (hp : HasType Γ p .boolTy) (hq : HasType Γ q .boolTy) :
    HasType Γ (conj p q) .boolTy := by
  have selector : HasType (extendBound pairTy Γ) (.bv 0) pairTy :=
    .bv pairTy_kinded (by simp [extendBound])
  exact .eq (.arr pairTy_kinded .boolTy)
    (.lam _ pairTy_kinded (.app (.app selector (hasType_weaken hp)) (hasType_weaken hq)))
    (.lam _ pairTy_kinded (.app (.app selector (.bool true)) (.bool true)))

/-- Everything the interpretation produces is a well-typed `Nucleus.Hol` term of
the synthesised type. -/
theorem elabTm_hasType : ∀ (t : Term) {ctx : ElabCtx} {σ : Typ} {a : HTm ctx.length},
    elabTm ctx t = some (σ, a) → HasType (ctxTypes ctx) a σ.denote := by
  intro t
  induction t with
  | var name type =>
      intro ctx σ a h
      obtain ⟨rfl, rfl⟩ := elabTm_var_inv h
      exact varTm_hasType ctx name _
  | tru =>
      intro ctx σ a h
      simp only [elabTm, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .bool true
  | eq type =>
      intro ctx σ a h
      simp only [elabTm, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact eqFun_hasType _ _
  | choose type =>
      intro ctx σ a h
      simp only [elabTm, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact chooseFun_hasType _ _
  | app function argument ihFunction ihArgument =>
      intro ctx σ a h
      obtain ⟨α, f, x, hf, hx, rfl⟩ := elabTm_app_inv h
      exact .app (ihFunction hf) (ihArgument hx)
  | lam name type body ihBody =>
      intro ctx σ a h
      obtain ⟨τ, b, hb, rfl, rfl⟩ := elabTm_lam_inv h
      exact .lam _ type.denote_kinded (ihBody hb)
  | ctx left right ihLeft ihRight =>
      intro ctx σ a h
      obtain ⟨l, r, hl, hr, rfl, rfl⟩ := elabTm_ctx_inv h
      exact conj_hasType (ihLeft hl) (ihRight hr)
  | br left oper right ihLeft ihOper ihRight =>
      intro ctx σ a h
      obtain ⟨α, β, l, f, r, hf, hl, hr, rfl⟩ := elabTm_br_inv h
      exact .app (.app (ihOper hf) (ihLeft hl)) (ihRight hr)

/-- Elaboration synthesises at most one type, so `hol.mm`'s typing is unique on
the annotated syntax. This is exactly the hypothesis `ax-eqtypi` needs, and it
is what the type annotations on `Term.eq` and `Term.choose` buy. -/
theorem elabTm_type_unique : ∀ (t : Term) {ctx ctx' : ElabCtx} {σ τ : Typ}
    {a : HTm ctx.length} {b : HTm ctx'.length},
    elabTm ctx t = some (σ, a) → elabTm ctx' t = some (τ, b) → σ = τ := by
  intro t
  induction t with
  | var name type =>
      intro ctx ctx' σ τ a b first second
      rw [(elabTm_var_inv first).1, (elabTm_var_inv second).1]
  | tru | eq _ | choose _ =>
      intro ctx ctx' σ τ a b first second
      simp only [elabTm, Option.some.injEq, Prod.mk.injEq] at first second
      rw [← first.1, ← second.1]
  | app function argument ihFunction _ =>
      intro ctx ctx' σ τ a b first second
      obtain ⟨α, f, x, hf, _, _⟩ := elabTm_app_inv first
      obtain ⟨α', f', x', hf', _, _⟩ := elabTm_app_inv second
      exact (Typ.arr.injEq α σ α' τ ▸ ihFunction hf hf').2
  | lam name type body ihBody =>
      intro ctx ctx' σ τ a b first second
      obtain ⟨ρ, u, hu, rfl, _⟩ := elabTm_lam_inv first
      obtain ⟨ρ', v, hv, rfl, _⟩ := elabTm_lam_inv second
      rw [ihBody hu hv]
  | ctx left right _ _ =>
      intro ctx ctx' σ τ a b first second
      obtain ⟨_, _, _, _, rfl, _⟩ := elabTm_ctx_inv first
      obtain ⟨_, _, _, _, rfl, _⟩ := elabTm_ctx_inv second
      rfl
  | br left oper right _ ihOper _ =>
      intro ctx ctx' σ τ a b first second
      obtain ⟨α, β, l, f, r, hf, _, _, _⟩ := elabTm_br_inv first
      obtain ⟨α', β', l', f', r', hf', _, _, _⟩ := elabTm_br_inv second
      have inner := (Typ.arr.injEq α (.arr β σ) α' (.arr β' τ) ▸ ihOper hf hf').2
      exact (Typ.arr.injEq β σ β' τ ▸ inner).2

/-! ## Environments -/

open Classical in
/-- Update a free-variable environment at one (name, type) pair. -/
noncomputable def updateFree (freeEnv : FreeEnv IndSig) (name : Nat) (type : Typ)
    (value : DenoteTy type.denote) : FreeEnv IndSig :=
  fun m A => if h : m = name ∧ A = type.denote then cast (congrArg DenoteTy h.2.symm) value
    else freeEnv m A

/-- An updated environment takes the new value at the updated pair. -/
@[simp] theorem updateFree_hit (freeEnv : FreeEnv IndSig) (name : Nat) (type : Typ)
    (value : DenoteTy type.denote) :
    updateFree freeEnv name type value name type.denote = value := by
  simp [updateFree]

/-- An updated environment is unchanged at every other pair. -/
theorem updateFree_miss (freeEnv : FreeEnv IndSig) {name m : Nat} {type ρ : Typ}
    (value : DenoteTy type.denote) (differs : ¬(m = name ∧ ρ = type)) :
    updateFree freeEnv name type value m ρ.denote = freeEnv m ρ.denote := by
  refine dif_neg ?_
  rintro ⟨rfl, hd⟩
  exact differs ⟨rfl, Typ.denote_injective hd⟩

/-- An elaboration context, a free environment and a bound environment *agree*
with a *logical* environment when every `hol.mm` variable is given the logical
environment's value: bound occurrences by the bound environment, free ones by
the free environment.

Splitting the logical environment off from `Eval`'s own free environment is what
makes the coherence lemma below go through: `Eval` never changes its free
environment when it goes under a binder, but the logical environment must. -/
def Agrees (ctx : ElabCtx) (logical freeEnv : FreeEnv IndSig)
    (boundEnv : BoundEnv (ctxTypes ctx)) : Prop :=
  (∀ (name : Nat) (type : Typ) (i : Fin ctx.length)
      (found : ctxLookup ctx name type = some i),
      boundEnv i type.denote (ctxLookup_types found) = logical name type.denote) ∧
  (∀ (name : Nat) (type : Typ), ctxLookup ctx name type = none →
      freeEnv name type.denote = logical name type.denote)

/-- Under no binders, the free environment *is* the logical environment. -/
theorem Agrees.nil (freeEnv : FreeEnv IndSig) (boundEnv : BoundEnv (ctxTypes [])) :
    Agrees [] freeEnv freeEnv boundEnv :=
  ⟨by intro name type i found; simp [ctxLookup] at found, by intro name type _; rfl⟩

/-- Going under a binder extends the bound and logical environments, leaving the
free environment alone — exactly what `Eval`'s lambda rule does. -/
theorem Agrees.cons {ctx : ElabCtx} {logical freeEnv : FreeEnv IndSig}
    {boundEnv : BoundEnv (ctxTypes ctx)} (agree : Agrees ctx logical freeEnv boundEnv)
    (name : Nat) (type : Typ) (value : DenoteTy type.denote) :
    Agrees ((name, type) :: ctx) (updateFree logical name type value) freeEnv
      (extendBoundEnv value boundEnv) := by
  constructor
  · intro m ρ i found
    by_cases hit : name = m ∧ type = ρ
    · obtain ⟨rfl, rfl⟩ := hit
      have zero : i = 0 := by
        simp only [ctxLookup] at found
        exact (Option.some.inj found).symm
      subst zero
      simp [extendBoundEnv]
    · have step : ∃ j, ctxLookup ctx m ρ = some j ∧ i = Fin.succ j := by
        simp only [ctxLookup, if_neg hit] at found
        obtain ⟨j, hj, hij⟩ := Option.map_eq_some_iff.mp found
        exact ⟨j, hj, hij.symm⟩
      obtain ⟨j, hj, rfl⟩ := step
      rw [updateFree_miss logical value (fun hd => hit ⟨hd.1.symm, hd.2.symm⟩)]
      simpa [extendBoundEnv] using agree.1 m ρ j hj
  · intro m ρ missing
    have hit : ¬(name = m ∧ type = ρ) := by
      intro equal
      simp [ctxLookup, equal] at missing
    simp only [ctxLookup, if_neg hit, Option.map_eq_none_iff] at missing
    rw [updateFree_miss logical value (fun hd => hit ⟨hd.1.symm, hd.2.symm⟩)]
    exact agree.2 m ρ missing

/-! ## Values of the interpreted constants -/

/-- The innermost binder evaluates to the value the environment was extended
with. -/
theorem eval_bv_zero {depth : Nat} {Γ : BoundCtx IndSig depth} {A : HTy} (hA : Kinded A)
    (freeEnv : FreeEnv IndSig) (boundEnv : BoundEnv Γ) (value : DenoteTy A) :
    Eval (extendBound A Γ) freeEnv (extendBoundEnv value boundEnv) (.bv 0) A value :=
  Eval.bv freeEnv (extendBoundEnv value boundEnv) hA
    (show extendBound A Γ 0 = A from rfl)

/-- The next binder out evaluates to the value that environment was extended
with. -/
theorem eval_bv_one {depth : Nat} {Γ : BoundCtx IndSig depth} {A B : HTy} (hA : Kinded A)
    (freeEnv : FreeEnv IndSig) (boundEnv : BoundEnv Γ) (outer : DenoteTy A)
    (inner : DenoteTy B) :
    Eval (extendBound B (extendBound A Γ)) freeEnv
      (extendBoundEnv inner (extendBoundEnv outer boundEnv)) (.bv (Fin.succ 0)) A outer :=
  Eval.bv freeEnv (extendBoundEnv inner (extendBoundEnv outer boundEnv)) hA
    (show extendBound B (extendBound A Γ) (Fin.succ 0) = A from rfl)

/-- A variable occurrence evaluates to the logical environment's value for it,
whether or not it happens to be bound: that is what `Agrees` guarantees. -/
theorem eval_varTm {ctx : ElabCtx} {name : Nat} {type : Typ}
    {logical freeEnv : FreeEnv IndSig} {boundEnv : BoundEnv (ctxTypes ctx)}
    (agree : Agrees ctx logical freeEnv boundEnv) :
    Eval (ctxTypes ctx) freeEnv boundEnv (varTm ctx name type) type.denote
      (logical name type.denote) := by
  unfold varTm
  split
  · rename_i i found
    have base := Eval.bv (Γ := ctxTypes ctx) (i := i) freeEnv boundEnv type.denote_kinded
      (ctxLookup_types found)
    rw [agree.1 name type i found] at base
    exact base
  · rename_i missing
    have base := Eval.fv name freeEnv boundEnv (A := type.denote) type.denote_kinded
    rw [agree.2 name type missing] at base
    exact base

open Classical in
/-- The value `hol.mm`'s `=` denotes at a fixed type. -/
noncomputable def eqValue (τ : Typ) :
    DenoteTy (Typ.arr τ (.arr τ .bool)).denote := fun x y => if x = y then true else false

/-- `eqValue` is `⊤` on equal arguments. -/
theorem eqValue_pos (τ : Typ) {x y : DenoteTy τ.denote} (equal : x = y) :
    eqValue τ x y = true := by
  unfold eqValue
  exact if_pos equal

/-- `eqValue` is `⊥` on distinct arguments. -/
theorem eqValue_neg (τ : Typ) {x y : DenoteTy τ.denote} (distinct : x ≠ y) :
    eqValue τ x y = false := by
  unfold eqValue
  exact if_neg distinct

/-- `=` denotes equality, in every context and environment. -/
theorem eval_eqFun {depth : Nat} {Γ : BoundCtx IndSig depth} (τ : Typ)
    (freeEnv : FreeEnv IndSig) (boundEnv : BoundEnv Γ) :
    Eval Γ freeEnv boundEnv (eqFun τ depth)
      (.arr τ.denote (.arr τ.denote .boolTy)) (eqValue τ) := by
  refine .lam τ.denote_kinded fun x => .lam τ.denote_kinded fun y => ?_
  show Eval _ _ _ _ _ (eqValue τ x y)
  by_cases equal : x = y
  · rw [eqValue_pos τ equal]
    exact .eqTrue τ.denote_kinded (eval_bv_one τ.denote_kinded freeEnv boundEnv x y)
      (eval_bv_zero τ.denote_kinded freeEnv (extendBoundEnv x boundEnv) y) equal
  · rw [eqValue_neg τ equal]
    exact .eqFalse τ.denote_kinded (eval_bv_one τ.denote_kinded freeEnv boundEnv x y)
      (eval_bv_zero τ.denote_kinded freeEnv (extendBoundEnv x boundEnv) y) equal

/-- The value `hol.mm`'s `@` denotes at a fixed type: `Nucleus.Hol`'s choice
operator. -/
noncomputable def chooseValueFun (τ : Typ) :
    DenoteTy (Typ.arr (.arr τ .bool) τ).denote := fun predicate => chooseValue τ.denote predicate

/-- `@` denotes choice, in every context and environment. -/
theorem eval_chooseFun {depth : Nat} {Γ : BoundCtx IndSig depth} (τ : Typ)
    (freeEnv : FreeEnv IndSig) (boundEnv : BoundEnv Γ) :
    Eval Γ freeEnv boundEnv (chooseFun τ depth)
      (.arr (.arr τ.denote .boolTy) τ.denote) (chooseValueFun τ) :=
  .lam (.arr τ.denote_kinded .boolTy) fun predicate =>
    .eps τ.denote_kinded
      (eval_bv_zero (.arr τ.denote_kinded .boolTy) freeEnv boundEnv predicate)

/-- The Church encoding of a pair of Booleans is the pair of `⊤`s exactly when
both components are `⊤`. This is what makes `conj` conjunction. -/
theorem conj_selector_iff (left right : Bool) :
    ((fun f : Bool → Bool → Bool => f left right) = fun f => f true true) ↔
      (left = true ∧ right = true) := by
  constructor
  · intro equal
    exact ⟨congrFun equal (fun a _ => a), congrFun equal (fun _ b => b)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The left-hand selector of `conj` evaluates to `fun f ↦ f p q`. -/
theorem eval_conj_left {depth : Nat} {Γ : BoundCtx IndSig depth} {freeEnv : FreeEnv IndSig}
    {boundEnv : BoundEnv Γ} {p q : HTm depth} {vp vq : Bool}
    (hp : Eval Γ freeEnv boundEnv p .boolTy vp) (hq : Eval Γ freeEnv boundEnv q .boolTy vq) :
    Eval Γ freeEnv boundEnv (.lam pairTy (.app (.app (.bv 0) (weaken p)) (weaken q)))
      (.arr pairTy .boolTy) (fun f => f vp vq) := by
  refine .lam pairTy_kinded fun selector => ?_
  have weakenedP : Eval (extendBound pairTy Γ) freeEnv (extendBoundEnv selector boundEnv)
      (weaken p) .boolTy vp :=
    hp.rename (ρ := Fin.succ) (target := extendBoundEnv selector boundEnv) (fun _ => rfl)
      (by intro i C lookup; rfl)
  have weakenedQ : Eval (extendBound pairTy Γ) freeEnv (extendBoundEnv selector boundEnv)
      (weaken q) .boolTy vq :=
    hq.rename (ρ := Fin.succ) (target := extendBoundEnv selector boundEnv) (fun _ => rfl)
      (by intro i C lookup; rfl)
  have inner : Eval (extendBound pairTy Γ) freeEnv (extendBoundEnv selector boundEnv)
      (.app (.bv 0) (weaken p)) (.arr .boolTy .boolTy) (selector vp) :=
    .app (eval_bv_zero pairTy_kinded freeEnv boundEnv selector) weakenedP
  have outer : Eval (extendBound pairTy Γ) freeEnv (extendBoundEnv selector boundEnv)
      (.app (.app (.bv 0) (weaken p)) (weaken q)) .boolTy (selector vp vq) :=
    .app inner weakenedQ
  exact outer

/-- The right-hand selector of `conj` evaluates to `fun f ↦ f ⊤ ⊤`. -/
theorem eval_conj_right {depth : Nat} {Γ : BoundCtx IndSig depth} {freeEnv : FreeEnv IndSig}
    {boundEnv : BoundEnv Γ} :
    Eval Γ freeEnv boundEnv (.lam pairTy (.app (.app (.bv 0) (.bool true)) (.bool true)))
      (.arr pairTy .boolTy) (fun f => f true true) := by
  refine .lam pairTy_kinded fun selector => ?_
  have inner : Eval (extendBound pairTy Γ) freeEnv (extendBoundEnv selector boundEnv)
      (.app (.bv 0) (.bool true)) (.arr .boolTy .boolTy) (selector true) :=
    .app (eval_bv_zero pairTy_kinded freeEnv boundEnv selector) (.boolean true)
  have outer : Eval (extendBound pairTy Γ) freeEnv (extendBoundEnv selector boundEnv)
      (.app (.app (.bv 0) (.bool true)) (.bool true)) .boolTy (selector true true) :=
    .app inner (.boolean true)
  exact outer

/-- The encoded context comma denotes conjunction. -/
theorem eval_conj {depth : Nat} {Γ : BoundCtx IndSig depth} {freeEnv : FreeEnv IndSig}
    {boundEnv : BoundEnv Γ} {p q : HTm depth} {vp vq : Bool}
    (hp : Eval Γ freeEnv boundEnv p .boolTy vp) (hq : Eval Γ freeEnv boundEnv q .boolTy vq) :
    Eval Γ freeEnv boundEnv (conj p q) .boolTy (vp && vq) := by
  by_cases both : vp = true ∧ vq = true
  · obtain ⟨rfl, rfl⟩ := both
    exact .eqTrue (.arr pairTy_kinded .boolTy) (eval_conj_left hp hq) eval_conj_right rfl
  · have false_case : (vp && vq) = false := by
      rcases Bool.eq_false_or_eq_true vp with hvp | hvp <;>
        rcases Bool.eq_false_or_eq_true vq with hvq | hvq <;> simp_all
    rw [false_case]
    exact .eqFalse (.arr pairTy_kinded .boolTy) (eval_conj_left hp hq) eval_conj_right
      (fun equal => both ((conj_selector_iff vp vq).mp equal))

/-! ## Coherence of the interpretation -/

set_option maxHeartbeats 1000000 in
/-- **Coherence.** The value of an interpreted term depends only on the logical
environment, not on which binders were used to reach it.

This is what lets a `hol.mm` axiom that compares a term elaborated *under* a
binder with the same term elaborated *without* one — `ax-beta`, `ax-17`,
`ax-distrc`, `ax-distrl`, `ax-leq` — be discharged semantically. -/
theorem elabEval_transfer : ∀ (t : Term) {ctx₁ ctx₂ : ElabCtx} {σ : Typ}
    {a₁ : HTm ctx₁.length} {a₂ : HTm ctx₂.length}
    {logical₁ logical₂ freeEnv₁ freeEnv₂ : FreeEnv IndSig}
    {boundEnv₁ : BoundEnv (ctxTypes ctx₁)} {boundEnv₂ : BoundEnv (ctxTypes ctx₂)}
    {value : DenoteTy σ.denote},
    elabTm ctx₁ t = some (σ, a₁) → elabTm ctx₂ t = some (σ, a₂) →
    Agrees ctx₁ logical₁ freeEnv₁ boundEnv₁ → Agrees ctx₂ logical₂ freeEnv₂ boundEnv₂ →
    (∀ n τ, (n, τ) ∈ freeVars t → logical₁ n τ.denote = logical₂ n τ.denote) →
    Eval (ctxTypes ctx₁) freeEnv₁ boundEnv₁ a₁ σ.denote value →
    Eval (ctxTypes ctx₂) freeEnv₂ boundEnv₂ a₂ σ.denote value := by
  intro t
  induction t with
  | var name type =>
      intro ctx₁ ctx₂ σ a₁ a₂ lg₁ lg₂ fe₁ fe₂ be₁ be₂ value h₁ h₂ ag₁ ag₂ freeAgree ev
      obtain ⟨rfl, rfl⟩ := elabTm_var_inv h₁
      obtain ⟨-, rfl⟩ := elabTm_var_inv h₂
      cases ev.unique (eval_varTm ag₁)
      rw [freeAgree name σ (by simp [freeVars])]
      exact eval_varTm ag₂
  | tru =>
      intro ctx₁ ctx₂ σ a₁ a₂ lg₁ lg₂ fe₁ fe₂ be₁ be₂ value h₁ h₂ ag₁ ag₂ freeAgree ev
      simp only [elabTm, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁
      obtain ⟨-, rfl⟩ := h₂
      cases ev.unique (Eval.boolean (Γ := ctxTypes ctx₁) (freeEnv := fe₁) (boundEnv := be₁) true)
      exact .boolean true
  | eq type =>
      intro ctx₁ ctx₂ σ a₁ a₂ lg₁ lg₂ fe₁ fe₂ be₁ be₂ value h₁ h₂ ag₁ ag₂ freeAgree ev
      simp only [elabTm, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁
      obtain ⟨-, rfl⟩ := h₂
      cases ev.unique (eval_eqFun type fe₁ be₁)
      exact eval_eqFun type fe₂ be₂
  | choose type =>
      intro ctx₁ ctx₂ σ a₁ a₂ lg₁ lg₂ fe₁ fe₂ be₁ be₂ value h₁ h₂ ag₁ ag₂ freeAgree ev
      simp only [elabTm, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁
      obtain ⟨-, rfl⟩ := h₂
      cases ev.unique (eval_chooseFun type fe₁ be₁)
      exact eval_chooseFun type fe₂ be₂
  | app function argument ihFunction ihArgument =>
      intro ctx₁ ctx₂ σ a₁ a₂ lg₁ lg₂ fe₁ fe₂ be₁ be₂ value h₁ h₂ ag₁ ag₂ freeAgree ev
      obtain ⟨α, f₁, x₁, hf₁, hx₁, rfl⟩ := elabTm_app_inv h₁
      obtain ⟨β, f₂, x₂, hf₂, hx₂, rfl⟩ := elabTm_app_inv h₂
      have domains : α = β :=
        (Typ.arr.injEq α σ β σ ▸ elabTm_type_unique function hf₁ hf₂).1
      subst domains
      cases ev with
      | app hfun harg =>
          have pinned := HasType.unique (elabTm_hasType function hf₁) hfun.typing
          simp only [Typ.denote, Expr.arr.injEq] at pinned
          obtain ⟨rfl, -⟩ := pinned
          refine .app (ihFunction hf₁ hf₂ ag₁ ag₂ ?_ hfun)
            (ihArgument hx₁ hx₂ ag₁ ag₂ ?_ harg)
          · exact fun n τ member => freeAgree n τ (by simp [freeVars, member])
          · exact fun n τ member => freeAgree n τ (by simp [freeVars, member])
  | lam name type body ihBody =>
      intro ctx₁ ctx₂ σ a₁ a₂ lg₁ lg₂ fe₁ fe₂ be₁ be₂ value h₁ h₂ ag₁ ag₂ freeAgree ev
      obtain ⟨τ₁, b₁, hb₁, rfl, rfl⟩ := elabTm_lam_inv h₁
      obtain ⟨τ₂, b₂, hb₂, codomains, rfl⟩ := elabTm_lam_inv h₂
      obtain ⟨-, rfl⟩ := Typ.arr.injEq type τ₁ type τ₂ ▸ codomains
      cases ev with
      | lam hA hbody =>
          refine .lam type.denote_kinded fun argument => ?_
          refine ihBody hb₁ hb₂ (ag₁.cons name type argument) (ag₂.cons name type argument)
            ?_ (hbody argument)
          intro n ν member
          by_cases hit : n = name ∧ ν = type
          · obtain ⟨rfl, rfl⟩ := hit
            rw [updateFree_hit, updateFree_hit]
          · rw [updateFree_miss lg₁ argument hit, updateFree_miss lg₂ argument hit]
            refine freeAgree n ν ?_
            simp only [freeVars, List.mem_filter, decide_eq_true_eq, ne_eq]
            exact ⟨member, fun equal =>
              hit ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩⟩
  | ctx left right ihLeft ihRight =>
      intro ctx₁ ctx₂ σ a₁ a₂ lg₁ lg₂ fe₁ fe₂ be₁ be₂ value h₁ h₂ ag₁ ag₂ freeAgree ev
      obtain ⟨l₁, r₁, hl₁, hr₁, rfl, rfl⟩ := elabTm_ctx_inv h₁
      obtain ⟨l₂, r₂, hl₂, hr₂, -, rfl⟩ := elabTm_ctx_inv h₂
      obtain ⟨vl, evl⟩ := (elabTm_hasType left hl₁).eval_exists fe₁ be₁
      obtain ⟨vr, evr⟩ := (elabTm_hasType right hr₁).eval_exists fe₁ be₁
      have evl₂ := ihLeft hl₁ hl₂ ag₁ ag₂
        (fun n τ member => freeAgree n τ (by simp [freeVars, member])) evl
      have evr₂ := ihRight hr₁ hr₂ ag₁ ag₂
        (fun n τ member => freeAgree n τ (by simp [freeVars, member])) evr
      cases ev.unique (eval_conj evl evr)
      exact eval_conj evl₂ evr₂
  | br left oper right ihLeft ihOper ihRight =>
      intro ctx₁ ctx₂ σ a₁ a₂ lg₁ lg₂ fe₁ fe₂ be₁ be₂ value h₁ h₂ ag₁ ag₂ freeAgree ev
      obtain ⟨α, β, l₁, f₁, r₁, hf₁, hl₁, hr₁, rfl⟩ := elabTm_br_inv h₁
      obtain ⟨α', β', l₂, f₂, r₂, hf₂, hl₂, hr₂, rfl⟩ := elabTm_br_inv h₂
      have operTypes := elabTm_type_unique oper hf₁ hf₂
      obtain ⟨rfl, inner⟩ := Typ.arr.injEq α (.arr β σ) α' (.arr β' σ) ▸ operTypes
      obtain ⟨rfl, -⟩ := Typ.arr.injEq β σ β' σ ▸ inner
      cases ev with
      | app houter hr =>
          cases houter with
          | app hfun hl =>
              have pinned := HasType.unique (elabTm_hasType oper hf₁) hfun.typing
              simp only [Typ.denote, Expr.arr.injEq] at pinned
              obtain ⟨rfl, rfl, -⟩ := pinned
              refine .app (.app (ihOper hf₁ hf₂ ag₁ ag₂ ?_ hfun)
                (ihLeft hl₁ hl₂ ag₁ ag₂ ?_ hl)) (ihRight hr₁ hr₂ ag₁ ag₂ ?_ hr)
              · exact fun n τ member => freeAgree n τ (by simp [freeVars, member])
              · exact fun n τ member => freeAgree n τ (by simp [freeVars, member])
              · exact fun n τ member => freeAgree n τ (by simp [freeVars, member])

/-- Coherence, as a biconditional. -/
theorem elabEval_iff (t : Term) {ctx₁ ctx₂ : ElabCtx} {σ : Typ}
    {a₁ : HTm ctx₁.length} {a₂ : HTm ctx₂.length}
    {logical₁ logical₂ freeEnv₁ freeEnv₂ : FreeEnv IndSig}
    {boundEnv₁ : BoundEnv (ctxTypes ctx₁)} {boundEnv₂ : BoundEnv (ctxTypes ctx₂)}
    {value : DenoteTy σ.denote}
    (h₁ : elabTm ctx₁ t = some (σ, a₁)) (h₂ : elabTm ctx₂ t = some (σ, a₂))
    (agree₁ : Agrees ctx₁ logical₁ freeEnv₁ boundEnv₁)
    (agree₂ : Agrees ctx₂ logical₂ freeEnv₂ boundEnv₂)
    (freeAgree : ∀ n τ, (n, τ) ∈ freeVars t → logical₁ n τ.denote = logical₂ n τ.denote) :
    Eval (ctxTypes ctx₁) freeEnv₁ boundEnv₁ a₁ σ.denote value ↔
      Eval (ctxTypes ctx₂) freeEnv₂ boundEnv₂ a₂ σ.denote value :=
  ⟨elabEval_transfer t h₁ h₂ agree₁ agree₂ freeAgree,
    elabEval_transfer t h₂ h₁ agree₂ agree₁ (fun n τ member => (freeAgree n τ member).symm)⟩

end Nucleus.Metamath.HolMM
