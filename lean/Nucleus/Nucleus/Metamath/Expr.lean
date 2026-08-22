import Mathlib.Data.List.Basic

/-!
# Metamath expressions and substitution

A Metamath expression is a typecode constant followed by a **flat sequence** of
math symbols — there is no grammar tree at this layer, and substitution splices
symbol sequences in place. This file mirrors `crates/logic/metamath/src/expr.rs`
and `subst.rs`.

Whether a symbol is a variable is *not* recorded in the expression: it is a
property of the surrounding database, so every definition here that needs the
distinction takes an explicit `isVar : Sym → Bool` classifier.

Two facts drive everything downstream:

* `substBody_append` — substitution is a homomorphism for sequence
  concatenation, which is what makes "splice in place" well defined; and
* `substBody_substBody` — substitutions compose, with `Subst.comp` as the
  composite. That is the lemma the distinct-variable metatheory in
  `Nucleus.Metamath.Verify` is built on.
-/

namespace Nucleus.Metamath

/-- A Metamath math symbol: a typecode, a constant, or a variable. -/
abbrev Sym := String

/-- A Metamath expression: a typecode constant plus a flat body of symbols.

Faithful to the surface language: `wff ( ph -> ps )` is `typecode = "wff"` with
`body = ["(", "ph", "->", "ps", ")"]`, *not* a nested tree. -/
structure Expr where
  /-- The typecode constant (`wff`, `term`, `class`, `|-`, …). -/
  typecode : Sym
  /-- Everything after the typecode, in order. -/
  body : List Sym
  deriving DecidableEq, Repr, Inhabited

/-- A substitution: variable names paired with the symbol sequences replacing
them.

An association list rather than a map, so that `Subst` is decidable-equal and
`Repr`-able. Lookup takes the first binding for a name. -/
abbrev Subst := List (Sym × List Sym)

namespace Subst

/-- The binding for `v`, if any. -/
def get? : Subst → Sym → Option (List Sym)
  | [], _ => none
  | (k, v) :: rest, s => if k = s then some v else get? rest s

@[simp] theorem get?_nil (v : Sym) : get? [] v = none := rfl

@[simp] theorem get?_cons_self (v : List Sym) (rest : Subst) (k : Sym) :
    get? ((k, v) :: rest) k = some v := by simp [get?]

theorem get?_cons_of_ne {k s : Sym} (h : k ≠ s) (v : List Sym) (rest : Subst) :
    get? ((k, v) :: rest) s = get? rest s := by simp [get?, h]

/-- What `σ` replaces the symbol `s` with. Unbound symbols — constants, and
variables outside the substitution's domain — pass through unchanged. -/
def image (σ : Subst) (s : Sym) : List Sym := (σ.get? s).getD [s]

@[simp] theorem image_nil (s : Sym) : image [] s = [s] := rfl

/-- A substitution whose domain consists only of variables. Every substitution
the verifier builds has this property: its domain is exactly the variables of
the applied assertion's floating hypotheses. -/
def MapsVariables (isVar : Sym → Bool) (σ : Subst) : Prop :=
  ∀ binding ∈ σ, isVar binding.1 = true

/-- A variable-only substitution leaves constants alone. -/
theorem image_of_not_isVar {isVar : Sym → Bool} {σ : Subst} (hσ : σ.MapsVariables isVar)
    {s : Sym} (hs : isVar s = false) : σ.image s = [s] := by
  have hnone : σ.get? s = none := by
    induction σ with
    | nil => rfl
    | cons binding rest ih =>
      obtain ⟨k, v⟩ := binding
      have hk : isVar k = true := hσ (k, v) (by simp)
      have hne : k ≠ s := by
        intro hEq
        rw [hEq, hs] at hk
        exact Bool.noConfusion hk
      rw [get?_cons_of_ne hne]
      exact ih fun b hb => hσ b (by simp [hb])
  simp [image, hnone]

end Subst

/-- Apply a substitution to a symbol sequence, splicing each bound variable's
replacement in place. -/
def substBody (σ : Subst) (body : List Sym) : List Sym := body.flatMap σ.image

@[simp] theorem substBody_nil (σ : Subst) : substBody σ [] = [] := rfl

@[simp] theorem substBody_cons (σ : Subst) (s : Sym) (rest : List Sym) :
    substBody σ (s :: rest) = σ.image s ++ substBody σ rest := by
  simp [substBody]

@[simp] theorem substBody_singleton (σ : Subst) (s : Sym) :
    substBody σ [s] = σ.image s := by
  simp

/-- Splicing is a homomorphism for sequence concatenation. -/
@[simp] theorem substBody_append (σ : Subst) (b₁ b₂ : List Sym) :
    substBody σ (b₁ ++ b₂) = substBody σ b₁ ++ substBody σ b₂ := by
  simp [substBody]

@[simp] theorem substBody_empty (body : List Sym) : substBody [] body = body := by
  induction body with
  | nil => rfl
  | cons s rest ih => rw [substBody_cons, Subst.image_nil, ih, List.singleton_append]

/-- Apply a substitution to an expression. The typecode is a constant and is
never substituted. -/
def applySubst (σ : Subst) (e : Expr) : Expr := ⟨e.typecode, substBody σ e.body⟩

@[simp] theorem applySubst_typecode (σ : Subst) (e : Expr) :
    (applySubst σ e).typecode = e.typecode := rfl

@[simp] theorem applySubst_body (σ : Subst) (e : Expr) :
    (applySubst σ e).body = substBody σ e.body := rfl

@[simp] theorem applySubst_empty (e : Expr) : applySubst [] e = e := by
  cases e
  simp [applySubst]

namespace Subst

/-- The composite substitution: `σ.comp τ` acts as "`σ` first, then `τ`".

`σ`'s bindings have `τ` pushed through them; `τ`'s own bindings are appended so
that symbols outside `σ`'s domain still see `τ`. Appending rather than merging
is correct precisely because `get?` takes the first match. -/
def comp (σ τ : Subst) : Subst :=
  σ.map (fun binding => (binding.1, substBody τ binding.2)) ++ τ

@[simp] theorem nil_comp (τ : Subst) : comp [] τ = τ := by simp [comp]

theorem cons_comp (k : Sym) (v : List Sym) (rest τ : Subst) :
    comp ((k, v) :: rest) τ = (k, substBody τ v) :: comp rest τ := rfl

theorem image_comp (σ τ : Subst) (s : Sym) :
    (σ.comp τ).image s = substBody τ (σ.image s) := by
  induction σ with
  | nil => rw [nil_comp, image_nil, substBody_singleton]
  | cons binding rest ih =>
    obtain ⟨k, v⟩ := binding
    rw [cons_comp]
    by_cases h : k = s
    · subst h
      rw [image, get?_cons_self, image, get?_cons_self]
      rfl
    · rw [image, get?_cons_of_ne h, image, get?_cons_of_ne h]
      exact ih

end Subst

/-- Substitutions compose: applying `σ` and then `τ` is applying `σ.comp τ`. -/
theorem substBody_substBody (σ τ : Subst) (body : List Sym) :
    substBody τ (substBody σ body) = substBody (σ.comp τ) body := by
  induction body with
  | nil => rfl
  | cons s rest ih =>
    rw [substBody_cons, substBody_append, ih, substBody_cons, Subst.image_comp]

/-- Composition, at the level of whole expressions. -/
theorem applySubst_applySubst (σ τ : Subst) (e : Expr) :
    applySubst τ (applySubst σ e) = applySubst (σ.comp τ) e := by
  cases e
  simp [applySubst, substBody_substBody]

/-- The variables occurring in a symbol sequence, in order and with repeats. -/
def bodyVars (isVar : Sym → Bool) (body : List Sym) : List Sym := body.filter isVar

@[simp] theorem bodyVars_nil (isVar : Sym → Bool) : bodyVars isVar [] = [] := rfl

@[simp] theorem bodyVars_append (isVar : Sym → Bool) (b₁ b₂ : List Sym) :
    bodyVars isVar (b₁ ++ b₂) = bodyVars isVar b₁ ++ bodyVars isVar b₂ := by
  simp [bodyVars]

theorem mem_bodyVars {isVar : Sym → Bool} {body : List Sym} {v : Sym} :
    v ∈ bodyVars isVar body ↔ v ∈ body ∧ isVar v = true := by
  simp [bodyVars]

/-- The variables of a substituted sequence are exactly the variables of the
images of its symbols. This is what lets a `$d` obligation be checked pointwise
over the substituted images. -/
theorem bodyVars_substBody (isVar : Sym → Bool) (σ : Subst) (body : List Sym) :
    bodyVars isVar (substBody σ body)
      = body.flatMap (fun s => bodyVars isVar (σ.image s)) := by
  induction body with
  | nil => rfl
  | cons s rest ih => rw [substBody_cons, bodyVars_append, ih, List.flatMap_cons]

/-- Every variable of a substituted sequence comes from the image of some
*variable* of the original. Constants contribute nothing, because the
substitution binds only variables — which is exactly the hypothesis
`Subst.MapsVariables` records. -/
theorem mem_bodyVars_substBody {isVar : Sym → Bool} {σ : Subst}
    (hσ : σ.MapsVariables isVar) {body : List Sym} {u : Sym}
    (hu : u ∈ bodyVars isVar (substBody σ body)) :
    ∃ x ∈ bodyVars isVar body, u ∈ bodyVars isVar (σ.image x) := by
  rw [bodyVars_substBody] at hu
  obtain ⟨x, hx, hux⟩ := List.mem_flatMap.mp hu
  have hvar : isVar x = true := by
    by_contra hnot
    have hfalse : isVar x = false := by
      cases hcase : isVar x with
      | false => rfl
      | true => exact absurd hcase hnot
    rw [Subst.image_of_not_isVar hσ hfalse] at hux
    obtain ⟨hmem, huvar⟩ := mem_bodyVars.mp hux
    rw [List.mem_singleton.mp hmem, hfalse] at huvar
    exact Bool.noConfusion huvar
  exact ⟨x, mem_bodyVars.mpr ⟨hx, hvar⟩, hux⟩

end Nucleus.Metamath
