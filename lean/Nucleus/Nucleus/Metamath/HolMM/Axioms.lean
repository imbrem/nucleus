import Nucleus.Metamath.HolMM.Interpretation

/-!
# `hol.mm`'s axioms, checked against the pointed-set semantics

`hol.mm` has 71 `$a` statements. Most are syntax constructors (`tv`, `kc`, `kl`,
…) or definitions (`df-*`); the genuine logical content is the `ax-*` family.
This file interprets `hol.mm`'s two judgment forms —

* `|- A : al` as `Typed A al`, and
* `|- R |= A` as `Seq R A`,

and then checks each axiom as a statement about `Typed`/`Seq`. Because
`Nucleus.Metamath.Provable`'s `apply` rule treats a `$p` theorem exactly like an
axiom of the same shape, validating the axioms is what a soundness argument for
the whole database reduces to.

`Seq R A` carries `Typed R bool` and `Typed A bool` as conjuncts. That is not
padding: it is precisely the reading under which `ax-cb1` and `ax-cb2` are sound,
and it is the reading `hol.mm`'s own comment on `ax-cb1` justifies ("every axiom
and inference rule that constructs a theorem of the form `R |= A` … also ensures
that `R : bool` and `A : bool`").

## Status of each axiom

**Proved sound here.** `ax-wv`, `ax-wl`, `ax-wc`, `ax-wct`, `ax-wctl`,
`ax-wctr`, `ax-wov`, `ax-weq`, `ax-wat`, `df-ov`, `ax-cb1`, `ax-cb2`, `ax-id`,
`ax-trud`, `ax-syl`, `ax-simpl`, `ax-simpr`, `ax-jca`, `ax-refl`, `ax-eqmp`,
`ax-ded`, `ax-ceq`, `ax-eqtypi`, `ax-eqtypri`, `ax-beta`, `ax-17`, `ax-distrc`,
`ax-leq`.

**Refuted here.** `ax-hbl1`. See `ax_hbl1_counterexample`.

**Not formalised.** `ax-distrl`, `ax-inst`, `ax-eta`, `ax-ac`, `ax-inf`,
`ax-wabs`, `ax-wrep`, `ax-tdef`, and the `df-*` definitions other than `df-ov`.
The module documentation of `Nucleus.Metamath.HolMM` says what is believed about
each and why.

This file leaves nothing unproved.
-/

namespace Nucleus.Metamath.HolMM

open Nucleus.Hol

/-! ## The two judgment forms -/

/-- `hol.mm`'s `|- A : al`. -/
def Typed (A : Term) (τ : Typ) : Prop := ∃ a, elabTm [] A = some (τ, a)

/-- `hol.mm`'s `|- R |= A`: both sides are Boolean terms, and the interpretation
of `R` semantically entails that of `A`.

The typedness conjuncts are what make `ax-cb1` and `ax-cb2` sound. -/
def Seq (R A : Term) : Prop :=
  ∃ r a : HTm 0, elabTm [] R = some (.bool, r) ∧ elabTm [] A = some (.bool, a) ∧
    Entails (Γ := ctxTypes []) [r] a

/-- Build an entailment from a pointwise implication. -/
theorem entails_intro {r a : HTm 0}
    (h : ∀ (freeEnv : FreeEnv IndSig) (boundEnv : BoundEnv (ctxTypes [])),
      Eval (ctxTypes []) freeEnv boundEnv r .boolTy true →
      Eval (ctxTypes []) freeEnv boundEnv a .boolTy true) :
    Entails (Γ := ctxTypes []) [r] a :=
  fun freeEnv boundEnv hyps => h freeEnv boundEnv (hyps r (by simp))

/-- Use an entailment at one environment. -/
theorem entails_elim {r a : HTm 0} (h : Entails (Γ := ctxTypes []) [r] a)
    {freeEnv : FreeEnv IndSig} {boundEnv : BoundEnv (ctxTypes [])}
    (hr : Eval (ctxTypes []) freeEnv boundEnv r .boolTy true) :
    Eval (ctxTypes []) freeEnv boundEnv a .boolTy true :=
  h freeEnv boundEnv (by intro p mem; rw [List.mem_singleton.mp mem]; exact hr)

/-! ## Elaboration is insensitive to the ambient binders -/

/-- Whether a term elaborates, and at which type, does not depend on the
binders in scope; only the interpretation of its variable occurrences does. -/
theorem elabTm_reindex : ∀ (t : Term) {ctx : ElabCtx} {σ : Typ} {a : HTm ctx.length},
    elabTm ctx t = some (σ, a) → ∀ ctx' : ElabCtx, ∃ b, elabTm ctx' t = some (σ, b) := by
  intro t
  induction t with
  | var name type =>
      intro ctx σ a h ctx'
      obtain ⟨rfl, -⟩ := elabTm_var_inv h
      exact ⟨_, rfl⟩
  | tru | eq _ | choose _ =>
      intro ctx σ a h ctx'
      simp only [elabTm, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨_, rfl⟩
  | app function argument ihFunction ihArgument =>
      intro ctx σ a h ctx'
      obtain ⟨α, f, x, hf, hx, -⟩ := elabTm_app_inv h
      obtain ⟨f', hf'⟩ := ihFunction hf ctx'
      obtain ⟨x', hx'⟩ := ihArgument hx ctx'
      exact ⟨_, elabTm_app hf' hx'⟩
  | lam name type body ihBody =>
      intro ctx σ a h ctx'
      obtain ⟨τ, b, hb, rfl, -⟩ := elabTm_lam_inv h
      obtain ⟨b', hb'⟩ := ihBody hb ((name, type) :: ctx')
      exact ⟨_, elabTm_lam hb'⟩
  | ctx left right ihLeft ihRight =>
      intro ctx σ a h ctx'
      obtain ⟨l, r, hl, hr, rfl, -⟩ := elabTm_ctx_inv h
      obtain ⟨l', hl'⟩ := ihLeft hl ctx'
      obtain ⟨r', hr'⟩ := ihRight hr ctx'
      exact ⟨_, elabTm_ctx hl' hr'⟩
  | br left oper right ihLeft ihOper ihRight =>
      intro ctx σ a h ctx'
      obtain ⟨α, β, l, f, r, hf, hl, hr, -⟩ := elabTm_br_inv h
      obtain ⟨f', hf'⟩ := ihOper hf ctx'
      obtain ⟨l', hl'⟩ := ihLeft hl ctx'
      obtain ⟨r', hr'⟩ := ihRight hr ctx'
      exact ⟨_, elabTm_br hf' hl' hr'⟩

/-! ## Syntax and typing axioms -/

/-- `ax-wv`: a typed variable has the type it is annotated with. -/
theorem ax_wv (x : Nat) (al : Typ) : Typed (.var x al) al := ⟨_, rfl⟩

/-- `ax-weq`: `=` is polymorphic in its argument type. -/
theorem ax_weq (al : Typ) : Typed (.eq al) (.arr al (.arr al .bool)) := ⟨_, rfl⟩

/-- `ax-wat`: `@` is polymorphic in its result type. -/
theorem ax_wat (al : Typ) : Typed (.choose al) (.arr (.arr al .bool) al) := ⟨_, rfl⟩

/-- `wtru`: `T.` is Boolean. -/
theorem wtru : Typed .tru .bool := ⟨_, rfl⟩

/-- `ax-wl`: the type of a lambda abstraction. -/
theorem ax_wl {T : Term} {be : Typ} (x : Nat) (al : Typ) (hT : Typed T be) :
    Typed (.lam x al T) (.arr al be) := by
  obtain ⟨t, ht⟩ := hT
  obtain ⟨t', ht'⟩ := elabTm_reindex T ht [(x, al)]
  exact ⟨_, elabTm_lam ht'⟩

/-- `ax-wc`: the type of a combination. -/
theorem ax_wc {F T : Term} {al be : Typ} (hF : Typed F (.arr al be)) (hT : Typed T al) :
    Typed (.app F T) be := by
  obtain ⟨f, hf⟩ := hF
  obtain ⟨t, ht⟩ := hT
  exact ⟨_, elabTm_app hf ht⟩

/-- `ax-wct`: a context of two Boolean terms is Boolean. -/
theorem ax_wct {S T : Term} (hS : Typed S .bool) (hT : Typed T .bool) :
    Typed (.ctx S T) .bool := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hT
  exact ⟨_, elabTm_ctx hs ht⟩

/-- `ax-wctl`: reverse closure for the left half of a context. -/
theorem ax_wctl {S T : Term} (h : Typed (.ctx S T) .bool) : Typed S .bool := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨l, r, hl, -, -, -⟩ := elabTm_ctx_inv ha
  exact ⟨l, hl⟩

/-- `ax-wctr`: reverse closure for the right half of a context. -/
theorem ax_wctr {S T : Term} (h : Typed (.ctx S T) .bool) : Typed T .bool := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨l, r, -, hr, -, -⟩ := elabTm_ctx_inv ha
  exact ⟨r, hr⟩

/-- `ax-wov`: the type of an infix operator application. -/
theorem ax_wov {F A B : Term} {al be ga : Typ} (hF : Typed F (.arr al (.arr be ga)))
    (hA : Typed A al) (hB : Typed B be) : Typed (.br A F B) ga := by
  obtain ⟨f, hf⟩ := hF
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨_, elabTm_br hf ha hb⟩

/-- `hol.mm` typing is unique, so `ax-eqtypi` and `ax-eqtypri` are sound: on the
annotated syntax a term determines its type. -/
theorem typed_unique {A : Term} {al be : Typ} (first : Typed A al) (second : Typed A be) :
    al = be := by
  obtain ⟨a, ha⟩ := first
  obtain ⟨b, hb⟩ := second
  exact elabTm_type_unique A ha hb

/-! ## Values of interpreted terms -/

/-- The interpretation of a closed `hol.mm` term always has a value. -/
theorem elab_eval_exists {A : Term} {τ : Typ} {a : HTm 0} (h : elabTm [] A = some (τ, a))
    (freeEnv : FreeEnv IndSig) (boundEnv : BoundEnv (ctxTypes [])) :
    ∃ value, Eval (ctxTypes []) freeEnv boundEnv a τ.denote value :=
  (elabTm_hasType A h).eval_exists freeEnv boundEnv

/-- Applying the interpretation of `=` to two values. -/
theorem eval_eqApp {τ : Typ} {depth : Nat} {Γ : BoundCtx IndSig depth}
    {freeEnv : FreeEnv IndSig} {boundEnv : BoundEnv Γ} {a b : HTm depth}
    {va vb : DenoteTy τ.denote}
    (ha : Eval Γ freeEnv boundEnv a τ.denote va)
    (hb : Eval Γ freeEnv boundEnv b τ.denote vb) :
    Eval Γ freeEnv boundEnv (.app (.app (eqFun τ depth) a) b) .boolTy (eqValue τ va vb) := by
  have inner : Eval Γ freeEnv boundEnv (.app (eqFun τ depth) a)
      (.arr τ.denote .boolTy) (eqValue τ va) := .app (eval_eqFun τ freeEnv boundEnv) ha
  have outer : Eval Γ freeEnv boundEnv (.app (.app (eqFun τ depth) a) b) .boolTy
      (eqValue τ va vb) := .app inner hb
  exact outer

/-- `eqValue` really is equality. -/
theorem eqValue_eq (τ : Typ) {x y : DenoteTy τ.denote} (h : eqValue τ x y = true) : x = y := by
  by_cases equal : x = y
  · exact equal
  · rw [eqValue_neg τ equal] at h
    exact Bool.noConfusion h

/-- Elaboration of `( ( = A ) B )`. -/
theorem elabTm_eqApp {ctx : ElabCtx} {al : Typ} {A B : Term} {a b : HTm ctx.length}
    (ha : elabTm ctx A = some (al, a)) (hb : elabTm ctx B = some (al, b)) :
    elabTm ctx (.app (.app (.eq al) A) B) =
      some (.bool, .app (.app (eqFun al ctx.length) a) b) :=
  elabTm_app (elabTm_app rfl ha) hb

/-- Inversion for the elaboration of `( ( = A ) B )`. -/
theorem elabTm_eqApp_inv {ctx : ElabCtx} {al σ : Typ} {A B : Term} {t : HTm ctx.length}
    (h : elabTm ctx (.app (.app (.eq al) A) B) = some (σ, t)) :
    ∃ a b : HTm ctx.length, elabTm ctx A = some (al, a) ∧ elabTm ctx B = some (al, b) ∧
      σ = .bool ∧ t = .app (.app (eqFun al ctx.length) a) b := by
  obtain ⟨α, f, b, hf, hb, rfl⟩ := elabTm_app_inv h
  obtain ⟨β, g, a, hg, ha, rfl⟩ := elabTm_app_inv hf
  have pair := Option.some.inj hg
  simp only [Prod.mk.injEq, Typ.arr.injEq] at pair
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := pair
  exact ⟨a, b, ha, hb, rfl, rfl⟩

/-- Both halves of a true context are true. -/
theorem eval_conj_elim {depth : Nat} {Γ : BoundCtx IndSig depth} {freeEnv : FreeEnv IndSig}
    {boundEnv : BoundEnv Γ} {p q : HTm depth} {vp vq : Bool}
    (hp : Eval Γ freeEnv boundEnv p .boolTy vp) (hq : Eval Γ freeEnv boundEnv q .boolTy vq)
    (h : Eval Γ freeEnv boundEnv (conj p q) .boolTy true) : vp = true ∧ vq = true := by
  have equal := h.unique (eval_conj hp hq)
  simpa using equal.symm

/-! ## Propositional and equality axioms -/

/-- `ax-cb1`: a context is Boolean. -/
theorem ax_cb1 {R A : Term} (h : Seq R A) : Typed R .bool := by
  obtain ⟨r, a, hr, -, -⟩ := h
  exact ⟨r, hr⟩

/-- `ax-cb2`: a theorem is Boolean. -/
theorem ax_cb2 {R A : Term} (h : Seq R A) : Typed A .bool := by
  obtain ⟨r, a, -, ha, -⟩ := h
  exact ⟨a, ha⟩

/-- `ax-id`: the identity inference. -/
theorem ax_id {R : Term} (hR : Typed R .bool) : Seq R R := by
  obtain ⟨r, hr⟩ := hR
  exact ⟨r, r, hr, hr, entails_intro fun _ _ hyp => hyp⟩

/-- `ax-trud`: `T.` follows from anything Boolean. -/
theorem ax_trud {R : Term} (hR : Typed R .bool) : Seq R .tru := by
  obtain ⟨r, hr⟩ := hR
  exact ⟨r, _, hr, rfl, entails_intro fun _ _ _ => .boolean true⟩

/-- `ax-syl`: syllogism. -/
theorem ax_syl {R S T : Term} (first : Seq R S) (second : Seq S T) : Seq R T := by
  obtain ⟨r, s, hr, hs, hrs⟩ := first
  obtain ⟨s', t, hs', ht, hst⟩ := second
  obtain rfl : s = s' := congrArg Prod.snd (Option.some.inj (hs.symm.trans hs'))
  exact ⟨r, t, hr, ht, entails_intro fun _ _ hyp => entails_elim hst (entails_elim hrs hyp)⟩

/-- `ax-jca`: join common antecedents. -/
theorem ax_jca {R S T : Term} (first : Seq R S) (second : Seq R T) : Seq R (.ctx S T) := by
  obtain ⟨r, s, hr, hs, hrs⟩ := first
  obtain ⟨r', t, hr', ht, hrt⟩ := second
  obtain rfl : r = r' := congrArg Prod.snd (Option.some.inj (hr.symm.trans hr'))
  refine ⟨r, conj s t, hr, elabTm_ctx hs ht, entails_intro fun freeEnv boundEnv hyp => ?_⟩
  exact eval_conj (entails_elim hrs hyp) (entails_elim hrt hyp)

/-- `ax-simpl`: extract the left assumption from a context. -/
theorem ax_simpl {R S : Term} (hR : Typed R .bool) (hS : Typed S .bool) :
    Seq (.ctx R S) R := by
  obtain ⟨r, hr⟩ := hR
  obtain ⟨s, hs⟩ := hS
  refine ⟨conj r s, r, elabTm_ctx hr hs, hr, entails_intro fun freeEnv boundEnv hyp => ?_⟩
  obtain ⟨vr, evr⟩ := elab_eval_exists hr freeEnv boundEnv
  obtain ⟨vs, evs⟩ := elab_eval_exists hs freeEnv boundEnv
  exact (eval_conj_elim evr evs hyp).1 ▸ evr

/-- `ax-simpr`: extract the right assumption from a context. -/
theorem ax_simpr {R S : Term} (hR : Typed R .bool) (hS : Typed S .bool) :
    Seq (.ctx R S) S := by
  obtain ⟨r, hr⟩ := hR
  obtain ⟨s, hs⟩ := hS
  refine ⟨conj r s, s, elabTm_ctx hr hs, hs, entails_intro fun freeEnv boundEnv hyp => ?_⟩
  obtain ⟨vr, evr⟩ := elab_eval_exists hr freeEnv boundEnv
  obtain ⟨vs, evs⟩ := elab_eval_exists hs freeEnv boundEnv
  exact (eval_conj_elim evr evs hyp).2 ▸ evs

/-- `ax-refl`: reflexivity of equality. -/
theorem ax_refl {A : Term} {al : Typ} (hA : Typed A al) :
    Seq .tru (.app (.app (.eq al) A) A) := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨_, _, rfl, elabTm_eqApp ha ha, entails_intro fun freeEnv boundEnv _ => ?_⟩
  obtain ⟨va, eva⟩ := elab_eval_exists ha freeEnv boundEnv
  have computed := eval_eqApp eva eva
  rw [eqValue_pos al (rfl : va = va)] at computed
  exact computed

/-- `ax-eqmp`: modus ponens for equality. -/
theorem ax_eqmp {R A B : Term} {al : Typ} (first : Seq R A)
    (second : Seq R (.app (.app (.eq al) A) B)) : Seq R B := by
  obtain ⟨r, a, hr, ha, hra⟩ := first
  obtain ⟨r', e, hr', he, hre⟩ := second
  obtain rfl : r = r' := congrArg Prod.snd (Option.some.inj (hr.symm.trans hr'))
  obtain ⟨a', b, ha', hb, -, rfl⟩ := elabTm_eqApp_inv he
  obtain rfl : al = .bool := elabTm_type_unique A ha' ha
  obtain rfl : a' = a := congrArg Prod.snd (Option.some.inj (ha'.symm.trans ha))
  refine ⟨r, b, hr, hb, entails_intro fun freeEnv boundEnv hyp => ?_⟩
  have aTrue := entails_elim hra hyp
  have eqTrue := entails_elim hre hyp
  obtain ⟨vb, evb⟩ := elab_eval_exists hb freeEnv boundEnv
  have same : true = eqValue Typ.bool true vb := eqTrue.unique (eval_eqApp aTrue evb)
  have vbTrue : vb = true := (eqValue_eq Typ.bool same.symm).symm
  rw [vbTrue] at evb
  exact evb

/-- `ax-ded`: the deduction theorem for equality. -/
theorem ax_ded {R S T : Term} (first : Seq (.ctx R S) T) (second : Seq (.ctx R T) S) :
    Seq R (.app (.app (.eq .bool) S) T) := by
  obtain ⟨rs, t, hrs, ht, hrst⟩ := first
  obtain ⟨rt, s, hrt, hs, hrts⟩ := second
  obtain ⟨r, s', hr, hs', -, rfl⟩ := elabTm_ctx_inv hrs
  obtain ⟨r', t', hr', ht', -, rfl⟩ := elabTm_ctx_inv hrt
  obtain rfl : r = r' := congrArg Prod.snd (Option.some.inj (hr.symm.trans hr'))
  obtain rfl : s' = s := congrArg Prod.snd (Option.some.inj (hs'.symm.trans hs))
  obtain rfl : t' = t := congrArg Prod.snd (Option.some.inj (ht'.symm.trans ht))
  refine ⟨r, _, hr, elabTm_eqApp hs ht, entails_intro fun freeEnv boundEnv hyp => ?_⟩
  obtain ⟨vs, evs⟩ := elab_eval_exists hs freeEnv boundEnv
  obtain ⟨vt, evt⟩ := elab_eval_exists ht freeEnv boundEnv
  have same : vs = vt := by
    by_cases hvs : vs = true
    · subst hvs
      exact entails_elim hrst (eval_conj hyp evs) |>.unique evt
    · have hvsFalse : vs = false := by
        cases vs with
        | false => rfl
        | true => exact absurd rfl hvs
      subst hvsFalse
      by_cases hvt : vt = true
      · subst hvt
        have sTrue := entails_elim hrts (eval_conj hyp evt)
        exact Bool.noConfusion (sTrue.unique evs)
      · cases vt with
        | false => rfl
        | true => exact absurd rfl hvt
  have computed := eval_eqApp evs evt
  rw [eqValue_pos Typ.bool same] at computed
  exact computed

/-- `ax-ceq`: congruence of equality for combinations. -/
theorem ax_ceq {F T A B : Term} {al be : Typ} (hF : Typed F (.arr al be))
    (hT : Typed T (.arr al be)) (hA : Typed A al) (hB : Typed B al) :
    Seq (.ctx (.app (.app (.eq (.arr al be)) F) T) (.app (.app (.eq al) A) B))
      (.app (.app (.eq be) (.app F A)) (.app T B)) := by
  obtain ⟨f, hf⟩ := hF
  obtain ⟨t, ht⟩ := hT
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  refine ⟨_, _, elabTm_ctx (elabTm_eqApp hf ht) (elabTm_eqApp ha hb),
    elabTm_eqApp (elabTm_app hf ha) (elabTm_app ht hb),
    entails_intro fun freeEnv boundEnv hyp => ?_⟩
  obtain ⟨vf, evf⟩ := elab_eval_exists hf freeEnv boundEnv
  obtain ⟨vt, evt⟩ := elab_eval_exists ht freeEnv boundEnv
  obtain ⟨va, eva⟩ := elab_eval_exists ha freeEnv boundEnv
  obtain ⟨vb, evb⟩ := elab_eval_exists hb freeEnv boundEnv
  have eqFT := eval_eqApp (τ := .arr al be) evf evt
  have eqAB := eval_eqApp (τ := al) eva evb
  obtain ⟨functions, arguments⟩ := eval_conj_elim eqFT eqAB hyp
  have sameFunction : vf = vt := eqValue_eq (.arr al be) functions
  have sameArgument : va = vb := eqValue_eq al arguments
  have applied : vf va = vt vb := by rw [sameFunction, sameArgument]
  have leftApp : Eval (ctxTypes []) freeEnv boundEnv (.app f a) be.denote (vf va) :=
    .app evf eva
  have rightApp : Eval (ctxTypes []) freeEnv boundEnv (.app t b) be.denote (vt vb) :=
    .app evt evb
  have computed := eval_eqApp (τ := be) leftApp rightApp
  rw [eqValue_pos be applied] at computed
  exact computed

/-- `df-ov`: the infix form is the curried application. It is valid because the
interpretation sends the two to the *same* `Nucleus.Hol` term. -/
theorem df_ov {F A B : Term} {al be ga : Typ} (hF : Typed F (.arr al (.arr be ga)))
    (hA : Typed A al) (hB : Typed B be) :
    Seq .tru (.app (.app (.eq ga) (.br A F B)) (.app (.app F A) B)) := by
  obtain ⟨f, hf⟩ := hF
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hbr : elabTm [] (.br A F B) = some (ga, .app (.app f a) b) := elabTm_br hf ha hb
  have happ : elabTm [] (.app (.app F A) B) = some (ga, .app (.app f a) b) :=
    elabTm_app (elabTm_app hf ha) hb
  refine ⟨_, _, rfl, elabTm_eqApp hbr happ, entails_intro fun freeEnv boundEnv _ => ?_⟩
  obtain ⟨value, evaluation⟩ := elab_eval_exists hbr freeEnv boundEnv
  have computed := eval_eqApp evaluation evaluation
  rw [eqValue_pos ga (rfl : value = value)] at computed
  exact computed

/-! ## The lambda fragment -/

/-- Updating an environment at a variable's own value changes nothing. -/
theorem updateFree_self (freeEnv : FreeEnv IndSig) (x : Nat) (al : Typ) (n : Nat) (ν : Typ) :
    updateFree freeEnv x al (freeEnv x al.denote) n ν.denote = freeEnv n ν.denote := by
  by_cases hit : n = x ∧ ν = al
  · obtain ⟨rfl, rfl⟩ := hit
    exact updateFree_hit freeEnv n ν _
  · exact updateFree_miss freeEnv _ hit

/-- Updating an environment at a variable that does not occur free changes
nothing the term can see. -/
theorem updateFree_notFree {A : Term} {x : Nat} {al : Typ} (freeEnv : FreeEnv IndSig)
    (argument : DenoteTy al.denote) (notFree : ∀ τ, (x, τ) ∉ freeVars A) :
    ∀ n ν, (n, ν) ∈ freeVars A →
      updateFree freeEnv x al argument n ν.denote = freeEnv n ν.denote := by
  intro n ν member
  refine updateFree_miss freeEnv argument ?_
  rintro ⟨rfl, rfl⟩
  exact notFree ν member

/-- Interpreting a body under one binder is interpreting it with no binders and
an updated logical environment. -/
theorem eval_lam_body {A : Term} {x : Nat} {al τ : Typ}
    {a₁ : HTm ([(x, al)] : ElabCtx).length} {a₀ : HTm ([] : ElabCtx).length}
    (h₁ : elabTm [(x, al)] A = some (τ, a₁)) (h₀ : elabTm [] A = some (τ, a₀))
    {freeEnv target : FreeEnv IndSig} {boundEnv boundEnv' : BoundEnv (ctxTypes [])}
    {argument : DenoteTy al.denote} {value : DenoteTy τ.denote}
    (agreeTarget : ∀ n ν, (n, ν) ∈ freeVars A →
      updateFree freeEnv x al argument n ν.denote = target n ν.denote)
    (hbody : Eval (ctxTypes [(x, al)]) freeEnv (extendBoundEnv argument boundEnv) a₁
      τ.denote value) :
    Eval (ctxTypes []) target boundEnv' a₀ τ.denote value :=
  elabEval_transfer A h₁ h₀ ((Agrees.nil freeEnv boundEnv).cons x al argument)
    (Agrees.nil target boundEnv') agreeTarget hbody

/-- Inversion for a redex: applying an interpreted lambda. -/
theorem eval_app_lam_inv {depth : Nat} {Γ : BoundCtx IndSig depth} {A B : HTy}
    {body : HTm (depth + 1)} {b : HTm depth} {freeEnv : FreeEnv IndSig}
    {boundEnv : BoundEnv Γ} {value : DenoteTy B} (typing : HasType Γ b A)
    (ev : Eval Γ freeEnv boundEnv (.app (.lam A body) b) B value) :
    ∃ argument, Eval Γ freeEnv boundEnv b A argument ∧
      Eval (extendBound A Γ) freeEnv (extendBoundEnv argument boundEnv) body B value := by
  cases ev with
  | app hfun harg =>
      have pinned := HasType.unique harg.typing typing
      subst pinned
      cases hfun with
      | lam hA hbody => exact ⟨_, harg, hbody _⟩

/-- The value of an interpreted lambda, together with the values of its body. -/
theorem eval_lam_of_body {depth : Nat} {Γ : BoundCtx IndSig depth} {A B : HTy}
    {body : HTm (depth + 1)} {freeEnv : FreeEnv IndSig} {boundEnv : BoundEnv Γ}
    (hA : Kinded A) (hbody : HasType (extendBound A Γ) body B) :
    ∃ F : DenoteTy (Expr.arr A B), Eval Γ freeEnv boundEnv (.lam A body) (.arr A B) F ∧
      ∀ argument, Eval (extendBound A Γ) freeEnv (extendBoundEnv argument boundEnv)
        body B (F argument) := by
  have lamTyping : HasType Γ (.lam A body) (.arr A B) := .lam body hA hbody
  obtain ⟨F, hF⟩ := lamTyping.eval_exists freeEnv boundEnv
  cases hF with
  | lam hA' hb => exact ⟨_, .lam hA' hb, hb⟩

/-- `ax-beta`: substituting a variable for itself. -/
theorem ax_beta {A : Term} {be : Typ} (x : Nat) (al : Typ) (hA : Typed A be) :
    Seq .tru (.app (.app (.eq be) (.app (.lam x al A) (.var x al))) A) := by
  obtain ⟨a₀, h₀⟩ := hA
  obtain ⟨a₁, h₁⟩ := elabTm_reindex A h₀ [(x, al)]
  have hvar : elabTm [] (.var x al) = some (al, varTm [] x al) := rfl
  have hlhs : elabTm [] (.app (.lam x al A) (.var x al)) =
      some (be, .app (.lam al.denote a₁) (varTm [] x al)) := elabTm_app (elabTm_lam h₁) hvar
  refine ⟨_, _, rfl, elabTm_eqApp hlhs h₀, entails_intro fun freeEnv boundEnv _ => ?_⟩
  obtain ⟨vL, evL⟩ := elab_eval_exists hlhs freeEnv boundEnv
  obtain ⟨vR, evR⟩ := elab_eval_exists h₀ freeEnv boundEnv
  have same : vL = vR := by
    obtain ⟨argument, harg, hbody⟩ :=
      eval_app_lam_inv (elabTm_hasType (.var x al) hvar) evL
    have argValue : argument = freeEnv x al.denote :=
      harg.unique (eval_varTm (Agrees.nil freeEnv boundEnv))
    subst argValue
    exact (eval_lam_body h₁ h₀ (fun n ν _ => updateFree_self freeEnv x al n ν) hbody).unique evR
  have computed := eval_eqApp evL evR
  rw [eqValue_pos be same] at computed
  exact computed

/-- `ax-17`: substituting for a variable that does not occur. -/
theorem ax_17 {A B : Term} {al be : Typ} (x : Nat) (hA : Typed A be) (hB : Typed B al)
    (notFree : ∀ τ, (x, τ) ∉ freeVars A) :
    Seq .tru (.br (.app (.lam x al A) B) (.eq be) A) := by
  obtain ⟨a₀, h₀⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨a₁, h₁⟩ := elabTm_reindex A h₀ [(x, al)]
  have hlhs : elabTm [] (.app (.lam x al A) B) = some (be, .app (.lam al.denote a₁) b) :=
    elabTm_app (elabTm_lam h₁) hb
  refine ⟨_, _, rfl, elabTm_br rfl hlhs h₀, entails_intro fun freeEnv boundEnv _ => ?_⟩
  obtain ⟨vL, evL⟩ := elab_eval_exists hlhs freeEnv boundEnv
  obtain ⟨vR, evR⟩ := elab_eval_exists h₀ freeEnv boundEnv
  have same : vL = vR := by
    obtain ⟨argument, harg, hbody⟩ := eval_app_lam_inv (elabTm_hasType B hb) evL
    exact (eval_lam_body h₁ h₀ (updateFree_notFree freeEnv argument notFree) hbody).unique evR
  have computed := eval_eqApp evL evR
  rw [eqValue_pos be same] at computed
  exact computed

set_option maxHeartbeats 1000000 in
/-- `ax-distrc`: substitution distributes over combination. -/
theorem ax_distrc {F A B : Term} {al be ga : Typ} (x : Nat) (hA : Typed A be)
    (hB : Typed B al) (hF : Typed F (.arr be ga)) :
    Seq .tru (.app (.app (.eq ga) (.app (.lam x al (.app F A)) B))
      (.app (.app (.lam x al F) B) (.app (.lam x al A) B))) := by
  obtain ⟨a₀, h₀⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨f₀, hf₀⟩ := hF
  obtain ⟨a₁, h₁⟩ := elabTm_reindex A h₀ [(x, al)]
  obtain ⟨f₁, hf₁⟩ := elabTm_reindex F hf₀ [(x, al)]
  have hlhs : elabTm [] (.app (.lam x al (.app F A)) B) =
      some (ga, .app (.lam al.denote (.app f₁ a₁)) b) :=
    elabTm_app (elabTm_lam (elabTm_app hf₁ h₁)) hb
  have hrhs : elabTm [] (.app (.app (.lam x al F) B) (.app (.lam x al A) B)) =
      some (ga, .app (.app (.lam al.denote f₁) b) (.app (.lam al.denote a₁) b)) :=
    elabTm_app (elabTm_app (elabTm_lam hf₁) hb) (elabTm_app (elabTm_lam h₁) hb)
  refine ⟨_, _, rfl, elabTm_eqApp hlhs hrhs, entails_intro fun freeEnv boundEnv _ => ?_⟩
  obtain ⟨vB, evB⟩ := elab_eval_exists hb freeEnv boundEnv
  obtain ⟨vL, evL⟩ := elab_eval_exists hlhs freeEnv boundEnv
  obtain ⟨vR, evR⟩ := elab_eval_exists hrhs freeEnv boundEnv
  obtain ⟨FF, hFF, hFFbody⟩ := eval_lam_of_body (freeEnv := freeEnv) (boundEnv := boundEnv)
    al.denote_kinded (elabTm_hasType F hf₁)
  obtain ⟨FA, hFA, hFAbody⟩ := eval_lam_of_body (freeEnv := freeEnv) (boundEnv := boundEnv)
    al.denote_kinded (elabTm_hasType A h₁)
  have lamInner : Eval (ctxTypes []) freeEnv boundEnv (.lam al.denote (.app f₁ a₁))
      (.arr al.denote ga.denote) (fun argument => FF argument (FA argument)) := by
    refine .lam al.denote_kinded fun argument => ?_
    have step : Eval (extendBound al.denote (ctxTypes [])) freeEnv
        (extendBoundEnv argument boundEnv) (.app f₁ a₁) ga.denote
        (FF argument (FA argument)) := .app (hFFbody argument) (hFAbody argument)
    exact step
  have left : Eval (ctxTypes []) freeEnv boundEnv (.app (.lam al.denote (.app f₁ a₁)) b)
      ga.denote (FF vB (FA vB)) := by
    have step := Eval.app lamInner evB
    exact step
  have rightFun : Eval (ctxTypes []) freeEnv boundEnv (.app (.lam al.denote f₁) b)
      (.arr be.denote ga.denote) (FF vB) := .app hFF evB
  have rightArg : Eval (ctxTypes []) freeEnv boundEnv (.app (.lam al.denote a₁) b)
      be.denote (FA vB) := .app hFA evB
  have right : Eval (ctxTypes []) freeEnv boundEnv
      (.app (.app (.lam al.denote f₁) b) (.app (.lam al.denote a₁) b)) ga.denote
      (FF vB (FA vB)) := .app rightFun rightArg
  have same : vL = vR := (evL.unique left).trans (evR.unique right).symm
  have computed := eval_eqApp (τ := ga) evL evR
  rw [eqValue_pos ga same] at computed
  exact computed

set_option maxHeartbeats 1000000 in
/-- `ax-leq`: congruence of equality under a binder. -/
theorem ax_leq {R A B : Term} {al be : Typ} (x : Nat)
    (notFreeR : ∀ τ, (x, τ) ∉ freeVars R)
    (hyp : Seq R (.app (.app (.eq be) A) B)) :
    Seq R (.app (.app (.eq (.arr al be)) (.lam x al A)) (.lam x al B)) := by
  obtain ⟨r, e, hr, he, hre⟩ := hyp
  obtain ⟨a₀, b₀, h₀, hb₀, -, rfl⟩ := elabTm_eqApp_inv he
  obtain ⟨a₁, h₁⟩ := elabTm_reindex A h₀ [(x, al)]
  obtain ⟨b₁, hb₁⟩ := elabTm_reindex B hb₀ [(x, al)]
  refine ⟨r, _, hr, elabTm_eqApp (elabTm_lam h₁) (elabTm_lam hb₁),
    entails_intro fun freeEnv boundEnv rTrue => ?_⟩
  obtain ⟨FA, hFA, hFAbody⟩ := eval_lam_of_body (freeEnv := freeEnv) (boundEnv := boundEnv)
    al.denote_kinded (elabTm_hasType A h₁)
  obtain ⟨FB, hFB, hFBbody⟩ := eval_lam_of_body (freeEnv := freeEnv) (boundEnv := boundEnv)
    al.denote_kinded (elabTm_hasType B hb₁)
  have same : FA = FB := by
    funext argument
    have leftValue : Eval (ctxTypes []) (updateFree freeEnv x al argument) boundEnv a₀
        be.denote (FA argument) :=
      eval_lam_body h₁ h₀ (fun _ _ _ => rfl) (hFAbody argument)
    have rightValue : Eval (ctxTypes []) (updateFree freeEnv x al argument) boundEnv b₀
        be.denote (FB argument) :=
      eval_lam_body hb₁ hb₀ (fun _ _ _ => rfl) (hFBbody argument)
    have rTarget : Eval (ctxTypes []) (updateFree freeEnv x al argument) boundEnv r
        .boolTy true :=
      elabEval_transfer R hr hr (Agrees.nil freeEnv boundEnv)
        (Agrees.nil (updateFree freeEnv x al argument) boundEnv)
        (fun n ν member => by
          refine (updateFree_miss freeEnv argument ?_).symm
          rintro ⟨rfl, rfl⟩
          exact notFreeR ν member) rTrue
    have equality := entails_elim hre rTarget
    exact eqValue_eq be (equality.unique (eval_eqApp (τ := be) leftValue rightValue)).symm
  have computed := eval_eqApp (τ := .arr al be) hFA hFB
  rw [eqValue_pos (.arr al be) same] at computed
  exact computed

/-- Inversion for the elaboration of the infix equation `[ A = B ]`. -/
theorem elabTm_brEq_inv {ctx : ElabCtx} {al σ : Typ} {A B : Term} {t : HTm ctx.length}
    (h : elabTm ctx (.br A (.eq al) B) = some (σ, t)) :
    ∃ a b : HTm ctx.length, elabTm ctx A = some (al, a) ∧ elabTm ctx B = some (al, b) ∧
      σ = .bool ∧ t = .app (.app (eqFun al ctx.length) a) b := by
  obtain ⟨α, β, l, f, r, hf, hl, hr, rfl⟩ := elabTm_br_inv h
  have pair := Option.some.inj hf
  simp only [Prod.mk.injEq, Typ.arr.injEq] at pair
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := pair
  exact ⟨l, r, hl, hr, rfl, rfl⟩

/-- `ax-eqtypi`: an equation transfers a type from its left to its right side.
Sound because `elabTm_type_unique` makes `hol.mm` typing unique on the annotated
syntax. -/
theorem ax_eqtypi {R A B : Term} {al τ : Typ} (hA : Typed A al)
    (hyp : Seq R (.br A (.eq τ) B)) : Typed B al := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨r, e, -, he, -⟩ := hyp
  obtain ⟨l, rr, hl, hr, -, -⟩ := elabTm_brEq_inv he
  obtain rfl : τ = al := elabTm_type_unique A hl ha
  exact ⟨rr, hr⟩

/-- `ax-eqtypri`: the mirror image of `ax-eqtypi`. -/
theorem ax_eqtypri {R A B : Term} {al τ : Typ} (hA : Typed A al)
    (hyp : Seq R (.br B (.eq τ) A)) : Typed B al := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨r, e, -, he, -⟩ := hyp
  obtain ⟨l, rr, hl, hr, -, -⟩ := elabTm_brEq_inv he
  obtain rfl : τ = al := elabTm_type_unique A hr ha
  exact ⟨l, hl⟩

set_option maxHeartbeats 1000000 in
/-- `ax-distrl`: substitution distributes over abstraction, provided the two
binders are distinct and the substituted term does not mention the inner one. -/
theorem ax_distrl {A B : Term} {al be ga : Typ} (x y : Nat) (distinct : x ≠ y)
    (hA : Typed A ga) (hB : Typed B al) (notFreeB : ∀ τ, (y, τ) ∉ freeVars B) :
    Seq .tru (.app (.app (.eq (.arr be ga)) (.app (.lam x al (.lam y be A)) B))
      (.lam y be (.app (.lam x al A) B))) := by
  obtain ⟨a₀, h₀⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨a₂, h₂⟩ := elabTm_reindex A h₀ [(y, be), (x, al)]
  obtain ⟨a₂', h₂'⟩ := elabTm_reindex A h₀ [(x, al), (y, be)]
  obtain ⟨b', hb'⟩ := elabTm_reindex B hb [(y, be)]
  have hlhs : elabTm [] (.app (.lam x al (.lam y be A)) B) =
      some (.arr be ga, .app (.lam al.denote (.lam be.denote a₂)) b) :=
    elabTm_app (elabTm_lam (elabTm_lam h₂)) hb
  have hrhs : elabTm [] (.lam y be (.app (.lam x al A) B)) =
      some (.arr be ga, .lam be.denote (.app (.lam al.denote a₂') b')) :=
    elabTm_lam (elabTm_app (elabTm_lam h₂') hb')
  refine ⟨_, _, rfl, elabTm_eqApp hlhs hrhs, entails_intro fun freeEnv boundEnv _ => ?_⟩
  obtain ⟨vL, evL⟩ := elab_eval_exists hlhs freeEnv boundEnv
  obtain ⟨vR, evR⟩ := elab_eval_exists hrhs freeEnv boundEnv
  obtain ⟨vB, evB, innerLam⟩ := eval_app_lam_inv (elabTm_hasType B hb) evL
  have same : vL = vR := by
    funext v
    have leftBody : Eval (ctxTypes [(y, be), (x, al)]) freeEnv
        (extendBoundEnv v (extendBoundEnv vB boundEnv)) a₂ ga.denote (vL v) := by
      cases innerLam with
      | lam hA' hbody => exact hbody v
    have rightBody : Eval (extendBound be.denote (ctxTypes [])) freeEnv
        (extendBoundEnv v boundEnv) (.app (.lam al.denote a₂') b') ga.denote (vR v) := by
      cases evR with
      | lam hA' hbody => exact hbody v
    obtain ⟨innerArg, innerEval, deepBody⟩ :=
      eval_app_lam_inv (elabTm_hasType B hb') rightBody
    have argSame : innerArg = vB := by
      refine Eval.unique ?_ evB
      exact elabEval_transfer B hb' hb ((Agrees.nil freeEnv boundEnv).cons y be v)
        (Agrees.nil freeEnv boundEnv)
        (fun n ν member => updateFree_miss freeEnv v (by
          rintro ⟨rfl, rfl⟩
          exact notFreeB ν member)) innerEval
    subst argSame
    have transferred : Eval (ctxTypes [(y, be), (x, al)]) freeEnv
        (extendBoundEnv v (extendBoundEnv innerArg boundEnv)) a₂ ga.denote (vR v) :=
      elabEval_transfer A h₂' h₂
        (((Agrees.nil freeEnv boundEnv).cons y be v).cons x al innerArg)
        (((Agrees.nil freeEnv boundEnv).cons x al innerArg).cons y be v)
        (fun n ν _ => by
          have swapX : ¬(x = y ∧ al = be) := fun h => distinct h.1
          by_cases hx : n = x ∧ ν = al
          · obtain ⟨rfl, rfl⟩ := hx
            rw [updateFree_hit, updateFree_miss (updateFree freeEnv n ν innerArg) v swapX,
              updateFree_hit]
          · by_cases hy : n = y ∧ ν = be
            · obtain ⟨rfl, rfl⟩ := hy
              rw [updateFree_miss (updateFree freeEnv n ν v) innerArg hx, updateFree_hit,
                updateFree_hit]
            · rw [updateFree_miss (updateFree freeEnv y be v) innerArg hx,
                updateFree_miss freeEnv v hy,
                updateFree_miss (updateFree freeEnv x al innerArg) v hy,
                updateFree_miss freeEnv innerArg hx])
        deepBody
    exact leftBody.unique transferred
  have computed := eval_eqApp (τ := .arr be ga) evL evR
  rw [eqValue_pos (.arr be ga) same] at computed
  exact computed

/-! ## `ax-hbl1` is refuted

`ax-hbl1` says that a substitution for `x` does not enter `\ x : be . A`, for
*any* `be` — including a `be` different from the type `al` the substitution is
made at. That forces `hol.mm`'s binders to capture by **name alone**, ignoring
the type annotation the surface syntax writes at every occurrence.

The interpretation here reads a variable as the pair (name, type), which is what
every standard presentation of HOL does and what `ax-beta`, `ax-17`,
`ax-distrc` and `ax-leq` are validated by above. Under that reading `ax-hbl1`
is false, and the instance below is a counterexample: with `al = bool`,
`be = ind`, `A = x : bool` and `B = T.`, the left-hand side is the constant
function `⊤` and the right-hand side is the constant function `x : bool`, which
the model may set to `⊥`.

The two readings are not reconcilable, which is the substantive finding: see the
module documentation of `Nucleus.Metamath.HolMM`. -/

/-- The instance of `ax-hbl1`'s conclusion that the interpretation refutes:
`[ ( \ x : bool . \ x : ind . x : bool   T. ) = \ x : ind . x : bool ]`. -/
def hbl1Instance : Term :=
  .br (.app (.lam 0 .bool (.lam 0 .ind (.var 0 .bool))) .tru) (.eq (.arr .ind .bool))
    (.lam 0 .ind (.var 0 .bool))

/-- The interpretation of the left-hand side of `hbl1Instance`. The inner `x`
occurrence is captured by the *outer* binder, because the two binders are for
different (name, type) pairs. -/
def hbl1Left : HTm 0 :=
  .app (.lam Typ.bool.denote (.lam Typ.ind.denote (.bv (Fin.succ 0)))) (.bool true)

/-- The interpretation of the right-hand side of `hbl1Instance`: the `x : bool`
occurrence is free, since the only binder is for `x : ind`. -/
def hbl1Right : HTm 0 := .lam Typ.ind.denote (.fv 0 Typ.bool.denote)

/-- What `hbl1Instance` elaborates to. -/
theorem hbl1_elab : elabTm [] hbl1Instance =
    some (.bool, .app (.app (eqFun (.arr .ind .bool) 0) hbl1Left) hbl1Right) := rfl

/-- The left-hand side denotes the constant function `⊤`. -/
theorem hbl1Left_eval :
    Eval (ctxTypes []) defaultFreeEnv emptyBoundEnv hbl1Left
      (Typ.arr .ind .bool).denote (fun _ => true) := by
  have inner : ∀ selector : DenoteTy Typ.bool.denote,
      Eval (extendBound Typ.bool.denote (ctxTypes [])) defaultFreeEnv
        (extendBoundEnv selector emptyBoundEnv) (.lam Typ.ind.denote (.bv (Fin.succ 0)))
        (.arr Typ.ind.denote Typ.bool.denote) (fun _ => selector) := by
    intro selector
    exact .lam Typ.ind.denote_kinded fun individual =>
      eval_bv_one Typ.bool.denote_kinded defaultFreeEnv emptyBoundEnv selector individual
  have outer : Eval (ctxTypes []) defaultFreeEnv emptyBoundEnv
      (.lam Typ.bool.denote (.lam Typ.ind.denote (.bv (Fin.succ 0))))
      (.arr Typ.bool.denote (.arr Typ.ind.denote Typ.bool.denote))
      (fun selector _ => selector) := .lam Typ.bool.denote_kinded inner
  have applied := Eval.app outer (Eval.boolean (Γ := ctxTypes []) true)
  exact applied

/-- The default environment sends every Boolean variable to `⊥`. -/
theorem defaultFreeEnv_bool (n : Nat) :
    (defaultFreeEnv : FreeEnv IndSig) n Typ.bool.denote = false := by
  simp [defaultFreeEnv, Typ.denote, defaultValue]

/-- The right-hand side denotes the constant function `x : bool`, which the
default environment sets to `⊥`. -/
theorem hbl1Right_eval :
    Eval (ctxTypes []) defaultFreeEnv emptyBoundEnv hbl1Right
      (Typ.arr .ind .bool).denote (fun _ => false) := by
  refine .lam Typ.ind.denote_kinded fun individual => ?_
  have step := Eval.fv (Γ := extendBound Typ.ind.denote (ctxTypes [])) 0 defaultFreeEnv
    (extendBoundEnv individual emptyBoundEnv) (A := Typ.bool.denote) Typ.bool.denote_kinded
  rw [defaultFreeEnv_bool] at step
  exact step

/-- **`ax-hbl1` is not valid in this interpretation.** Its hypotheses hold and
its conclusion fails. -/
theorem ax_hbl1_counterexample :
    Typed (.var 0 .bool) .bool ∧ Typed .tru .bool ∧ ¬Seq .tru hbl1Instance := by
  refine ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ?_⟩
  rintro ⟨r, a, hr, ha, entail⟩
  obtain rfl : r = .bool true := (congrArg Prod.snd (Option.some.inj hr)).symm
  obtain rfl := congrArg Prod.snd (Option.some.inj (ha.symm.trans hbl1_elab))
  have trueSide := entails_elim entail
    (Eval.boolean (Γ := ctxTypes []) (freeEnv := defaultFreeEnv)
      (boundEnv := emptyBoundEnv) true)
  have falseSide := eval_eqApp (τ := .arr .ind .bool) hbl1Left_eval hbl1Right_eval
  have distinct : (fun _ => true : DenoteTy (Typ.arr .ind .bool).denote) ≠ fun _ => false :=
    fun equal => Bool.noConfusion (congrFun equal (defaultValue Typ.ind.denote))
  rw [eqValue_neg (.arr .ind .bool) distinct] at falseSide
  exact Bool.noConfusion (trueSide.unique falseSide)

end Nucleus.Metamath.HolMM
