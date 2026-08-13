import Nucleus.HolLN.Scope

/-!
# Locally nameless opening, closing, and substitution

Bound substitution instantiates de Bruijn variables.  Free substitution is
capture avoiding because its range is weakened below binders.  Closing turns a
chosen free name into the newest bound variable, and opening reverses it.
-/

namespace Nucleus.HolLN

universe u

def liftSub {Base : Type u} {m n : Nat} (σ : Fin m -> Tm Base n) :
    Fin (m + 1) -> Tm Base (n + 1) :=
  Fin.cases (.bv 0) (fun i => weaken (σ i))

def instantiate {Base : Type u} {m n : Nat} (σ : Fin m -> Tm Base n) :
    Tm Base m -> Tm Base n
  | .bv i => σ i
  | .fv name A => .fv name A
  | .app f x => .app (instantiate σ f) (instantiate σ x)
  | .lam A body => .lam A (instantiate (liftSub σ) body)
  | .bool b => .bool b
  | .zero => .zero
  | .succ value => .succ (instantiate σ value)
  | .eq A x y => .eq A (instantiate σ x) (instantiate σ y)
  | .eps A p => .eps A (instantiate σ p)
  | .abs A p x => .abs A p (instantiate σ x)
  | .rep A p x => .rep A p (instantiate σ x)

def openBound {Base : Type u} {n : Nat} (body : Tm Base (n + 1))
    (replacement : Tm Base n) : Tm Base n :=
  instantiate (Fin.cases replacement .bv) body

def openFree {Base : Type u} {n : Nat} (body : Tm Base (n + 1))
    (name : Nat) (A : Ty Base) : Tm Base n :=
  openBound body (.fv name A)

/-- Instantiate a predicate from its fixed one-variable context at any depth. -/
def instantiateOne {Base : Type u} {n : Nat} (predicate : Tm Base 1)
    (replacement : Tm Base n) : Tm Base n :=
  instantiate (fun _ => replacement) predicate

def substFree {Base : Type u} {n : Nat} (name : Nat) (replacement : Tm Base n) :
    Tm Base n -> Tm Base n
  | .bv i => .bv i
  | .fv other A => if other = name then replacement else .fv other A
  | .app f x => .app (substFree name replacement f) (substFree name replacement x)
  | .lam A body => .lam A (substFree name (weaken replacement) body)
  | .bool b => .bool b
  | .zero => .zero
  | .succ value => .succ (substFree name replacement value)
  | .eq A x y => .eq A (substFree name replacement x) (substFree name replacement y)
  | .eps A p => .eps A (substFree name replacement p)
  | .abs A p x => .abs A p (substFree name replacement x)
  | .rep A p x => .rep A p (substFree name replacement x)

/-- General closing traversal. `fresh` is the newly introduced binder and `ρ`
embeds the bound variables already present in the source. -/
def closeAux {Base : Type u} {m n : Nat} (name : Nat) (fresh : Fin n)
    (ρ : Fin m -> Fin n) : Tm Base m -> Tm Base n
  | .bv i => .bv (ρ i)
  | .fv other A => if other = name then .bv fresh else .fv other A
  | .app f x => .app (closeAux name fresh ρ f) (closeAux name fresh ρ x)
  | .lam A body => .lam A (closeAux name fresh.succ (liftRen ρ) body)
  | .bool b => .bool b
  | .zero => .zero
  | .succ value => .succ (closeAux name fresh ρ value)
  | .eq A x y => .eq A (closeAux name fresh ρ x) (closeAux name fresh ρ y)
  | .eps A p => .eps A (closeAux name fresh ρ p)
  | .abs A p x => .abs A p (closeAux name fresh ρ x)
  | .rep A p x => .rep A p (closeAux name fresh ρ x)

/-- Close a free name as a new outermost binder. -/
def close {Base : Type u} {n : Nat} (name : Nat) (term : Tm Base n) :
    Tm Base (n + 1) :=
  closeAux name 0 Fin.succ term

theorem liftRen_id (n : Nat) : liftRen (fun i : Fin n => i) = fun i => i := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

theorem rename_id {Base : Type u} : {n : Nat} -> (t : Tm Base n) ->
    rename (fun i => i) t = t
  | _, .bv _ => by simp [rename]
  | _, .fv _ _ => by simp [rename]
  | _, .app f x => by simp [rename, rename_id f, rename_id x]
  | _, .lam A body => by
      simp [rename, liftRen_id, rename_id body]
  | _, .bool _ => by simp [rename]
  | _, .zero => by simp [rename]
  | _, .succ value => by simp [rename, rename_id value]
  | _, .eq A x y => by simp [rename, rename_id x, rename_id y]
  | _, .eps A p => by simp [rename, rename_id p]
  | _, .abs A p x => by simp [rename, rename_id x]
  | _, .rep A p x => by simp [rename, rename_id x]

theorem rename_comp {Base : Type u} {m n q : Nat}
    (ρ : Fin m -> Fin n) (τ : Fin n -> Fin q) : (t : Tm Base m) ->
    rename τ (rename ρ t) = rename (fun i => τ (ρ i)) t
  | .bv _ => by simp [rename]
  | .fv _ _ => by simp [rename]
  | .app f x => by simp [rename, rename_comp ρ τ f, rename_comp ρ τ x]
  | .lam A body => by
      simp only [rename]
      rw [rename_comp]
      congr 2
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
  | .bool _ => by simp [rename]
  | .zero => by simp [rename]
  | .succ value => by simp [rename, rename_comp ρ τ value]
  | .eq A x y => by simp [rename, rename_comp ρ τ x, rename_comp ρ τ y]
  | .eps A p => by simp [rename, rename_comp ρ τ p]
  | .abs A p x => by simp [rename, rename_comp ρ τ x]
  | .rep A p x => by simp [rename, rename_comp ρ τ x]

theorem liftSub_bound {Base : Type u} (n : Nat) :
    liftSub (fun i : Fin n => (.bv i : Tm Base n)) =
      fun i => (.bv i : Tm Base (n + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [liftSub, weaken, rename]

/-- Simultaneous bound instantiation by the original variables is identity. -/
theorem instantiate_identity {Base : Type u} : {n : Nat} -> (term : Tm Base n) ->
    instantiate (fun i => .bv i) term = term
  | _, .bv i => by simp [instantiate]
  | _, .fv name A => by simp [instantiate]
  | _, .app f x => by
      simp [instantiate, instantiate_identity f, instantiate_identity x]
  | n, .lam A body => by
      simp only [instantiate]
      rw [liftSub_bound n]
      rw [instantiate_identity body]
  | _, .bool value => by simp [instantiate]
  | _, .zero => by simp [instantiate]
  | _, .succ value => by simp [instantiate, instantiate_identity value]
  | _, .eq A x y => by
      simp [instantiate, instantiate_identity x, instantiate_identity y]
  | _, .eps A p => by simp [instantiate, instantiate_identity p]
  | _, .abs A p x => by simp [instantiate, instantiate_identity x]
  | _, .rep A p x => by simp [instantiate, instantiate_identity x]

theorem weaken_free {Base : Type u} {n : Nat} (name : Nat) (A : Ty Base) :
    weaken (.fv name A : Tm Base n) = (.fv name A : Tm Base (n + 1)) := by
  simp [weaken, rename]

theorem substFree_fresh {Base : Type u} (name : Nat) {n : Nat}
    (replacement : Tm Base n) : (term : Tm Base n) -> Fresh name term ->
      substFree name replacement term = term
  | .bv i, _ => by simp [substFree]
  | .fv other A, freshness => by
      have h : other ≠ name := by
        intro equality
        exact freshness (Or.inl equality)
      simp [substFree, h]
  | .app f x, freshness => by
      have hf : Fresh name f := fun found => freshness (Or.inl found)
      have hx : Fresh name x := fun found => freshness (Or.inr found)
      simp [substFree, substFree_fresh name replacement f hf,
        substFree_fresh name replacement x hx]
  | .lam A body, freshness => by
      have hbody : Fresh name body := fun found => freshness (Or.inr found)
      simp [substFree, substFree_fresh name (weaken replacement) body hbody]
  | .bool value, _ => by simp [substFree]
  | .zero, _ => by simp [substFree]
  | .succ value, freshness => by
      simp [substFree, substFree_fresh name replacement value freshness]
  | .eq A x y, freshness => by
      have hx : Fresh name x := fun found => freshness (Or.inr (Or.inl found))
      have hy : Fresh name y := fun found => freshness (Or.inr (Or.inr found))
      simp [substFree, substFree_fresh name replacement x hx,
        substFree_fresh name replacement y hy]
  | .eps A p, freshness => by
      have hp : Fresh name p := fun found => freshness (Or.inr found)
      simp [substFree, substFree_fresh name replacement p hp]
  | .abs A p x, freshness => by
      have hx : Fresh name x := fun found => freshness (Or.inr (Or.inr found))
      simp [substFree, substFree_fresh name replacement x hx]
  | .rep A p x, freshness => by
      have hx : Fresh name x := fun found => freshness (Or.inr (Or.inr found))
      simp [substFree, substFree_fresh name replacement x hx]

theorem substFree_rename {Base : Type u} (name : Nat) :
    {m n : Nat} -> (replacement : Tm Base m) -> (ρ : Fin m -> Fin n) ->
      (term : Tm Base m) ->
      substFree name (rename ρ replacement) (rename ρ term) =
        rename ρ (substFree name replacement term)
  | _, _, replacement, ρ, .bv i => by simp [substFree, rename]
  | _, _, replacement, ρ, .fv other A => by
      by_cases h : other = name <;> simp [substFree, rename, h]
  | _, _, replacement, ρ, .app f x => by
      simp [substFree, rename, substFree_rename name replacement ρ f,
        substFree_rename name replacement ρ x]
  | _, _, replacement, ρ, .lam A body => by
      simp only [substFree, rename]
      have replacementNaturality :
          weaken (rename ρ replacement) = rename (liftRen ρ) (weaken replacement) := by
        simp only [weaken, rename_comp]
        congr 1
      rw [replacementNaturality]
      rw [substFree_rename name (weaken replacement) (liftRen ρ) body]
  | _, _, replacement, ρ, .bool value => by simp [substFree, rename]
  | _, _, replacement, ρ, .zero => by simp [substFree, rename]
  | _, _, replacement, ρ, .succ value => by
      simp [substFree, rename, substFree_rename name replacement ρ value]
  | _, _, replacement, ρ, .eq A x y => by
      simp [substFree, rename, substFree_rename name replacement ρ x,
        substFree_rename name replacement ρ y]
  | _, _, replacement, ρ, .eps A p => by
      simp [substFree, rename, substFree_rename name replacement ρ p]
  | _, _, replacement, ρ, .abs A p x => by
      simp [substFree, rename, substFree_rename name replacement ρ x]
  | _, _, replacement, ρ, .rep A p x => by
      simp [substFree, rename, substFree_rename name replacement ρ x]

theorem substFree_weaken {Base : Type u} (name : Nat) {n : Nat}
    (replacement term : Tm Base n) :
    substFree name (weaken replacement) (weaken term) =
      weaken (substFree name replacement term) :=
  substFree_rename name replacement Fin.succ term

/-- Standard composition law for substitutions at distinct free names. -/
theorem substFree_comp {Base : Type u} {n : Nat} {first second : Nat}
    (different : first ≠ second) (replacement : Tm Base n)
    (freshReplacement : Fresh second replacement) (secondReplacement : Tm Base n) :
    (term : Tm Base n) ->
      substFree first replacement (substFree second secondReplacement term) =
        substFree second (substFree first replacement secondReplacement)
          (substFree first replacement term)
  | .bv i => by simp [substFree]
  | .fv name A => by
      by_cases hfirst : name = first
      · subst name
        have hsecond : first ≠ second := different
        simp [substFree, hsecond,
          substFree_fresh second (substFree first replacement secondReplacement)
            replacement freshReplacement]
      · by_cases hsecond : name = second
        · subst name
          simp [substFree, hfirst]
        · simp [substFree, hfirst, hsecond]
  | .app f x => by
      simp [substFree, substFree_comp different replacement freshReplacement secondReplacement f,
        substFree_comp different replacement freshReplacement secondReplacement x]
  | .lam A body => by
      simp only [substFree]
      have ih := substFree_comp different (weaken replacement)
          (fresh_weaken_iff second replacement |>.2 freshReplacement)
          (weaken secondReplacement) body
      rw [substFree_weaken] at ih
      exact congrArg (Hol.lam A) ih
  | .bool value => by simp [substFree]
  | .zero => by simp [substFree]
  | .succ value => by
      simp [substFree,
        substFree_comp different replacement freshReplacement secondReplacement value]
  | .eq A x y => by
      simp [substFree, substFree_comp different replacement freshReplacement secondReplacement x,
        substFree_comp different replacement freshReplacement secondReplacement y]
  | .eps A p => by
      simp [substFree,
        substFree_comp different replacement freshReplacement secondReplacement p]
  | .abs A p x => by
      simp [substFree,
        substFree_comp different replacement freshReplacement secondReplacement x]
  | .rep A p x => by
      simp [substFree,
        substFree_comp different replacement freshReplacement secondReplacement x]

/-- Opening the newest binder itself returns the supplied argument. -/
@[simp] theorem openBound_zero {Base : Type u} {n : Nat} (replacement : Tm Base n) :
    openBound (.bv 0 : Tm Base (n + 1)) replacement = replacement := by
  simp [openBound, instantiate]

/-- Opening ignores an outer binder that a term does not use. -/
theorem instantiate_rename_leftInverse {Base : Type u} {m n : Nat}
    (ρ : Fin m -> Fin n) (σ : Fin n -> Tm Base m)
    (restores : ∀ i, σ (ρ i) = .bv i) : (term : Tm Base m) ->
      instantiate σ (rename ρ term) = term
  | .bv i => by simp [rename, instantiate, restores]
  | .fv name A => by simp [rename, instantiate]
  | .app f x => by
      simp [rename, instantiate, instantiate_rename_leftInverse ρ σ restores f,
        instantiate_rename_leftInverse ρ σ restores x]
  | .lam A body => by
      simp only [rename, instantiate]
      congr 2
      apply instantiate_rename_leftInverse (liftRen ρ) (liftSub σ)
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [liftRen, liftSub]
      · simp [liftRen, liftSub, restores, weaken, rename]
  | .bool value => by simp [rename, instantiate]
  | .zero => by simp [rename, instantiate]
  | .succ value => by
      simp [rename, instantiate, instantiate_rename_leftInverse ρ σ restores value]
  | .eq A x y => by
      simp [rename, instantiate, instantiate_rename_leftInverse ρ σ restores x,
        instantiate_rename_leftInverse ρ σ restores y]
  | .eps A p => by
      simp [rename, instantiate, instantiate_rename_leftInverse ρ σ restores p]
  | .abs A p x => by
      simp [rename, instantiate, instantiate_rename_leftInverse ρ σ restores x]
  | .rep A p x => by
      simp [rename, instantiate, instantiate_rename_leftInverse ρ σ restores x]

@[simp] theorem openBound_weaken {Base : Type u} :
    {n : Nat} -> (term replacement : Tm Base n) -> openBound (weaken term) replacement = term
  | _, term, replacement => by
      apply instantiate_rename_leftInverse Fin.succ (Fin.cases replacement .bv)
      intro i
      rfl

theorem closeAux_rename {Base : Type u} {m m' n n' : Nat} (name : Nat)
    (fresh : Fin n) (ρ : Fin m -> Fin n) (κ : Fin m -> Fin m')
    (τ : Fin n -> Fin n') (ρ' : Fin m' -> Fin n')
    (commutes : ∀ i, ρ' (κ i) = τ (ρ i)) : (term : Tm Base m) ->
    closeAux name (τ fresh) ρ' (rename κ term) =
      rename τ (closeAux name fresh ρ term)
  | .bv i => by simp [rename, closeAux, commutes]
  | .fv other A => by
      by_cases h : other = name <;> simp [rename, closeAux, h]
  | .app f x => by
      simp [rename, closeAux,
        closeAux_rename name fresh ρ κ τ ρ' commutes f,
        closeAux_rename name fresh ρ κ τ ρ' commutes x]
  | .lam A body => by
      simp only [rename, closeAux]
      congr 2
      apply closeAux_rename name fresh.succ (liftRen ρ) (liftRen κ)
          (liftRen τ) (liftRen ρ') _ body
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp [liftRen, commutes]
  | .bool value => by simp [rename, closeAux]
  | .zero => by simp [rename, closeAux]
  | .succ value => by
      simp [rename, closeAux,
        closeAux_rename name fresh ρ κ τ ρ' commutes value]
  | .eq A x y => by
      simp [rename, closeAux,
        closeAux_rename name fresh ρ κ τ ρ' commutes x,
        closeAux_rename name fresh ρ κ τ ρ' commutes y]
  | .eps A p => by
      simp [rename, closeAux,
        closeAux_rename name fresh ρ κ τ ρ' commutes p]
  | .abs A p x => by
      simp [rename, closeAux,
        closeAux_rename name fresh ρ κ τ ρ' commutes x]
  | .rep A p x => by
      simp [rename, closeAux,
        closeAux_rename name fresh ρ κ τ ρ' commutes x]

theorem closeAux_weaken {Base : Type u} {m n : Nat} (name : Nat)
    (fresh : Fin n) (ρ : Fin m -> Fin n) (term : Tm Base m) :
    closeAux name fresh.succ (liftRen ρ) (weaken term) =
      weaken (closeAux name fresh ρ term) := by
  apply closeAux_rename name fresh ρ Fin.succ Fin.succ (liftRen ρ)
  intro i
  rfl

theorem closeAux_instantiate {Base : Type u} {m n : Nat} (name : Nat)
    (fresh : Fin n) (ρ : Fin m -> Fin n) (σ : Fin n -> Tm Base m)
    (roundTrip : ∀ i, closeAux name fresh ρ (σ i) = .bv i) :
    (term : Tm Base n) -> Fresh name term ->
      closeAux name fresh ρ (instantiate σ term) = term
  | .bv i, _ => by simpa [instantiate] using roundTrip i
  | .fv other A, freshness => by
      have h : other ≠ name := by
        intro equality
        exact freshness (Or.inl equality)
      simp [instantiate, closeAux, h]
  | .app f x, freshness => by
      have hf : Fresh name f := fun found => freshness (Or.inl found)
      have hx : Fresh name x := fun found => freshness (Or.inr found)
      simp [instantiate, closeAux, closeAux_instantiate name fresh ρ σ roundTrip f hf,
        closeAux_instantiate name fresh ρ σ roundTrip x hx]
  | .lam A body, freshness => by
      have hbody : Fresh name body := fun found => freshness (Or.inr found)
      simp only [instantiate, closeAux]
      congr 2
      apply closeAux_instantiate name fresh.succ (liftRen ρ) (liftSub σ) _ body hbody
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [liftSub, closeAux, liftRen]
      · rw [show liftSub σ j.succ = weaken (σ j) by rfl]
        rw [closeAux_weaken, roundTrip]
        simp [weaken, rename]
  | .bool value, _ => by simp [instantiate, closeAux]
  | .zero, _ => by simp [instantiate, closeAux]
  | .succ value, freshness => by
      simpa [instantiate, closeAux] using
        closeAux_instantiate name fresh ρ σ roundTrip value freshness
  | .eq A x y, freshness => by
      have hx : Fresh name x := fun found => freshness (Or.inr (Or.inl found))
      have hy : Fresh name y := fun found => freshness (Or.inr (Or.inr found))
      simp [instantiate, closeAux, closeAux_instantiate name fresh ρ σ roundTrip x hx,
        closeAux_instantiate name fresh ρ σ roundTrip y hy]
  | .eps A p, freshness => by
      have hp : Fresh name p := fun found => freshness (Or.inr found)
      simpa [instantiate, closeAux] using
        closeAux_instantiate name fresh ρ σ roundTrip p hp
  | .abs A p x, freshness => by
      have hx : Fresh name x := fun found => freshness (Or.inr (Or.inr found))
      simpa [instantiate, closeAux] using
        closeAux_instantiate name fresh ρ σ roundTrip x hx
  | .rep A p x, freshness => by
      have hx : Fresh name x := fun found => freshness (Or.inr (Or.inr found))
      simpa [instantiate, closeAux] using
        closeAux_instantiate name fresh ρ σ roundTrip x hx

/-- Closing after opening recovers a term when the chosen opening name was
fresh in the original body. -/
theorem close_openFree {Base : Type u} (name : Nat) {n : Nat}
    (A : Ty Base) (body : Tm Base (n + 1)) (freshness : Fresh name body) :
    close name (openFree body name A) = body := by
  apply closeAux_instantiate name (0 : Fin (n + 1)) Fin.succ
      (Fin.cases (.fv name A) .bv) _ body freshness
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [closeAux]
  · simp [closeAux]

end Nucleus.HolLN
