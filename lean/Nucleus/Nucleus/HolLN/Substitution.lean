import Mathlib.Tactic
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
  Fin.cases (.bound 0) (fun i => weaken (σ i))

def instantiate {Base : Type u} {m n : Nat} (σ : Fin m -> Tm Base n) :
    Tm Base m -> Tm Base n
  | .bound i => σ i
  | .free a => .free a
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
  instantiate (Fin.cases replacement .bound) body

def openFree {Base : Type u} {n : Nat} (body : Tm Base (n + 1))
    (name : Nat) : Tm Base n :=
  openBound body (.free name)

/-- Instantiate a predicate from its fixed one-variable context at any depth. -/
def instantiateOne {Base : Type u} {n : Nat} (predicate : Tm Base 1)
    (replacement : Tm Base n) : Tm Base n :=
  instantiate (fun _ => replacement) predicate

def substFree {Base : Type u} {n : Nat} (name : Nat) (replacement : Tm Base n) :
    Tm Base n -> Tm Base n
  | .bound i => .bound i
  | .free a => if a = name then replacement else .free a
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
  | .bound i => .bound (ρ i)
  | .free a => if a = name then .bound fresh else .free a
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
  | _, .bound _ => by simp [rename]
  | _, .free _ => by simp [rename]
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
  | .bound _ => by simp [rename]
  | .free _ => by simp [rename]
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

theorem weaken_free {Base : Type u} {n : Nat} (name : Nat) :
    weaken (.free name : Tm Base n) = (.free name : Tm Base (n + 1)) := by
  simp [weaken, rename]

theorem substFree_identity {Base : Type u} (name : Nat) :
    {n : Nat} -> (t : Tm Base n) -> substFree name (.free name) t = t
  | _, .bound _ => by simp [substFree]
  | _, .free other => by
      by_cases h : other = name <;> simp [substFree, h]
  | _, .app f x => by simp [substFree, substFree_identity name f, substFree_identity name x]
  | _, .lam A body => by simp [substFree, weaken_free, substFree_identity name body]
  | _, .bool _ => by simp [substFree]
  | _, .zero => by simp [substFree]
  | _, .succ value => by simp [substFree, substFree_identity name value]
  | _, .eq A x y => by simp [substFree, substFree_identity name x, substFree_identity name y]
  | _, .eps A p => by simp [substFree, substFree_identity name p]
  | _, .abs A p x => by simp [substFree, substFree_identity name x]
  | _, .rep A p x => by simp [substFree, substFree_identity name x]

theorem instantiate_closeAux {Base : Type u} {m n : Nat} (name : Nat)
    (fresh : Fin n) (ρ : Fin m -> Fin n) (σ : Fin n -> Tm Base m)
    (opensFresh : σ fresh = .free name)
    (restores : ∀ i, σ (ρ i) = .bound i) :
    (term : Tm Base m) -> instantiate σ (closeAux name fresh ρ term) = term
  | .bound i => by simp [closeAux, instantiate, restores]
  | .free other => by
      by_cases h : other = name <;> simp [closeAux, instantiate, h, opensFresh]
  | .app f x => by
      simp [closeAux, instantiate, instantiate_closeAux name fresh ρ σ opensFresh restores f,
        instantiate_closeAux name fresh ρ σ opensFresh restores x]
  | .lam A body => by
      simp only [closeAux, instantiate]
      congr 2
      apply instantiate_closeAux name fresh.succ (liftRen ρ) (liftSub σ)
      · simp [liftSub, opensFresh, weaken_free]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [liftRen, liftSub]
        · simp [liftRen, liftSub, restores, weaken, rename]
  | .bool value => by simp [closeAux, instantiate]
  | .zero => by simp [closeAux, instantiate]
  | .succ value => by
      simp [closeAux, instantiate,
        instantiate_closeAux name fresh ρ σ opensFresh restores value]
  | .eq A x y => by
      simp [closeAux, instantiate, instantiate_closeAux name fresh ρ σ opensFresh restores x,
        instantiate_closeAux name fresh ρ σ opensFresh restores y]
  | .eps A p => by
      simp [closeAux, instantiate,
        instantiate_closeAux name fresh ρ σ opensFresh restores p]
  | .abs A p x => by
      simp [closeAux, instantiate,
        instantiate_closeAux name fresh ρ σ opensFresh restores x]
  | .rep A p x => by
      simp [closeAux, instantiate,
        instantiate_closeAux name fresh ρ σ opensFresh restores x]

/-- Opening a freshly closed outer binder is an unconditional round trip. -/
theorem openFree_close {Base : Type u} (name : Nat) {n : Nat} (term : Tm Base n) :
    openFree (close name term) name = term := by
  apply instantiate_closeAux name (0 : Fin (n + 1)) Fin.succ
  · rfl
  · intro i
    rfl

end Nucleus.HolLN
