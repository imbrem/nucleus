import Mathlib.Data.Finset.Basic

/-!
# Finite dictionaries

`Dict K V` is an extensional finite partial function. It keeps lookup as the
primary operation and carries its finite key set with a proof that the two
views agree.
-/

namespace Nucleus

universe u v

structure Dict (K : Type u) (V : Type v) [DecidableEq K] where
  lookup : K → Option V
  keys : Finset K
  mem_keys : ∀ key, key ∈ keys ↔ (lookup key).isSome

namespace Dict

variable {K : Type u} {V : Type v} [DecidableEq K]

@[ext]
theorem ext {left right : Dict K V}
    (lookup_eq : ∀ key, left.lookup key = right.lookup key) : left = right := by
  cases left with
  | mk leftLookup leftKeys leftMem =>
    cases right with
    | mk rightLookup rightKeys rightMem =>
      have functions : leftLookup = rightLookup := funext lookup_eq
      subst functions
      have keys : leftKeys = rightKeys := by
        ext key
        rw [leftMem, rightMem]
      subst keys
      rfl

def empty : Dict K V where
  lookup := fun _ => none
  keys := ∅
  mem_keys := by simp

instance : EmptyCollection (Dict K V) := ⟨empty⟩

@[simp] theorem lookup_empty (key : K) : (∅ : Dict K V).lookup key = none := rfl

@[simp] theorem keys_empty : (∅ : Dict K V).keys = ∅ := rfl

def singleton (key : K) (value : V) : Dict K V where
  lookup := fun candidate => if candidate = key then some value else none
  keys := {key}
  mem_keys := by
    intro candidate
    simp

@[simp] theorem lookup_singleton_self (key : K) (value : V) :
    (singleton key value).lookup key = some value := by
  simp [singleton]

def insert (dict : Dict K V) (key : K) (value : V) : Dict K V where
  lookup := fun candidate => if candidate = key then some value else dict.lookup candidate
  keys := Insert.insert key dict.keys
  mem_keys := by
    intro candidate
    by_cases equality : candidate = key
    · subst equality
      simp
    · simp [equality, dict.mem_keys]

@[simp] theorem lookup_insert_self (dict : Dict K V) (key : K) (value : V) :
    (dict.insert key value).lookup key = some value := by
  simp [insert]

@[simp] theorem lookup_insert_of_ne (dict : Dict K V) {key candidate : K}
    (different : candidate ≠ key) (value : V) :
    (dict.insert key value).lookup candidate = dict.lookup candidate := by
  simp [insert, different]

def erase (dict : Dict K V) (key : K) : Dict K V where
  lookup := fun candidate => if candidate = key then none else dict.lookup candidate
  keys := dict.keys.erase key
  mem_keys := by
    intro candidate
    by_cases equality : candidate = key
    · subst equality
      simp
    · simp [equality, dict.mem_keys]

@[simp] theorem lookup_erase_self (dict : Dict K V) (key : K) :
    (dict.erase key).lookup key = none := by
  simp [erase]

def getD (dict : Dict K V) (key : K) (fallback : V) : V :=
  (dict.lookup key).getD fallback

def contains (dict : Dict K V) (key : K) : Bool :=
  (dict.lookup key).isSome

@[simp] theorem contains_eq_true {dict : Dict K V} {key : K} :
    dict.contains key = true ↔ key ∈ dict.keys := by
  simp [contains, ← dict.mem_keys]

end Dict

end Nucleus
