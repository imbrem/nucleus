import Nucleus.HolLN.Syntax

/-!
# Scope, freshness, and renaming

Although `Fin` makes every `Tm n` scoped at `n` by construction, required
depth remains useful as the certificate later raw representations compute.
`RecursiveScopedAt` is the direct recursive predicate; its equivalence with
the numerical `ScopedAt` definition is proved below.
-/

namespace Nucleus.HolLN

universe u

def liftRen {m n : Nat} (ρ : Fin m -> Fin n) : Fin (m + 1) -> Fin (n + 1) :=
  Fin.cases 0 (fun i => Fin.succ (ρ i))

def rename {Base : Type u} {m n : Nat} (ρ : Fin m -> Fin n) : Tm Base m -> Tm Base n
  | .bound i => .bound (ρ i)
  | .free name A => .free name A
  | .app f x => .app (rename ρ f) (rename ρ x)
  | .lam A body => .lam A (rename (liftRen ρ) body)
  | .bool b => .bool b
  | .zero => .zero
  | .succ value => .succ (rename ρ value)
  | .eq A x y => .eq A (rename ρ x) (rename ρ y)
  | .eps A p => .eps A (rename ρ p)
  | .abs A p x => .abs A p (rename ρ x)
  | .rep A p x => .rep A p (rename ρ x)

def weaken {Base : Type u} {n : Nat} : Tm Base n -> Tm Base (n + 1) :=
  rename Fin.succ

def FreeIn {Base : Type u} (name : Nat) : {s : HolSort} -> {n : Nat} ->
    Hol Base s n -> Prop
  | _, _, .base _ => False
  | _, _, .boolTy => False
  | _, _, .natTy => False
  | _, _, .arr A B => FreeIn name A ∨ FreeIn name B
  | _, _, .sub A p => FreeIn name A ∨ FreeIn name p
  | _, _, .bound _ => False
  | _, _, .free freeName A => freeName = name ∨ FreeIn name A
  | _, _, .app f x => FreeIn name f ∨ FreeIn name x
  | _, _, .lam A body => FreeIn name A ∨ FreeIn name body
  | _, _, .bool _ => False
  | _, _, .zero => False
  | _, _, .succ value => FreeIn name value
  | _, _, .eq A x y => FreeIn name A ∨ FreeIn name x ∨ FreeIn name y
  | _, _, .eps A p => FreeIn name A ∨ FreeIn name p
  | _, _, .abs A p x => FreeIn name A ∨ FreeIn name p ∨ FreeIn name x
  | _, _, .rep A p x => FreeIn name A ∨ FreeIn name p ∨ FreeIn name x

def Fresh {Base : Type u} (name : Nat) {s : HolSort} {n : Nat}
    (expression : Hol Base s n) : Prop :=
  ¬ FreeIn name expression

theorem freeIn_rename_iff {Base : Type u} (name : Nat) {m n : Nat}
    (ρ : Fin m -> Fin n) : (term : Tm Base m) ->
      FreeIn name (rename ρ term) ↔ FreeIn name term
  | .bound i => by simp [rename, FreeIn]
  | .free other A => by simp [rename, FreeIn]
  | .app f x => by
      simp [rename, FreeIn, freeIn_rename_iff name ρ f, freeIn_rename_iff name ρ x]
  | .lam A body => by
      simp [rename, FreeIn, freeIn_rename_iff name (liftRen ρ) body]
  | .bool value => by simp [rename, FreeIn]
  | .zero => by simp [rename, FreeIn]
  | .succ value => by
      simpa [rename, FreeIn] using freeIn_rename_iff name ρ value
  | .eq A x y => by
      simp [rename, FreeIn, freeIn_rename_iff name ρ x, freeIn_rename_iff name ρ y]
  | .eps A p => by
      simp [rename, FreeIn, freeIn_rename_iff name ρ p]
  | .abs A p x => by
      simp [rename, FreeIn, freeIn_rename_iff name ρ x]
  | .rep A p x => by
      simp [rename, FreeIn, freeIn_rename_iff name ρ x]

theorem fresh_rename_iff {Base : Type u} (name : Nat) {m n : Nat}
    (ρ : Fin m -> Fin n) (term : Tm Base m) :
    Fresh name (rename ρ term) ↔ Fresh name term := by
  simp [Fresh, freeIn_rename_iff]

theorem fresh_weaken_iff {Base : Type u} (name : Nat) {n : Nat} (term : Tm Base n) :
    Fresh name (weaken term) ↔ Fresh name term := by
  exact fresh_rename_iff name Fin.succ term

def RequiredDepth {Base : Type u} : {n : Nat} -> Tm Base n -> Nat
  | _, .bound i => i.val + 1
  | _, .free _ _ => 0
  | _, .app f x => max (RequiredDepth f) (RequiredDepth x)
  | _, .lam _ body => (RequiredDepth body).pred
  | _, .bool _ => 0
  | _, .zero => 0
  | _, .succ value => RequiredDepth value
  | _, .eq _ x y => max (RequiredDepth x) (RequiredDepth y)
  | _, .eps _ p => RequiredDepth p
  | _, .abs _ _ x => RequiredDepth x
  | _, .rep _ _ x => RequiredDepth x

def ScopedAt {Base : Type u} (depth : Nat) {n : Nat} (term : Tm Base n) : Prop :=
  RequiredDepth term ≤ depth

def RecursiveScopedAt {Base : Type u} (depth : Nat) : {n : Nat} -> Tm Base n -> Prop
  | _, .bound i => i.val < depth
  | _, .free _ _ => True
  | _, .app f x => RecursiveScopedAt depth f ∧ RecursiveScopedAt depth x
  | _, .lam _ body => RecursiveScopedAt (depth + 1) body
  | _, .bool _ => True
  | _, .zero => True
  | _, .succ value => RecursiveScopedAt depth value
  | _, .eq _ x y => RecursiveScopedAt depth x ∧ RecursiveScopedAt depth y
  | _, .eps _ p => RecursiveScopedAt depth p
  | _, .abs _ _ x => RecursiveScopedAt depth x
  | _, .rep _ _ x => RecursiveScopedAt depth x

theorem requiredDepth_le_index {Base : Type u} : {n : Nat} -> (t : Tm Base n) ->
    RequiredDepth t ≤ n
  | _, .bound i => by simpa [RequiredDepth] using Nat.succ_le_of_lt i.isLt
  | _, .free _ _ => by simp [RequiredDepth]
  | _, .app f x => by
      simp only [RequiredDepth]
      exact Nat.max_le.mpr ⟨requiredDepth_le_index f, requiredDepth_le_index x⟩
  | n, .lam _ body => by
      simp only [RequiredDepth]
      exact Nat.pred_le_iff.mpr
        (by simpa [Nat.add_comm] using requiredDepth_le_index body)
  | _, .bool _ => by simp [RequiredDepth]
  | _, .zero => by simp [RequiredDepth]
  | _, .succ value => by simpa [RequiredDepth] using requiredDepth_le_index value
  | _, .eq _ x y => by
      simp only [RequiredDepth]
      exact Nat.max_le.mpr ⟨requiredDepth_le_index x, requiredDepth_le_index y⟩
  | _, .eps _ p => by simpa [RequiredDepth] using requiredDepth_le_index p
  | _, .abs _ _ x => by simpa [RequiredDepth] using requiredDepth_le_index x
  | _, .rep _ _ x => by simpa [RequiredDepth] using requiredDepth_le_index x

theorem scopedAt_index {Base : Type u} {n : Nat} (t : Tm Base n) : ScopedAt n t :=
  requiredDepth_le_index t

theorem recursiveScopedAt_iff {Base : Type u} (depth : Nat) :
    {n : Nat} -> (t : Tm Base n) ->
    RecursiveScopedAt depth t ↔ ScopedAt depth t
  | _, .bound i => by simp [RecursiveScopedAt, ScopedAt, RequiredDepth, Nat.succ_le_iff]
  | _, .free _ _ => by simp [RecursiveScopedAt, ScopedAt, RequiredDepth]
  | _, .app f x => by
      simp [RecursiveScopedAt, ScopedAt, RequiredDepth, recursiveScopedAt_iff depth f,
        recursiveScopedAt_iff depth x, Nat.max_le]
  | _, .lam A body => by
      simp [RecursiveScopedAt, ScopedAt, RequiredDepth,
        recursiveScopedAt_iff (depth + 1) body]
  | _, .bool _ => by simp [RecursiveScopedAt, ScopedAt, RequiredDepth]
  | _, .zero => by simp [RecursiveScopedAt, ScopedAt, RequiredDepth]
  | _, .succ value => by
      simpa [RecursiveScopedAt, ScopedAt, RequiredDepth] using
        recursiveScopedAt_iff depth value
  | _, .eq A x y => by
      simp [RecursiveScopedAt, ScopedAt, RequiredDepth, recursiveScopedAt_iff depth x,
        recursiveScopedAt_iff depth y, Nat.max_le]
  | _, .eps A p => by simpa [RecursiveScopedAt, ScopedAt, RequiredDepth] using
      recursiveScopedAt_iff depth p
  | _, .abs A p x => by simpa [RecursiveScopedAt, ScopedAt, RequiredDepth] using
      recursiveScopedAt_iff depth x
  | _, .rep A p x => by simpa [RecursiveScopedAt, ScopedAt, RequiredDepth] using
      recursiveScopedAt_iff depth x

end Nucleus.HolLN
