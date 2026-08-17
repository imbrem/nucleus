import Nucleus.Hol.Signature

namespace Nucleus.Hol

universe u

def liftRen {m n : Nat} (ρ : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

def rename {Sig : Signature} {m n : Nat} (ρ : Fin m → Fin n) : Tm Sig m → Tm Sig n
  | .primTm symbol => .primTm symbol
  | .bv i => .bv (ρ i)
  | .fv name A => .fv name A
  | .app f x => .app (rename ρ f) (rename ρ x)
  | .lam A body => .lam A (rename (liftRen ρ) body)
  | .bool value => .bool value
  | .eq A x y => .eq A (rename ρ x) (rename ρ y)
  | .eps A p => .eps A (rename ρ p)
  | .abs A p x => .abs A p (rename ρ x)
  | .rep A p x => .rep A p (rename ρ x)

def weaken {Sig : Signature} {depth : Nat} (tm : Tm Sig depth) : Tm Sig (depth + 1) :=
  rename Fin.succ tm

def liftSub {Sig : Signature} {m n : Nat} (σ : Fin m → Tm Sig n) :
    Fin (m + 1) → Tm Sig (n + 1) :=
  Fin.cases (.bv 0) (fun i => weaken (σ i))

def instantiate {Sig : Signature} {m n : Nat} (σ : Fin m → Tm Sig n) :
    Tm Sig m → Tm Sig n
  | .primTm symbol => .primTm symbol
  | .bv i => σ i
  | .fv name A => .fv name A
  | .app f x => .app (instantiate σ f) (instantiate σ x)
  | .lam A body => .lam A (instantiate (liftSub σ) body)
  | .bool value => .bool value
  | .eq A x y => .eq A (instantiate σ x) (instantiate σ y)
  | .eps A p => .eps A (instantiate σ p)
  | .abs A p x => .abs A p (instantiate σ x)
  | .rep A p x => .rep A p (instantiate σ x)

def openBound {Sig : Signature} {depth : Nat} (body : Tm Sig (depth + 1))
    (replacement : Tm Sig depth) : Tm Sig depth :=
  instantiate (Fin.cases replacement .bv) body

def instantiateOne {Sig : Signature} {depth : Nat} (predicate : Tm Sig 1)
    (replacement : Tm Sig depth) : Tm Sig depth :=
  instantiate (fun _ => replacement) predicate

def FreeIn {Sig : Signature} (name : Nat) : {sort : HolSort} → {depth : Nat} →
    Expr Sig sort depth → Prop
  | _, _, .primFam _ | _, _, .primTm _ | _, _, .boolTy | _, _, .bv _ | _, _, .bool _ => False
  | _, _, .arr A B | _, _, .tyApp A B | _, _, .app A B | _, _, .lam A B |
      _, _, .eps A B => FreeIn name A ∨ FreeIn name B
  | _, _, .sub A p => FreeIn name A ∨ FreeIn name p
  | _, _, .fv other A => other = name ∨ FreeIn name A
  | _, _, .eq A x y | _, _, .abs A x y | _, _, .rep A x y =>
      FreeIn name A ∨ FreeIn name x ∨ FreeIn name y

abbrev Fresh {Sig : Signature} (name : Nat) {sort : HolSort} {depth : Nat}
    (expression : Expr Sig sort depth) : Prop := ¬ FreeIn name expression

end Nucleus.Hol
