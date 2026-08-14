import Nucleus.Hol.FamilySub

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

def liftRen {m n : Nat} (ρ : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

def rename (ρ : Fin m → Fin n) : Tm Sig types m → Tm Sig types n
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

def weaken (tm : Tm Sig types depth) : Tm Sig types (depth + 1) :=
  rename Fin.succ tm

def liftSub (σ : Fin m → Tm Sig types n) : Fin (m + 1) → Tm Sig types (n + 1) :=
  Fin.cases (.bv 0) (fun i => weaken (σ i))

def instantiate (σ : Fin m → Tm Sig types n) : Tm Sig types m → Tm Sig types n
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

def openBound (body : Tm Sig types (depth + 1))
    (replacement : Tm Sig types depth) : Tm Sig types depth :=
  instantiate (Fin.cases replacement .bv) body

def instantiateOne (predicate : Tm Sig types 1)
    (replacement : Tm Sig types depth) : Tm Sig types depth :=
  instantiate (fun _ => replacement) predicate

def FreeIn (name : Nat) : {sort : HolSort} → {depth : Nat} →
    Expr Sig types sort depth → Prop
  | _, _, .primFam _ | _, _, .primTm _ | _, _, .boolTy | _, _, .tyBv _ |
      _, _, .bv _ | _, _, .bool _ => False
  | _, _, .arr A B | _, _, .tyApp A B | _, _, .app A B | _, _, .lam A B |
      _, _, .eps A B => FreeIn name A ∨ FreeIn name B
  | _, _, .tyLam body => FreeIn name body
  | _, _, .sub A p => FreeIn name A ∨ FreeIn name p
  | _, _, .fv other A => other = name ∨ FreeIn name A
  | _, _, .eq A x y | _, _, .abs A x y | _, _, .rep A x y =>
      FreeIn name A ∨ FreeIn name x ∨ FreeIn name y

abbrev Fresh (name : Nat) (expression : Expr Sig types sort depth) : Prop :=
  ¬ FreeIn name expression

set_option linter.defProp false in
def Checks.renameTm {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types m} {Δ : BoundCtx Sig types n}
    {t : Tm Sig types m} {A : Ty Sig types} (typing : HasType Γ t A)
    (ρ : Fin m → Fin n) (contexts : ∀ i, Δ (ρ i) = Γ i) :
    HasType Δ (rename ρ t) A :=
  match typing with
  | .primTm rule => by simpa [rename] using (.primTm (Γ := Δ) rule)
  | .bv hA lookup => by simpa [rename] using (.bv hA ((contexts _).trans lookup))
  | .fv name hA => by simpa [rename] using (.fv name hA)
  | .app hf hx => by simpa [rename] using
      (.app (Checks.renameTm hf ρ contexts) (Checks.renameTm hx ρ contexts))
  | .lam body hA hb => by simpa [rename] using (.lam (rename (liftRen ρ) body) hA
      (Checks.renameTm (Δ := extendBound _ Δ) hb (liftRen ρ) (by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact contexts j)))
  | .bool value => by simpa [rename] using (.bool (Γ := Δ) value)
  | .eq hA hx hy => by simpa [rename] using
      (.eq hA (Checks.renameTm hx ρ contexts) (Checks.renameTm hy ρ contexts))
  | .eps hA hp => by simpa [rename] using (.eps hA (Checks.renameTm hp ρ contexts))
  | .abs hA hp hx => by simpa [rename] using (.abs hA hp (Checks.renameTm hx ρ contexts))
  | .rep hA hp hx => by simpa [rename] using (.rep hA hp (Checks.renameTm hx ρ contexts))

theorem HasType.weaken {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {t : Tm Sig types depth} {A B : Ty Sig types}
    (typing : HasType Γ t A) : HasType (extendBound B Γ) (weaken t) A :=
  Checks.renameTm typing Fin.succ (fun _ => rfl)

def WellTypedSub {Sig : Signature} [SigTyping Sig]
    (Γ : BoundCtx Sig types m) (Δ : BoundCtx Sig types n)
    (σ : Fin m → Tm Sig types n) : Prop :=
  ∀ i, HasType Δ (σ i) (Γ i)

theorem liftWellTypedSub {Sig : Signature} [SigTyping Sig]
    {types : List Kind} {A : Ty Sig types}
    {Γ : BoundCtx Sig types m} {Δ : BoundCtx Sig types n}
    {σ : Fin m → Tm Sig types n} (wellTyped : WellTypedSub Γ Δ σ)
    (hA : Kinded A) :
    WellTypedSub (Sig := Sig) (extendBound A Γ) (extendBound A Δ)
      (liftSub (Sig := Sig) (types := types) σ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .bv hA rfl
  · exact (wellTyped j).weaken

set_option linter.defProp false in
def Checks.instantiateTm {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types m} {Δ : BoundCtx Sig types n}
    {t : Tm Sig types m} {A : Ty Sig types} (typing : HasType Γ t A)
    (σ : Fin m → Tm Sig types n) (wellTyped : WellTypedSub Γ Δ σ) :
    HasType Δ (instantiate σ t) A :=
  match typing with
  | .primTm rule => by simpa [instantiate] using (.primTm (Γ := Δ) rule)
  | .bv (i := i) hA lookup => by
      have variableTyping := wellTyped i
      rw [lookup] at variableTyping
      simpa [instantiate] using variableTyping
  | .fv name hA => by simpa [instantiate] using (.fv (Γ := Δ) name hA)
  | .app hf hx => by simpa [instantiate] using
      (.app (Checks.instantiateTm hf σ wellTyped)
        (Checks.instantiateTm hx σ wellTyped))
  | .lam body hA hb => by simpa [instantiate] using
      (.lam (instantiate (liftSub (Sig := Sig) (types := types) σ) body) hA
        (Checks.instantiateTm hb (liftSub (Sig := Sig) (types := types) σ)
          (liftWellTypedSub (Sig := Sig) wellTyped hA)))
  | .bool value => by simpa [instantiate] using (.bool (Γ := Δ) value)
  | .eq hA hx hy => by simpa [instantiate] using
      (.eq hA (Checks.instantiateTm hx σ wellTyped)
        (Checks.instantiateTm hy σ wellTyped))
  | .eps hA hp => by simpa [instantiate] using
      (.eps hA (Checks.instantiateTm hp σ wellTyped))
  | .abs hA hp hx => by simpa [instantiate] using
      (.abs hA hp (Checks.instantiateTm hx σ wellTyped))
  | .rep hA hp hx => by simpa [instantiate] using
      (.rep hA hp (Checks.instantiateTm hx σ wellTyped))

def TypedCtx {Sig : Signature} [SigTyping Sig]
    (Γ : BoundCtx Sig types depth) : Prop := ∀ i, Kinded (Γ i)

theorem HasType.openBound {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {body : Tm Sig types (depth + 1)}
    {replacement : Tm Sig types depth} {A B : Ty Sig types}
    (typedContext : TypedCtx Γ)
    (bodyTyping : HasType (extendBound A Γ) body B)
    (replacementTyping : HasType Γ replacement A) :
    HasType Γ (openBound body replacement) B := by
  apply bodyTyping.instantiateTm (Fin.cases replacement .bv)
  intro i
  exact Fin.cases replacementTyping (fun j => .bv (typedContext j) rfl) i

theorem HasType.instantiateOne {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {predicate : Tm Sig types 1}
    {replacement : Tm Sig types depth}
    {A B : Ty Sig types} (predicateTyping :
      HasType (extendBound A emptyBound) predicate B)
    (replacementTyping : HasType Γ replacement A) :
    HasType Γ (instantiateOne predicate replacement) B := by
  apply predicateTyping.instantiateTm (fun _ => replacement)
  intro i
  exact Fin.cases replacementTyping (fun j => Fin.elim0 j) i

end Nucleus.Hol.FamilySub
