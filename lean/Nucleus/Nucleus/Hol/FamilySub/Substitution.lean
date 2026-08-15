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

@[simp] theorem rename_bv (ρ : Fin m → Fin n) (i : Fin m) :
    rename (Sig := Sig) (types := types) ρ (.bv i) = .bv (ρ i) := by
  simp [rename]

@[simp] theorem weaken_bv (i : Fin depth) :
    weaken (Sig := Sig) (types := types) (.bv i) = .bv i.succ := by
  simp [weaken]

@[simp] theorem instantiate_bv (σ : Fin m → Tm Sig types n) (i : Fin m) :
    instantiate σ (.bv i) = σ i := by
  simp [instantiate]

@[simp] theorem liftSub_zero (σ : Fin m → Tm Sig types n) :
    liftSub σ 0 = (.bv 0 : Tm Sig types (n + 1)) := rfl

@[simp] theorem liftSub_succ (σ : Fin m → Tm Sig types n) (i : Fin m) :
    liftSub σ i.succ = weaken (σ i) := rfl

theorem instantiate_rename (term : Tm Sig types m)
    (ρ : Fin m → Fin n) (σ : Fin n → Tm Sig types k) (τ : Fin m → Fin k)
    (commute : ∀ i, σ (ρ i) = .bv (τ i)) :
    instantiate σ (rename ρ term) = rename τ term := by
  cases term with
  | primTm | fv | bool => simp [rename, instantiate]
  | bv i => simpa [rename, instantiate] using commute i
  | app function argument =>
      simp only [rename, instantiate]
      rw [instantiate_rename function ρ σ τ commute,
        instantiate_rename argument ρ σ τ commute]
  | lam A body =>
      simp only [rename, instantiate]
      congr 1
      apply instantiate_rename body (liftRen ρ) (liftSub σ) (liftRen τ)
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · simp [liftRen, liftSub, commute j, weaken]
  | eq A left right =>
      simp only [rename, instantiate]
      rw [instantiate_rename left ρ σ τ commute,
        instantiate_rename right ρ σ τ commute]
  | eps A predicate =>
      simp only [rename, instantiate]
      rw [instantiate_rename predicate ρ σ τ commute]
  | abs A predicate value | rep A predicate value =>
      simp only [rename, instantiate]
      rw [instantiate_rename value ρ σ τ commute]
termination_by sizeOf term

@[simp] theorem rename_id (term : Tm Sig types m) : rename id term = term := by
  cases term with
  | primTm | fv | bv | bool => simp [rename]
  | app function argument =>
      simp only [rename]
      rw [rename_id function, rename_id argument]
  | lam A body =>
      simp only [rename]
      have lifted : liftRen (id : Fin m → Fin m) = id := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [lifted, rename_id body]
  | eq A left right =>
      simp only [rename]
      rw [rename_id left, rename_id right]
  | eps A predicate =>
      simp only [rename]
      rw [rename_id predicate]
  | abs A predicate value | rep A predicate value =>
      simp only [rename]
      rw [rename_id value]
termination_by sizeOf term

theorem rename_comp (term : Tm Sig types m) (ρ : Fin m → Fin n)
    (τ : Fin n → Fin k) :
    rename τ (rename ρ term) = rename (fun i => τ (ρ i)) term := by
  cases term with
  | primTm | fv | bv | bool => simp [rename]
  | app function argument =>
      simp only [rename]
      rw [rename_comp function, rename_comp argument]
  | lam A body =>
      simp only [rename]
      have lifted : (fun i => liftRen τ (liftRen ρ i)) =
          liftRen (fun i => τ (ρ i)) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [rename_comp body, lifted]
  | eq A left right =>
      simp only [rename]
      rw [rename_comp left, rename_comp right]
  | eps A predicate =>
      simp only [rename]
      rw [rename_comp predicate]
  | abs A predicate value | rep A predicate value =>
      simp only [rename]
      rw [rename_comp value]
termination_by sizeOf term

theorem instantiate_rename_cancel (term : Tm Sig types m)
    (ρ : Fin m → Fin n) (σ : Fin n → Tm Sig types m)
    (cancel : ∀ i, σ (ρ i) = .bv i) :
    instantiate σ (rename ρ term) = term := by
  simpa using instantiate_rename term ρ σ id (by simpa using cancel)

@[simp] theorem openBound_weaken (term : Tm Sig types depth)
    (replacement : Tm Sig types depth) :
    openBound (weaken term) replacement = term := by
  apply instantiate_rename_cancel term Fin.succ (Fin.cases replacement .bv)
  intro i
  rfl

@[simp] theorem instantiate_head_weaken (term : Tm Sig types depth)
    (replacement : Tm Sig types depth) :
    instantiate (Fin.cases replacement .bv) (weaken term) = term :=
  openBound_weaken term replacement

@[simp] theorem instantiate_lift_head_weaken_weaken (term : Tm Sig types depth)
    (replacement : Tm Sig types depth) :
    instantiate (liftSub (Fin.cases replacement .bv)) (weaken (weaken term)) =
      weaken term := by
  rw [show weaken (weaken term) = rename (fun i => Fin.succ (Fin.succ i)) term by
    exact rename_comp term Fin.succ Fin.succ]
  apply instantiate_rename term (fun i => (Fin.succ (Fin.succ i)))
    (liftSub (Fin.cases replacement .bv)) Fin.succ
  intro i
  simp [liftSub, weaken]

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

theorem HasTypeDefEq.renameTm {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types m} {Δ : BoundCtx Sig types n}
    {t : Tm Sig types m} {A : Ty Sig types} (typing : HasTypeDefEq Γ t A)
    (ρ : Fin m → Fin n) (contexts : ∀ i, Δ (ρ i) = Γ i) :
    HasTypeDefEq Δ (rename ρ t) A := by
  induction typing generalizing n with
  | exact raw => exact .exact (raw.renameTm ρ contexts)
  | app _ _ ihf ihx => simpa [rename] using
      (HasTypeDefEq.app (ihf ρ contexts) (ihx ρ contexts))
  | lam body hA _ ih =>
      simpa [rename] using (HasTypeDefEq.lam (rename (liftRen ρ) body) hA
        (ih (liftRen ρ) (by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · rfl
          · exact contexts j)))
  | eq hA _ _ ihx ihy => simpa [rename] using
      (HasTypeDefEq.eq hA (ihx ρ contexts) (ihy ρ contexts))
  | eps hA _ ih => simpa [rename] using (HasTypeDefEq.eps hA (ih ρ contexts))
  | abs hA hp _ ih => simpa [rename] using (HasTypeDefEq.abs hA hp (ih ρ contexts))
  | rep hA hp _ ih => simpa [rename] using (HasTypeDefEq.rep hA hp (ih ρ contexts))
  | conv _ hB conversion ih => exact .conv (ih ρ contexts) hB conversion

theorem HasTypeDefEq.weaken {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {t : Tm Sig types depth} {A B : Ty Sig types}
    (typing : HasTypeDefEq Γ t A) :
    HasTypeDefEq (extendBound B Γ) (FamilySub.weaken t) A := by
  apply typing.renameTm Fin.succ
  intro i
  rfl

def WellTypedDefEqSub {Sig : Signature} [SigTyping Sig]
    (Γ : BoundCtx Sig types m) (Δ : BoundCtx Sig types n)
    (σ : Fin m → Tm Sig types n) : Prop :=
  ∀ i, HasTypeDefEq Δ (σ i) (Γ i)

theorem liftWellTypedDefEqSub {Sig : Signature} [SigTyping Sig]
    {types : List Kind} {A : Ty Sig types}
    {Γ : BoundCtx Sig types m} {Δ : BoundCtx Sig types n}
    {σ : Fin m → Tm Sig types n} (wellTyped : WellTypedDefEqSub Γ Δ σ)
    (hA : Kinded A) :
    WellTypedDefEqSub (extendBound A Γ) (extendBound A Δ)
      (liftSub (Sig := Sig) (types := types) σ) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .exact (.bv hA rfl)
  · exact (wellTyped j).weaken

set_option linter.defProp false in
def Checks.instantiateDefEq {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types m} {Δ : BoundCtx Sig types n}
    {t : Tm Sig types m} {A : Ty Sig types} (typing : HasType Γ t A)
    (σ : Fin m → Tm Sig types n) (wellTyped : WellTypedDefEqSub Γ Δ σ) :
    HasTypeDefEq Δ (instantiate σ t) A :=
  match typing with
  | .primTm rule => .exact (by simpa [instantiate] using (.primTm (Γ := Δ) rule))
  | .bv (i := i) hA lookup => by
      have variableTyping := wellTyped i
      rw [lookup] at variableTyping
      simpa [instantiate] using variableTyping
  | .fv name hA => .exact (by simpa [instantiate] using (.fv (Γ := Δ) name hA))
  | .app hf hx => by simpa [instantiate] using
      (HasTypeDefEq.app (Checks.instantiateDefEq hf σ wellTyped)
        (Checks.instantiateDefEq hx σ wellTyped))
  | .lam body hA hb => by simpa [instantiate] using
      (HasTypeDefEq.lam (instantiate (liftSub σ) body) hA
        (Checks.instantiateDefEq hb (liftSub σ)
          (liftWellTypedDefEqSub wellTyped hA)))
  | .bool value => .exact (by simpa [instantiate] using (.bool (Γ := Δ) value))
  | .eq hA hx hy => by simpa [instantiate] using
      (HasTypeDefEq.eq hA (Checks.instantiateDefEq hx σ wellTyped)
        (Checks.instantiateDefEq hy σ wellTyped))
  | .eps hA hp => by simpa [instantiate] using
      (HasTypeDefEq.eps hA (Checks.instantiateDefEq hp σ wellTyped))
  | .abs hA hp hx => by simpa [instantiate] using
      (HasTypeDefEq.abs hA hp (Checks.instantiateDefEq hx σ wellTyped))
  | .rep hA hp hx => by simpa [instantiate] using
      (HasTypeDefEq.rep hA hp (Checks.instantiateDefEq hx σ wellTyped))

theorem HasTypeDefEq.instantiateTm {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types m} {Δ : BoundCtx Sig types n}
    {t : Tm Sig types m} {A : Ty Sig types} (typing : HasTypeDefEq Γ t A)
    (σ : Fin m → Tm Sig types n) (wellTyped : WellTypedDefEqSub Γ Δ σ) :
    HasTypeDefEq Δ (instantiate σ t) A := by
  induction typing generalizing n with
  | exact raw => exact raw.instantiateDefEq σ wellTyped
  | app _ _ ihf ihx => simpa [instantiate] using
      (HasTypeDefEq.app (ihf σ wellTyped) (ihx σ wellTyped))
  | lam body hA _ ih =>
      simpa [instantiate] using (HasTypeDefEq.lam (instantiate (liftSub σ) body) hA
        (ih (liftSub σ) (liftWellTypedDefEqSub wellTyped hA)))
  | eq hA _ _ ihx ihy => simpa [instantiate] using
      (HasTypeDefEq.eq hA (ihx σ wellTyped) (ihy σ wellTyped))
  | eps hA _ ih => simpa [instantiate] using (HasTypeDefEq.eps hA (ih σ wellTyped))
  | abs hA hp _ ih => simpa [instantiate] using
      (HasTypeDefEq.abs hA hp (ih σ wellTyped))
  | rep hA hp _ ih => simpa [instantiate] using
      (HasTypeDefEq.rep hA hp (ih σ wellTyped))
  | conv _ hB conversion ih => exact .conv (ih σ wellTyped) hB conversion

theorem HasTypeDefEq.openBound {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig types depth} {body : Tm Sig types (depth + 1)}
    {replacement : Tm Sig types depth} {A B : Ty Sig types}
    (typedContext : TypedCtx Γ) (bodyTyping : HasTypeDefEq (extendBound A Γ) body B)
    (replacementTyping : HasTypeDefEq Γ replacement A) :
    HasTypeDefEq Γ (openBound body replacement) B := by
  apply bodyTyping.instantiateTm (Fin.cases replacement .bv)
  intro i
  exact Fin.cases replacementTyping (fun j => .exact (.bv (typedContext j) rfl)) i

theorem HasTypeDefEq.renameTypes {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig source depth} {t : Tm Sig source depth} {A : Ty Sig source}
    (typing : HasTypeDefEq Γ t A) (ρ : TyRen source target) :
    HasTypeDefEq (renameBoundCtx ρ Γ) (FamilySub.renameTypes ρ t)
      (FamilySub.renameTypes ρ A) := by
  induction typing generalizing target with
  | exact raw => exact .exact (raw.renameTypes ρ)
  | app _ _ ihf ihx => simpa using (HasTypeDefEq.app (ihf ρ) (ihx ρ))
  | lam body hA _ ih =>
      have bodyTyping := ih ρ
      rw [renameBoundCtx_extend] at bodyTyping
      simpa using (HasTypeDefEq.lam (FamilySub.renameTypes ρ body)
        (by simpa using hA.renameTypes ρ) bodyTyping)
  | eq hA _ _ ihx ihy =>
      simpa using (HasTypeDefEq.eq (by simpa using hA.renameTypes ρ)
        (ihx ρ) (ihy ρ))
  | eps hA _ ih =>
      simpa using (HasTypeDefEq.eps (by simpa using hA.renameTypes ρ) (ih ρ))
  | abs hA hp _ ih =>
      simpa using (HasTypeDefEq.abs (by simpa using hA.renameTypes ρ)
        (by simpa using hp.renameTypes ρ) (ih ρ))
  | rep hA hp _ ih =>
      simpa using (HasTypeDefEq.rep (by simpa using hA.renameTypes ρ)
        (by simpa using hp.renameTypes ρ) (ih ρ))
  | conv _ hB conversion ih =>
      exact .conv (ih ρ) (by simpa using hB.renameTypes ρ) (conversion.renameTypes ρ)

theorem HasTypeDefEq.instantiateTypes {Sig : Signature} [SigTyping Sig]
    {Γ : BoundCtx Sig source depth} {t : Tm Sig source depth} {A : Ty Sig source}
    (typing : HasTypeDefEq Γ t A) {σ : TySub Sig source target}
    (wellFormed : WellFormedTySub σ) :
    HasTypeDefEq (instantiateBoundCtx σ Γ) (FamilySub.instantiateTypes σ t)
      (FamilySub.instantiateTypes σ A) := by
  induction typing generalizing target with
  | exact raw => exact .exact (raw.instantiateTypes wellFormed)
  | app _ _ ihf ihx => simpa using
      (HasTypeDefEq.app (ihf wellFormed) (ihx wellFormed))
  | lam body hA _ ih =>
      have bodyTyping := ih wellFormed
      rw [instantiateBoundCtx_extend] at bodyTyping
      simpa using (HasTypeDefEq.lam (FamilySub.instantiateTypes σ body)
        (by simpa using hA.instantiateTypes wellFormed) bodyTyping)
  | eq hA _ _ ihx ihy =>
      simpa using (HasTypeDefEq.eq (by simpa using hA.instantiateTypes wellFormed)
        (ihx wellFormed) (ihy wellFormed))
  | eps hA _ ih =>
      simpa using (HasTypeDefEq.eps (by simpa using hA.instantiateTypes wellFormed)
        (ih wellFormed))
  | abs hA hp _ ih =>
      simpa using (HasTypeDefEq.abs
        (by simpa using hA.instantiateTypes wellFormed)
        (by simpa using hp.instantiateTypes wellFormed) (ih wellFormed))
  | rep hA hp _ ih =>
      simpa using (HasTypeDefEq.rep
        (by simpa using hA.instantiateTypes wellFormed)
        (by simpa using hp.instantiateTypes wellFormed) (ih wellFormed))
  | conv _ hB conversion ih =>
      exact .conv (ih wellFormed)
        (by simpa using hB.instantiateTypes wellFormed)
        (conversion.instantiateTypes σ)

end Nucleus.Hol.FamilySub
