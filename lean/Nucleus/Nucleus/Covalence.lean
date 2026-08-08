import Nucleus.HolOmega.Consistency
import Nucleus.HolOmega.Conversion
import Nucleus.HolOmega.ProofTyping
import Nucleus.HolOmega.TypingSubstitution

/-! Minimal sorted Covalence with typed holes and proof lowering. -/

universe u v

namespace Nucleus.Covalence

open HolOmega

variable {Base : Type u} {I : Type v} {J : Type v}

/-- Ranks are annotations, not hole-bearing syntax. These are the three
expected HOL sorts from issue #457; entailment remains a judgement below. -/
inductive HolSort (Base : Type u) where
  | kindAt (rank : Nat)
  | typeAt (kind : RKind)
  | termAt (type : Ty Base)

structure Broken where
  tag : Nat
  deriving DecidableEq, Repr

/-- Stored vocabulary tags. `cast` is intentionally absent: it is a dialect
operation compiled during sorted repair, not a persisted schema row. -/
inductive HolTag (Base : Type u) where
  | hole (name : Nat)
  | atom (value : Base)
  | tyVar | tyLam | tyApp | tyAll | tyBool | tyArr | tySub
  | tmVar | tmApp | tmLam | tmTyApp | tmTyLam | tmBool | tmEq | tmEps | tmAbs | tmRep

/-- The recursive, untyped tree is exactly the in-memory row shape: a tag and
three optional child rows. For term rows the third child is the stored type
annotation; accessing it never descends into `lhs` or `rhs`. -/
inductive Hol (Base : Type u) where
  | node (tag : HolTag Base) (lhs rhs ty : Option (Hol Base))

abbrev Hol.View (Base : Type u) :=
  HolTag Base × Option (Hol Base) × Option (Hol Base) × Option (Hol Base)

def Hol.view : Hol Base → Hol.View Base
  | .node tag lhs rhs ty => (tag, lhs, rhs, ty)

def Hol.ofView : Hol.View Base → Hol Base
  | (tag, lhs, rhs, ty) => .node tag lhs rhs ty

def Hol.viewEquiv : Hol Base ≃ Hol.View Base where
  toFun := Hol.view
  invFun := Hol.ofView
  left_inv h := by cases h; rfl
  right_inv v := by rcases v with ⟨tag, lhs, rhs, ty⟩; rfl

/-- One-layer stored annotation projection. A missing annotation becomes a
named annotation hole; no other child is inspected. -/
def Hol.ty (missingName : Nat) : Hol Base → Hol Base
  | .node _ _ _ (some ty) => ty
  | .node _ _ _ none => .node (.hole missingName) none none none

/-- Exact persistent row and image types. Tree unfolding replaces each child
tree in `Hol.View` by its content index without changing field order. -/
abbrev Row (Base : Type u) (Index : Type v) :=
  HolTag Base × Option Index × Option Index × Option Index

abbrev Image (Base : Type u) (Index : Type v) := Index → Option (Row Base Index)

def Row.map (f : I → J) : Row Base I → Row Base J
  | (tag, lhs, rhs, ty) => (tag, lhs.map f, rhs.map f, ty.map f)

def canonicalTy : (K : Kind) → Nat → Ty Base
  | .star, _ => .tyBool
  | .arr K L, r => .tyLam ⟨K, r⟩ (canonicalTy L r)

theorem canonicalTy_kinded (K : Kind) (r : Nat) (Δ : KindCtx) :
    Kinded Δ (canonicalTy (Base := Base) K r) ⟨K, r⟩ := by
  induction K with
  | star => exact .tyBool
  | arr K L _ ihL => exact .tyLam (ihL (⟨K, r⟩ :: Δ))

structure RepairedTy (Base : Type u) (Δ : KindCtx) (RK : RKind) where
  tree : Ty Base
  formed : Kinded Δ tree RK

/-- Type formation is total at every requested ranked kind. -/
def repairTy (_ : Broken) (Δ : KindCtx) (RK : RKind) : RepairedTy Base Δ RK :=
  ⟨canonicalTy RK.kind RK.rank, canonicalTy_kinded RK.kind RK.rank Δ⟩

/-- One named typed hole. Its open lowering is a fresh variable in the
extended context; `Filling` is the family of every legal closing term. -/
structure Hole (Base : Type u) (Δ : KindCtx) (Γ : TmCtx Base) (A : Ty Base) where
  name : Nat
  formed : Kinded Δ A ⟨.kind.star, rank⟩

def Hole.Filling (h : Hole Base Δ Γ A) := {t : Tm Base // HasType Δ Γ t A}

/-- One simultaneous assignment for every named, typed hole. Repeated uses of
the same name/type are therefore forced to receive the same term. -/
def FillingEnv (Base : Type u) (Δ : KindCtx) (Γ : TmCtx Base) :=
  ∀ (name : Nat) (A : Ty Base) (r : Nat), Kinded Δ A ⟨.kind.star, r⟩ →
    {t : Tm Base // HasType Δ Γ t A}

def Hole.open (h : Hole Base Δ Γ A) :
    {t : Tm Base // HasType Δ (A :: Γ) t A} := ⟨.tmVar 0, .tmVar rfl⟩

def Hole.canonical (h : Hole Base Δ Γ A) : h.Filling :=
  ⟨.tmEps A (.tmLam A (.tmBool true)), .tmEps h.formed (.tmLam h.formed .tmBool)⟩

theorem Hole.fillings_nonempty (h : Hole Base Δ Γ A) : Nonempty h.Filling :=
  ⟨h.canonical⟩

def canonicalFillingEnv (Base : Type u) (Δ : KindCtx) (Γ : TmCtx Base) :
    FillingEnv Base Δ Γ := fun name A r hA => (Hole.mk name hA).canonical

theorem fillingEnvs_nonempty : Nonempty (FillingEnv Base Δ Γ) :=
  ⟨canonicalFillingEnv Base Δ Γ⟩

def FillingEnv.weaken (f : FillingEnv Base Δ Γ) (B : Ty Base) :
    FillingEnv Base Δ (B :: Γ) := fun name A r hA =>
  ⟨(f name A r hA).1.rename Nat.succ, (f name A r hA).2.weaken⟩

/-- The row-shaped Covalence term family. Its type annotation is the index,
so `.ty` below is a one-layer projection and never traverses children.
Constructors are intrinsically sorted: callers provide children, not raw
`HasType` certificates. -/
inductive SortedHol (Base : Type u) (Δ : KindCtx) (Γ : TmCtx Base) : Ty Base → Type u
  | hole (name : Nat) (formed : Kinded Δ A ⟨.kind.star, r⟩) : SortedHol Base Δ Γ A
  | bool (b : Bool) : SortedHol Base Δ Γ .tyBool
  | app : SortedHol Base Δ Γ (.tyArr A B) → SortedHol Base Δ Γ A → SortedHol Base Δ Γ B
  | lam (formed : Kinded Δ A ⟨.kind.star, r⟩) :
      SortedHol Base Δ (A :: Γ) B → SortedHol Base Δ Γ (.tyArr A B)
  | eq (formed : Kinded Δ A ⟨.kind.star, r⟩) :
      SortedHol Base Δ Γ A → SortedHol Base Δ Γ A → SortedHol Base Δ Γ .tyBool
  | eps (formed : Kinded Δ A ⟨.kind.star, r⟩) :
      SortedHol Base Δ Γ (.tyArr A .tyBool) → SortedHol Base Δ Γ A
  | cast (term : SortedHol Base Δ Γ A) (target : Ty Base)
      (formed : Kinded Δ target ⟨.kind.star, r⟩)
      (decision : TyConv Δ A target ⊕ Nat) : SortedHol Base Δ Γ target

/-- Nonrecursive projection of the stored row annotation. -/
def SortedHol.ty {A : Ty Base} (_ : SortedHol Base Δ Γ A) : Ty Base := A

@[simp] theorem SortedHol.ty_eq {A : Ty Base} (t : SortedHol Base Δ Γ A) : t.ty = A := rfl

/-- Uniform lowering of an annotated row under a simultaneous hole filling.
A successful cast retains the child's raw term and applies core conversion;
a failed cast selects the named typed hole at the target annotation. -/
def SortedHol.lower (f : FillingEnv Base Δ Γ) : (t : SortedHol Base Δ Γ A) →
    {raw : Tm Base // HasType Δ Γ raw A}
  | .hole name hA => f name A _ hA
  | .bool b => ⟨.tmBool b, .tmBool⟩
  | .app g x => ⟨.tmApp (g.lower f).1 (x.lower f).1, .tmApp (g.lower f).2 (x.lower f).2⟩
  | .lam hA body =>
      ⟨.tmLam A (body.lower (f.weaken A)).1, .tmLam hA (body.lower (f.weaken A)).2⟩
  | .eq hA x y => ⟨.tmEq A (x.lower f).1 (y.lower f).1,
      .tmEq hA (x.lower f).2 (y.lower f).2⟩
  | .eps hA p => ⟨.tmEps A (p.lower f).1, .tmEps hA (p.lower f).2⟩
  | .cast term target htarget decision =>
      match decision with
      | .inl hc => ⟨(term.lower f).1, .conv (term.lower f).2 hc⟩
      | .inr name => f name target _ htarget

def SortedHol.repair (t : SortedHol Base Δ Γ A) : {raw : Tm Base // HasType Δ Γ raw A} :=
  t.lower (canonicalFillingEnv Base Δ Γ)

/-- A sorted term node. Malformed nodes carry only the formation evidence of
the expected type, which suffices to turn them into named holes. -/
inductive TermNode (Base : Type u) (Δ : KindCtx) (Γ : TmCtx Base) (A : Ty Base)
  | valid (t : Tm Base) (typed : HasType Δ Γ t A)
  | hole (h : Hole Base Δ Γ A)
  | broken (payload : Broken) (formed : Kinded Δ A ⟨.kind.star, rank⟩)

def TermNode.asHole : TermNode Base Δ Γ A → Hole Base Δ Γ A
  | .hole h => h
  | .broken b hA => ⟨b.tag, hA⟩
  | .valid _ ht => by
      have hA := HasType.formed ht
      exact ⟨0, hA.choose_spec⟩

/-- Every node has an open, typed lowering. Valid syntax is weakened; holes
become the fresh variable zero. -/
def TermNode.open : (n : TermNode Base Δ Γ A) →
    {t : Tm Base // HasType Δ (A :: Γ) t A}
  | .valid t ht => ⟨t.rename Nat.succ, ht.weaken⟩
  | .hole h => h.open
  | .broken b hA => (Hole.mk b.tag hA).open

/-- Filling is total and ranges over all typed terms of the claimed type. -/
def TermNode.fill (n : TermNode Base Δ Γ A) (f : FillingEnv Base Δ Γ) :
    {t : Tm Base // HasType Δ Γ t A} :=
  match n with
  | .valid t ht => ⟨t, ht⟩
  | .hole h => f h.name A _ h.formed
  | .broken b hA => f b.tag A _ hA

def TermNode.repair (n : TermNode Base Δ Γ A) : {t : Tm Base // HasType Δ Γ t A} :=
  n.fill (canonicalFillingEnv Base Δ Γ)

/-- Covalence entailment has actual logical constructors. Syntax holes may
occur in their term arguments, but there is deliberately no hole-as-proof
constructor. -/
inductive CovProves {Base : Type u} (Δ : KindCtx) (Γ : TmCtx Base)
    (H : Hyps Base) : TermNode Base Δ Γ .tyBool → Type u
  | hyp (hH : TypedHyps Δ Γ H) (hp : p ∈ H) :
      CovProves Δ Γ H (.valid p (hH.lookup hp))
  | truth (hH : TypedHyps Δ Γ H) :
      CovProves Δ Γ H (.valid (.tmBool true) .tmBool)
  | eqRefl (hH : TypedHyps Δ Γ H) (hA : Kinded Δ A ⟨.kind.star, r⟩)
      (x : TermNode Base Δ Γ A) :
      CovProves Δ Γ H (.valid (.tmEq A x.repair.1 x.repair.1)
        (.tmEq hA x.repair.2 x.repair.2))

/-- The simultaneous family of fillings used by a Covalence derivation.
Logical leaves have no holes; equality reflexivity may contain one typed term
hole, filled by any member of its full family. -/
def CovProves.Fillings {n : TermNode Base Δ Γ .tyBool} :
    CovProves Δ Γ H n → Type u
  | _ => FillingEnv Base Δ Γ

/-- Filling-dependent raw conclusion. This, rather than canonical repair, is
the meaning of a Covalence proof. -/
def CovProves.lowerTerm {n : TermNode Base Δ Γ .tyBool}
    (d : CovProves Δ Γ H n) : d.Fillings → Tm Base
  | f => match d with
    | .hyp _ _ => n.fill f |>.1
    | .truth _ => .tmBool true
    | .eqRefl _ _ x => .tmEq _ (x.fill f).1 (x.fill f).1

/-- Uniform entailment lowering: every legal filling produces an ordinary
raw HOL-omega proof. -/
def CovProves.lower {n : TermNode Base Δ Γ .tyBool}
    (d : CovProves Δ Γ H n) : (f : d.Fillings) → Proves Δ Γ H (d.lowerTerm f) := by
  intro f
  cases d with
  | hyp hH hp => exact .hyp hH hp
  | truth hH => exact .truth hH
  | eqRefl hH hA x => exact .eqRefl hH (x.fill f).2 hA

def CovProves.canonicalFilling {n : TermNode Base Δ Γ .tyBool}
    (d : CovProves Δ Γ H n) : d.Fillings := canonicalFillingEnv Base Δ Γ

theorem CovProves.fillings_nonempty {n : TermNode Base Δ Γ .tyBool}
    (d : CovProves Δ Γ H n) : Nonempty d.Fillings := ⟨d.canonicalFilling⟩

/-- The canonical filling really is one member of the full filling family. -/
theorem TermNode.canonical_is_filling (n : TermNode Base Δ Γ A) :
    n.asHole.canonical ∈ Set.univ := Set.mem_univ _

/-- Model-independent Covalence consistency. A derivation whose repaired
empty-context conclusion is raw false would lower to a forbidden raw proof. -/
theorem empty_not_proves_false
    {n : TermNode Empty ([] : KindCtx) ([] : TmCtx Empty) .tyBool}
    (hfalse : ∀ (d : CovProves [] [] [] n),
      d.lowerTerm d.canonicalFilling = .tmBool false) : ¬ CovProves [] [] [] n := by
  intro d
  have raw : Proves ([] : KindCtx) ([] : TmCtx Empty) [] (.tmBool false) := by
    rw [← hfalse d]
    exact d.lower d.canonicalFilling
  exact HolOmega.raw_not_proves_false raw

end Nucleus.Covalence
