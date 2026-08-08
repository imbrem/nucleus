import Nucleus.HolOmega.Consistency
import Nucleus.HolOmega.ProofTyping
import Nucleus.HolOmega.TypingSubstitution

/-! Minimal sorted Covalence with typed holes and proof lowering. -/

universe u

namespace Nucleus.Covalence

open HolOmega

/-- Ranks are annotations, not hole-bearing syntax. These are the three
expected HOL sorts from issue #457; entailment remains a judgement below. -/
inductive HolSort (Base : Type u) where
  | kindAt (rank : Nat)
  | typeAt (kind : RKind)
  | termAt (type : Ty Base)

structure Broken where
  tag : Nat
  deriving DecidableEq, Repr

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

def Hole.open (h : Hole Base Δ Γ A) :
    {t : Tm Base // HasType Δ (A :: Γ) t A} := ⟨.tmVar 0, .tmVar rfl⟩

def Hole.canonical (h : Hole Base Δ Γ A) : h.Filling :=
  ⟨.tmEps A (.tmLam A (.tmBool true)), .tmEps h.formed (.tmLam h.formed .tmBool)⟩

theorem Hole.fillings_nonempty (h : Hole Base Δ Γ A) : Nonempty h.Filling :=
  ⟨h.canonical⟩

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
def TermNode.fill (n : TermNode Base Δ Γ A) (f : n.asHole.Filling) :
    {t : Tm Base // HasType Δ Γ t A} :=
  match n with
  | .valid t ht => ⟨t, ht⟩
  | .hole _ | .broken .. => ⟨f.1, f.2⟩

def TermNode.repair (n : TermNode Base Δ Γ A) : {t : Tm Base // HasType Δ Γ t A} :=
  n.fill n.asHole.canonical

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
  | .hyp .. | .truth .. => PUnit
  | .eqRefl _ _ x => x.asHole.Filling

/-- Filling-dependent raw conclusion. This, rather than canonical repair, is
the meaning of a Covalence proof. -/
def CovProves.lowerTerm {n : TermNode Base Δ Γ .tyBool}
    (d : CovProves Δ Γ H n) : d.Fillings → Tm Base
  | .unit => match d with
    | .hyp _ _ => n.repair.1
    | .truth _ => .tmBool true
  | f => match d with
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
    (d : CovProves Δ Γ H n) : d.Fillings := by
  cases d with
  | hyp | truth => exact .unit
  | eqRefl _ _ x => exact x.asHole.canonical

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
