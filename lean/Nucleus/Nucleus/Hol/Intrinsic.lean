import Nucleus.Hol.Soundness

/-! # Checked intrinsic façade and equivalence with the raw kernel -/

namespace Nucleus.Hol

universe u
set_option relaxedAutoImplicit true

abbrev BoolTm {Sig : Signature} [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) := Checked Sig Γ (.boolTy : Ty Sig)

abbrev HolProp {Sig : Signature} [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) := BoolTm Γ

abbrev PropCtx {Sig : Signature} [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) := List (BoolTm Γ)

abbrev ClosedPropCtx {Sig : Signature} [SigTyping Sig] :=
  PropCtx (emptyBound : BoundCtx Sig 0)

namespace Checked

@[ext] theorem ext {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A : Ty Sig} {left right : Checked Sig Γ A}
    (terms : left.tm = right.tm) : left = right := by
  cases left
  cases right
  cases terms
  rfl

def boolean {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} (value : Bool) : BoolTm Γ :=
  ⟨.bool value, .bool value⟩

instance {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} : Coe Bool (BoolTm Γ) where
  coe := boolean

def app {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A B : Ty Sig}
    (function : Checked Sig Γ (.arr A B)) (argument : Checked Sig Γ A) :
    Checked Sig Γ B := ⟨.app function.tm argument.tm, .app function.typing argument.typing⟩

def bv {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A : Ty Sig} (hA : Kinded A)
    (index : Fin depth) (lookup : Γ index = A) : Checked Sig Γ A :=
  ⟨.bv index, .bv hA lookup⟩

def fv {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A : Ty Sig} (name : Nat) (hA : Kinded A) :
    Checked Sig Γ A := ⟨.fv name A, .fv name hA⟩

def lam {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A B : Ty Sig} (hA : Kinded A)
    (body : Checked Sig (extendBound A Γ) B) : Checked Sig Γ (.arr A B) :=
  ⟨.lam A body.tm, .lam body.tm hA body.typing⟩

def eq {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A : Ty Sig} (hA : Kinded A)
    (left right : Checked Sig Γ A) : BoolTm Γ :=
  ⟨.eq A left.tm right.tm, .eq hA left.typing right.typing⟩

def eps {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A : Ty Sig} (hA : Kinded A)
    (predicate : Checked Sig Γ (.arr A .boolTy)) : Checked Sig Γ A :=
  ⟨.eps A predicate.tm, .eps hA predicate.typing⟩

def abs {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A : Ty Sig} (hA : Kinded A)
    (predicate : Checked Sig (extendBound A emptyBound) .boolTy)
    (value : Checked Sig Γ A) : Checked Sig Γ (.sub A predicate.tm) :=
  ⟨.abs A predicate.tm value.tm, .abs hA predicate.typing value.typing⟩

def rep {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} {A : Ty Sig} (hA : Kinded A)
    (predicate : Checked Sig (extendBound A emptyBound) .boolTy)
    (value : Checked Sig Γ (.sub A predicate.tm)) : Checked Sig Γ A :=
  ⟨.rep A predicate.tm value.tm, .rep hA predicate.typing value.typing⟩

end Checked

namespace PropCtx

def terms {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} (context : PropCtx Γ) : List (Tm Sig depth) :=
  context.map Checked.tm

theorem typed {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} (context : PropCtx Γ) : TypedHyps Γ context.terms := by
  intro p member
  obtain ⟨checked, _, rfl⟩ := List.mem_map.mp member
  exact checked.typing

def ofTyped {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} (hypotheses : List (Tm Sig depth))
    (typed : TypedHyps Γ hypotheses) : PropCtx Γ :=
  hypotheses.attach.map fun member => ⟨member.1, typed member.1 member.2⟩

@[simp] theorem terms_ofTyped {Sig : Signature} [SigTyping Sig] {depth : Nat}
    {Γ : BoundCtx Sig depth} (hypotheses : List (Tm Sig depth))
    (typed : TypedHyps Γ hypotheses) : (ofTyped hypotheses typed).terms = hypotheses := by
  simp [ofTyped, terms]

end PropCtx

namespace Intrinsic

variable {Sig : Signature} [SigTyping Sig] {depth : Nat}
  {Γ : BoundCtx Sig depth} {H : PropCtx Γ} {p : BoolTm Γ} {A : Ty Sig}

structure EqTm {Sig : Signature} [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) {A : Ty Sig}
    (left right : Checked Sig Γ A) : Type u where
  proof : Nucleus.Hol.EqTm Γ left.tm right.tm A

structure Proves {Sig : Signature} [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) (H : PropCtx Γ) (p : BoolTm Γ) : Type u where
  proof : Nucleus.Hol.Proves Γ H.terms p.tm

namespace Proves

def hyp {p : BoolTm Γ} (member : p ∈ H) : Proves Γ H p :=
  ⟨.hyp (PropCtx.typed H) (List.mem_map_of_mem member)⟩

def truth : Proves Γ H (Checked.boolean true) := ⟨.truth (PropCtx.typed H)⟩

def eqRefl (hA : Kinded A) (x : Checked Sig Γ A) :
    Proves Γ H (Checked.eq hA x x) := ⟨.eqRefl (PropCtx.typed H) hA x.typing⟩

def eqMp (hA : Kinded A) (predicate : Checked Sig Γ (.arr A .boolTy))
    (x y : Checked Sig Γ A) (equality : Proves Γ H (Checked.eq hA x y))
    (application : Proves Γ H (Checked.app predicate x)) :
    Proves Γ H (Checked.app predicate y) :=
  ⟨.eqMp (PropCtx.typed H) hA predicate.typing x.typing y.typing
    equality.proof application.proof⟩

def choice (hA : Kinded A) (predicate : Checked Sig Γ (.arr A .boolTy))
    (x : Checked Sig Γ A) (premise : Proves Γ H (Checked.app predicate x)) :
    Proves Γ H (Checked.app predicate (Checked.eps hA predicate)) :=
  ⟨.choice (PropCtx.typed H) hA predicate.typing x.typing premise.proof⟩

def convert {p q : BoolTm Γ} (equality : EqTm Γ p q)
    (premise : Proves Γ H p) : Proves Γ H q :=
  ⟨.convert (PropCtx.typed H) equality.proof premise.proof⟩

def eqOfEqTm (hA : Kinded A) {x y : Checked Sig Γ A} (equality : EqTm Γ x y) :
    Proves Γ H (Checked.eq hA x y) :=
  ⟨.eqOfEqTm (PropCtx.typed H) hA equality.proof⟩

def antisymm (p q : BoolTm Γ) (left : Proves Γ (p :: H) q)
    (right : Proves Γ (q :: H) p) : Proves Γ H (Checked.eq .boolTy p q) :=
  ⟨.antisymm (PropCtx.typed H) p.typing q.typing (PropCtx.typed (p :: H))
    (PropCtx.typed (q :: H)) left.proof right.proof⟩

def absRep (hA : Kinded A)
    (predicate : Checked Sig (extendBound A emptyBound) .boolTy)
    (x : Checked Sig Γ (.sub A predicate.tm)) :
    Proves Γ H (Checked.eq (.sub hA predicate.typing)
      (Checked.abs hA predicate (Checked.rep hA predicate x)) x) :=
  ⟨.absRep (PropCtx.typed H) hA predicate.typing x.typing⟩

def repAbs (hA : Kinded A)
    (predicate : Checked Sig (extendBound A emptyBound) .boolTy)
    (x : Checked Sig Γ A) (instantiated : BoolTm Γ)
    (term_eq : instantiated.tm = instantiateOne predicate.tm x.tm)
    (premise : Proves Γ H instantiated) :
    Proves Γ H (Checked.eq hA
      (Checked.rep hA predicate (Checked.abs hA predicate x)) x) := by
  refine ⟨.repAbs (PropCtx.typed H) hA predicate.typing x.typing ?_ ?_⟩
  · exact term_eq ▸ instantiated.typing
  · exact term_eq ▸ premise.proof

def toKernel (proof : Proves Γ H p) : Nucleus.Hol.Proves Γ H.terms p.tm := proof.proof

def ofKernel (proof : Nucleus.Hol.Proves Γ H.terms p.tm) : Proves Γ H p := ⟨proof⟩

end Proves

theorem proves_iff_kernel : Nonempty (Proves Γ H p) ↔
    Nonempty (Nucleus.Hol.Proves Γ H.terms p.tm) := by
  constructor <;> rintro ⟨proof⟩
  · exact ⟨proof.proof⟩
  · exact ⟨⟨proof⟩⟩

/-- Every well-typed raw sequent has a canonical checked presentation. -/
theorem raw_iff_checked {hypotheses : List (Tm Sig depth)} {raw : Tm Sig depth}
    (typed : TypedHyps Γ hypotheses) (hp : HasType Γ raw .boolTy) :
    Nonempty (Nucleus.Hol.Proves Γ hypotheses raw) ↔
      Nonempty (Proves Γ (PropCtx.ofTyped hypotheses typed) ⟨raw, hp⟩) := by
  rw [proves_iff_kernel, PropCtx.terms_ofTyped]

theorem EqTm.sound [UniqueSigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    {left right : Checked Sig Γ A} (equality : EqTm Γ left right)
    (freeEnv : FreeEnv Sig) (boundEnv : BoundEnv Γ)
    {leftValue rightValue : DenoteTy A}
    (leftEval : Eval Γ freeEnv boundEnv left.tm A leftValue)
    (rightEval : Eval Γ freeEnv boundEnv right.tm A rightValue) :
    leftValue = rightValue :=
  equality.proof.sound freeEnv boundEnv leftEval rightEval

theorem Proves.sound [UniqueSigTyping Sig] [FamilyModel Sig] [TermModel Sig]
    (proof : Proves Γ H p) :
    Entails (Γ := Γ) H.terms p.tm := proof.proof.sound

end Intrinsic

end Nucleus.Hol
