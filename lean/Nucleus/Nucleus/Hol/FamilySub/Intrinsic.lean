import Nucleus.Hol.FamilySub.Kernel

/-! # Intrinsic terms modulo type-family definitional equality -/

namespace Nucleus.Hol.FamilySub

set_option relaxedAutoImplicit true

structure DefEqChecked (Sig : Signature) [SigTyping Sig] {types : List Kind} {depth : Nat}
    (Γ : BoundCtx Sig types depth) (A : Ty Sig types) where
  tm : Tm Sig types depth
  typing : HasTypeDefEq Γ tm A

namespace DefEqChecked

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {A B : Ty Sig types}

@[ext] theorem ext {left right : DefEqChecked Sig Γ A}
    (terms : left.tm = right.tm) : left = right := by
  cases left
  cases right
  cases terms
  rfl

def ofRaw (tm : Tm Sig types depth) (typing : HasType Γ tm A) :
    DefEqChecked Sig Γ A := ⟨tm, .exact typing⟩

def bv (hA : Kinded A) (index : Fin depth) (lookup : Γ index = A) :
    DefEqChecked Sig Γ A := ⟨.bv index, .exact (.bv hA lookup)⟩

def fv (name : Nat) (hA : Kinded A) : DefEqChecked Sig Γ A :=
  ⟨.fv name A, .exact (.fv name hA)⟩

def boolean (value : Bool) : DefEqChecked Sig Γ .boolTy :=
  ⟨.bool value, .exact (.bool value)⟩

def conv (term : DefEqChecked Sig Γ A) (hB : Kinded B) (conversion : FamEq Sig A B) :
    DefEqChecked Sig Γ B := ⟨term.tm, .conv term.typing hB conversion⟩

def weaken {C : Ty Sig types} (term : DefEqChecked Sig Γ A) :
    DefEqChecked Sig (extendBound C Γ) A :=
  ⟨FamilySub.weaken term.tm, term.typing.weaken⟩

def app (function : DefEqChecked Sig Γ (.arr A B)) (argument : DefEqChecked Sig Γ A) :
    DefEqChecked Sig Γ B :=
  ⟨.app function.tm argument.tm, .app function.typing argument.typing⟩

def lam (hA : Kinded A) (body : DefEqChecked Sig (extendBound A Γ) B) :
    DefEqChecked Sig Γ (.arr A B) :=
  ⟨.lam A body.tm, .lam body.tm hA body.typing⟩

def eq (hA : Kinded A) (left right : DefEqChecked Sig Γ A) :
    DefEqChecked Sig Γ .boolTy :=
  ⟨.eq A left.tm right.tm, .eq hA left.typing right.typing⟩

def eps (hA : Kinded A) (predicate : DefEqChecked Sig Γ (.arr A .boolTy)) :
    DefEqChecked Sig Γ A :=
  ⟨.eps A predicate.tm, .eps hA predicate.typing⟩

/-- Choice-based existential quantification over an intrinsically checked
body. -/
def existsTm (hA : Kinded A) (body : DefEqChecked Sig (extendBound A Γ) .boolTy) :
    DefEqChecked Sig Γ .boolTy :=
  let predicate := DefEqChecked.lam hA body
  predicate.app (predicate.eps hA)

def abs (hA : Kinded A) (predicate : Tm Sig types 1)
    (predicateTyping : HasType (extendBound A emptyBound) predicate .boolTy)
    (value : DefEqChecked Sig Γ A) : DefEqChecked Sig Γ (.sub A predicate) :=
  ⟨.abs A predicate value.tm, .abs hA predicateTyping value.typing⟩

def rep (hA : Kinded A) (predicate : Tm Sig types 1)
    (predicateTyping : HasType (extendBound A emptyBound) predicate .boolTy)
    (value : DefEqChecked Sig Γ (.sub A predicate)) : DefEqChecked Sig Γ A :=
  ⟨.rep A predicate value.tm, .rep hA predicateTyping value.typing⟩

def openBound (typedContext : TypedCtx Γ)
    (body : DefEqChecked Sig (extendBound A Γ) B)
    (argument : DefEqChecked Sig Γ A) : DefEqChecked Sig Γ B :=
  ⟨FamilySub.openBound body.tm argument.tm,
    body.typing.openBound typedContext argument.typing⟩

end DefEqChecked

abbrev BoolTm {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
    (Γ : BoundCtx Sig types depth) := DefEqChecked Sig Γ (.boolTy : Ty Sig types)

abbrev HolProp {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
    (Γ : BoundCtx Sig types depth) := BoolTm Γ

abbrev PropCtx {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
    (Γ : BoundCtx Sig types depth) := List (BoolTm Γ)

abbrev ClosedPropCtx {Sig : Signature} [SigTyping Sig] {types : List Kind} :=
  PropCtx (emptyBound : BoundCtx Sig types 0)

namespace PropCtx

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth}

def terms (context : PropCtx Γ) : List (Tm Sig types depth) :=
  context.map DefEqChecked.tm

theorem typed (context : PropCtx Γ) : TypedHyps Γ context.terms := by
  intro p member
  obtain ⟨checked, _, rfl⟩ := List.mem_map.mp member
  exact checked.typing

def ofTyped (hypotheses : List (Tm Sig types depth)) (typed : TypedHyps Γ hypotheses) :
    PropCtx Γ :=
  hypotheses.attach.map fun member => ⟨member.1, typed member.1 member.2⟩

@[simp] theorem terms_ofTyped (hypotheses : List (Tm Sig types depth))
    (typed : TypedHyps Γ hypotheses) : (ofTyped hypotheses typed).terms = hypotheses := by
  simp [ofTyped, terms]

end PropCtx

namespace Intrinsic

universe u

variable {Sig : Signature} [SigTyping Sig] {types : List Kind} {depth : Nat}
  {Γ : BoundCtx Sig types depth} {H : PropCtx Γ} {p : BoolTm Γ}
  {A : Ty Sig types}

structure EqTm (left right : DefEqChecked Sig Γ A) : Type u where
  proof : FamilySub.EqTm Γ left.tm right.tm A

namespace EqTm

def refl (term : DefEqChecked Sig Γ A) : EqTm term term :=
  ⟨.refl term.typing⟩

def symm {left right : DefEqChecked Sig Γ A} (equality : EqTm left right) :
    EqTm right left :=
  ⟨.symm equality.proof⟩

def trans {left middle right : DefEqChecked Sig Γ A}
    (first : EqTm left middle) (second : EqTm middle right) : EqTm left right :=
  ⟨.trans first.proof second.proof⟩

def app {functionLeft functionRight : DefEqChecked Sig Γ (.arr A B)}
    {argumentLeft argumentRight : DefEqChecked Sig Γ A}
    (functionEquality : EqTm functionLeft functionRight)
    (argumentEquality : EqTm argumentLeft argumentRight) :
    EqTm (functionLeft.app argumentLeft) (functionRight.app argumentRight) :=
  ⟨.app functionEquality.proof argumentEquality.proof⟩

def lam (hA : Kinded A)
    {bodyLeft bodyRight : DefEqChecked Sig (extendBound A Γ) B}
    (bodyEquality : EqTm bodyLeft bodyRight) :
    EqTm (DefEqChecked.lam hA bodyLeft) (DefEqChecked.lam hA bodyRight) :=
  ⟨.lam hA bodyEquality.proof⟩

def beta (typedContext : TypedCtx Γ) (hA : Kinded A)
    (body : DefEqChecked Sig (extendBound A Γ) B)
    (argument : DefEqChecked Sig Γ A) :
    EqTm ((DefEqChecked.lam hA body).app argument)
      (body.openBound typedContext argument) :=
  ⟨.beta body.tm argument.tm hA body.typing argument.typing
    (body.typing.openBound typedContext argument.typing)⟩

end EqTm

structure Proves (Γ : BoundCtx Sig types depth) (H : PropCtx Γ) (p : BoolTm Γ) : Type u where
  proof : FamilySub.Proves Γ H.terms p.tm

def eqFromLeftBody (hA : Kinded A) (left : DefEqChecked Sig Γ A) :
    BoolTm (extendBound A Γ) :=
  DefEqChecked.eq hA left.weaken (DefEqChecked.bv hA 0 rfl)

def eqToRightBody (hA : Kinded A) (right : DefEqChecked Sig Γ A) :
    BoolTm (extendBound A Γ) :=
  DefEqChecked.eq hA (DefEqChecked.bv hA 0 rfl) right.weaken

def appFromLeftBody (hA : Kinded A) (hB : Kinded B)
    (function : DefEqChecked Sig Γ (.arr A B)) (argument : DefEqChecked Sig Γ A) :
    BoolTm (extendBound (.arr A B) Γ) :=
  let varied := DefEqChecked.bv (.arr hA hB) 0 rfl
  DefEqChecked.eq hB (function.app argument).weaken (varied.app argument.weaken)

theorem eqFromLeftBody_open (typed : TypedCtx Γ) (hA : Kinded A)
    (left argument : DefEqChecked Sig Γ A) :
    (eqFromLeftBody hA left).openBound typed argument =
      DefEqChecked.eq hA left argument := by
  apply DefEqChecked.ext
  simp [eqFromLeftBody, DefEqChecked.openBound, DefEqChecked.eq,
    DefEqChecked.weaken, DefEqChecked.bv, FamilySub.openBound, instantiate]

theorem eqToRightBody_open (typed : TypedCtx Γ) (hA : Kinded A)
    (right argument : DefEqChecked Sig Γ A) :
    (eqToRightBody hA right).openBound typed argument =
      DefEqChecked.eq hA argument right := by
  apply DefEqChecked.ext
  simp [eqToRightBody, DefEqChecked.openBound, DefEqChecked.eq,
    DefEqChecked.weaken, DefEqChecked.bv, FamilySub.openBound, instantiate]

theorem appFromLeftBody_open (typed : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (function varied : DefEqChecked Sig Γ (.arr A B))
    (argument : DefEqChecked Sig Γ A) :
    (appFromLeftBody hA hB function argument).openBound typed varied =
      DefEqChecked.eq hB (function.app argument) (varied.app argument) := by
  apply DefEqChecked.ext
  simp [appFromLeftBody, DefEqChecked.openBound, DefEqChecked.eq,
    DefEqChecked.app, DefEqChecked.weaken, DefEqChecked.bv,
    FamilySub.openBound, instantiate]

namespace Proves

def hyp {p : BoolTm Γ} (member : p ∈ H) : Proves Γ H p :=
  ⟨.hyp (PropCtx.typed H) (List.mem_map_of_mem member)⟩

def truth : Proves Γ H (DefEqChecked.boolean true) :=
  ⟨.truth (PropCtx.typed H)⟩

def eqRefl (hA : Kinded A) (x : DefEqChecked Sig Γ A) :
    Proves Γ H (DefEqChecked.eq hA x x) :=
  ⟨.eqRefl (PropCtx.typed H) hA x.typing⟩

def eqMp (hA : Kinded A) (predicate : DefEqChecked Sig Γ (.arr A .boolTy))
    (x y : DefEqChecked Sig Γ A) (equality : Proves Γ H (DefEqChecked.eq hA x y))
    (application : Proves Γ H (predicate.app x)) : Proves Γ H (predicate.app y) :=
  ⟨.eqMp (PropCtx.typed H) hA predicate.typing x.typing y.typing
    equality.proof application.proof⟩

def choice (hA : Kinded A) (predicate : DefEqChecked Sig Γ (.arr A .boolTy))
    (x : DefEqChecked Sig Γ A) (premise : Proves Γ H (predicate.app x)) :
    Proves Γ H (predicate.app (predicate.eps hA)) :=
  ⟨.choice (PropCtx.typed H) hA predicate.typing x.typing premise.proof⟩

/-- HOL existential introduction, where `∃ x, p x` is the usual choice-based
definition `p (ε p)`. -/
def existsIntro (hA : Kinded A) (predicate : DefEqChecked Sig Γ (.arr A .boolTy))
    (witness : DefEqChecked Sig Γ A) (premise : Proves Γ H (predicate.app witness)) :
    Proves Γ H (predicate.app (predicate.eps hA)) :=
  choice hA predicate witness premise

def convert {p q : BoolTm Γ} (equality : EqTm p q) (premise : Proves Γ H p) :
    Proves Γ H q :=
  ⟨.convert (PropCtx.typed H) equality.proof premise.proof⟩

def betaReduce (typedContext : TypedCtx Γ) (hA : Kinded A)
    (body : DefEqChecked Sig (extendBound A Γ) .boolTy)
    (argument : DefEqChecked Sig Γ A)
    (premise : Proves Γ H ((DefEqChecked.lam hA body).app argument)) :
    Proves Γ H (body.openBound typedContext argument) :=
  convert (EqTm.beta typedContext hA body argument) premise

def betaExpand (typedContext : TypedCtx Γ) (hA : Kinded A)
    (body : DefEqChecked Sig (extendBound A Γ) .boolTy)
    (argument : DefEqChecked Sig Γ A)
    (premise : Proves Γ H (body.openBound typedContext argument)) :
    Proves Γ H ((DefEqChecked.lam hA body).app argument) :=
  convert (EqTm.beta typedContext hA body argument).symm premise

def existsIntroBody (typedContext : TypedCtx Γ) (hA : Kinded A)
    (body : DefEqChecked Sig (extendBound A Γ) .boolTy)
    (witness : DefEqChecked Sig Γ A)
    (premise : Proves Γ H (body.openBound typedContext witness)) :
    Proves Γ H (DefEqChecked.existsTm hA body) := by
  apply existsIntro hA (DefEqChecked.lam hA body) witness
  exact betaExpand typedContext hA body witness premise

def eqOfEqTm (hA : Kinded A) {x y : DefEqChecked Sig Γ A} (equality : EqTm x y) :
    Proves Γ H (DefEqChecked.eq hA x y) :=
  ⟨.eqOfEqTm (PropCtx.typed H) hA equality.proof⟩

def eqSymm (typedContext : TypedCtx Γ) (hA : Kinded A)
    (x y : DefEqChecked Sig Γ A)
    (equality : Proves Γ H (DefEqChecked.eq hA x y)) :
    Proves Γ H (DefEqChecked.eq hA y x) := by
  let body := eqToRightBody hA x
  let predicate := DefEqChecked.lam hA body
  have openedX := eqToRightBody_open typedContext hA x x
  have atX : Proves Γ H (body.openBound typedContext x) :=
    openedX.symm ▸ eqRefl hA x
  have predicateAtX : Proves Γ H (predicate.app x) :=
    betaExpand typedContext hA body x atX
  have predicateAtY : Proves Γ H (predicate.app y) :=
    eqMp hA predicate x y equality predicateAtX
  have openedY := eqToRightBody_open typedContext hA x y
  exact openedY ▸ betaReduce typedContext hA body y predicateAtY

def eqTrans (typedContext : TypedCtx Γ) (hA : Kinded A)
    (x y z : DefEqChecked Sig Γ A)
    (first : Proves Γ H (DefEqChecked.eq hA x y))
    (second : Proves Γ H (DefEqChecked.eq hA y z)) :
    Proves Γ H (DefEqChecked.eq hA x z) := by
  let body := eqFromLeftBody hA x
  let predicate := DefEqChecked.lam hA body
  have openedY := eqFromLeftBody_open typedContext hA x y
  have atY : Proves Γ H (body.openBound typedContext y) := openedY.symm ▸ first
  have predicateAtY : Proves Γ H (predicate.app y) :=
    betaExpand typedContext hA body y atY
  have predicateAtZ : Proves Γ H (predicate.app z) :=
    eqMp hA predicate y z second predicateAtY
  have openedZ := eqFromLeftBody_open typedContext hA x z
  exact openedZ ▸ betaReduce typedContext hA body z predicateAtZ

def appCongr (typedContext : TypedCtx Γ) (hA : Kinded A) (hB : Kinded B)
    (function varied : DefEqChecked Sig Γ (.arr A B))
    (argument : DefEqChecked Sig Γ A)
    (equality : Proves Γ H (DefEqChecked.eq (.arr hA hB) function varied)) :
    Proves Γ H (DefEqChecked.eq hB (function.app argument) (varied.app argument)) := by
  let functionTy : Ty Sig types := .arr A B
  let hFunction : Kinded functionTy := .arr hA hB
  let body := appFromLeftBody hA hB function argument
  let predicate := DefEqChecked.lam hFunction body
  have openedFunction := appFromLeftBody_open typedContext hA hB function function argument
  have atFunction : Proves Γ H (body.openBound typedContext function) :=
    openedFunction.symm ▸ eqRefl hB (function.app argument)
  have predicateAtFunction : Proves Γ H (predicate.app function) :=
    betaExpand typedContext hFunction body function atFunction
  have predicateAtVaried : Proves Γ H (predicate.app varied) :=
    eqMp hFunction predicate function varied equality predicateAtFunction
  have openedVaried := appFromLeftBody_open typedContext hA hB function varied argument
  exact openedVaried ▸ betaReduce typedContext hFunction body varied predicateAtVaried

def antisymm (p q : BoolTm Γ) (left : Proves Γ (p :: H) q)
    (right : Proves Γ (q :: H) p) : Proves Γ H (DefEqChecked.eq .boolTy p q) :=
  ⟨.antisymm (PropCtx.typed H) p.typing q.typing (PropCtx.typed (p :: H))
    (PropCtx.typed (q :: H)) left.proof right.proof⟩

def absRep (hA : Kinded A) (predicate : Tm Sig types 1)
    (predicateTyping : HasType (extendBound A emptyBound) predicate .boolTy)
    (x : DefEqChecked Sig Γ (.sub A predicate)) :
    Proves Γ H (DefEqChecked.eq (.sub hA predicateTyping)
      (DefEqChecked.abs hA predicate predicateTyping
        (DefEqChecked.rep hA predicate predicateTyping x)) x) :=
  ⟨.absRep (PropCtx.typed H) hA (.exact predicateTyping) x.typing⟩

def repAbs (hA : Kinded A) (predicate : Tm Sig types 1)
    (predicateTyping : HasType (extendBound A emptyBound) predicate .boolTy)
    (x : DefEqChecked Sig Γ A) (instantiated : BoolTm Γ)
    (term_eq : instantiated.tm = instantiateOne predicate x.tm)
    (premise : Proves Γ H instantiated) :
    Proves Γ H (DefEqChecked.eq hA
      (DefEqChecked.rep hA predicate predicateTyping
        (DefEqChecked.abs hA predicate predicateTyping x)) x) := by
  refine ⟨.repAbs (PropCtx.typed H) hA (.exact predicateTyping) x.typing ?_ ?_⟩
  · exact term_eq ▸ instantiated.typing
  · exact term_eq ▸ premise.proof

def repPredOfWitness (hA : Kinded A) (predicate : Tm Sig types 1)
    (predicateTyping : HasType (extendBound A emptyBound) predicate .boolTy)
    (witness : DefEqChecked Sig Γ A) (witnessPredicate : BoolTm Γ)
    (witnessTermEq : witnessPredicate.tm = instantiateOne predicate witness.tm)
    (value : DefEqChecked Sig Γ (.sub A predicate))
    (representationPredicate : BoolTm Γ)
    (representationTermEq :
      representationPredicate.tm = instantiateOne predicate
        (DefEqChecked.rep hA predicate predicateTyping value).tm)
    (premise : Proves Γ H witnessPredicate) :
    Proves Γ H representationPredicate := by
  have witnessPredicateTyping :
      HasTypeDefEq Γ (instantiateOne predicate witness.tm) .boolTy :=
    witnessTermEq ▸ witnessPredicate.typing
  have representationPredicateTyping :
      HasTypeDefEq Γ
        (instantiateOne predicate
          (DefEqChecked.rep hA predicate predicateTyping value).tm) .boolTy :=
    representationTermEq ▸ representationPredicate.typing
  have witnessProof :
      FamilySub.Proves Γ H.terms (instantiateOne predicate witness.tm) :=
    witnessTermEq ▸ premise.proof
  have result := FamilySub.Proves.repPredOfWitness (PropCtx.typed H) hA
    (.exact predicateTyping) witness.typing witnessPredicateTyping value.typing
    representationPredicateTyping witnessProof
  exact ⟨representationTermEq.symm ▸ result⟩

def toKernel (proof : Proves Γ H p) : FamilySub.Proves Γ H.terms p.tm := proof.proof

def ofKernel (proof : FamilySub.Proves Γ H.terms p.tm) : Proves Γ H p := ⟨proof⟩

end Proves

theorem proves_iff_kernel : Nonempty (Proves Γ H p) ↔
    Nonempty (FamilySub.Proves Γ H.terms p.tm) := by
  constructor <;> rintro ⟨proof⟩
  · exact ⟨proof.proof⟩
  · exact ⟨⟨proof⟩⟩

/-- Every definitionally well-typed raw sequent has a canonical checked
presentation, and the checked façade carries exactly the same certificates. -/
theorem raw_iff_checked {hypotheses : List (Tm Sig types depth)}
    {raw : Tm Sig types depth} (typed : TypedHyps Γ hypotheses)
    (hp : HasTypeDefEq Γ raw .boolTy) :
    Nonempty (FamilySub.Proves Γ hypotheses raw) ↔
      Nonempty (Proves Γ (PropCtx.ofTyped hypotheses typed) ⟨raw, hp⟩) := by
  rw [proves_iff_kernel, PropCtx.terms_ofTyped]

end Intrinsic

end Nucleus.Hol.FamilySub
