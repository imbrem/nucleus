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

def ofRaw (tm : Tm Sig types depth) (typing : HasType Γ tm A) :
    DefEqChecked Sig Γ A := ⟨tm, .exact typing⟩

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

def abs (hA : Kinded A) (predicate : Tm Sig types 1)
    (predicateTyping : HasType (extendBound A emptyBound) predicate .boolTy)
    (value : DefEqChecked Sig Γ A) : DefEqChecked Sig Γ (.sub A predicate) :=
  ⟨.abs A predicate value.tm, .abs hA predicateTyping value.typing⟩

def rep (hA : Kinded A) (predicate : Tm Sig types 1)
    (predicateTyping : HasType (extendBound A emptyBound) predicate .boolTy)
    (value : DefEqChecked Sig Γ (.sub A predicate)) : DefEqChecked Sig Γ A :=
  ⟨.rep A predicate value.tm, .rep hA predicateTyping value.typing⟩

end DefEqChecked

end Nucleus.Hol.FamilySub
