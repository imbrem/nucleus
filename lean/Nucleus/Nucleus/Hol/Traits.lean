import Nucleus.Hol.Kernel

/-! # Abstract core HOL syntax, typing, and proof rules -/

namespace Nucleus.Hol

universe u
set_option relaxedAutoImplicit true

inductive Language (Sig : Signature) where
  | marker (sort : HolSort) (symbol : Sig sort)

/-! The sort of type expressions is deliberately abstract.  In simple HOL it
is `Kind`; other implementations may use a flat sort, richer HOL-omega kinds,
or a non-tree/content-addressed representation. -/
class TypeSyntax (L : Type u) where
  Srt : Type u
  Fam : Srt → Type u
  tmSort : Srt

abbrev TypeSyntax.Ty (L : Type u) [TypeSyntax L] :=
  TypeSyntax.Fam (L := L) TypeSyntax.tmSort

class BooleanTypeSyntax (L : Type u) [TypeSyntax L] where
  boolTy : TypeSyntax.Ty L

class FunctionTypeSyntax (L : Type u) [TypeSyntax L] where
  arr : TypeSyntax.Ty L → TypeSyntax.Ty L → TypeSyntax.Ty L

/-- The higher-kinded application fragment.  It is intentionally absent from
the minimal and simple-type interfaces. -/
class AppliedTypeSyntax (L : Type u) [TypeSyntax L] where
  appSort : TypeSyntax.Srt (L := L) → TypeSyntax.Srt (L := L) →
    TypeSyntax.Srt (L := L)
  app : TypeSyntax.Fam (L := L) (appSort domain codomain) →
    TypeSyntax.Fam (L := L) domain → TypeSyntax.Fam (L := L) codomain

class SubtypeTypeSyntax (L : Type u) [TypeSyntax L] where
  SubPred : TypeSyntax.Ty L → Type u
  sub : (A : TypeSyntax.Ty L) → SubPred A → TypeSyntax.Ty L

class TermSyntax (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L]
    [FunctionTypeSyntax L] [SubtypeTypeSyntax L] where
  Tm : Nat → Type u
  Ctx : Nat → Type u
  Lookup : Ctx depth → Fin depth → TypeSyntax.Ty L → Prop
  empty : Ctx 0
  extend : TypeSyntax.Ty L → Ctx depth → Ctx (depth + 1)
  bv : Fin depth → Tm depth
  fv : Nat → TypeSyntax.Ty L → Tm depth
  app : Tm depth → Tm depth → Tm depth
  lam : TypeSyntax.Ty L → Tm (depth + 1) → Tm depth
  bool : Bool → Tm depth
  subPredTm : {A : TypeSyntax.Ty L} → SubtypeTypeSyntax.SubPred (L := L) A → Tm 1
  eq : TypeSyntax.Ty L → Tm depth → Tm depth → Tm depth
  eps : TypeSyntax.Ty L → Tm depth → Tm depth
  abs : (A : TypeSyntax.Ty L) → SubtypeTypeSyntax.SubPred A →
    Tm depth → Tm depth
  rep : (A : TypeSyntax.Ty L) → SubtypeTypeSyntax.SubPred A →
    Tm depth → Tm depth

class TypingRules (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L]
    [FunctionTypeSyntax L] [SubtypeTypeSyntax L] [TermSyntax L] where
  Formed : {sort : TypeSyntax.Srt (L := L)} → TypeSyntax.Fam (L := L) sort → Prop
  HasType : TermSyntax.Ctx (L := L) depth → TermSyntax.Tm (L := L) depth →
    TypeSyntax.Ty L → Prop
  boolTy : Formed BooleanTypeSyntax.boolTy
  arr : Formed A → Formed B → Formed (FunctionTypeSyntax.arr A B)
  bv : Formed A → TermSyntax.Lookup (L := L) Γ i A →
    HasType Γ (TermSyntax.bv i) A
  fv : Formed A → HasType Γ (TermSyntax.fv name A) A
  app : HasType Γ f (FunctionTypeSyntax.arr A B) → HasType Γ x A →
    HasType Γ (TermSyntax.app f x) B
  lam : Formed A → HasType (TermSyntax.extend A Γ) body B →
    HasType Γ (TermSyntax.lam A body) (FunctionTypeSyntax.arr A B)
  bool : HasType Γ (TermSyntax.bool value) BooleanTypeSyntax.boolTy
  eq : Formed A → HasType Γ x A → HasType Γ y A →
    HasType Γ (TermSyntax.eq A x y) BooleanTypeSyntax.boolTy
  eps : Formed A → HasType Γ p (FunctionTypeSyntax.arr A BooleanTypeSyntax.boolTy) →
    HasType Γ (TermSyntax.eps A p) A
  subtype : Formed A →
    HasType (TermSyntax.extend A TermSyntax.empty) (TermSyntax.subPredTm p)
      BooleanTypeSyntax.boolTy →
    Formed (SubtypeTypeSyntax.sub A p)
  abs : Formed A →
    HasType (TermSyntax.extend A TermSyntax.empty) (TermSyntax.subPredTm p)
      BooleanTypeSyntax.boolTy →
    HasType Γ x A → HasType Γ (TermSyntax.abs A p x) (SubtypeTypeSyntax.sub A p)
  rep : Formed A →
    HasType (TermSyntax.extend A TermSyntax.empty) (TermSyntax.subPredTm p)
      BooleanTypeSyntax.boolTy →
    HasType Γ x (SubtypeTypeSyntax.sub A p) → HasType Γ (TermSyntax.rep A p x) A

class AppliedTypeTypingRules (L : Type u) [TypeSyntax L] [AppliedTypeSyntax L]
    [BooleanTypeSyntax L] [FunctionTypeSyntax L] [SubtypeTypeSyntax L]
    [TermSyntax L] [TypingRules L] where
  app : TypingRules.Formed (L := L) F → TypingRules.Formed (L := L) A →
    TypingRules.Formed (L := L) (AppliedTypeSyntax.app F A)

class BindingSyntax (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L]
    [FunctionTypeSyntax L] [SubtypeTypeSyntax L] [TermSyntax L] where
  weaken : TermSyntax.Tm (L := L) depth → TermSyntax.Tm (L := L) (depth + 1)
  openBound : TermSyntax.Tm (L := L) (depth + 1) → TermSyntax.Tm (L := L) depth →
    TermSyntax.Tm (L := L) depth
  instantiateOne : TermSyntax.Tm (L := L) 1 → TermSyntax.Tm (L := L) depth →
    TermSyntax.Tm (L := L) depth
  Fresh : Nat → TermSyntax.Tm (L := L) depth → Prop

class EqualityRules (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L]
    [FunctionTypeSyntax L] [SubtypeTypeSyntax L] [TermSyntax L] [BindingSyntax L]
    [TypingRules L] where
  EqTm : TermSyntax.Ctx (L := L) depth → TermSyntax.Tm (L := L) depth →
    TermSyntax.Tm (L := L) depth → TypeSyntax.Ty L → Type u
  refl : TypingRules.HasType (L := L) Γ t A → EqTm Γ t t A
  symm : EqTm Γ t u A → EqTm Γ u t A
  trans : EqTm Γ t u A → EqTm Γ u v A → EqTm Γ t v A
  app : EqTm Γ f g (FunctionTypeSyntax.arr A B) → EqTm Γ x y A →
    EqTm Γ (TermSyntax.app f x) (TermSyntax.app g y) B
  lam : TypingRules.Formed (L := L) A →
    EqTm (TermSyntax.extend A Γ) t u B →
    EqTm Γ (TermSyntax.lam A t) (TermSyntax.lam A u) (FunctionTypeSyntax.arr A B)
  beta : TypingRules.Formed (L := L) A →
    TypingRules.HasType (L := L) (TermSyntax.extend A Γ) body B →
    TypingRules.HasType (L := L) Γ x A →
    TypingRules.HasType (L := L) Γ (BindingSyntax.openBound body x) B →
    EqTm Γ (TermSyntax.app (TermSyntax.lam A body) x) (BindingSyntax.openBound body x) B
  eta : BindingSyntax.Fresh (L := L) name f →
    TypingRules.HasType (L := L) Γ f (FunctionTypeSyntax.arr A B) →
    TypingRules.HasType (L := L) Γ
      (TermSyntax.lam A (TermSyntax.app (BindingSyntax.weaken f) (TermSyntax.bv 0)))
      (FunctionTypeSyntax.arr A B) →
    EqTm Γ (TermSyntax.lam A (TermSyntax.app (BindingSyntax.weaken f) (TermSyntax.bv 0))) f
      (FunctionTypeSyntax.arr A B)

class ProofRules (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L]
    [FunctionTypeSyntax L] [SubtypeTypeSyntax L] [TermSyntax L] [BindingSyntax L]
    [TypingRules L]
    [EqualityRules L] where
  Proves : TermSyntax.Ctx (L := L) depth → List (TermSyntax.Tm (L := L) depth) →
    TermSyntax.Tm (L := L) depth → Type u
  Typed : TermSyntax.Ctx (L := L) depth → List (TermSyntax.Tm (L := L) depth) → Prop
  hyp : Typed Γ H → p ∈ H → Proves Γ H p
  truth : Typed Γ H → Proves Γ H (TermSyntax.bool true)
  falseElim : Typed Γ H →
    TypingRules.HasType (L := L) Γ p BooleanTypeSyntax.boolTy →
    Proves Γ H (TermSyntax.bool false) → Proves Γ H p
  boolCases : Typed Γ H →
    TypingRules.HasType (L := L) Γ p BooleanTypeSyntax.boolTy →
    Typed Γ (p :: H) → Typed Γ (TermSyntax.eq BooleanTypeSyntax.boolTy p
      (TermSyntax.bool false) :: H) →
    Proves Γ (p :: H) q →
    Proves Γ (TermSyntax.eq BooleanTypeSyntax.boolTy p (TermSyntax.bool false) :: H) q →
    Proves Γ H q
  eqRefl : Typed Γ H → TypingRules.Formed (L := L) A →
    TypingRules.HasType (L := L) Γ x A →
    Proves Γ H (TermSyntax.eq A x x)
  eqMp : Typed Γ H → TypingRules.Formed (L := L) A →
    TypingRules.HasType (L := L) Γ p (FunctionTypeSyntax.arr A BooleanTypeSyntax.boolTy) →
    TypingRules.HasType (L := L) Γ x A → TypingRules.HasType (L := L) Γ y A →
    Proves Γ H (TermSyntax.eq A x y) → Proves Γ H (TermSyntax.app p x) →
    Proves Γ H (TermSyntax.app p y)
  choice : Typed Γ H → TypingRules.Formed (L := L) A →
    TypingRules.HasType (L := L) Γ p (FunctionTypeSyntax.arr A BooleanTypeSyntax.boolTy) →
    TypingRules.HasType (L := L) Γ x A → Proves Γ H (TermSyntax.app p x) →
    Proves Γ H (TermSyntax.app p (TermSyntax.eps A p))
  generalize : Typed Γ H → TypingRules.Formed (L := L) A →
    TypingRules.HasType (L := L) (TermSyntax.extend A Γ) body BooleanTypeSyntax.boolTy →
    Proves (TermSyntax.extend A Γ) (H.map BindingSyntax.weaken) body →
    Proves Γ H (TermSyntax.eq (FunctionTypeSyntax.arr A BooleanTypeSyntax.boolTy)
      (TermSyntax.lam A body) (TermSyntax.lam A (TermSyntax.bool true)))
  weakenBound : Typed Γ H → TypingRules.Formed (L := L) A →
    Typed (TermSyntax.extend A Γ) K →
    (∀ q, q ∈ H → BindingSyntax.weaken q ∈ K) →
    Proves Γ H p →
    Proves (TermSyntax.extend A Γ) K (BindingSyntax.weaken p)
  convert : Typed Γ H → EqualityRules.EqTm (L := L) Γ p q BooleanTypeSyntax.boolTy →
    Proves Γ H p → Proves Γ H q
  eqOfEqTm : Typed Γ H → TypingRules.Formed (L := L) A →
    EqualityRules.EqTm (L := L) Γ x y A → Proves Γ H (TermSyntax.eq A x y)
  antisymm : Typed Γ H →
    TypingRules.HasType (L := L) Γ p BooleanTypeSyntax.boolTy →
    TypingRules.HasType (L := L) Γ q BooleanTypeSyntax.boolTy →
    Typed Γ (p :: H) → Typed Γ (q :: H) → Proves Γ (p :: H) q →
    Proves Γ (q :: H) p → Proves Γ H (TermSyntax.eq BooleanTypeSyntax.boolTy p q)
  absRep : Typed Γ H → TypingRules.Formed (L := L) A →
    TypingRules.HasType (L := L) (TermSyntax.extend A TermSyntax.empty)
      (TermSyntax.subPredTm p) BooleanTypeSyntax.boolTy →
    TypingRules.HasType (L := L) Γ x (SubtypeTypeSyntax.sub A p) →
    Proves Γ H (TermSyntax.eq (SubtypeTypeSyntax.sub A p)
      (TermSyntax.abs A p (TermSyntax.rep A p x)) x)
  repAbs : Typed Γ H → TypingRules.Formed (L := L) A →
    TypingRules.HasType (L := L) (TermSyntax.extend A TermSyntax.empty)
      (TermSyntax.subPredTm p) BooleanTypeSyntax.boolTy →
    TypingRules.HasType (L := L) Γ x A →
    TypingRules.HasType (L := L) Γ
      (BindingSyntax.instantiateOne (TermSyntax.subPredTm p) x) BooleanTypeSyntax.boolTy →
    Proves Γ H (BindingSyntax.instantiateOne (TermSyntax.subPredTm p) x) →
    Proves Γ H (TermSyntax.eq A (TermSyntax.rep A p (TermSyntax.abs A p x)) x)

instance {Sig : Signature} : TypeSyntax (Language Sig) where
  Srt := Kind
  Fam := Nucleus.Hol.Fam Sig
  tmSort := .star

instance {Sig : Signature} : BooleanTypeSyntax (Language Sig) where
  boolTy := .boolTy

instance {Sig : Signature} : FunctionTypeSyntax (Language Sig) where
  arr := .arr

instance {Sig : Signature} : AppliedTypeSyntax (Language Sig) where
  appSort := .arr
  app := .tyApp

instance {Sig : Signature} : SubtypeTypeSyntax (Language Sig) where
  SubPred := fun _ => Tm Sig 1
  sub := .sub

instance {Sig : Signature} : TermSyntax (Language Sig) where
  Tm := Nucleus.Hol.Tm Sig
  Ctx := BoundCtx Sig
  Lookup := fun Γ i A => Γ i = A
  empty := emptyBound
  extend := extendBound
  bv := .bv
  fv := .fv
  app := .app
  lam := .lam
  bool := .bool
  subPredTm := id
  eq := .eq
  eps := .eps
  abs := .abs
  rep := .rep

instance {Sig : Signature} [SigTyping Sig] : TypingRules (Language Sig) where
  Formed := Nucleus.Hol.Kinded
  HasType := Nucleus.Hol.HasType
  boolTy := .boolTy
  arr := .arr
  bv := .bv
  fv := .fv _
  app := .app
  lam := .lam _
  bool := .bool _
  eq := .eq
  eps := .eps
  subtype := .sub
  abs := .abs
  rep := .rep

instance {Sig : Signature} : BindingSyntax (Language Sig) where
  weaken := Nucleus.Hol.weaken
  openBound := Nucleus.Hol.openBound
  instantiateOne := Nucleus.Hol.instantiateOne
  Fresh := fun name (tm : Tm Sig _) => Nucleus.Hol.Fresh name tm

instance {Sig : Signature} [SigTyping Sig] : AppliedTypeTypingRules (Language Sig) where
  app := .tyApp

instance {Sig : Signature} [SigTyping Sig] : EqualityRules (Language Sig) where
  EqTm := Nucleus.Hol.EqTm
  refl := .refl
  symm := .symm
  trans := .trans
  app := .app
  lam := .lam
  beta := fun hA hbody hx hopen => .beta _ _ hA hbody hx hopen
  eta := fun fresh hf heta => .eta _ fresh hf heta

instance {Sig : Signature} [SigTyping Sig] : ProofRules (Language Sig) where
  Proves := Nucleus.Hol.Proves
  Typed := Nucleus.Hol.TypedHyps
  hyp := .hyp
  truth := .truth
  falseElim := .falseElim
  boolCases := .boolCases
  eqRefl := .eqRefl
  eqMp := .eqMp
  choice := .choice
  generalize := .generalize
  weakenBound := .weakenBound
  convert := .convert
  eqOfEqTm := fun typed hA equality => .eqOfEqTm typed hA equality
  antisymm := .antisymm
  absRep := .absRep
  repAbs := .repAbs

/-- Intrinsic terms are derived generically by pairing syntax with typing evidence. -/
structure TypedTm (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L]
    [FunctionTypeSyntax L] [SubtypeTypeSyntax L] [TermSyntax L] [TypingRules L]
    {depth : Nat} (Γ : TermSyntax.Ctx (L := L) depth)
    (A : TypeSyntax.Ty L) where
  tm : TermSyntax.Tm (L := L) depth
  typing : TypingRules.HasType (L := L) Γ tm A

abbrev AbstractBoolTm (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L]
    [FunctionTypeSyntax L] [SubtypeTypeSyntax L] [TermSyntax L] [TypingRules L] :=
  TypedTm L TermSyntax.empty BooleanTypeSyntax.boolTy

instance (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L] [FunctionTypeSyntax L]
    [SubtypeTypeSyntax L] [TermSyntax L] [BindingSyntax L] [TypingRules L] [EqualityRules L]
    [ProofRules L] : CoeSort (AbstractBoolTm L) Prop where
  coe proposition := Nonempty (ProofRules.Proves (L := L) TermSyntax.empty [] proposition.tm)

def falseTm (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L] [FunctionTypeSyntax L]
    [SubtypeTypeSyntax L] [TermSyntax L] [TypingRules L] : AbstractBoolTm L :=
  ⟨TermSyntax.bool false, TypingRules.bool⟩

class Consistency (L : Type u) [TypeSyntax L] [BooleanTypeSyntax L]
    [FunctionTypeSyntax L] [SubtypeTypeSyntax L] [TermSyntax L] [BindingSyntax L] [TypingRules L]
    [EqualityRules L] [ProofRules L] : Prop where
  false_unprovable : ¬ (falseTm L : Prop)

/-- A rule-provider marker that retains `Sig` syntax and typing while adding no
extension rules beyond the core instances above. -/
inductive NoRules (Sig : Signature) where
  | marker (sort : HolSort) (symbol : Sig sort)

end Nucleus.Hol
