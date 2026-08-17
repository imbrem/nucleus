import Nucleus.Hol.Signature

/-!
# Tag names for extensible HOL syntax

Naming is intentionally weaker than canonical serialization.  `TagName` merely
chooses a representation; `InjectiveTagName` certifies uniqueness within one
vocabulary; and `HolTagName` additionally separates extension tags from the
fixed core-HOL namespace.
-/

namespace Nucleus.Hol

universe u v

class TagName (α : Type u) (Name : outParam (Type v)) where
  tagName : α → Name

export TagName (tagName)

class InjectiveTagName (α : Type u) (Name : outParam (Type v))
    extends TagName α Name where
  injective : Function.Injective tagName

/-- The tags owned by core HOL rather than by an extension signature. -/
inductive BasicTag where
  | tyBool | tyArr | tyApp | tySub
  | tmBv | tmFv | tmApp | tmLam | tmBool | tmEq | tmEps | tmAbs | tmRep
  deriving DecidableEq, Repr

def BasicTag.name : BasicTag → String
  | .tyBool => "ty.bool"
  | .tyArr => "ty.arr"
  | .tyApp => "ty.app"
  | .tySub => "ty.sub"
  | .tmBv => "tm.bv"
  | .tmFv => "tm.fv"
  | .tmApp => "tm.app"
  | .tmLam => "tm.lam"
  | .tmBool => "tm.bool"
  | .tmEq => "tm.eq"
  | .tmEps => "tm.eps"
  | .tmAbs => "tm.abs"
  | .tmRep => "tm.rep"

instance : TagName BasicTag String := ⟨BasicTag.name⟩

theorem BasicTag.name_injective : Function.Injective BasicTag.name := by
  intro left right equality
  cases left <;> cases right <;> simp_all [BasicTag.name]

instance : InjectiveTagName BasicTag String where
  injective := BasicTag.name_injective

/-- The dependent sum of all symbols in a sorted signature. -/
inductive Symbol (Sig : Signature) where
  | mk {sort : HolSort} (value : Sig sort)

/-- A combined tag is either owned by core HOL or by the signature. -/
inductive Tag (Sig : Signature) where
  | basic (tag : BasicTag)
  | signature (symbol : Symbol Sig)

instance {Sig : Signature} [TagName (Symbol Sig) String] : TagName (Tag Sig) String where
  tagName
    | .basic tag => tagName tag
    | .signature symbol => tagName symbol

/-- The head constructor tag of a HOL expression.  This is the promised lifted
`TagName` instance: once a signature can name its symbols, every `Expr Sig`
can name its outer JSON constructor. -/
def Expr.headTag {Sig : Signature} : {sort : HolSort} → {depth : Nat} →
    Expr Sig sort depth → Tag Sig
  | _, _, .primFam symbol => .signature (.mk symbol)
  | _, _, .primTm symbol => .signature (.mk symbol)
  | _, _, .boolTy => .basic .tyBool
  | _, _, .arr _ _ => .basic .tyArr
  | _, _, .tyApp _ _ => .basic .tyApp
  | _, _, .sub _ _ => .basic .tySub
  | _, _, .bv _ => .basic .tmBv
  | _, _, .fv _ _ => .basic .tmFv
  | _, _, .app _ _ => .basic .tmApp
  | _, _, .lam _ _ => .basic .tmLam
  | _, _, .bool _ => .basic .tmBool
  | _, _, .eq _ _ _ => .basic .tmEq
  | _, _, .eps _ _ => .basic .tmEps
  | _, _, .abs _ _ _ => .basic .tmAbs
  | _, _, .rep _ _ _ => .basic .tmRep

instance {Sig : Signature} [TagName (Symbol Sig) String] {sort : HolSort} {depth : Nat} :
    TagName (Expr Sig sort depth) String where
  tagName expression := tagName expression.headTag

/-- Canonical combined HOL tagging requires signature names to be injective and
disjoint from every core tag.  Plain `TagName` does not impose either property. -/
class HolTagName (Sig : Signature) extends InjectiveTagName (Symbol Sig) String where
  disjoint : ∀ (basic : BasicTag) (symbol : Symbol Sig),
    BasicTag.name basic ≠ TagName.tagName symbol

instance {Sig : Signature} [HolTagName Sig] : InjectiveTagName (Tag Sig) String where
  injective := by
    intro left right equality
    cases left with
    | basic left =>
        cases right with
        | basic right => exact congrArg Tag.basic (InjectiveTagName.injective equality)
        | signature right => exact False.elim (HolTagName.disjoint left right equality)
    | signature left =>
        cases right with
        | basic right => exact False.elim (HolTagName.disjoint right left equality.symm)
        | signature right =>
            have symbols : left = right :=
              InjectiveTagName.injective (α := Symbol Sig) equality
            cases symbols
            rfl

/-- The empty signature has a vacuous canonical tag namespace. -/
instance : HolTagName FiniteSig where
  tagName symbol := by cases symbol with | mk value => exact nomatch value
  injective left := by cases left with | mk value => exact nomatch value
  disjoint _ symbol := by cases symbol with | mk value => exact nomatch value

def NatSig.tagName : Symbol NatSig → String
  | .mk .natTy => "ty.nat"
  | .mk .zero => "tm.zero"
  | .mk .succ => "tm.succ"

instance : HolTagName NatSig where
  tagName := NatSig.tagName
  injective := by
    intro left right equality
    rcases left with ⟨value⟩
    rcases right with ⟨value'⟩
    cases value <;> cases value' <;> simp_all [NatSig.tagName]
  disjoint := by
    intro basic symbol
    cases basic <;> rcases symbol with ⟨value⟩ <;> cases value <;> decide

end Nucleus.Hol
