import Nucleus.Hol.Signature

/-!
# Small interfaces for HOL presentations

These classes intentionally expose only the common core needed by the first
finite-vs-natural experiment.  More connectives and proof rules can be added
without coupling generic constructions to a concrete syntax representation.
-/

namespace Nucleus.Hol

universe u

set_option relaxedAutoImplicit true

/-- Marker selecting the signature-parametric implementation. -/
inductive Language (Sig : Signature) where
  | marker (sort : HolSort) (symbol : Sig sort)

/-- Operations available from an extrinsically typed HOL syntax. -/
class UntypedSyntax (L : Type u) where
  Ty : Type u
  Tm : Nat → Type u
  boolTy : Ty
  arr : Ty → Ty → Ty
  app : Tm depth → Tm depth → Tm depth
  bool : Bool → Tm depth
  eq : Ty → Tm depth → Tm depth → Tm depth

/-- Kinding and typing for an untyped syntax. -/
class Typing (L : Type u) [UntypedSyntax L] where
  Ctx : Nat → Type u
  empty : Ctx 0
  Kinded : UntypedSyntax.Ty (L := L) → Prop
  HasType : Ctx depth → UntypedSyntax.Tm (L := L) depth →
    UntypedSyntax.Ty (L := L) → Prop

/-- An intrinsic façade whose inhabitants retain the extrinsic typing proof. -/
class IntrinsicSyntax (L : Type u) [UntypedSyntax L] [Typing L] where
  Checked : (depth : Nat) →
    Typing.Ctx (L := L) depth → UntypedSyntax.Ty (L := L) → Type u
  tm : Checked depth Γ A → UntypedSyntax.Tm (L := L) depth
  typing : (checked : Checked depth Γ A) →
    Typing.HasType (L := L) Γ (tm checked) A

/-- The deliberately small common proof-system surface.  Extension-specific
rules, such as successor injectivity, belong to later extension classes. -/
class ProofSystem (L : Type u) [UntypedSyntax L] [Typing L] where
  EqTm : Typing.Ctx (L := L) depth →
    UntypedSyntax.Tm (L := L) depth → UntypedSyntax.Tm (L := L) depth →
    UntypedSyntax.Ty (L := L) → Type u
  Proves : Typing.Ctx (L := L) depth →
    List (UntypedSyntax.Tm (L := L) depth) →
    UntypedSyntax.Tm (L := L) depth → Type u
  refl : Typing.HasType (L := L) Γ tm A → EqTm Γ tm tm A
  symm : EqTm Γ left right A → EqTm Γ right left A
  trans : EqTm Γ left middle A → EqTm Γ middle right A → EqTm Γ left right A
  app : EqTm Γ f g (UntypedSyntax.arr A B) → EqTm Γ x y A →
    EqTm Γ (UntypedSyntax.app f x) (UntypedSyntax.app g y) B
  hyp : Typing.HasType (L := L) Γ p UntypedSyntax.boolTy → p ∈ H → Proves Γ H p
  truth : Proves Γ H (UntypedSyntax.bool true)
  eqRefl : Typing.Kinded (L := L) A → Typing.HasType (L := L) Γ x A →
    Proves Γ H (UntypedSyntax.eq A x x)

instance {Sig : Signature} : UntypedSyntax (Language Sig) where
  Ty := Nucleus.Hol.Ty Sig
  Tm := Nucleus.Hol.Tm Sig
  boolTy := .boolTy
  arr := .arr
  app := .app
  bool := .bool
  eq := .eq

instance {Sig : Signature} [SigTyping Sig] : Typing (Language Sig) where
  Ctx := BoundCtx Sig
  empty := emptyBound
  Kinded := Nucleus.Hol.Kinded
  HasType := Nucleus.Hol.HasType

instance {Sig : Signature} [SigTyping Sig] : IntrinsicSyntax (Language Sig) where
  Checked := fun _ => Nucleus.Hol.Checked Sig
  tm := fun checked => checked.tm
  typing := fun checked => checked.typing

/-! ## A minimal reusable core proof implementation -/

inductive CoreEqTm {Sig : Signature} [SigTyping Sig] : {depth : Nat} →
    BoundCtx Sig depth → Tm Sig depth → Tm Sig depth → Ty Sig → Type u where
  | refl (typing : HasType Γ tm A) : CoreEqTm Γ tm tm A
  | symm : CoreEqTm Γ left right A → CoreEqTm Γ right left A
  | trans : CoreEqTm Γ left middle A → CoreEqTm Γ middle right A →
      CoreEqTm Γ left right A
  | app : CoreEqTm Γ f g (.arr A B) → CoreEqTm Γ x y A →
      CoreEqTm Γ (.app f x) (.app g y) B

inductive CoreProves {Sig : Signature} [SigTyping Sig] {depth : Nat}
    (Γ : BoundCtx Sig depth) : List (Tm Sig depth) → Tm Sig depth → Type u where
  | hyp (typing : HasType Γ p .boolTy) (member : p ∈ H) : CoreProves Γ H p
  | truth : CoreProves Γ H (.bool true)
  | eqRefl (hA : Kinded A) (typing : HasType Γ x A) :
      CoreProves Γ H (.eq A x x)

instance {Sig : Signature} [SigTyping Sig] : ProofSystem (Language Sig) where
  EqTm := CoreEqTm
  Proves := CoreProves
  refl := CoreEqTm.refl
  symm := CoreEqTm.symm
  trans := CoreEqTm.trans
  app := CoreEqTm.app
  hyp := CoreProves.hyp
  truth := CoreProves.truth
  eqRefl := CoreProves.eqRefl

/-- The two initial languages differ only in their signature and signature
typing instance; generic clients use the same four interfaces. -/
abbrev FiniteLanguage := Language FiniteSig
abbrev NatLanguage := Language NatSig

end Nucleus.Hol
