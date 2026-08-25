import Nucleus.HolE.Named.Conversion
import Nucleus.HolE.Named.Lower

/-!
# Weakening named lowering by an outer type scope

Named binders are stored from innermost to outermost.  Appending a scope on
the right therefore adds binders outside every binder already in the source
scope.  A named expression which lowered before that extension continues to
lower, with its locally nameless type variables embedded into the longer
context.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

noncomputable local instance (priority := low) {α : Type _} : DecidableEq α :=
  Classical.decEq α

/-- Add an outer scope after all existing, more local type binders. -/
def TyScope.appendOuter : TyScope inner → TyScope outer → TyScope (inner ++ outer)
  | .nil, outerScope => outerScope
  | .cons name rest, outerScope => .cons name (rest.appendOuter outerScope)

/-- Embed a heterogeneous de Bruijn index through a right context append. -/
def appendRight : Nucleus.HolE.TyVar inner kind →
    Nucleus.HolE.TyVar (inner ++ outer) kind
  | .zero => .zero
  | .succ item => .succ (appendRight item)

abbrev appendRightRen (inner outer : List Kind) :
    Nucleus.HolE.TyRen inner (inner ++ outer) :=
  fun item => appendRight item

@[simp] theorem TyScope.appendOuter_nil (outerScope : TyScope outer) :
    (.nil : TyScope []).appendOuter outerScope = outerScope := rfl

@[simp] theorem TyScope.appendOuter_cons (name : Nat) (rest : TyScope inner)
    (outerScope : TyScope outer) :
    (TyScope.cons (kind := kind) name rest).appendOuter outerScope =
      TyScope.cons name (rest.appendOuter outerScope) := rfl

@[simp] theorem appendRight_zero :
    appendRight (outer := outer)
      (Nucleus.HolE.TyVar.zero : Nucleus.HolE.TyVar (kind :: inner) kind) =
      Nucleus.HolE.TyVar.zero := rfl

@[simp] theorem appendRight_succ (item : Nucleus.HolE.TyVar inner kind) :
    appendRight (outer := outer)
      (Nucleus.HolE.TyVar.succ (other := other) item) =
      Nucleus.HolE.TyVar.succ (appendRight item) := rfl

@[simp] theorem liftTyRen_appendRight (inner outer : List Kind)
    (item : Nucleus.HolE.TyVar (kind :: inner) resultKind) :
    Nucleus.HolE.liftTyRen (appendRightRen inner outer) item =
      appendRight (outer := outer) item := by
  cases item <;> rfl

theorem appendRightRen_cons (inner outer : List Kind) :
    (fun {resultKind} (item : Nucleus.HolE.TyVar (kind :: inner) resultKind) =>
      appendRight (outer := outer) item) =
    (fun {resultKind} (item : Nucleus.HolE.TyVar (kind :: inner) resultKind) =>
      Nucleus.HolE.liftTyRen (kind := kind) (appendRightRen inner outer) item) := by
  funext resultKind item
  exact (liftTyRen_appendRight inner outer item).symm

/-- A lookup already resolved by the inner scope is unaffected by appending
outer binders.  No claim is made for an unresolved lookup: the new outer
scope may intentionally capture it. -/
theorem lookupTy_appendOuter_of_some (innerScope : TyScope inner)
    (outerScope : TyScope outer)
    (found : lookupTy wanted innerScope = some item) :
    lookupTy wanted (innerScope.appendOuter outerScope) =
      some (appendRight item) := by
  induction innerScope with
  | nil => simp [lookupTy] at found
  | @cons inner headKind name rest ih =>
      simp only [TyScope.appendOuter_cons, lookupTy]
      simp only [lookupTy] at found
      by_cases sameName : wanted.name = name
      · simp only [sameName] at found ⊢
        by_cases sameKind : wanted.sort = headKind
        · simp only [sameKind, ↓reduceDIte, Option.some.injEq] at found ⊢
          subst sameKind
          cases found
          rfl
        · simp only [sameKind, ↓reduceDIte] at found ⊢
          cases restFound : lookupTy wanted rest with
          | none => simp [restFound] at found
          | some restItem =>
              simp only [restFound, Option.map_some, Option.some.injEq] at found
              cases found
              rw [ih restFound]
              rfl
      · simp only [sameName] at found ⊢
        cases restFound : lookupTy wanted rest with
        | none => simp [restFound] at found
        | some restItem =>
            simp only [restFound, Option.map_some] at found
            cases found
            rw [ih restFound]
            rfl

private def LoweringAppendOuter (expression : Expr Sig Nat sort) : Prop :=
  match sort with
  | .kind _ => ∀ {inner outer lowered} (innerScope : TyScope inner)
      (outerScope : TyScope outer),
      lowerFam innerScope expression = some lowered →
      lowerFam (innerScope.appendOuter outerScope) expression =
        some (Nucleus.HolE.renameTypes (appendRightRen inner outer) lowered)
  | .tm => ∀ {inner outer depth lowered} (innerScope : TyScope inner)
      (outerScope : TyScope outer) (termScope : TmScope Sig depth),
      lowerTm innerScope termScope expression = some lowered →
      lowerTm (innerScope.appendOuter outerScope) termScope expression =
        some (Nucleus.HolE.renameTypes (appendRightRen inner outer) lowered)

/-- Lowering commutes with appending binders outside the current type scope,
provided the expression already lowered before the extension. -/
private theorem lowering_appendOuter (expression : Expr Sig Nat sort) :
    LoweringAppendOuter expression := by
  induction expression with
  | boolTy =>
      intro inner outer lowered innerScope outerScope found
      simp only [lowerFam] at found ⊢
      cases Option.some.inj found
      rfl
  | arr domain codomain ihDomain ihCodomain =>
      intro inner outer lowered innerScope outerScope found
      simp only [lowerFam] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨d, hd, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨c, hc, result⟩
      cases Option.some.inj result
      rw [ihDomain innerScope outerScope hd, ihCodomain innerScope outerScope hc]
      rfl
  | tyApp function argument ihFunction ihArgument =>
      intro inner outer lowered innerScope outerScope found
      simp only [lowerFam] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨f, hf, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨a, ha, result⟩
      cases Option.some.inj result
      rw [ihFunction innerScope outerScope hf, ihArgument innerScope outerScope ha]
      rfl
  | @tyLam domain codomain name body ih =>
      intro inner outer lowered innerScope outerScope found
      simp only [lowerFam] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨b, hb, result⟩
      cases Option.some.inj result
      have bodyWeakened := ih (TyScope.cons name innerScope) outerScope hb
      simp only [TyScope.appendOuter_cons] at bodyWeakened
      rw [bodyWeakened]
      rw [appendRightRen_cons]
      rfl
  | tyFv name kind =>
      intro inner outer lowered innerScope outerScope found
      simp only [lowerFam] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨item, itemFound, result⟩
      cases Option.some.inj result
      rw [lookupTy_appendOuter_of_some innerScope outerScope itemFound]
      rfl
  | sub carrier name predicate ihCarrier ihPredicate =>
      intro inner outer lowered innerScope outerScope found
      simp only [lowerFam] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨a, ha, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨p, hp, result⟩
      cases Option.some.inj result
      rw [ihCarrier innerScope outerScope ha,
        ihPredicate innerScope outerScope (.cons ⟨name, carrier⟩ .nil) hp]
      rfl
  | tyExists name predicate ih =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨p, hp, result⟩
      cases Option.some.inj result
      have predicateWeakened := ih (TyScope.cons name innerScope) outerScope .nil hp
      simp only [TyScope.appendOuter_cons] at predicateWeakened
      rw [predicateWeakened]
      rw [appendRightRen_cons]
      rfl
  | model name predicate ih =>
      intro inner outer lowered innerScope outerScope found
      simp only [lowerFam] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨p, hp, result⟩
      cases Option.some.inj result
      have predicateWeakened := ih (TyScope.cons name innerScope) outerScope .nil hp
      simp only [TyScope.appendOuter_cons] at predicateWeakened
      rw [predicateWeakened]
      rw [appendRightRen_cons]
      rfl
  | primFam symbol =>
      intro inner outer lowered innerScope outerScope found
      simp only [lowerFam] at found ⊢
      cases Option.some.inj found
      rfl
  | primTm symbol =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      cases Option.some.inj found
      rfl
  | tmFv name type ih =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      cases lookup : lookupTm ⟨name, type⟩ termScope with
      | some index =>
          simp only [lookup] at found ⊢
          cases Option.some.inj found
          rfl
      | none =>
          simp only [lookup] at found ⊢
          rcases Option.bind_eq_some_iff.mp found with ⟨a, ha, result⟩
          cases Option.some.inj result
          rw [ih innerScope outerScope ha]
          rfl
  | app function argument ihFunction ihArgument =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨f, hf, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨a, ha, result⟩
      cases Option.some.inj result
      rw [ihFunction innerScope outerScope termScope hf,
        ihArgument innerScope outerScope termScope ha]
      rfl
  | lam name domain body ihDomain ihBody =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨a, ha, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨b, hb, result⟩
      cases Option.some.inj result
      rw [ihDomain innerScope outerScope ha,
        ihBody innerScope outerScope (.cons ⟨name, domain⟩ termScope) hb]
      rfl
  | bool value =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      cases Option.some.inj found
      rfl
  | eq type left right ihType ihLeft ihRight =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨a, ha, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨l, hl, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨r, hr, result⟩
      cases Option.some.inj result
      rw [ihType innerScope outerScope ha,
        ihLeft innerScope outerScope termScope hl,
        ihRight innerScope outerScope termScope hr]
      rfl
  | eps type predicate ihType ihPredicate =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨a, ha, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨p, hp, result⟩
      cases Option.some.inj result
      rw [ihType innerScope outerScope ha,
        ihPredicate innerScope outerScope termScope hp]
      rfl
  | abs carrier name predicate value ihCarrier ihPredicate ihValue =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨a, ha, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨p, hp, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨x, hx, result⟩
      cases Option.some.inj result
      rw [ihCarrier innerScope outerScope ha,
        ihPredicate innerScope outerScope (.cons ⟨name, carrier⟩ .nil) hp,
        ihValue innerScope outerScope termScope hx]
      rfl
  | rep carrier name predicate value ihCarrier ihPredicate ihValue =>
      intro inner outer depth lowered innerScope outerScope termScope found
      simp only [lowerTm] at found ⊢
      rcases Option.bind_eq_some_iff.mp found with ⟨a, ha, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨p, hp, rest⟩
      rcases Option.bind_eq_some_iff.mp rest with ⟨x, hx, result⟩
      cases Option.some.inj result
      rw [ihCarrier innerScope outerScope ha,
        ihPredicate innerScope outerScope (.cons ⟨name, carrier⟩ .nil) hp,
        ihValue innerScope outerScope termScope hx]
      rfl

/-- Public family-specialized outer weakening law. -/
theorem lowerFam_appendOuter (innerScope : TyScope inner)
    (outerScope : TyScope outer) (family : Fam Sig kind)
    (found : lowerFam innerScope family = some lowered) :
    lowerFam (innerScope.appendOuter outerScope) family =
      some (Nucleus.HolE.renameTypes (appendRightRen inner outer) lowered) :=
  lowering_appendOuter family innerScope outerScope found

/-- Public term-specialized outer weakening law. -/
theorem lowerTm_appendOuter (innerScope : TyScope inner)
    (outerScope : TyScope outer) (termScope : TmScope Sig depth)
    (term : Tm Sig)
    (found : lowerTm innerScope termScope term = some lowered) :
    lowerTm (innerScope.appendOuter outerScope) termScope term =
      some (Nucleus.HolE.renameTypes (appendRightRen inner outer) lowered) :=
  lowering_appendOuter term innerScope outerScope termScope found

/-- A closed named family conversion remains valid beneath any outer named
type scope. Endpoint kinding is explicit because arbitrary signature-provided
family equality certificates need not establish it themselves. -/
def FamEq.weakenOuter
    {Sig : Signature} [Nucleus.HolE.SigTyping Sig]
    [Nucleus.HolE.SigFamilyEquality Sig]
    {kind : Kind} {left right : Fam Sig kind}
    (conversion : FamEq (Sig := Sig) (.nil : TyScope []) left right)
    (leftKinded : Nucleus.HolE.Kinded (Sig := Sig) conversion.loweredLeft)
    (rightKinded : Nucleus.HolE.Kinded (Sig := Sig) conversion.loweredRight)
    (outerScope : TyScope outer) : FamEq outerScope left right where
  loweredLeft := Nucleus.HolE.renameTypes (appendRightRen [] outer)
    conversion.loweredLeft
  loweredRight := Nucleus.HolE.renameTypes (appendRightRen [] outer)
    conversion.loweredRight
  leftLowering := by
    simpa using lowerFam_appendOuter (.nil : TyScope []) outerScope left
      conversion.leftLowering
  rightLowering := by
    simpa using lowerFam_appendOuter (.nil : TyScope []) outerScope right
      conversion.rightLowering
  derivation := conversion.derivation.renameTypes leftKinded rightKinded
    (appendRightRen [] outer)

end Nucleus.HolE.Named
