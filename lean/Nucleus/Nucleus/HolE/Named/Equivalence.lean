import Nucleus.HolE.Named.Alpha
import Nucleus.HolE.Named.Quote

/-!
# Equivalence of named and locally nameless HolE

Quotation is proved inverse to lowering under scopes whose names are resolved
by lowering and lie below the next fresh binder name.  The closed equivalence
is the empty-scope specialization.
-/

namespace Nucleus.HolE.Named

set_option relaxedAutoImplicit true

def TyNames.Valid (scope : TyScope types) (names : TyNames types) : Prop :=
  ∀ {kind} (item : Nucleus.HolE.TyVar types kind),
    lookupTy ⟨names item, kind⟩ scope = some item

def TyNames.Below (next : Nat) (names : TyNames types) : Prop :=
  ∀ {kind} (item : Nucleus.HolE.TyVar types kind), names item < next

def TmNames.Valid (scope : TmScope Sig depth) (names : TmNames Sig depth) : Prop :=
  ∀ item, lookupTm (names item) scope = some item

def TmNames.Below (next : Nat) (names : TmNames Sig depth) : Prop :=
  ∀ item, (names item).name < next

def TmScope.Above (floor : Nat) : TmScope Sig depth → Prop
  | .nil => True
  | .cons declaration rest => floor ≤ declaration.name ∧ TmScope.Above floor rest

def FVarsBelow (floor : Nat) (expression : Nucleus.HolE.Expr Sig types sort depth) : Prop :=
  ∀ name, name ∈ Nucleus.HolE.fvarIndices expression → name < floor

theorem FVarsBelow.mono (below : FVarsBelow floor expression)
    (subset : Nucleus.HolE.fvarIndices child ⊆ Nucleus.HolE.fvarIndices expression) :
    FVarsBelow floor child := by
  intro name membership
  exact below name (subset membership)

theorem lookupTm_none_of_lt (above : TmScope.Above floor scope)
    (small : wanted.name < floor) : lookupTm wanted scope = none := by
  induction scope with
  | nil => rfl
  | cons current rest ih =>
      rcases above with ⟨currentAbove, restAbove⟩
      have different : wanted ≠ current := by
        intro equality
        have namesEqual := congrArg Decl.name equality
        omega
      simp [lookupTm, different, ih restAbove]

theorem emptyTyNames_valid : TyNames.Valid .nil emptyTyNames := by
  intro kind item
  exact nomatch item

theorem emptyTyNames_below (next : Nat) : TyNames.Below next emptyTyNames := by
  intro kind item
  exact nomatch item

theorem emptyTmNames_valid : TmNames.Valid (.nil : TmScope Sig 0) emptyTmNames := by
  intro item
  exact Fin.elim0 item

theorem emptyTmNames_below (next : Nat) : TmNames.Below next (emptyTmNames (Sig := Sig)) := by
  intro item
  exact Fin.elim0 item

theorem emptyTmScope_above (floor : Nat) :
    TmScope.Above floor (.nil : TmScope Sig 0) := trivial

@[simp] theorem lookupTy_head (name : Nat) (kind : Kind) (scope : TyScope types) :
    lookupTy ⟨name, kind⟩ (.cons (kind := kind) name scope) = some .zero := by
  simp [lookupTy]

theorem lookupTy_cons_of_name_ne {wanted : TyDecl} {current : TyDecl}
    (different : wanted.name ≠ current.name) :
    lookupTy wanted (.cons (kind := current.sort) current.name scope) =
      (lookupTy wanted scope).map Nucleus.HolE.TyVar.succ := by
  simp [lookupTy, different]

@[simp] theorem lookupTm_head (declaration : TmDecl Sig) (scope : TmScope Sig depth) :
    lookupTm declaration (.cons declaration scope) = some 0 := by
  simp [lookupTm]

theorem lookupTm_cons_of_name_ne {wanted current : TmDecl Sig}
    (different : wanted.name ≠ current.name) :
    lookupTm wanted (.cons current scope) = (lookupTm wanted scope).map Fin.succ := by
  have declarationsDifferent : wanted ≠ current := by
    intro equality
    exact different (congrArg Decl.name equality)
  simp [lookupTm, declarationsDifferent]

theorem extendTyNames_valid (valid : TyNames.Valid scope names)
    (below : TyNames.Below next names) :
    TyNames.Valid (.cons (kind := domain) next scope) (extendTyNames next names) := by
  intro kind item
  cases item with
  | zero => exact lookupTy_head next domain scope
  | succ item =>
      change lookupTy ⟨names item, kind⟩ (.cons (kind := domain) next scope) =
        some (.succ item)
      rw [lookupTy_cons_of_name_ne (current := ⟨next, domain⟩)]
      · rw [valid item]
        rfl
      · exact Nat.ne_of_lt (below item)

theorem extendTyNames_below (below : TyNames.Below next names) :
    TyNames.Below (next + 1) (extendTyNames (kind := kind) next names) := by
  intro itemKind item
  cases item with
  | zero =>
      change next < next + 1
      omega
  | succ item => exact Nat.lt_succ_of_lt (below item)

theorem extendTmNames_valid {Sig : Signature} {depth : Nat} {scope : TmScope Sig depth}
    {names : TmNames Sig depth} (valid : TmNames.Valid scope names)
    (below : TmNames.Below next names) (declaration : TmDecl Sig)
    (declarationName : declaration.name = next) :
    TmNames.Valid (.cons declaration scope) (extendTmNames declaration names) := by
  intro item
  refine Fin.cases ?_ (fun old => ?_) item
  · exact lookupTm_head declaration scope
  · rw [lookupTm_cons_of_name_ne]
    · have nameAt : extendTmNames declaration names old.succ = names old := rfl
      rw [nameAt, valid old]
      rfl
    · rw [declarationName]
      exact Nat.ne_of_lt (below old)

theorem extendTmNames_below {Sig : Signature} {depth : Nat}
    {names : TmNames Sig depth} (below : TmNames.Below next names)
    (declaration : TmDecl Sig) (declarationName : declaration.name = next) :
    TmNames.Below (next + 1) (extendTmNames declaration names) := by
  intro item
  refine Fin.cases ?_ (fun old => ?_) item
  · simp [extendTmNames, declarationName]
  · exact Nat.lt_succ_of_lt (below old)

theorem TmScope.Above.cons {Sig : Signature} {depth floor : Nat}
    {scope : TmScope Sig depth} (above : TmScope.Above floor scope)
    (declaration : TmDecl Sig) (declarationAbove : floor ≤ declaration.name) :
    TmScope.Above floor (.cons declaration scope) :=
  ⟨declarationAbove, above⟩

private def rank : Nucleus.HolE.Expr Sig types sort depth → Nat
  | .boolTy | .tyBv _ | .primFam _ | .primTm _ | .bv _ | .bool _ => 1
  | .arr A B | .tyApp A B | .app A B => rank A + rank B + 1
  | .tyLam body | .tyExists body | .tyForall body | .model body => rank body + 1
  | .sub A predicate | .lam A predicate | .eps A predicate =>
      rank A + rank predicate + 1
  | .fv _ A => rank A + 1
  | .eq A left right | .abs A left right | .rep A left right =>
      rank A + rank left + rank right + 1

mutual
/-- Lowering after quotation is the identity on type families. -/
theorem lowerFam_quote (floor next : Nat) (floorNext : floor ≤ next)
    (typeScope : TyScope types) (typeNames : TyNames types)
    (tyValid : TyNames.Valid typeScope typeNames)
    (tyBelow : TyNames.Below next typeNames)
    (family : Nucleus.HolE.Fam Sig types kind)
    (freeBelow : FVarsBelow floor family) :
    lowerFam typeScope (quote next typeNames emptyTmNames family) = some family :=
  match family with
  | .boolTy => by simp [quote, lowerFam]
  | .arr A B => by
      have freeA : FVarsBelow floor A := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freeB : FVarsBelow floor B := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      simp only [quote, lowerFam]
      rw [lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow A freeA,
        lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow B freeB]
      rfl
  | .tyApp F A => by
      have freeF : FVarsBelow floor F := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freeA : FVarsBelow floor A := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      simp only [quote, lowerFam]
      rw [lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow F freeF,
        lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow A freeA]
      rfl
  | .tyLam body => by
      have bodyFree : FVarsBelow floor body := by
        intro name membership
        apply freeBelow name
        simpa [Nucleus.HolE.fvarIndices] using membership
      simp only [quote, lowerFam]
      rw [lowerFam_quote floor (next + 1) (by omega)
        (.cons next typeScope) (extendTyNames next typeNames)
        (extendTyNames_valid tyValid tyBelow) (extendTyNames_below tyBelow) body bodyFree]
      rfl
  | .tyBv item => by
      simp only [quote, lowerFam]
      rw [tyValid item]
      rfl
  | .sub A predicate => by
      have freeA : FVarsBelow floor A := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freePredicate : FVarsBelow floor predicate := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      let namedA := quote next typeNames emptyTmNames A
      let declaration : TmDecl Sig := ⟨next, namedA⟩
      have termValid : TmNames.Valid (.cons declaration .nil)
          (extendTmNames declaration emptyTmNames) :=
        extendTmNames_valid emptyTmNames_valid (emptyTmNames_below next) declaration rfl
      have termBelow : TmNames.Below (next + 1)
          (extendTmNames declaration emptyTmNames) :=
        extendTmNames_below (emptyTmNames_below next) declaration rfl
      have scopeAbove : TmScope.Above floor (.cons declaration (.nil : TmScope Sig 0)) :=
        (emptyTmScope_above floor).cons declaration floorNext
      simp only [quote, lowerFam]
      rw [lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow A freeA]
      rw [lowerTm_quote floor (next + 1) (by omega) typeScope typeNames tyValid
        (fun item => Nat.lt_succ_of_lt (tyBelow item)) (.cons declaration .nil)
        (extendTmNames declaration emptyTmNames) termValid termBelow scopeAbove
        predicate freePredicate]
      rfl
  | .model predicate => by
      have predicateFree : FVarsBelow floor predicate := by
        intro name membership
        apply freeBelow name
        simpa [Nucleus.HolE.fvarIndices] using membership
      simp only [quote, lowerFam]
      rw [lowerTm_quote floor (next + 1) (by omega)
        (.cons (kind := .star) next typeScope) (extendTyNames next typeNames)
        (extendTyNames_valid tyValid tyBelow) (extendTyNames_below tyBelow)
        .nil emptyTmNames emptyTmNames_valid (emptyTmNames_below (next + 1))
        (emptyTmScope_above floor) predicate predicateFree]
      rfl
  | .primFam symbol => by simp [quote, lowerFam]
termination_by rank family
decreasing_by all_goals (simp [rank] <;> omega)

/-- Lowering after quotation is the identity on terms. -/
theorem lowerTm_quote (floor next : Nat) (floorNext : floor ≤ next)
    (typeScope : TyScope types) (typeNames : TyNames types)
    (tyValid : TyNames.Valid typeScope typeNames)
    (tyBelow : TyNames.Below next typeNames)
    (termScope : TmScope Sig depth) (termNames : TmNames Sig depth)
    (tmValid : TmNames.Valid termScope termNames)
    (tmBelow : TmNames.Below next termNames)
    (scopeAbove : TmScope.Above floor termScope)
    (term : Nucleus.HolE.Tm Sig types depth)
    (freeBelow : FVarsBelow floor term) :
    lowerTm typeScope termScope (quote next typeNames termNames term) = some term :=
  match term with
  | .tyExists predicate => by
      have predicateFree : FVarsBelow floor predicate := by
        intro name membership
        apply freeBelow name
        simpa [Nucleus.HolE.fvarIndices] using membership
      simp only [quote, lowerTm]
      rw [lowerTm_quote floor (next + 1) (by omega)
        (.cons (kind := .star) next typeScope) (extendTyNames next typeNames)
        (extendTyNames_valid tyValid tyBelow) (extendTyNames_below tyBelow)
        .nil emptyTmNames emptyTmNames_valid (emptyTmNames_below (next + 1))
        (emptyTmScope_above floor) predicate predicateFree]
      rfl
  | .tyForall predicate => by
      have predicateFree : FVarsBelow floor predicate := by
        intro name membership
        apply freeBelow name
        simpa [Nucleus.HolE.fvarIndices] using membership
      simp only [quote, lowerTm]
      rw [lowerTm_quote floor (next + 1) (by omega)
        (.cons (kind := .star) next typeScope) (extendTyNames next typeNames)
        (extendTyNames_valid tyValid tyBelow) (extendTyNames_below tyBelow)
        .nil emptyTmNames emptyTmNames_valid (emptyTmNames_below (next + 1))
        (emptyTmScope_above floor) predicate predicateFree]
      rfl
  | .primTm symbol => by simp [quote, lowerTm]
  | .bv item => by
      simp only [quote, lowerTm]
      rw [tmValid item]
  | .fv name A => by
      have nameSmall : name < floor := by
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices]
      have freeA : FVarsBelow floor A := by
        intro inner membership
        apply freeBelow inner
        simp [Nucleus.HolE.fvarIndices, membership]
      simp only [quote, lowerTm]
      rw [lookupTm_none_of_lt scopeAbove nameSmall]
      rw [lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow A freeA]
      rfl
  | .app function argument => by
      have freeFunction : FVarsBelow floor function := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freeArgument : FVarsBelow floor argument := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      simp only [quote, lowerTm]
      rw [lowerTm_quote floor next floorNext typeScope typeNames tyValid tyBelow termScope
        termNames tmValid tmBelow scopeAbove function freeFunction]
      rw [lowerTm_quote floor next floorNext typeScope typeNames tyValid tyBelow termScope
        termNames tmValid tmBelow scopeAbove argument freeArgument]
      rfl
  | .lam A body => by
      have freeA : FVarsBelow floor A := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freeBody : FVarsBelow floor body := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      let namedA := quote next typeNames emptyTmNames A
      let declaration : TmDecl Sig := ⟨next, namedA⟩
      have extendedValid : TmNames.Valid (.cons declaration termScope)
          (extendTmNames declaration termNames) :=
        extendTmNames_valid tmValid tmBelow declaration rfl
      have extendedBelow : TmNames.Below (next + 1)
          (extendTmNames declaration termNames) :=
        extendTmNames_below tmBelow declaration rfl
      have extendedAbove : TmScope.Above floor (.cons declaration termScope) :=
        scopeAbove.cons declaration floorNext
      simp only [quote, lowerTm]
      rw [lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow A freeA]
      rw [lowerTm_quote floor (next + 1) (by omega) typeScope typeNames tyValid
        (fun item => Nat.lt_succ_of_lt (tyBelow item)) (.cons declaration termScope)
        (extendTmNames declaration termNames) extendedValid extendedBelow extendedAbove
        body freeBody]
      rfl
  | .bool value => by simp [quote, lowerTm]
  | .eq A left right => by
      have freeA : FVarsBelow floor A := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freeLeft : FVarsBelow floor left := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freeRight : FVarsBelow floor right := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      simp only [quote, lowerTm]
      rw [lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow A freeA,
        lowerTm_quote floor next floorNext typeScope typeNames tyValid tyBelow termScope
          termNames tmValid tmBelow scopeAbove left freeLeft,
        lowerTm_quote floor next floorNext typeScope typeNames tyValid tyBelow termScope
          termNames tmValid tmBelow scopeAbove right freeRight]
      rfl
  | .eps A predicate => by
      have freeA : FVarsBelow floor A := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freePredicate : FVarsBelow floor predicate := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      simp only [quote, lowerTm]
      rw [lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow A freeA,
        lowerTm_quote floor next floorNext typeScope typeNames tyValid tyBelow termScope
          termNames tmValid tmBelow scopeAbove predicate freePredicate]
      rfl
  | .abs A predicate value | .rep A predicate value => by
      have freeA : FVarsBelow floor A := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freePredicate : FVarsBelow floor predicate := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      have freeValue : FVarsBelow floor value := by
        intro name membership
        apply freeBelow name
        simp [Nucleus.HolE.fvarIndices, membership]
      let namedA := quote next typeNames emptyTmNames A
      let declaration : TmDecl Sig := ⟨next, namedA⟩
      have predicateValid : TmNames.Valid (.cons declaration .nil)
          (extendTmNames declaration emptyTmNames) :=
        extendTmNames_valid emptyTmNames_valid (emptyTmNames_below next) declaration rfl
      have predicateBelow : TmNames.Below (next + 1)
          (extendTmNames declaration emptyTmNames) :=
        extendTmNames_below (emptyTmNames_below next) declaration rfl
      have predicateAbove : TmScope.Above floor (.cons declaration (.nil : TmScope Sig 0)) :=
        (emptyTmScope_above floor).cons declaration floorNext
      simp only [quote, lowerTm]
      rw [lowerFam_quote floor next floorNext typeScope typeNames tyValid tyBelow A freeA]
      rw [lowerTm_quote floor (next + 1) (by omega) typeScope typeNames tyValid
        (fun item => Nat.lt_succ_of_lt (tyBelow item)) (.cons declaration .nil)
        (extendTmNames declaration emptyTmNames) predicateValid predicateBelow predicateAbove
        predicate freePredicate]
      rw [lowerTm_quote floor next floorNext typeScope typeNames tyValid tyBelow termScope
        termNames tmValid tmBelow scopeAbove value freeValue]
      rfl
termination_by rank term
decreasing_by all_goals (simp [rank] <;> omega)
end

/-- Quoting and then lowering a closed type family recovers the original family. -/
@[simp] theorem lowerFam_quoteClosed (family : Nucleus.HolE.Fam Sig [] kind) :
    lowerFam .nil (quoteClosed family) = some family := by
  apply lowerFam_quote (Nucleus.HolE.freshIndex family)
    (Nucleus.HolE.freshIndex family) le_rfl .nil emptyTyNames
    emptyTyNames_valid (emptyTyNames_below _) family
  intro name membership
  exact Nucleus.HolE.lt_freshIndex membership

/-- Quoting and then lowering a closed term recovers the original term. -/
@[simp] theorem lowerTm_quoteClosed (term : Nucleus.HolE.Tm Sig [] 0) :
    lowerTm .nil .nil (quoteClosed term) = some term := by
  apply lowerTm_quote (Nucleus.HolE.freshIndex term)
    (Nucleus.HolE.freshIndex term) le_rfl .nil emptyTyNames
    emptyTyNames_valid (emptyTyNames_below _) .nil emptyTmNames
    emptyTmNames_valid (emptyTmNames_below _) (emptyTmScope_above _) term
  intro name membership
  exact Nucleus.HolE.lt_freshIndex membership

/-- Closed, scope-resolving named type families. -/
abbrev ClosedFamExpr (Sig : Signature) (kind : Kind) :=
  ScopedExpr Sig (.nil : TyScope []) (.nil : TmScope Sig 0) (.kind kind)

/-- Closed, scope-resolving named terms. -/
abbrev ClosedTmExpr (Sig : Signature) :=
  ScopedExpr Sig (.nil : TyScope []) (.nil : TmScope Sig 0) .tm

/-- Alpha-equivalence classes of closed named type families. -/
abbrev ClosedFamQuotient (Sig : Signature) (kind : Kind) :=
  Quotient (inferInstance : Setoid (ClosedFamExpr Sig kind))

/-- Alpha-equivalence classes of closed named terms. -/
abbrev ClosedTmQuotient (Sig : Signature) :=
  Quotient (inferInstance : Setoid (ClosedTmExpr Sig))

noncomputable def quoteClosedFamScoped (family : Nucleus.HolE.Fam Sig [] kind) :
    ClosedFamExpr Sig kind where
  expression := quoteClosed family
  lowerable := ⟨family, lowerFam_quoteClosed family⟩

noncomputable def quoteClosedTmScoped (term : Nucleus.HolE.Tm Sig [] 0) :
    ClosedTmExpr Sig where
  expression := quoteClosed term
  lowerable := ⟨term, lowerTm_quoteClosed term⟩

noncomputable def ClosedFamQuotient.toLN :
    ClosedFamQuotient Sig kind → Nucleus.HolE.Fam Sig [] kind :=
  Quotient.lift (fun expression => expression.lowered)
    (fun _ _ equivalent => ScopedExpr.lowered_eq_of_alpha equivalent)

noncomputable def ClosedTmQuotient.toLN :
    ClosedTmQuotient Sig → Nucleus.HolE.Tm Sig [] 0 :=
  Quotient.lift (fun expression => expression.lowered)
    (fun _ _ equivalent => ScopedExpr.lowered_eq_of_alpha equivalent)

noncomputable def ClosedFamQuotient.ofLN
    (family : Nucleus.HolE.Fam Sig [] kind) : ClosedFamQuotient Sig kind :=
  Quotient.mk _ (quoteClosedFamScoped family)

noncomputable def ClosedTmQuotient.ofLN
    (term : Nucleus.HolE.Tm Sig [] 0) : ClosedTmQuotient Sig :=
  Quotient.mk _ (quoteClosedTmScoped term)

@[simp] theorem ClosedFamQuotient.toLN_ofLN
    (family : Nucleus.HolE.Fam Sig [] kind) :
    ClosedFamQuotient.toLN (ClosedFamQuotient.ofLN family) = family := by
  change (quoteClosedFamScoped family).lowered = family
  have lowered := (quoteClosedFamScoped family).lower_lowered
  change lowerFam .nil (quoteClosed family) =
    some (quoteClosedFamScoped family).lowered at lowered
  rw [lowerFam_quoteClosed family] at lowered
  exact (Option.some.inj lowered).symm

@[simp] theorem ClosedTmQuotient.toLN_ofLN (term : Nucleus.HolE.Tm Sig [] 0) :
    ClosedTmQuotient.toLN (ClosedTmQuotient.ofLN term) = term := by
  change (quoteClosedTmScoped term).lowered = term
  have lowered := (quoteClosedTmScoped term).lower_lowered
  change lowerTm .nil .nil (quoteClosed term) =
    some (quoteClosedTmScoped term).lowered at lowered
  rw [lowerTm_quoteClosed term] at lowered
  exact (Option.some.inj lowered).symm

theorem ClosedFamQuotient.ofLN_toLN (named : ClosedFamQuotient Sig kind) :
    ClosedFamQuotient.ofLN (ClosedFamQuotient.toLN named) = named := by
  refine Quotient.inductionOn named ?_
  intro expression
  apply Quotient.sound
  change Alpha .nil .nil (quoteClosed expression.lowered) expression.expression
  refine ⟨expression.lowered, ?_, expression.lower_lowered⟩
  exact lowerFam_quoteClosed expression.lowered

theorem ClosedTmQuotient.ofLN_toLN (named : ClosedTmQuotient Sig) :
    ClosedTmQuotient.ofLN (ClosedTmQuotient.toLN named) = named := by
  refine Quotient.inductionOn named ?_
  intro expression
  apply Quotient.sound
  change Alpha .nil .nil (quoteClosed expression.lowered) expression.expression
  refine ⟨expression.lowered, ?_, expression.lower_lowered⟩
  exact lowerTm_quoteClosed expression.lowered

/-- Closed named type families modulo alpha-equivalence are exactly locally
nameless type families. -/
noncomputable def closedFamEquiv :
    ClosedFamQuotient Sig kind ≃ Nucleus.HolE.Fam Sig [] kind where
  toFun := ClosedFamQuotient.toLN
  invFun := ClosedFamQuotient.ofLN
  left_inv := ClosedFamQuotient.ofLN_toLN
  right_inv := ClosedFamQuotient.toLN_ofLN

/-- Closed named terms modulo alpha-equivalence are exactly locally nameless
terms. -/
noncomputable def closedTmEquiv :
    ClosedTmQuotient Sig ≃ Nucleus.HolE.Tm Sig [] 0 where
  toFun := ClosedTmQuotient.toLN
  invFun := ClosedTmQuotient.ofLN
  left_inv := ClosedTmQuotient.ofLN_toLN
  right_inv := ClosedTmQuotient.toLN_ofLN

end Nucleus.HolE.Named
