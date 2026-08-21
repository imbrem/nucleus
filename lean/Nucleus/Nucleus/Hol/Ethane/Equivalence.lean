import Nucleus.Hol.Ethane.Conversion

/-!
# Named and locally nameless Ethane are equivalent

The locally nameless Ethane fragment is characterized extensionally as the
image of successful lowering.  Closed named syntax modulo alpha conversion is
equivalent to that image.  This formulation is independent of binder-name
selection and cannot accidentally include the old primitive subtype nodes.
-/

namespace Nucleus.Hol.Ethane

set_option relaxedAutoImplicit true

/-- A closed named Ethane expression whose binders resolve. -/
structure ClosedExpr (Sig : Signature) (sort : HolSort) where
  expression : Expr Sig Nat sort
  lowerable : Expr.Lowerable (.nil : TyScope []) (.nil : TmScope Sig 0) expression

namespace ClosedExpr

/-- The unique locally nameless value selected by successful lowering. -/
noncomputable def lowered (expression : ClosedExpr Sig sort) :
    Nucleus.HolE.Expr Sig [] sort (Nucleus.HolE.Named.scopeDepth sort 0) :=
  Classical.choose (show ∃ lowered,
    expression.expression.lower (.nil : TyScope []) (.nil : TmScope Sig 0) =
      some lowered from expression.lowerable)

@[simp] theorem lower_lowered (expression : ClosedExpr Sig sort) :
    expression.expression.lower (.nil : TyScope []) (.nil : TmScope Sig 0) =
      some expression.lowered :=
  Classical.choose_spec (show ∃ lowered,
    expression.expression.lower (.nil : TyScope []) (.nil : TmScope Sig 0) =
      some lowered from expression.lowerable)

instance : Setoid (ClosedExpr Sig sort) where
  r left right := left.expression.Alpha (.nil : TyScope []) (.nil : TmScope Sig 0)
    right.expression
  iseqv := ⟨
    fun expression => .refl expression.lowerable,
    Expr.Alpha.symm,
    Expr.Alpha.trans⟩

theorem lowered_eq_of_equivalent {left right : ClosedExpr Sig sort}
    (equivalent : left ≈ right) : left.lowered = right.lowered := by
  have equality := equivalent.lower_eq
  rw [left.lower_lowered, right.lower_lowered] at equality
  exact Option.some.inj equality

end ClosedExpr

/-- Closed named Ethane syntax modulo alpha conversion. -/
abbrev ClosedQuotient (Sig : Signature) (sort : HolSort) :=
  Quotient (inferInstance : Setoid (ClosedExpr Sig sort))

/-- The exact locally nameless image of closed Ethane syntax. -/
@[ext] structure ClosedImage (Sig : Signature) (sort : HolSort) where
  expression : Nucleus.HolE.Expr Sig [] sort (Nucleus.HolE.Named.scopeDepth sort 0)
  preimage : ∃ named : Expr Sig Nat sort,
    named.lower (.nil : TyScope []) (.nil : TmScope Sig 0) = some expression

namespace ClosedQuotient

noncomputable def toImage : ClosedQuotient Sig sort → ClosedImage Sig sort :=
  Quotient.lift
    (fun named => ⟨named.lowered, ⟨named.expression, named.lower_lowered⟩⟩)
    (fun left right equivalent => by
      apply ClosedImage.ext
      exact ClosedExpr.lowered_eq_of_equivalent equivalent)

noncomputable def ofImage (image : ClosedImage Sig sort) : ClosedQuotient Sig sort :=
  let named := Classical.choose image.preimage
  let lowering := Classical.choose_spec image.preimage
  Quotient.mk _ ({ expression := named, lowerable := ⟨image.expression, lowering⟩ } :
    ClosedExpr Sig sort)

@[simp] theorem toImage_ofImage (image : ClosedImage Sig sort) :
    toImage (ofImage image) = image := by
  apply ClosedImage.ext
  let selected : ClosedExpr Sig sort :=
    { expression := Classical.choose image.preimage
      lowerable := ⟨image.expression, Classical.choose_spec image.preimage⟩ }
  change selected.lowered = image.expression
  have chosen : selected.expression.lower (.nil : TyScope []) (.nil : TmScope Sig 0) =
      some image.expression := Classical.choose_spec image.preimage
  rw [selected.lower_lowered] at chosen
  exact Option.some.inj chosen

@[simp] theorem ofImage_toImage (named : ClosedQuotient Sig sort) :
    ofImage (toImage named) = named := by
  refine Quotient.inductionOn named ?_
  intro source
  apply Quotient.sound
  change Expr.Alpha (.nil : TyScope []) (.nil : TmScope Sig 0)
    (Classical.choose (toImage (Quotient.mk _ source)).preimage) source.expression
  refine ⟨source.lowered, ?_, source.lower_lowered⟩
  exact Classical.choose_spec (toImage (Quotient.mk _ source)).preimage

/-- The alpha quotient of closed named Ethane is exactly its locally nameless
image. -/
noncomputable def equivalence : ClosedQuotient Sig sort ≃ ClosedImage Sig sort where
  toFun := toImage
  invFun := ofImage
  left_inv := ofImage_toImage
  right_inv := toImage_ofImage

end ClosedQuotient

end Nucleus.Hol.Ethane
