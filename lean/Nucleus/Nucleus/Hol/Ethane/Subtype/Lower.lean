import Nucleus.Hol.Ethane.Subtype
import Nucleus.HolE.Named.Lower

/-!
# Lowering Ethane's derived logic

`Nucleus.Hol.Ethane.Expr`'s connectives and quantifiers are named macros;
`Nucleus.HolE.EmptyLogic`'s are the same macros over locally nameless syntax.
They are visibly the same encodings written twice, and this is where that stops
being a matter of reading them side by side.

Each lemma says: lowering the named macro produces the locally nameless one,
given that the operands lower.  Nothing here is specific to the subtype
package; the package's own lowering is built on top.

The binder-taking encodings lower their operands in an *extended* scope,
because they drop them under a binder.  That obligation is left to the caller
rather than discharged here.

## What this does not yet reach

The point of the layer is to lower the subtype package itself, so that
`Nucleus.HolE.Empty.SubtypePackage.Eval.existsType_true` transports to the
named construction the Rust kernel mirrors.  One lemma stands between here and
there, and it is not a small one:

```text
  lowering with a declaration inserted at position `k` produces
  `rename (skipping k)` of lowering without it
```

— weakening at a position, not just at the top.  The top-level form does not
induct: under a `lam` the scope grows on both sides and the inserted
declaration is no longer outermost, so the renaming becomes `liftRen` rather
than `Fin.succ`.  Both constructions genuinely need it, because both weaken
the caller's predicate explicitly as they drop it under the package's binders
(`Checked.lean` uses `weakenClosedTerm` for exactly this).

Until that lands, "the sentence the kernel builds is true" remains a theorem
about a parallel term plus a reading of two definitions side by side.  What is
established here is that the *derived logic* the two constructions are written
in agrees on the nose, which is the part that was most in doubt.
-/

namespace Nucleus.Hol.Ethane.Expr

open Nucleus.HolE.Named

set_option relaxedAutoImplicit true

variable {Sig : Signature} {types : List Kind} {depth : Nat}
  {typeScope : TyScope types} {termScope : TmScope Sig depth}

@[simp] theorem lower_falsehood :
    lowerTm typeScope termScope (falsehood (Sig := Sig) (Name := Nat)).toHolE
      = some (.bool false) := by
  simp [falsehood, toHolE, lowerTm]

@[simp] theorem lower_truth :
    lowerTm typeScope termScope (truth (Sig := Sig) (Name := Nat)).toHolE
      = some (.bool true) := by
  simp [truth, toHolE, lowerTm]

theorem lower_not {p : Tm Sig} {lowered}
    (hp : lowerTm typeScope termScope p.toHolE = some lowered) :
    lowerTm typeScope termScope (not p).toHolE
      = some (.eq .boolTy lowered (.bool false)) := by
  simp [not, falsehood, toHolE, lowerTm, lowerFam, hp]

theorem lower_forallTm {name : Nat} {A : Ty Sig} {body : Tm Sig} {lA lbody}
    (hA : lowerFam typeScope A.toHolE = some lA)
    (hbody : lowerTm typeScope (.cons ⟨name, A.toHolE⟩ termScope) body.toHolE = some lbody) :
    lowerTm typeScope termScope (forallTm name A body).toHolE
      = some (.eq (.arr lA .boolTy) (.lam lA lbody) (.lam lA (.bool true))) := by
  simp [forallTm, truth, toHolE, lowerTm, lowerFam, hA, hbody]

theorem lower_existsTm {name : Nat} {A : Ty Sig} {body : Tm Sig} {lA lbody}
    (hA : lowerFam typeScope A.toHolE = some lA)
    (hbody : lowerTm typeScope (.cons ⟨name, A.toHolE⟩ termScope) body.toHolE = some lbody) :
    lowerTm typeScope termScope (existsTm name A body).toHolE
      = some (.app (.lam lA lbody) (.eps lA (.lam lA lbody))) := by
  simp [existsTm, toHolE, lowerTm, hA, hbody]

/-- The named type of the function variable the conjunction encoding binds. -/
abbrev conjunctionTy : Nucleus.HolE.Named.Ty Sig :=
  .arr .boolTy (.arr .boolTy .boolTy)

/-- Its locally nameless image. -/
abbrev loweredConjunctionTy : Nucleus.HolE.Fam Sig types .star :=
  .arr .boolTy (.arr .boolTy .boolTy)

theorem lower_and {functionName : Nat} {left right : Tm Sig} {lleft lright}
    (hleft : lowerTm typeScope (.cons ⟨functionName, conjunctionTy⟩ termScope)
      left.toHolE = some lleft)
    (hright : lowerTm typeScope (.cons ⟨functionName, conjunctionTy⟩ termScope)
      right.toHolE = some lright) :
    lowerTm typeScope termScope (and functionName left right).toHolE
      = some (.eq (.arr loweredConjunctionTy .boolTy)
          (.lam loweredConjunctionTy (.app (.app (.bv 0) lleft) lright))
          (.lam loweredConjunctionTy
            (.app (.app (.bv 0) (.bool true)) (.bool true)))) := by
  simp [and, truth, toHolE, lowerTm, lowerFam, lookupTm, hleft, hright]

theorem lower_or {functionName : Nat} {left right : Tm Sig} {lleft lright}
    (hleft : lowerTm typeScope (.cons ⟨functionName, conjunctionTy⟩ termScope)
      left.toHolE = some lleft)
    (hright : lowerTm typeScope (.cons ⟨functionName, conjunctionTy⟩ termScope)
      right.toHolE = some lright) :
    lowerTm typeScope termScope (or functionName left right).toHolE
      = some (.eq .boolTy
          (.eq (.arr loweredConjunctionTy .boolTy)
            (.lam loweredConjunctionTy
              (.app (.app (.bv 0) (.eq .boolTy lleft (.bool false)))
                (.eq .boolTy lright (.bool false))))
            (.lam loweredConjunctionTy
              (.app (.app (.bv 0) (.bool true)) (.bool true))))
          (.bool false)) := by
  simpa [or] using lower_not (lower_and (lower_not hleft) (lower_not hright))

theorem lower_imp {functionName : Nat} {left right : Tm Sig} {lleft lright}
    (hleft : lowerTm typeScope (.cons ⟨functionName, conjunctionTy⟩ termScope)
      left.toHolE = some lleft)
    (hright : lowerTm typeScope (.cons ⟨functionName, conjunctionTy⟩ termScope)
      right.toHolE = some lright) :
    lowerTm typeScope termScope (imp functionName left right).toHolE
      = some (.eq .boolTy
          (.eq (.arr loweredConjunctionTy .boolTy)
            (.lam loweredConjunctionTy
              (.app (.app (.bv 0) lleft) (.eq .boolTy lright (.bool false))))
            (.lam loweredConjunctionTy
              (.app (.app (.bv 0) (.bool true)) (.bool true))))
          (.bool false)) := by
  simpa [imp] using lower_not (lower_and hleft (lower_not hright))

end Nucleus.Hol.Ethane.Expr
