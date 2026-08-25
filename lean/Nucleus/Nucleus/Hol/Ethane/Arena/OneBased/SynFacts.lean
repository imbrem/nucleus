import Nucleus.Hol.Ethane.Arena.OneBased.Rules

/-!
# Checked syntactic facts for one-based Ethane arenas

This file is the proof-theoretic model of Rust's `SynFact` cache.  The cache is
not a second equality oracle.  Each occupied slot contains a small LCF object
whose denotation is checked against resolved, named Ethane syntax; free slots
contain only allocator links.

The three relations are nested: literal syntax refines named alpha, which
refines the existing alpha-beta-eta conversion judgment.  A fact with neither
`var` nor `val` is direct; one with both is a concrete capture-avoiding
substitution. With `var` present and `val` absent, a fact quantifies over every
well-formed, classifier-compatible replacement. `val` without `var` remains
reserved.

`Model` remains opaque to conversion.  Alpha-renaming its implicit binder is
available through named alpha, but the local conversion-congruence interface
below has no constructor beneath `model`.
-/

namespace Nucleus.Hol.Ethane.OneBased

open Nucleus
set_option relaxedAutoImplicit true

namespace SynFact

def Direct (fact : SynFact) : Prop := fact.var = none ∧ fact.val = none

def Active (fact : SynFact) : Prop := ∃ subVar value,
  fact.var = some subVar ∧ fact.val = some value

/-- A universal substitution fact leaves `val` absent: it holds for every
well-formed replacement compatible with `var`. -/
def Universal (fact : SynFact) : Prop := ∃ subVar,
  fact.var = some subVar ∧ fact.val = none

/-- The checked API accepts a direct fact, a universal substitution, or a
concrete substitution.  `var = none, val = some _` remains reserved. -/
def EndpointsValid (fact : SynFact) : Prop :=
  fact.Direct ∨ fact.Universal ∨ fact.Active

theorem endpointsValid_iff (fact : SynFact) : fact.EndpointsValid ↔
    (fact.var = none ∧ fact.val = none) ∨
      (∃ subVar, fact.var = some subVar ∧ fact.val = none) ∨
      ∃ subVar value, fact.var = some subVar ∧ fact.val = some value :=
  Iff.rfl

theorem not_endpointsValid_val_only {rel : SynRel} {value input output : Ref} :
    ¬ EndpointsValid { rel, var := none, val := some value, input, output } := by
  simp [EndpointsValid, Direct, Universal, Active]

end SynFact

namespace detail.Expr

/-- Imported proxies are not closed syntax.  Until a separate closedness fact
exists, active substitution cannot inspect or cross one. -/
def IsProxy : detail.Expr → Prop
  | .tmRef .. | .tyRef .. | .kindRef .. => True
  | _ => False

/-- Root shapes considered by Rust `syn_sub_leaf`. A free-variable caller must
also establish that its category/name differs from the target; a `tmFv` caller
must additionally prove that the target does not occur in its type child. -/
def ActiveSubstitutionLeaf : detail.Expr → Prop
  | .kindStar | .boolTy | .bool _ | .tyFv .. | .tmFv .. => True
  | _ => False

/-- Roots accepted by active generic congruence.  Binders have dedicated
rules, and proxies are conservatively opaque. -/
def ActiveCongruenceRoot : detail.Expr → Prop
  | .tyLam .. | .lam .. | .tyExists .. | .model .. => False
  | .tmRef .. | .tyRef .. | .kindRef .. => False
  | _ => True

/-- The raw freshness scanner may descend only through local rows.  Encountering
a proxy is conservatively reported as possible occurrence by Rust. -/
def FreshnessInspectable (expression : detail.Expr) : Prop := ¬ expression.IsProxy

@[simp] theorem tmRef_not_active_leaf (source : ImportId) (foreign : Ref) :
    ¬ ActiveSubstitutionLeaf (.tmRef source foreign) := by simp [ActiveSubstitutionLeaf]

@[simp] theorem tyRef_not_active_leaf (source : ImportId) (foreign : Ref) :
    ¬ ActiveSubstitutionLeaf (.tyRef source foreign) := by simp [ActiveSubstitutionLeaf]

@[simp] theorem kindRef_not_active_leaf (source : ImportId) (foreign : Ref) :
    ¬ ActiveSubstitutionLeaf (.kindRef source foreign) := by simp [ActiveSubstitutionLeaf]

@[simp] theorem proxy_not_active_congruence {expression : detail.Expr}
    (proxy : expression.IsProxy) : ¬ expression.ActiveCongruenceRoot := by
  cases expression <;> simp_all [IsProxy, ActiveCongruenceRoot]

@[simp] theorem proxy_not_freshnessInspectable {expression : detail.Expr}
    (proxy : expression.IsProxy) : ¬ expression.FreshnessInspectable := by
  simp [FreshnessInspectable, proxy]

end detail.Expr

/-! ## Semantic relations on resolved named values -/

namespace Value

/-- Compatibility of the separately advertised classifiers carried by
resolved values.  Term classifiers are compared by family conversion, not by
literal syntax; this is the semantic image of Rust's classifier union-find. -/
inductive Compatible : Value → Value → Prop where
  | kind (kind : Kind) : Compatible (.kind kind) (.kind kind)
  | family (kind : Kind) (left right : EmptyExpr (.kind kind)) :
      Compatible (.family kind left) (.family kind right)
  | term {leftType rightType : EmptyTy} {left right : EmptyTm}
      (conversion : Nonempty (Nucleus.HolE.Named.FamEq
        (.nil : TyScope []) leftType.toHolE rightType.toHolE)) :
      Compatible (.term leftType left) (.term rightType right)

theorem compatible_refl {value : Value} (wellFormed : value.WellFormed) :
    Compatible value value := by
  cases value with
  | kind kind => exact .kind kind
  | family kind expression => exact .family kind expression expression
  | term type expression =>
      rcases wellFormed with ⟨loweredExpression, loweredType,
        expressionLowering, typeLowering, typing⟩
      exact .term ⟨Nucleus.HolE.Named.FamEq.refl typeLowering⟩

theorem Compatible.symm {left right : Value} (compatible : Compatible left right) :
    Compatible right left := by
  cases compatible with
  | kind kind => exact .kind kind
  | family kind left right => exact .family kind right left
  | term conversion =>
      rcases conversion with ⟨conversion⟩
      exact .term ⟨conversion.symm⟩

/-- Compatible resolved values necessarily inhabit the same syntax category. -/
theorem Compatible.tagSort_eq {left right : Value}
    (compatible : Compatible left right) : left.tagSort = right.tagSort := by
  cases compatible <;> rfl

theorem Compatible.trans {left middle right : Value}
    (leftMiddle : Compatible left middle)
    (middleWellFormed : middle.WellFormed)
    (middleRight : Compatible middle right) : Compatible left right := by
  cases leftMiddle with
  | kind kind => cases middleRight; exact .kind kind
  | family kind left middle =>
      cases middleRight
      exact .family kind left _
  | term leftConversion =>
      cases middleRight with
      | term rightConversion =>
          rcases leftConversion with ⟨leftConversion⟩
          rcases rightConversion with ⟨rightConversion⟩
          rcases middleWellFormed with
            ⟨loweredMiddle, loweredMiddleType, middleLowering,
              middleTypeLowering, middleTyping⟩
          change Nucleus.HolE.Named.lowerFam (.nil : TyScope []) _ =
            some loweredMiddleType at middleTypeLowering
          rw [leftConversion.rightLowering] at middleTypeLowering
          have same := Option.some.inj middleTypeLowering
          subst loweredMiddleType
          exact .term ⟨leftConversion.trans middleTyping.typeKinded rightConversion⟩

/-- Literal named syntax, deliberately ignoring the advertised classifier of
a term value.  Classifier compatibility is carried separately by `Valid`. -/
inductive SyntaxEqual : Value → Value → Prop where
  | kind (kind : Kind) : SyntaxEqual (.kind kind) (.kind kind)
  | family {kind : Kind} (expression : EmptyExpr (.kind kind)) :
      SyntaxEqual (.family kind expression) (.family kind expression)
  | term {leftType rightType : EmptyTy} (expression : EmptyTm) :
      SyntaxEqual (.term leftType expression) (.term rightType expression)

theorem syntaxEqual_refl (value : Value) : SyntaxEqual value value := by
  cases value with
  | kind kind => exact .kind kind
  | family kind expression => exact .family expression
  | term type expression => exact .term expression

theorem SyntaxEqual.symm {left right : Value} (equal : SyntaxEqual left right) :
    SyntaxEqual right left := by
  cases equal with
  | kind kind => exact .kind kind
  | family expression => exact .family expression
  | term expression => exact .term expression

theorem SyntaxEqual.trans {left middle right : Value}
    (leftMiddle : SyntaxEqual left middle)
    (middleRight : SyntaxEqual middle right) : SyntaxEqual left right := by
  cases leftMiddle with
  | kind kind => cases middleRight; exact .kind kind
  | family expression => cases middleRight; exact .family expression
  | term expression => cases middleRight; exact .term expression

/-- Named alpha equivalence compares syntax while leaving advertised term
classifiers to the separate compatibility judgment. -/
inductive Alpha : Value → Value → Prop where
  | kind (kind : Kind) : Alpha (.kind kind) (.kind kind)
  | family {kind : Kind} {left right : EmptyExpr (.kind kind)}
      (equivalent : Nucleus.Hol.Ethane.Expr.Alpha
        (.nil : TyScope []) (.nil : TmScope ArenaSig 0) left right) :
      Alpha (.family kind left) (.family kind right)
  | term {leftType rightType : EmptyTy} {left right : EmptyTm}
      (equivalent : Nucleus.Hol.Ethane.Expr.Alpha
        (.nil : TyScope []) (.nil : TmScope ArenaSig 0) left right) :
      Alpha (.term leftType left) (.term rightType right)

theorem alpha_refl {value : Value} (wellFormed : value.WellFormed) :
    Alpha value value := by
  cases value with
  | kind kind => exact .kind kind
  | family kind expression =>
      rcases wellFormed with ⟨lowered, _classification, lowering, _⟩
      exact .family ⟨lowered, lowering, lowering⟩
  | term type expression =>
      rcases wellFormed with ⟨lowered, _loweredType, lowering, _⟩
      change Nucleus.Hol.Ethane.Expr.lower (.nil : TyScope [])
        (.nil : TmScope ArenaSig 0) expression = some lowered at lowering
      exact .term ⟨lowered, lowering, lowering⟩

theorem SyntaxEqual.alpha {left right : Value} (equal : SyntaxEqual left right)
    (leftWellFormed : left.WellFormed) : Alpha left right := by
  cases equal with
  | kind kind => exact .kind kind
  | family expression =>
      rcases leftWellFormed with ⟨lowered, _classification, lowering, _⟩
      exact .family ⟨lowered, lowering, lowering⟩
  | term expression =>
      rcases leftWellFormed with ⟨lowered, _type, lowering, _⟩
      change Nucleus.Hol.Ethane.Expr.lower (.nil : TyScope [])
        (.nil : TmScope ArenaSig 0) expression = some lowered at lowering
      exact .term ⟨lowered, lowering, lowering⟩

theorem Alpha.symm {left right : Value} (equivalent : Alpha left right) :
    Alpha right left := by
  cases equivalent with
  | kind kind => exact .kind kind
  | family equivalent => exact .family equivalent.symm
  | term equivalent => exact .term equivalent.symm

theorem Alpha.trans {left middle right : Value}
    (leftMiddle : Alpha left middle) (middleRight : Alpha middle right) :
    Alpha left right := by
  cases leftMiddle with
  | kind kind => cases middleRight; exact .kind kind
  | family leftMiddle =>
      cases middleRight with
      | family middleRight => exact .family (leftMiddle.trans middleRight)
  | term leftMiddle =>
      cases middleRight with
      | term middleRight => exact .term (leftMiddle.trans middleRight)

/-- Named alpha is a sound fragment of the existing Ethane conversion. -/
theorem Alpha.equal {left right : Value} (equivalent : Alpha left right)
    (compatible : Compatible left right)
    (leftWellFormed : left.WellFormed) (rightWellFormed : right.WellFormed) :
    Equal left right := by
  cases equivalent with
  | kind kind => exact .kind kind
  | family equivalent => exact equal_family_alpha equivalent
  | term equivalent =>
      cases compatible with
      | term classifierConversion =>
          rcases equivalent with ⟨lowered, leftLowering, rightLowering⟩
          rcases classifierConversion with ⟨classifierConversion⟩
          rcases leftWellFormed with
            ⟨typedLowered, loweredType, leftTyping, typeLowering, typing⟩
          change Nucleus.Hol.Ethane.Expr.lower (.nil : TyScope [])
            (.nil : TmScope ArenaSig 0) _ = some typedLowered at leftTyping
          rw [leftLowering] at leftTyping
          have same := Option.some.inj leftTyping
          subst typedLowered
          exact .term ⟨lowered, loweredType, leftLowering,
              typeLowering, typing⟩ rightWellFormed ⟨classifierConversion⟩
            ⟨Nucleus.Hol.Ethane.Reference.EqTm.complete
              leftLowering rightLowering typeLowering (.refl typing)⟩

end Value

namespace SynRel

/-- Denotation of the three cached relations. -/
def Holds : SynRel → Value → Value → Prop
  | .syn, left, right => Value.SyntaxEqual left right
  | .alpha, left, right => Value.Alpha left right
  | .conv, left, right => Value.Equal left right

theorem holds_refl (wellFormed : value.WellFormed) :
    Holds relation value value := by
  cases relation with
  | syn => exact Value.syntaxEqual_refl value
  | alpha => exact Value.alpha_refl wellFormed
  | conv => exact Value.equal_self wellFormed

theorem Holds.symm (related : Holds relation left right) :
    Holds relation right left := by
  cases relation with
  | syn => exact Value.SyntaxEqual.symm related
  | alpha => exact Value.Alpha.symm related
  | conv => exact Value.Equal.symm related

theorem Holds.trans (leftMiddle : Holds relation left middle)
    (middleWellFormed : middle.WellFormed)
    (middleRight : Holds relation middle right) : Holds relation left right := by
  cases relation with
  | syn => exact Value.SyntaxEqual.trans leftMiddle middleRight
  | alpha => exact Value.Alpha.trans leftMiddle middleRight
  | conv => exact Value.Equal.trans leftMiddle middleWellFormed middleRight

/-- Semantic weakening along `syn ≤ alpha ≤ conv`. -/
theorem Holds.refine (refinement : source.Refines target)
    (compatible : Value.Compatible left right)
    (leftWellFormed : left.WellFormed) (rightWellFormed : right.WellFormed)
    (related : Holds source left right) : Holds target left right := by
  cases source <;> cases target
  all_goals simp [Refines, rank] at refinement
  case syn.syn => exact related
  case syn.alpha => exact related.alpha leftWellFormed
  case syn.conv =>
    exact (related.alpha leftWellFormed).equal compatible
      leftWellFormed rightWellFormed
  case alpha.alpha => exact related
  case alpha.conv => exact related.equal compatible leftWellFormed rightWellFormed
  case conv.conv => exact related

end SynRel

/-! ## Substitution and local LCF rules -/

namespace Value

namespace NamedSubstitution

/-- Immediate named-syntax children.  Constructor parameters (kinds, names,
booleans, and primitive symbols) are payload, not children. -/
def children : EmptySyn → List EmptySyn
  | .boolTy | .tyFv .. | .primFam .. | .primTm .. | .bool _ => []
  | .arr left right | .app left right => [left, right]
  | .tyApp _ _ function argument => [function, argument]
  | .tyLam _ _ _ body => [body]
  | .tyExists _ body | .model _ body => [body]
  | .tmFv _ type => [type]
  | .lam _ domain body => [domain, body]
  | .eq type left right => [type, left, right]
  | .eps type predicate => [type, predicate]

/-- Occurrence in raw named syntax.  Binder-aware freshness below asks about
the replacement, where every occurrence is free relative to the binder being
crossed. -/
inductive Occurs (needle : EmptySyn) : EmptySyn → Prop where
  | root : Occurs needle needle
  | child {parent child : EmptySyn} : child ∈ children parent →
      Occurs needle child → Occurs needle parent

def Fresh (binder replacement : EmptySyn) : Prop := ¬ Occurs binder replacement

def IsTyVariable : EmptySyn → Prop
  | .tyFv .. => True
  | _ => False

def IsTmVariable : EmptySyn → Prop
  | .tmFv .. => True
  | _ => False

/-- Rust deliberately treats two variable rows with the same category and
name as ambiguous at the generic congruence boundary, even when their
classifier references differ. -/
def SameVariableName : EmptySyn → EmptySyn → Prop
  | .tyFv left _, .tyFv right _ => left = right
  | .tmFv left _, .tmFv right _ => left = right
  | _, _ => False

/-- Equal non-binding constructor payload.  Children are related separately.
There is intentionally no case for `tyLam`, `lam`, `tyExists`, or `model`. -/
inductive SameHead : EmptySyn → EmptySyn → Prop where
  | boolTy : SameHead .boolTy .boolTy
  | arr : SameHead (.arr left right) (.arr left' right')
  | tyApp : SameHead (.tyApp domain codomain function argument)
      (.tyApp domain codomain function' argument')
  | tyFv {kind : Kind} : SameHead (.tyFv name kind) (.tyFv name kind)
  | primFam {kind : Kind} : SameHead (.primFam kind symbol) (.primFam kind symbol)
  | primTm : SameHead (.primTm symbol) (.primTm symbol)
  | tmFv : SameHead (.tmFv name type) (.tmFv name type')
  | app : SameHead (.app function argument) (.app function' argument')
  | bool : SameHead (.bool value) (.bool value)
  | eq : SameHead (.eq type left right) (.eq type' left' right')
  | eps : SameHead (.eps type predicate) (.eps type' predicate')

end NamedSubstitution

/-- Capture-avoiding substitution on named Ethane syntax, presented as the
local derivation grammar checked by Rust.

The ordinary congruence case covers leaves as an empty child list.  Binding
constructors are separate so shadowing and freshness cannot be forgotten.
`Model` has substitution and alpha behavior, but its conversion-congruence
restriction is imposed by `Congruence` below. -/
inductive NamedSubstitution (needle replacement : EmptySyn) :
    EmptySyn → EmptySyn → Prop where
  | hit : NamedSubstitution needle replacement needle replacement
  | miss (absent : ¬ NamedSubstitution.Occurs needle input) :
      NamedSubstitution needle replacement input input
  | congr (different : ¬ NamedSubstitution.SameVariableName needle input)
      (head : NamedSubstitution.SameHead input output)
      (children : List.Forall₂ (NamedSubstitution needle replacement)
        (NamedSubstitution.children input) (NamedSubstitution.children output)) :
      NamedSubstitution needle replacement input output
  | tyLamShadow {domain codomain name body}
      (shadowed : needle = .tyFv name domain) :
      NamedSubstitution needle replacement
        (.tyLam domain codomain name body) (.tyLam domain codomain name body)
  | tyLamCongr {domain codomain name body body'}
      (notShadowed : needle ≠ .tyFv name domain)
      (fresh : NamedSubstitution.Fresh (.tyFv name domain) replacement)
      (bodyStep : NamedSubstitution needle replacement body body') :
      NamedSubstitution needle replacement
        (.tyLam domain codomain name body) (.tyLam domain codomain name body')
  | lamTmShadow {name domain body}
      (shadowed : needle = .tmFv name domain) :
      NamedSubstitution needle replacement
        (.lam name domain body) (.lam name domain body)
  | lamTmCongr {name domain body body'}
      (termNeedle : NamedSubstitution.IsTmVariable needle)
      (notShadowed : needle ≠ .tmFv name domain)
      (fresh : NamedSubstitution.Fresh (.tmFv name domain) replacement)
      (bodyStep : NamedSubstitution needle replacement body body') :
      NamedSubstitution needle replacement
        (.lam name domain body) (.lam name domain body')
  | lamTyCongr {name domain domain' body body'}
      (typeNeedle : NamedSubstitution.IsTyVariable needle)
      (domainStep : NamedSubstitution needle replacement domain domain')
      (bodyStep : NamedSubstitution needle replacement body body') :
      NamedSubstitution needle replacement
        (.lam name domain body) (.lam name domain' body')
  | tyExistsShadow {name body}
      (shadowed : needle = .tyFv name .star) :
      NamedSubstitution needle replacement
        (.tyExists name body) (.tyExists name body)
  | tyExistsTyCongr {name body body'}
      (typeNeedle : NamedSubstitution.IsTyVariable needle)
      (notShadowed : needle ≠ .tyFv name .star)
      (fresh : NamedSubstitution.Fresh (.tyFv name .star) replacement)
      (bodyStep : NamedSubstitution needle replacement body body') :
      NamedSubstitution needle replacement
        (.tyExists name body) (.tyExists name body')
  | tyExistsTmCongr {name body body'}
      (termNeedle : NamedSubstitution.IsTmVariable needle)
      (bodyStep : NamedSubstitution needle replacement body body') :
      NamedSubstitution needle replacement
        (.tyExists name body) (.tyExists name body')
  | modelShadow {name body}
      (shadowed : needle = .tyFv name .star) :
      NamedSubstitution needle replacement (.model name body) (.model name body)
  | modelTyCongr {name body body'}
      (typeNeedle : NamedSubstitution.IsTyVariable needle)
      (notShadowed : needle ≠ .tyFv name .star)
      (fresh : NamedSubstitution.Fresh (.tyFv name .star) replacement)
      (bodyStep : NamedSubstitution needle replacement body body') :
      NamedSubstitution needle replacement (.model name body) (.model name body')
  | modelTmCongr {name body body'}
      (termNeedle : NamedSubstitution.IsTmVariable needle)
      (bodyStep : NamedSubstitution needle replacement body body') :
      NamedSubstitution needle replacement (.model name body) (.model name body')

/-- The exact named-syntax criterion behind Rust
`require_substitution_leaf`. A term variable is a leaf only when the
substituted variable is absent from its type annotation; comparing the two
variable names alone is insufficient because `Model` embeds terms in types. -/
inductive NamedSubstitution.LeafInvariant (needle : EmptySyn) : EmptySyn → Prop where
  | boolTy : LeafInvariant needle .boolTy
  | bool (value : Bool) : LeafInvariant needle (.bool value)
  | tyFv {name : Nat} {kind : Kind}
      (different : ¬ SameVariableName needle (.tyFv name kind)) :
      LeafInvariant needle (.tyFv name kind)
  | tmFv {name : Nat} {type : EmptySyn}
      (different : ¬ SameVariableName needle (.tmFv name type))
      (annotationFree : ¬ Occurs needle type) :
      LeafInvariant needle (.tmFv name type)

/-- The leaf check supplies precisely the child derivation required by `tmFv`
congruence. -/
theorem NamedSubstitution.LeafInvariant.substitution
    (checked : LeafInvariant needle input) :
    NamedSubstitution needle replacement input input := by
  cases checked with
  | boolTy =>
      exact .congr (by simp [SameVariableName]) .boolTy (by simp [children])
  | bool value =>
      exact .congr (by simp [SameVariableName]) .bool (by simp [children])
  | tyFv different => exact .congr different .tyFv (by simp [children])
  | tmFv different annotationFree =>
      apply NamedSubstitution.congr different .tmFv
      exact .cons (.miss annotationFree) .nil

/-- Every checked term-variable leaf carries its annotation obligation. -/
theorem NamedSubstitution.LeafInvariant.tmFv_annotationFree
    (checked : LeafInvariant needle (.tmFv name type)) :
    ¬ Occurs needle type := by
  cases checked with
  | tmFv _ annotationFree => exact annotationFree

/-- The generic unchanged-leaf derivation used by both concrete and universal
Rust leaf rules. -/
theorem NamedSubstitution.leaf
    (different : ¬ NamedSubstitution.SameVariableName needle input)
    (head : NamedSubstitution.SameHead input input)
    (noChildren : NamedSubstitution.children input = []) :
    NamedSubstitution needle replacement input input := by
  refine NamedSubstitution.congr different head ?_
  simp [noChildren]

/-- Semantic result of the local capture-avoiding substitution checker.
Resolved kinds contain no named syntax and are unchanged; all other values
carry a concrete recursive named-syntax derivation. -/
inductive Substitutes (subVar replacement : Value) : Value → Value → Prop where
  | kind (kind : Kind) : Substitutes subVar replacement (.kind kind) (.kind kind)
  | syntax {input output : Value}
      {variableSyntax replacementSyntax inputSyntax outputSyntax : EmptySyn}
      (variableIsSyntax : subVar.syntax? = some variableSyntax)
      (replacementIsSyntax : replacement.syntax? = some replacementSyntax)
      (inputIsSyntax : input.syntax? = some inputSyntax)
      (outputIsSyntax : output.syntax? = some outputSyntax)
      (derivation : NamedSubstitution variableSyntax replacementSyntax inputSyntax outputSyntax) :
      Substitutes subVar replacement input output

/-- The variable case `[replacement / subVar] subVar = replacement`.
This is the primitive substitution LCF rule used by Rust `syn_sub_var`. -/
theorem Substitutes.varCase {subVar replacement : Value}
    {variableSyntax replacementSyntax : EmptySyn}
    (variableIsSyntax : subVar.syntax? = some variableSyntax)
    (replacementIsSyntax : replacement.syntax? = some replacementSyntax) :
    Substitutes subVar replacement subVar replacement :=
  .syntax variableIsSyntax replacementIsSyntax variableIsSyntax
    replacementIsSyntax .hit

/-- Denotation of one local direct or active-substitution judgment. -/
def LocalSynMeaning (relation : SynRel) (subVar replacement : Option Value)
    (input output : Value) : Prop :=
  match subVar, replacement with
  | none, none => Compatible input output ∧ SynRel.Holds relation input output
  | some subVar, none =>
      ∀ replacement, replacement.WellFormed → Compatible subVar replacement →
        ∃ substituted, Substitutes subVar replacement input substituted ∧
          substituted.WellFormed ∧ Compatible substituted output ∧
          SynRel.Holds relation substituted output
  | some subVar, some replacement =>
      ∃ substituted, Substitutes subVar replacement input substituted ∧
        substituted.WellFormed ∧ Compatible substituted output ∧
        SynRel.Holds relation substituted output
  | _, _ => False

/-- An observational, substitution-level formulation of `subVar` not being
free in `input`: every compatible well-formed replacement leaves the resolved
syntax unchanged.  Relating this predicate to the finite named `fvars` set
requires the usual no-name-confusion hypothesis because the Rust checker
conservatively rejects equal names with different classifiers. -/
def SubstitutionFree (subVar input : Value) : Prop :=
  ∀ replacement, replacement.WellFormed → Compatible subVar replacement →
    Substitutes subVar replacement input input

/-- Literal equality plus substitution-freeness is sufficient for the
universal `syn` fact.  This is the proved direction of the expected
`[·/x]a =_syn b` characterization; the converse needs substitution
determinism and the finite-FV/no-name-confusion bridge. -/
theorem universal_syn_of_literal_and_substitution_free
    (free : SubstitutionFree subVar input)
    (inputWellFormed : input.WellFormed)
    (compatible : Compatible input output)
    (literal : SyntaxEqual input output) :
    LocalSynMeaning .syn (some subVar) none input output := by
  intro replacement replacementWellFormed replacementCompatible
  exact ⟨input, free replacement replacementWellFormed replacementCompatible,
    inputWellFormed, compatible, literal⟩

/-- A checked structural congruence step.  `underModel` identifies the one
opaque family constructor; conversion congruence is forbidden there. -/
structure Congruence (relation : SynRel) (underModel : Bool)
    (subVar replacement : Option Value) (input output : Value) : Prop where
  semantic : LocalSynMeaning relation subVar replacement input output
  modelOpaque : underModel = true → relation ≠ .conv

theorem no_conversion_congruence_under_model
    (congruence : Congruence .conv true subVar replacement input output) : False := by
  exact congruence.modelOpaque rfl rfl

end Value

/-- Denotation of one local judgment before arena references are introduced. -/
def SynMeaning (relation : SynRel) (subVar replacement : Option Value)
    (input output : Value) : Prop :=
  Value.LocalSynMeaning relation subVar replacement input output

/-- Proof-relevant local rules from which checked cache entries are minted.
The beta and eta constructors consume the named rules already proved sound in
`Rules.lean`; congruence carries its structural substitution witness and the
explicit `Model` guard. -/
inductive SynInference : SynRel → Option Value → Option Value →
    Value → Value → Prop where
  | direct (compatible : Value.Compatible input output)
      (related : SynRel.Holds relation input output) :
      SynInference relation none none input output
  | substitution (substitutes : Value.Substitutes subVar replacement input substituted)
      (substitutedWellFormed : substituted.WellFormed)
      (compatible : Value.Compatible substituted output)
      (related : SynRel.Holds relation substituted output) :
      SynInference relation (some subVar) (some replacement) input output
  | universalSubstitution
      (substitutes : ∀ replacement, replacement.WellFormed →
        Value.Compatible subVar replacement →
        ∃ substituted, Value.Substitutes subVar replacement input substituted ∧
          substituted.WellFormed ∧ Value.Compatible substituted output ∧
          SynRel.Holds relation substituted output) :
      SynInference relation (some subVar) none input output
  | refine (source : SynInference finer subVar replacement input output)
      (refinement : finer.Refines relation)
      (inputWellFormed : input.WellFormed)
      (outputWellFormed : output.WellFormed) :
      SynInference relation subVar replacement input output
  | congr (rule : Value.Congruence relation underModel subVar replacement input output) :
      SynInference relation subVar replacement input output
  | familyBeta {kind : Kind} {source target : EmptyExpr (.kind kind)}
      (sourceWellFormed : Value.WellFormed (.family kind source))
      (targetWellFormed : Value.WellFormed (.family kind target))
      (step : Nucleus.HolE.Named.FamBeta
        (.nil : TyScope []) source.toHolE target.toHolE)
      (bodyKinded : Nucleus.HolE.Kinded step.body)
      (argumentKinded : Nucleus.HolE.Kinded step.argument) :
      SynInference .conv none none (.family kind source) (.family kind target)
  | termBeta {sourceType targetType : EmptyTy} {source target : EmptyTm}
      (sourceWellFormed : Value.WellFormed (.term sourceType source))
      (targetWellFormed : Value.WellFormed (.term targetType target))
      (compatible : Value.Compatible
        (.term sourceType source) (.term targetType target))
      (step : Nucleus.HolE.Named.TmBeta
        (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
        source.toHolE target.toHolE) :
      SynInference .conv none none
        (.term sourceType source) (.term targetType target)
  | termEta {sourceType targetType : EmptyTy} {source target : EmptyTm}
      (sourceWellFormed : Value.WellFormed (.term sourceType source))
      (targetWellFormed : Value.WellFormed (.term targetType target))
      (compatible : Value.Compatible
        (.term sourceType source) (.term targetType target))
      (step : Nucleus.HolE.Named.TmEta
        (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
        source.toHolE target.toHolE) :
      SynInference .conv none none
        (.term sourceType source) (.term targetType target)

namespace SynInference

/-- A semantic cache judgment remains true when its relation is weakened
along `syn ≤ alpha ≤ conv`.  This is the proposition-level contract of
Rust `Kernel::syn_refine`; unlike the proof-relevant constructor it does not
require retaining the inference that originally minted the fact. -/
theorem meaningRefine
    (source : SynMeaning finer subVar replacement input output)
    (refinement : finer.Refines relation)
    (inputWellFormed : input.WellFormed)
    (outputWellFormed : output.WellFormed) :
    SynMeaning relation subVar replacement input output := by
  unfold SynMeaning at source ⊢
  cases subVar <;> cases replacement
  · exact ⟨source.1, source.2.refine refinement source.1
      inputWellFormed outputWellFormed⟩
  · exact False.elim source
  · intro replacement replacementWellFormed compatibleReplacement
    rcases source replacement replacementWellFormed compatibleReplacement with
      ⟨substituted, substitutes, substitutedWellFormed, compatible, related⟩
    exact ⟨substituted, substitutes, substitutedWellFormed, compatible,
      related.refine refinement compatible substitutedWellFormed outputWellFormed⟩
  · rcases source with ⟨substituted, substitutes,
      substitutedWellFormed, compatible, related⟩
    exact ⟨substituted, substitutes, substitutedWellFormed, compatible,
      related.refine refinement compatible substitutedWellFormed outputWellFormed⟩

/-- Compose any direct, universal, or concrete-substitution judgment on the
left with a direct judgment on the right.  The substitution endpoints are
preserved; both input relations may be weakened to the result relation.  This
is the semantic rule implemented by Rust `Kernel::syn_trans`. -/
theorem SynMeaning.trans_direct
    (left : SynMeaning leftRelation subVar replacement input middle)
    (right : SynMeaning rightRelation none none middle output)
    (leftRefines : leftRelation.Refines relation)
    (rightRefines : rightRelation.Refines relation)
    (inputWellFormed : input.WellFormed)
    (middleWellFormed : middle.WellFormed)
    (outputWellFormed : output.WellFormed) :
    SynMeaning relation subVar replacement input output := by
  unfold SynMeaning Value.LocalSynMeaning at left right ⊢
  rcases right with ⟨middleOutputCompatible, middleOutputRelated⟩
  cases subVar <;> cases replacement
  · rcases left with ⟨inputMiddleCompatible, inputMiddleRelated⟩
    have inputOutputCompatible :=
      inputMiddleCompatible.trans middleWellFormed middleOutputCompatible
    exact ⟨inputOutputCompatible,
      (inputMiddleRelated.refine leftRefines inputMiddleCompatible
          inputWellFormed middleWellFormed).trans middleWellFormed
        (middleOutputRelated.refine rightRefines middleOutputCompatible
          middleWellFormed outputWellFormed)⟩
  · exact False.elim left
  · intro universalReplacement universalReplacementWellFormed
      universalReplacementCompatible
    rcases left universalReplacement universalReplacementWellFormed
      universalReplacementCompatible with
      ⟨substituted, substitutes, substitutedWellFormed,
        substitutedMiddleCompatible, substitutedMiddleRelated⟩
    have substitutedOutputCompatible :=
      substitutedMiddleCompatible.trans middleWellFormed middleOutputCompatible
    exact ⟨substituted, substitutes, substitutedWellFormed,
      substitutedOutputCompatible,
      (substitutedMiddleRelated.refine leftRefines substitutedMiddleCompatible
          substitutedWellFormed middleWellFormed).trans middleWellFormed
        (middleOutputRelated.refine rightRefines middleOutputCompatible
          middleWellFormed outputWellFormed)⟩
  · rcases left with ⟨substituted, substitutes, substitutedWellFormed,
        substitutedMiddleCompatible, substitutedMiddleRelated⟩
    have substitutedOutputCompatible :=
      substitutedMiddleCompatible.trans middleWellFormed middleOutputCompatible
    exact ⟨substituted, substitutes, substitutedWellFormed,
      substitutedOutputCompatible,
      (substitutedMiddleRelated.refine leftRefines substitutedMiddleCompatible
          substitutedWellFormed middleWellFormed).trans middleWellFormed
        (middleOutputRelated.refine rightRefines middleOutputCompatible
          middleWellFormed outputWellFormed)⟩

/-- Every local inference denotes its advertised direct or substitution
judgment.  This is the LCF soundness theorem used by the checked constructor. -/
theorem sound (inference : SynInference relation subVar replacement input output) :
    SynMeaning relation subVar replacement input output := by
  induction inference with
  | direct compatible related => exact ⟨compatible, related⟩
  | substitution substitutes substitutedWellFormed compatible related =>
      exact ⟨_, substitutes, substitutedWellFormed, compatible, related⟩
  | universalSubstitution substitutes => exact substitutes
  | refine source refinement inputWellFormed outputWellFormed sourceSound =>
      exact meaningRefine sourceSound refinement inputWellFormed outputWellFormed
  | congr rule => exact rule.semantic
  | familyBeta sourceWellFormed targetWellFormed step bodyKinded argumentKinded =>
      exact ⟨Value.Compatible.family _ _ _,
        Value.equal_family_beta step bodyKinded argumentKinded⟩
  | termBeta sourceWellFormed targetWellFormed compatible step =>
      cases compatible with
      | term classifierConversion =>
          exact ⟨Value.Compatible.term classifierConversion,
            Value.equal_term_beta sourceWellFormed targetWellFormed
              classifierConversion step⟩
  | termEta sourceWellFormed targetWellFormed compatible step =>
      cases compatible with
      | term classifierConversion =>
          exact ⟨Value.Compatible.term classifierConversion,
            Value.equal_term_eta sourceWellFormed targetWellFormed
              classifierConversion step⟩

/-- Proof-relevant form of `Kernel::syn_trans`: the left premise may carry a
universal or concrete substitution, while the right premise must be direct. -/
theorem transDirect
    (left : SynInference leftRelation subVar replacement input middle)
    (right : SynInference rightRelation none none middle output)
    (leftRefines : leftRelation.Refines relation)
    (rightRefines : rightRelation.Refines relation)
    (inputWellFormed : input.WellFormed)
    (middleWellFormed : middle.WellFormed)
    (outputWellFormed : output.WellFormed) :
    SynInference relation subVar replacement input output := by
  have meaning := SynMeaning.trans_direct left.sound right.sound leftRefines
    rightRefines inputWellFormed middleWellFormed outputWellFormed
  unfold SynMeaning Value.LocalSynMeaning at meaning
  cases subVar <;> cases replacement
  · exact .direct meaning.1 meaning.2
  · exact False.elim meaning
  · exact .universalSubstitution meaning
  · rcases meaning with ⟨substituted, substitutes, substitutedWellFormed,
      compatible, related⟩
    exact .substitution substitutes substitutedWellFormed compatible related

theorem refine_direct (source : SynRel.Holds finer input output)
    (refinement : finer.Refines relation)
    (compatible : Value.Compatible input output)
    (inputWellFormed : input.WellFormed) (outputWellFormed : output.WellFormed) :
    SynInference relation none none input output :=
  .direct compatible
    (source.refine refinement compatible inputWellFormed outputWellFormed)

/-- Proof-relevant form of the primitive Rust `syn_sub_var` rule. -/
theorem substitutionVariable
    (variableIsSyntax : subVar.syntax? = some variableSyntax)
    (replacementIsSyntax : replacement.syntax? = some replacementSyntax)
    (replacementWellFormed : replacement.WellFormed) :
    SynInference .syn (some subVar) (some replacement) subVar replacement :=
  .substitution
    (Value.Substitutes.varCase variableIsSyntax replacementIsSyntax)
    replacementWellFormed (Value.compatible_refl replacementWellFormed)
    (Value.syntaxEqual_refl replacement)

/-- A concrete substitution fact for a leaf or larger expression already
shown invariant by the named substitution calculus. -/
theorem substitutionUnchanged
    (substitutes : Value.Substitutes subVar replacement input input)
    (inputWellFormed : input.WellFormed) :
    SynInference .syn (some subVar) (some replacement) input input :=
  .substitution substitutes inputWellFormed
    (Value.compatible_refl inputWellFormed) (Value.syntaxEqual_refl input)

/-- Proof-relevant form shared by Rust `syn_sub_leaf_forall` and future
closed-import rules. -/
theorem universalSubstitutionUnchanged
    (free : Value.SubstitutionFree subVar input)
    (inputWellFormed : input.WellFormed) :
    SynInference .syn (some subVar) none input input :=
  .universalSubstitution
    (Value.universal_syn_of_literal_and_substitution_free free inputWellFormed
      (Value.compatible_refl inputWellFormed) (Value.syntaxEqual_refl input))

theorem familyBeta_sound {kind : Kind} {source target : EmptyExpr (.kind kind)}
    (_sourceWellFormed : Value.WellFormed (.family kind source))
    (_targetWellFormed : Value.WellFormed (.family kind target))
    (step : Nucleus.HolE.Named.FamBeta
      (.nil : TyScope []) source.toHolE target.toHolE)
    (bodyKinded : Nucleus.HolE.Kinded step.body)
    (argumentKinded : Nucleus.HolE.Kinded step.argument) :
    SynRel.Holds .conv (.family kind source) (.family kind target) :=
  Value.equal_family_beta step bodyKinded argumentKinded

theorem termBeta_sound {sourceType targetType : EmptyTy} {source target : EmptyTm}
    (sourceWellFormed : Value.WellFormed (.term sourceType source))
    (targetWellFormed : Value.WellFormed (.term targetType target))
    (classifierConversion : Nonempty (Nucleus.HolE.Named.FamEq
      (.nil : TyScope []) sourceType.toHolE targetType.toHolE))
    (step : Nucleus.HolE.Named.TmBeta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      source.toHolE target.toHolE) :
    SynRel.Holds .conv (.term sourceType source) (.term targetType target) :=
  Value.equal_term_beta sourceWellFormed targetWellFormed
    classifierConversion step

theorem termEta_sound {sourceType targetType : EmptyTy} {source target : EmptyTm}
    (sourceWellFormed : Value.WellFormed (.term sourceType source))
    (targetWellFormed : Value.WellFormed (.term targetType target))
    (classifierConversion : Nonempty (Nucleus.HolE.Named.FamEq
      (.nil : TyScope []) sourceType.toHolE targetType.toHolE))
    (step : Nucleus.HolE.Named.TmEta
      (.nil : TyScope []) (.nil : TmScope ArenaSig 0)
      source.toHolE target.toHolE) :
    SynRel.Holds .conv (.term sourceType source) (.term targetType target) :=
  Value.equal_term_eta sourceWellFormed targetWellFormed
    classifierConversion step

end SynInference

/-! ## Valid facts and the checked wrapper -/

namespace SynFact

/-- Semantic validity relative to the row arena and import resolver.

Endpoint classifier compatibility belongs to the direct branch of
`SynMeaning`.  An active type substitution may deliberately retype a term,
for example `[bool / α] (x : α) = (x : bool)`; its substituted value is checked
for compatibility with the advertised output inside `SynMeaning` instead. -/
def Valid (resolve : Resolver) (arena : Arena) (fact : SynFact) : Prop :=
  ∃ input output,
    Resolves resolve arena.withoutSyn fact.input input ∧
    Resolves resolve arena.withoutSyn fact.output output ∧
    input.WellFormed ∧ output.WellFormed ∧
    match fact.var, fact.val with
    | none, none => SynMeaning fact.rel none none input output
    | some variableRef, none =>
        ∃ subVar,
          Resolves resolve arena.withoutSyn variableRef subVar ∧
          subVar.WellFormed ∧
          SynMeaning fact.rel (some subVar) none input output
    | some variableRef, some replacementRef =>
        ∃ subVar replacement,
          Resolves resolve arena.withoutSyn variableRef subVar ∧
          Resolves resolve arena.withoutSyn replacementRef replacement ∧
          subVar.WellFormed ∧ replacement.WellFormed ∧
          SynMeaning fact.rel (some subVar) (some replacement) input output
    | _, _ => False

theorem Valid.endpointsValid (valid : SynFact.Valid resolve arena fact) :
    SynFact.EndpointsValid fact := by
  rcases valid with ⟨input, output, inputResolves, outputResolves,
    inputWellFormed, outputWellFormed, valid⟩
  cases varEq : fact.var <;> cases valEq : fact.val
  · exact Or.inl ⟨varEq, valEq⟩
  · simp [varEq, valEq] at valid
  · exact Or.inr (Or.inl ⟨_, varEq, valEq⟩)
  · exact Or.inr (Or.inr ⟨_, _, varEq, valEq⟩)

/-- A valid direct cache fact always proves semantic equality of its endpoint
references.  Finer syntactic and alpha relations are weakened to conversion;
the syntax-only row table contributes no hidden equality information. -/
theorem Valid.direct_referenceEqual
    (valid : SynFact.Valid resolve arena fact) (direct : fact.Direct) :
    ReferenceEqual resolve arena fact.input fact.output := by
  rcases valid with ⟨input, output, inputResolved, outputResolved,
    inputWellFormed, outputWellFormed, meaning⟩
  rcases direct with ⟨varNone, valNone⟩
  simp only [varNone, valNone, SynMeaning, Value.LocalSynMeaning] at meaning
  have refinement : fact.rel.Refines .conv := by
    cases fact.rel <;> decide
  let compatible := meaning.1
  have equal := meaning.2.refine refinement compatible inputWellFormed outputWellFormed
  exact ⟨input, output,
    (resolves_withoutSyn_iff resolve arena fact.input input).mp inputResolved,
    (resolves_withoutSyn_iff resolve arena fact.output output).mp outputResolved,
    inputWellFormed, outputWellFormed, equal⟩

/-- Exact semantic contract of Rust `Kernel::syn_refl`. -/
theorem Valid.refl (resolved : Resolves resolve arena.withoutSyn reference value)
    (wellFormed : value.WellFormed) :
    SynFact.Valid resolve arena
      { rel := relation, input := reference, output := reference } := by
  have compatible := Value.compatible_refl wellFormed
  exact ⟨value, value, resolved, resolved, wellFormed, wellFormed,
    compatible, SynRel.holds_refl wellFormed⟩

/-- Exact semantic contract of Rust `Kernel::syn_refine`.  The endpoint and
substitution references are unchanged; only the relation is weakened. -/
theorem Valid.refine (valid : SynFact.Valid resolve arena fact)
    (refinement : fact.rel.Refines relation) :
    SynFact.Valid resolve arena { fact with rel := relation } := by
  rcases valid with ⟨input, output, inputResolves, outputResolves,
    inputWellFormed, outputWellFormed, meaning⟩
  refine ⟨input, output, inputResolves, outputResolves, inputWellFormed,
    outputWellFormed, ?_⟩
  cases varEq : fact.var <;> cases valEq : fact.val
  · simp only [varEq, valEq] at meaning ⊢
    exact SynInference.meaningRefine meaning refinement
      inputWellFormed outputWellFormed
  · simp only [varEq, valEq] at meaning
  · simp only [varEq, valEq] at meaning ⊢
    rcases meaning with ⟨subVar, subVarResolves, subVarWellFormed, meaning⟩
    exact ⟨subVar, subVarResolves, subVarWellFormed,
      SynInference.meaningRefine meaning refinement
        inputWellFormed outputWellFormed⟩
  · simp only [varEq, valEq] at meaning ⊢
    rcases meaning with ⟨subVar, replacement, subVarResolves,
      replacementResolves, subVarWellFormed, replacementWellFormed, meaning⟩
    exact ⟨subVar, replacement, subVarResolves, replacementResolves,
      subVarWellFormed, replacementWellFormed,
      SynInference.meaningRefine meaning refinement
        inputWellFormed outputWellFormed⟩

/-- Exact semantic contract of Rust `Kernel::syn_symm`.  Symmetry is exposed
only for direct facts, so no substitution judgment is reversed. -/
theorem Valid.symm (valid : SynFact.Valid resolve arena fact)
    (direct : fact.Direct) :
    SynFact.Valid resolve arena
      { rel := fact.rel, input := fact.output, output := fact.input } := by
  rcases valid with ⟨input, output, inputResolves, outputResolves,
    inputWellFormed, outputWellFormed, meaning⟩
  rcases direct with ⟨varEq, valEq⟩
  simp only [varEq, valEq] at meaning
  exact ⟨output, input, outputResolves, inputResolves, outputWellFormed,
    inputWellFormed, meaning.1.symm, meaning.2.symm⟩

/-- The checked LCF wrapper.  Code consuming facts should accept this type;
unchecked wire payloads become checked only through `ofInference`. -/
structure Checked (resolve : Resolver) (arena : Arena) where
  fact : SynFact
  valid : fact.Valid resolve arena

/-- The sole introduction boundary for a checked fact: all row references
must resolve and the supplied local inference must match the payload. -/
def Checked.ofInference {resolve : Resolver} {arena : Arena} {fact : SynFact}
    {input output : Value}
    (inputResolves : Resolves resolve arena.withoutSyn fact.input input)
    (outputResolves : Resolves resolve arena.withoutSyn fact.output output)
    (inputWellFormed : input.WellFormed)
    (outputWellFormed : output.WellFormed)
    (inference : match fact.var, fact.val with
      | none, none => SynInference fact.rel none none input output
      | some variableRef, none =>
          ∃ subVar,
            Resolves resolve arena.withoutSyn variableRef subVar ∧
            subVar.WellFormed ∧
            SynInference fact.rel (some subVar) none input output
      | some variableRef, some replacementRef =>
          ∃ subVar replacement,
            Resolves resolve arena.withoutSyn variableRef subVar ∧
            Resolves resolve arena.withoutSyn replacementRef replacement ∧
            subVar.WellFormed ∧ replacement.WellFormed ∧
            SynInference fact.rel (some subVar) (some replacement) input output
      | _, _ => False) : Checked resolve arena := by
  refine ⟨fact, input, output, inputResolves, outputResolves,
    inputWellFormed, outputWellFormed, ?_⟩
  cases varEq : fact.var <;> cases valEq : fact.val
  · simp only [varEq, valEq] at inference ⊢
    exact SynInference.sound inference
  · simp only [varEq, valEq] at inference
  · simp only [varEq, valEq] at inference ⊢
    rcases inference with ⟨subVar, variableResolves, variableWellFormed, derivation⟩
    exact ⟨subVar, variableResolves, variableWellFormed, derivation.sound⟩
  · simp only [varEq, valEq] at inference
    rcases inference with ⟨subVar, replacement, variableResolves,
      replacementResolves, variableWellFormed, replacementWellFormed, derivation⟩
    exact ⟨subVar, replacement, variableResolves, replacementResolves,
      variableWellFormed, replacementWellFormed, derivation.sound⟩

/-- Checked result returned by the logical core of Rust `Kernel::syn_refl`.
Slot allocation is handled separately by `FullKernel.push`. -/
def Checked.refl (relation : SynRel)
    (resolved : Resolves resolve arena.withoutSyn reference value)
    (wellFormed : value.WellFormed) : Checked resolve arena :=
  ⟨{ rel := relation, input := reference, output := reference },
    Valid.refl resolved wellFormed⟩

/-- Checked result returned by the logical core of Rust
`Kernel::syn_refine`. -/
def Checked.refine (source : Checked resolve arena)
    (refinement : source.fact.rel.Refines relation) : Checked resolve arena :=
  ⟨{ source.fact with rel := relation }, source.valid.refine refinement⟩

/-- Checked result returned by the logical core of Rust `Kernel::syn_symm`. -/
def Checked.symm (source : Checked resolve arena) (direct : source.fact.Direct) :
    Checked resolve arena :=
  ⟨{ rel := source.fact.rel,
      input := source.fact.output, output := source.fact.input },
    source.valid.symm direct⟩

end SynFact

/-! ## Free-list table and semantic preservation -/

/-- The fact-table API viewed through the actual wire arena. -/
abbrev SynArena := Arena

namespace SynArena

private def withSyn (state : SynArena) (facts : List SynSlot)
    (free : Option SynFactId) : SynArena :=
  match state with
  | .mk imports axs dense _ _ ctx assume assert =>
      .mk imports axs dense facts free ctx assume assert

@[simp] private theorem withoutSyn_withSyn
    (state : SynArena) (facts : List SynSlot) (free : Option SynFactId) :
    (withSyn state facts free).withoutSyn = state.withoutSyn := by
  cases state
  rfl

@[simp] private theorem valid_withSyn_iff
    (state : SynArena) (facts : List SynSlot) (free : Option SynFactId) :
    SynFact.Valid resolve (withSyn state facts free) fact ↔
      SynFact.Valid resolve state fact := by
  cases state
  rfl

private def slotAt : Nat → List SynSlot → Option SynSlot
  | _, [] => none
  | 0, slot :: _ => some slot
  | position + 1, _ :: slots => slotAt position slots

private theorem slotAt_mem {position : Nat} {slots : List SynSlot} {slot : SynSlot}
    (found : slotAt position slots = some slot) : slot ∈ slots := by
  induction slots generalizing position with
  | nil => simp [slotAt] at found
  | cons head tail ih =>
      cases position with
      | zero =>
          simp only [slotAt, Option.some.injEq] at found
          subst slot
          simp
      | succ position =>
          simp only [slotAt] at found
          exact List.mem_cons_of_mem head (ih found)

def factSlot? (state : SynArena) (id : SynFactId) : Option SynSlot :=
  slotAt id.position state.synFacts

def fact? (state : SynArena) (id : SynFactId) : Option SynFact :=
  match state.factSlot? id with
  | some (.fact fact) => some fact
  | _ => none

/-- Logical cache safety: every occupied slot is a valid fact.  Allocator
links are deliberately absent from the trusted proposition. -/
def Sound (resolve : Resolver) (state : SynArena) : Prop :=
  ∀ fact, SynSlot.fact fact ∈ state.synFacts →
    SynFact.Valid resolve state fact

/-- Looking up an occupied slot in a sound fact arena recovers its validity. -/
theorem Sound.fact?_valid {resolve : Resolver} {state : SynArena}
    {id : SynFactId} {fact : SynFact} (sound : Sound resolve state)
    (found : state.fact? id = some fact) : SynFact.Valid resolve state fact := by
  unfold fact? at found
  cases slotFound : state.factSlot? id with
  | none => simp [slotFound] at found
  | some slot =>
      cases slot with
      | free free => simp [slotFound] at found
      | fact stored =>
          simp only [slotFound, Option.some.injEq] at found
          subst stored
          apply sound fact
          apply slotAt_mem
          simpa [factSlot?] using slotFound

def append (state : SynArena) (fact : SynFact) : SynArena :=
  withSyn state (state.synFacts ++ [.fact fact]) state.synFree

private def replaceAt : Nat → SynFact → List SynSlot → Option (List SynSlot)
  | _, _, [] => none
  | 0, fact, .fact _ :: slots => some (.fact fact :: slots)
  | 0, _, .free _ :: _ => none
  | position + 1, fact, slot :: slots => do
      return slot :: (← replaceAt position fact slots)

def replace (state : SynArena) (id : SynFactId) (fact : SynFact) : Option SynArena := do
  let slots ← replaceAt id.position fact state.synFacts
  return withSyn state slots state.synFree

/-- Replace the free-list head by an occupied fact and return its successor. -/
private def reuseAt : Nat → SynFact → List SynSlot →
    Option (Option SynFactId × List SynSlot)
  | _, _, [] => none
  | 0, fact, .free free :: slots => some (free.next, .fact fact :: slots)
  | 0, _, .fact _ :: _ => none
  | position + 1, fact, slot :: slots => do
      let (next, tail) ← reuseAt position fact slots
      return (next, slot :: tail)

private def removeAt : Nat → Option SynFactId → List SynSlot →
    Option (List SynSlot)
  | _, _, [] => none
  | 0, head, .fact _ :: slots => some (.free ⟨head⟩ :: slots)
  | 0, _, .free _ :: _ => none
  | position + 1, head, slot :: slots => do
      return slot :: (← removeAt position head slots)

/-- The reachable free-list spine.  Positions, rather than IDs, are recorded
in the visited set so `Nodup` directly excludes allocator cycles. -/
inductive FreeChain (slots : List SynSlot) : Option SynFactId → List Nat → Prop where
  | nil : FreeChain slots none []
  | cons {id next : SynFactId} {visited : List Nat}
      (lookup : slotAt id.position slots = some (.free ⟨some next⟩))
      (fresh : id.position ∉ visited)
      (tail : FreeChain slots (some next) visited) :
      FreeChain slots (some id) (id.position :: visited)
  | last {id : SynFactId}
      (lookup : slotAt id.position slots = some (.free ⟨none⟩)) :
      FreeChain slots (some id) [id.position]

/-- Following `synFree` stays in-range, visits only free slots, and cannot
repeat a position.  Unreachable holes are permitted; `rebuildFree` restores
the stronger all-holes-reachable canonical form. -/
def FreeListSafe (state : SynArena) : Prop :=
  ∃ visited, FreeChain state.synFacts state.synFree visited

theorem freeListSafe_empty : FreeListSafe Arena.empty :=
  ⟨[], .nil⟩

private theorem FreeChain.position_free
    (chain : FreeChain slots head visited) (member : position ∈ visited) :
    ∃ free, slotAt position slots = some (.free free) := by
  induction chain with
  | nil => simp at member
  | cons lookup fresh tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, lookup⟩
      · exact ih member
  | last lookup =>
      simp only [List.mem_singleton] at member
      subst position
      exact ⟨_, lookup⟩

private theorem FreeChain.transport (chain : FreeChain slots head visited)
    (same : ∀ position ∈ visited, slotAt position result = slotAt position slots) :
    FreeChain result head visited := by
  induction chain with
  | nil => exact .nil
  | cons lookup fresh tail ih =>
      apply FreeChain.cons
      · rw [same _ (by simp), lookup]
      · exact fresh
      · apply ih
        intro position member
        exact same position (by simp [member])
  | last lookup =>
      apply FreeChain.last
      rw [same _ (by simp), lookup]

set_option linter.flexible false in
private theorem removeAt_target
    (removed : removeAt position head slots = some result) :
    ∃ old, slotAt position slots = some (.fact old) ∧
      slotAt position result = some (.free ⟨head⟩) := by
  induction position generalizing slots result with
  | zero =>
      cases slots with
      | nil => simp [removeAt] at removed
      | cons slot slots =>
          cases slot with
          | free free => simp [removeAt] at removed
          | fact old =>
              simp [removeAt] at removed
              subst result
              exact ⟨old, rfl, rfl⟩
  | succ position ih =>
      cases slots with
      | nil => simp [removeAt] at removed
      | cons slot slots =>
          cases equation : removeAt position head slots with
          | none => simp [removeAt, equation] at removed
          | some tail =>
              simp [removeAt, equation] at removed
              subst result
              simpa [slotAt] using ih equation

set_option linter.flexible false in
private theorem removeAt_other
    (removed : removeAt target head slots = some result)
    (different : position ≠ target) :
    slotAt position result = slotAt position slots := by
  induction target generalizing slots result position with
  | zero =>
      cases slots with
      | nil => simp [removeAt] at removed
      | cons slot slots =>
          cases slot with
          | free free => simp [removeAt] at removed
          | fact old =>
              simp [removeAt] at removed
              subst result
              cases position with
              | zero => contradiction
              | succ position => rfl
  | succ target ih =>
      cases slots with
      | nil => simp [removeAt] at removed
      | cons slot slots =>
          cases equation : removeAt target head slots with
          | none => simp [removeAt, equation] at removed
          | some tail =>
              simp [removeAt, equation] at removed
              subst result
              cases position with
              | zero => rfl
              | succ position =>
                  simp only [slotAt]
                  apply ih equation
                  omega

set_option linter.flexible false in
private theorem reuseAt_target
    (reused : reuseAt position fact slots = some (next, result)) :
    slotAt position slots = some (.free ⟨next⟩) ∧
      slotAt position result = some (.fact fact) := by
  induction position generalizing slots result with
  | zero =>
      cases slots with
      | nil => simp [reuseAt] at reused
      | cons slot slots =>
          cases slot with
          | fact old => simp [reuseAt] at reused
          | free old =>
              simp [reuseAt] at reused
              rcases reused with ⟨rfl, rfl⟩
              exact ⟨rfl, rfl⟩
  | succ position ih =>
      cases slots with
      | nil => simp [reuseAt] at reused
      | cons slot slots =>
          cases equation : reuseAt position fact slots with
          | none => simp [reuseAt, equation] at reused
          | some pair =>
              rcases pair with ⟨tailNext, tail⟩
              simp [reuseAt, equation] at reused
              rcases reused with ⟨rfl, rfl⟩
              simpa [slotAt] using ih equation

set_option linter.flexible false in
private theorem reuseAt_other
    (reused : reuseAt target fact slots = some (next, result))
    (different : position ≠ target) :
    slotAt position result = slotAt position slots := by
  induction target generalizing slots result position with
  | zero =>
      cases slots with
      | nil => simp [reuseAt] at reused
      | cons slot slots =>
          cases slot with
          | fact old => simp [reuseAt] at reused
          | free old =>
              simp [reuseAt] at reused
              rcases reused with ⟨rfl, rfl⟩
              cases position with
              | zero => contradiction
              | succ position => rfl
  | succ target ih =>
      cases slots with
      | nil => simp [reuseAt] at reused
      | cons slot slots =>
          cases equation : reuseAt target fact slots with
          | none => simp [reuseAt, equation] at reused
          | some pair =>
              rcases pair with ⟨tailNext, tail⟩
              simp [reuseAt, equation] at reused
              rcases reused with ⟨rfl, rfl⟩
              cases position with
              | zero => rfl
              | succ position =>
                  simp only [slotAt]
                  apply ih equation
                  omega

set_option linter.flexible false in
private theorem replaceAt_target
    (replaced : replaceAt position fact slots = some result) :
    ∃ old, slotAt position slots = some (.fact old) ∧
      slotAt position result = some (.fact fact) := by
  induction position generalizing slots result with
  | zero =>
      cases slots with
      | nil => simp [replaceAt] at replaced
      | cons slot slots =>
          cases slot with
          | free free => simp [replaceAt] at replaced
          | fact old =>
              simp [replaceAt] at replaced
              subst result
              exact ⟨old, rfl, rfl⟩
  | succ position ih =>
      cases slots with
      | nil => simp [replaceAt] at replaced
      | cons slot slots =>
          cases equation : replaceAt position fact slots with
          | none => simp [replaceAt, equation] at replaced
          | some tail =>
              simp [replaceAt, equation] at replaced
              subst result
              simpa [slotAt] using ih equation

set_option linter.flexible false in
private theorem replaceAt_other
    (replaced : replaceAt target fact slots = some result)
    (different : position ≠ target) :
    slotAt position result = slotAt position slots := by
  induction target generalizing slots result position with
  | zero =>
      cases slots with
      | nil => simp [replaceAt] at replaced
      | cons slot slots =>
          cases slot with
          | free free => simp [replaceAt] at replaced
          | fact old =>
              simp [replaceAt] at replaced
              subst result
              cases position with
              | zero => contradiction
              | succ position => rfl
  | succ target ih =>
      cases slots with
      | nil => simp [replaceAt] at replaced
      | cons slot slots =>
          cases equation : replaceAt target fact slots with
          | none => simp [replaceAt, equation] at replaced
          | some tail =>
              simp [replaceAt, equation] at replaced
              subst result
              cases position with
              | zero => rfl
              | succ position =>
                  simp only [slotAt]
                  apply ih equation
                  omega

private theorem slotAt_append_of_some
    (lookup : slotAt position slots = some slot) :
    slotAt position (slots ++ suffix) = some slot := by
  induction position generalizing slots with
  | zero =>
      cases slots <;> simp_all [slotAt]
  | succ position ih =>
      cases slots with
      | nil => simp [slotAt] at lookup
      | cons head slots =>
          simp only [List.cons_append, slotAt]
          exact ih lookup

private theorem FreeChain.append (chain : FreeChain slots head visited)
    (suffix : List SynSlot) : FreeChain (slots ++ suffix) head visited := by
  induction chain with
  | nil => exact .nil
  | cons lookup fresh tail ih =>
      exact .cons (slotAt_append_of_some lookup) fresh ih
  | last lookup => exact .last (slotAt_append_of_some lookup)

def remove (state : SynArena) (id : SynFactId) : Option SynArena := do
  let slots ← removeAt id.position state.synFree state.synFacts
  return withSyn state slots (some id)

/-- Turn a zero-based position into the corresponding one-based wire ID.
The `none` branch is the mathematical analogue of Rust's checked overflow. -/
def idAt? (position : Nat) : Option SynFactId :=
  if position + 1 ≤ SynFactId.maxInclusive then
    SynFactId.ofUInt64? (UInt64.ofNat (position + 1))
  else none

private theorem uint64_ofNat_toNat (value : Nat) (fits : value < 2 ^ 64) :
    (UInt64.ofNat value).toNat = value := by
  change value % 2 ^ 64 = value
  exact Nat.mod_eq_of_lt fits

private theorem idAt?_position {id : SynFactId}
    (found : idAt? position = some id) :
    id.position = position := by
  unfold idAt? at found
  split at found
  next bounded =>
    have fits : position + 1 < 2 ^ 64 := by
      simp only [SynFactId.maxInclusive] at bounded
      omega
    unfold SynFactId.ofUInt64? at found
    split at found
    next valid =>
      injection found with found
      subst id
      change (position + 1) % 2 ^ 64 - 1 = position
      rw [Nat.mod_eq_of_lt fits]
      omega
    next zero => simp at found
  next overflow => simp at found

/-- Rust `Arena::push_syn_fact`: reuse the reachable free-list head when one
exists, otherwise append and return the new one-based ID. -/
def push (state : SynArena) (fact : SynFact) :
    Option (SynFactId × SynArena) :=
  match state.synFree with
  | some id => do
      let (next, slots) ← reuseAt id.position fact state.synFacts
      return (id, withSyn state slots next)
  | none => do
      let id ← idAt? state.synFacts.length
      return (id, append state fact)

set_option linter.flexible false in
theorem withoutSyn_push {state result : SynArena} {id : SynFactId}
    {fact : SynFact} (pushed : push state fact = some (id, result)) :
    result.withoutSyn = state.withoutSyn := by
  unfold push at pushed
  cases headEq : state.synFree with
  | none =>
      simp only [headEq] at pushed
      cases idEq : idAt? state.synFacts.length with
      | none => simp [idEq] at pushed
      | some appendedId =>
          simp [idEq] at pushed
          rcases pushed with ⟨rfl, rfl⟩
          simp [append]
  | some head =>
      simp only [headEq] at pushed
      cases reuseEq : reuseAt head.position fact state.synFacts with
      | none => simp [reuseEq] at pushed
      | some pair =>
          rcases pair with ⟨next, slots⟩
          simp [reuseEq] at pushed
          rcases pushed with ⟨rfl, rfl⟩
          simp

/-- Reverse scan used after truncation.  Facts stay put; every retained free
slot is relinked to the next retained free slot at a larger position. -/
private def rebuildFrom : Nat → List SynSlot →
    Option SynFactId × List SynSlot
  | _, [] => (none, [])
  | position, slot :: slots =>
      let (tailHead, rebuiltTail) := rebuildFrom (position + 1) slots
      match slot with
      | .fact fact => (tailHead, .fact fact :: rebuiltTail)
      | .free _ =>
          match idAt? position with
          | none => (tailHead, .free ⟨tailHead⟩ :: rebuiltTail)
          | some id => (some id, .free ⟨tailHead⟩ :: rebuiltTail)

private theorem slotAt_prefix (lengthEq : pre.length = position) :
    slotAt position (pre ++ slot :: suffix) = some slot := by
  induction pre generalizing position with
  | nil =>
      subst position
      rfl
  | cons head pre ih =>
      cases position with
      | zero => simp at lengthEq
      | succ position =>
          simp only [List.cons_append, slotAt]
          apply ih
          simpa using Nat.succ.inj lengthEq

private theorem rebuildFrom_freeChain (pre slots : List SynSlot)
    (lengthEq : pre.length = position) :
    ∃ visited,
      FreeChain (pre ++ (rebuildFrom position slots).2)
        (rebuildFrom position slots).1 visited ∧
      ∀ member ∈ visited, position ≤ member := by
  induction slots generalizing position pre with
  | nil =>
      exact ⟨[], by simp [rebuildFrom, FreeChain.nil]⟩
  | cons slot slots ih =>
      cases tailEq : rebuildFrom (position + 1) slots with
      | mk tailHead rebuiltTail =>
          cases slot with
          | fact fact =>
              have tail := ih (position := position + 1)
                (pre := pre ++ [.fact fact]) (by simp [lengthEq])
              rcases tail with ⟨visited, chain, bounded⟩
              refine ⟨visited, ?_, ?_⟩
              · simpa [rebuildFrom, tailEq, List.append_assoc] using chain
              · intro member memberIn
                exact Nat.le_trans (Nat.le_add_right position 1)
                  (bounded member memberIn)
          | free free =>
              cases idEq : idAt? position with
              | none =>
                  have tail := ih (position := position + 1)
                    (pre := pre ++ [.free ⟨tailHead⟩])
                    (by simp [lengthEq])
                  rcases tail with ⟨visited, chain, bounded⟩
                  refine ⟨visited, ?_, ?_⟩
                  · simpa [rebuildFrom, tailEq, idEq, List.append_assoc] using chain
                  · intro member memberIn
                    exact Nat.le_trans (Nat.le_add_right position 1)
                      (bounded member memberIn)
              | some id =>
                  have tail := ih (position := position + 1)
                    (pre := pre ++ [.free ⟨tailHead⟩])
                    (by simp [lengthEq])
                  rcases tail with ⟨visited, chain, bounded⟩
                  have idPosition := idAt?_position idEq
                  have fresh : id.position ∉ visited := by
                    intro member
                    have later := bounded id.position member
                    omega
                  refine ⟨id.position :: visited, ?_, ?_⟩
                  · have lookup : slotAt id.position
                        (pre ++ .free ⟨tailHead⟩ :: rebuiltTail) =
                        some (.free ⟨tailHead⟩) := by
                      rw [idPosition]
                      exact slotAt_prefix lengthEq
                    have linked : FreeChain
                        (pre ++ .free ⟨tailHead⟩ :: rebuiltTail)
                        (some id) (id.position :: visited) := by
                      have tailChain : FreeChain
                          (pre ++ .free ⟨tailHead⟩ :: rebuiltTail)
                          tailHead visited := by
                        simpa [tailEq, List.append_assoc] using chain
                      cases tailHead with
                      | none =>
                          cases tailChain
                          exact .last lookup
                      | some next => exact .cons lookup fresh tailChain
                    simpa [rebuildFrom, tailEq, idEq, List.append_assoc] using linked
                  · intro member memberIn
                    simp only [List.mem_cons] at memberIn
                    rcases memberIn with rfl | memberIn
                    · omega
                    · exact Nat.le_trans (Nat.le_add_right position 1)
                        (bounded member memberIn)

def rebuildFree (state : SynArena) : SynArena :=
  let rebuilt := rebuildFrom 0 state.synFacts
  withSyn state rebuilt.2 rebuilt.1

def truncate (state : SynArena) (length : Nat) : SynArena :=
  rebuildFree (withSyn state (state.synFacts.take length) state.synFree)

theorem withoutSyn_replace {state result : SynArena} {id : SynFactId}
    {fact : SynFact} (replaced : replace state id fact = some result) :
    result.withoutSyn = state.withoutSyn := by
  unfold replace at replaced
  cases equation : replaceAt id.position fact state.synFacts with
  | none => simp [equation] at replaced
  | some slots =>
      simp [equation] at replaced
      subst result
      simp

theorem withoutSyn_remove {state result : SynArena} {id : SynFactId}
    (removed : remove state id = some result) :
    result.withoutSyn = state.withoutSyn := by
  unfold remove at removed
  cases equation : removeAt id.position state.synFree state.synFacts with
  | none => simp [equation] at removed
  | some slots =>
      simp [equation] at removed
      subst result
      simp

@[simp] theorem withoutSyn_truncate (state : SynArena) (length : Nat) :
    (truncate state length).withoutSyn = state.withoutSyn := by
  simp [truncate, rebuildFree]

set_option linter.flexible false in
private theorem valid_of_replaceAt
    {resolve : Resolver} {arena : Arena}
    (replaced : replaceAt position new slots = some result)
    (oldSound : ∀ fact, SynSlot.fact fact ∈ slots →
      SynFact.Valid resolve arena fact)
    (newValid : SynFact.Valid resolve arena new) :
    ∀ fact, SynSlot.fact fact ∈ result →
      SynFact.Valid resolve arena fact := by
  induction position generalizing slots result with
  | zero =>
      cases slots with
      | nil => simp [replaceAt] at replaced
      | cons slot slots =>
          cases slot with
          | free free => simp [replaceAt] at replaced
          | fact old =>
              simp [replaceAt] at replaced
              subst result
              intro fact member
              simp only [List.mem_cons, SynSlot.fact.injEq] at member
              rcases member with rfl | member
              · exact newValid
              · exact oldSound fact (by simp [member])
  | succ position ih =>
      cases slots with
      | nil => simp [replaceAt] at replaced
      | cons slot slots =>
          cases equation : replaceAt position new slots with
          | none => simp [replaceAt, equation] at replaced
          | some tail =>
          simp [replaceAt, equation] at replaced
          subst result
          have tailSound : ∀ fact, SynSlot.fact fact ∈ slots →
              SynFact.Valid resolve arena fact := by
            intro fact member
            exact oldSound fact (by simp [member])
          have resultSound := ih equation tailSound
          intro fact member
          simp only [List.mem_cons] at member
          rcases member with member | member
          · subst slot
            exact oldSound fact (by simp)
          · exact resultSound fact member

set_option linter.flexible false in
private theorem valid_of_reuseAt
    {resolve : Resolver} {arena : Arena}
    (reused : reuseAt position new slots = some (next, result))
    (oldSound : ∀ fact, SynSlot.fact fact ∈ slots →
      SynFact.Valid resolve arena fact)
    (newValid : SynFact.Valid resolve arena new) :
    ∀ fact, SynSlot.fact fact ∈ result →
      SynFact.Valid resolve arena fact := by
  induction position generalizing slots result with
  | zero =>
      cases slots with
      | nil => simp [reuseAt] at reused
      | cons slot slots =>
          cases slot with
          | fact old => simp [reuseAt] at reused
          | free old =>
              simp [reuseAt] at reused
              rcases reused with ⟨rfl, rfl⟩
              intro fact member
              simp only [List.mem_cons, SynSlot.fact.injEq] at member
              rcases member with rfl | member
              · exact newValid
              · exact oldSound fact (by simp [member])
  | succ position ih =>
      cases slots with
      | nil => simp [reuseAt] at reused
      | cons slot slots =>
          cases equation : reuseAt position new slots with
          | none => simp [reuseAt, equation] at reused
          | some pair =>
              rcases pair with ⟨tailNext, tail⟩
              simp [reuseAt, equation] at reused
              rcases reused with ⟨rfl, rfl⟩
              have tailSound : ∀ fact, SynSlot.fact fact ∈ slots →
                  SynFact.Valid resolve arena fact := by
                intro fact member
                exact oldSound fact (by simp [member])
              have resultSound := ih equation tailSound
              intro fact member
              simp only [List.mem_cons] at member
              rcases member with member | member
              · subst slot
                exact oldSound fact (by simp)
              · exact resultSound fact member

set_option linter.flexible false in
private theorem valid_of_removeAt
    {resolve : Resolver} {arena : Arena}
    (removed : removeAt position head slots = some result)
    (oldSound : ∀ fact, SynSlot.fact fact ∈ slots →
      SynFact.Valid resolve arena fact) :
    ∀ fact, SynSlot.fact fact ∈ result →
      SynFact.Valid resolve arena fact := by
  induction position generalizing slots result with
  | zero =>
      cases slots with
      | nil => simp [removeAt] at removed
      | cons slot slots =>
          cases slot with
          | free free => simp [removeAt] at removed
          | fact old =>
              simp [removeAt] at removed
              subst result
              intro fact member
              simp only [List.mem_cons] at member
              rcases member with impossible | member
              · cases impossible
              · exact oldSound fact (by simp [member])
  | succ position ih =>
      cases slots with
      | nil => simp [removeAt] at removed
      | cons slot slots =>
          cases equation : removeAt position head slots with
          | none => simp [removeAt, equation] at removed
          | some tail =>
          simp [removeAt, equation] at removed
          subst result
          have tailSound : ∀ fact, SynSlot.fact fact ∈ slots →
              SynFact.Valid resolve arena fact := by
            intro fact member
            exact oldSound fact (by simp [member])
          have resultSound := ih equation tailSound
          intro fact member
          simp only [List.mem_cons] at member
          rcases member with member | member
          · subst slot
            exact oldSound fact (by simp)
          · exact resultSound fact member

private theorem valid_rebuildFrom
    {resolve : Resolver} {arena : Arena}
    (oldSound : ∀ fact, SynSlot.fact fact ∈ slots →
      SynFact.Valid resolve arena fact) :
    ∀ fact, SynSlot.fact fact ∈ (rebuildFrom position slots).2 →
      SynFact.Valid resolve arena fact := by
  induction slots generalizing position with
  | nil => simp [rebuildFrom]
  | cons slot slots ih =>
      cases slot with
      | fact value =>
          simp only [rebuildFrom]
          intro candidate member
          simp only [List.mem_cons, SynSlot.fact.injEq] at member
          rcases member with equal | member
          · exact oldSound candidate (by simp [equal])
          · exact ih (position := position + 1)
              (fun fact member => oldSound fact (by simp [member])) candidate member
      | free value =>
          cases next : idAt? position <;>
            simp only [rebuildFrom, next, List.mem_cons]
          all_goals
          intro fact member
          rcases member with impossible | member
          · cases impossible
          · exact ih (position := position + 1)
              (fun fact member => oldSound fact (by simp [member])) fact member

theorem Sound.append {resolve : Resolver} {state : SynArena} {fact : SynFact}
    (sound : Sound resolve state)
    (valid : SynFact.Valid resolve state fact) : Sound resolve (append state fact) := by
  unfold Sound at sound ⊢
  cases state
  intro candidate member
  simp only [SynArena.append, withSyn, Arena.synFacts, List.mem_append, List.mem_singleton,
    SynSlot.fact.injEq] at member
  rcases member with member | rfl
  · exact valid_withSyn_iff _ _ _ |>.2 (sound candidate member)
  · exact valid_withSyn_iff _ _ _ |>.2 valid

set_option linter.flexible false in
theorem Sound.push {resolve : Resolver} {state result : SynArena}
    {id : SynFactId} {fact : SynFact}
    (sound : Sound resolve state)
    (valid : SynFact.Valid resolve state fact)
    (pushed : push state fact = some (id, result)) : Sound resolve result := by
  unfold SynArena.push at pushed
  cases headEq : state.synFree with
  | none =>
      simp only [headEq] at pushed
      cases idEq : idAt? state.synFacts.length with
      | none => simp [idEq] at pushed
      | some appendedId =>
          simp [idEq] at pushed
          rcases pushed with ⟨rfl, rfl⟩
          exact sound.append valid
  | some head =>
      simp only [headEq] at pushed
      cases reuseEq : reuseAt head.position fact state.synFacts with
      | none => simp [reuseEq] at pushed
      | some pair =>
          rcases pair with ⟨next, slots⟩
          simp [reuseEq] at pushed
          rcases pushed with ⟨rfl, rfl⟩
          unfold Sound
          intro candidate member
          apply (valid_withSyn_iff state slots next).2
          have member' : SynSlot.fact candidate ∈ slots := by
            cases state
            exact member
          exact valid_of_reuseAt reuseEq sound valid candidate member'

set_option linter.flexible false in
theorem FreeListSafe.push {state result : SynArena} {id : SynFactId}
    {fact : SynFact} (safe : FreeListSafe state)
    (pushed : push state fact = some (id, result)) : FreeListSafe result := by
  unfold SynArena.push at pushed
  cases headEq : state.synFree with
  | none =>
      simp only [headEq] at pushed
      cases idEq : idAt? state.synFacts.length with
      | none => simp [idEq] at pushed
      | some appendedId =>
          simp [idEq] at pushed
          rcases pushed with ⟨rfl, rfl⟩
          rcases safe with ⟨visited, chain⟩
          unfold FreeListSafe
          cases state
          exact ⟨visited, chain.append [.fact fact]⟩
  | some head =>
      simp only [headEq] at pushed
      cases reuseEq : reuseAt head.position fact state.synFacts with
      | none => simp [reuseEq] at pushed
      | some pair =>
          rcases pair with ⟨next, slots⟩
          simp [reuseEq] at pushed
          rcases pushed with ⟨rfl, rfl⟩
          rcases safe with ⟨visited, chain⟩
          simp only [headEq] at chain
          rcases reuseAt_target reuseEq with ⟨oldLookup, newLookup⟩
          cases chain with
          | @cons _ _ tailVisited chainLookup fresh tail =>
              rw [oldLookup] at chainLookup
              have nextEq := SynSlot.free.inj (Option.some.inj chainLookup)
              simp only [SynFree.mk.injEq] at nextEq
              subst next
              cases state
              refine ⟨tailVisited, ?_⟩
              apply tail.transport
              intro position member
              apply reuseAt_other reuseEq
              intro equal
              subst position
              exact fresh member
          | last chainLookup =>
              rw [oldLookup] at chainLookup
              have nextEq := SynSlot.free.inj (Option.some.inj chainLookup)
              simp only [SynFree.mk.injEq] at nextEq
              subst next
              cases state
              exact ⟨[], .nil⟩

set_option linter.flexible false in
theorem Sound.replace {resolve : Resolver} {state result : SynArena}
    {id : SynFactId} {fact : SynFact} (sound : Sound resolve state)
    (valid : SynFact.Valid resolve state fact)
    (replaced : replace state id fact = some result) : Sound resolve result := by
  unfold SynArena.replace at replaced
  cases equation : replaceAt id.position fact state.synFacts with
  | none => simp [equation] at replaced
  | some slots =>
      simp [equation] at replaced
      subst result
      unfold Sound
      intro candidate member
      apply (valid_withSyn_iff state slots state.synFree).2
      have member' : SynSlot.fact candidate ∈ slots := by
        cases state
        exact member
      exact valid_of_replaceAt equation sound valid candidate member'

set_option linter.flexible false in
theorem FreeListSafe.replace {state result : SynArena} {id : SynFactId}
    {fact : SynFact} (safe : FreeListSafe state)
    (replaced : replace state id fact = some result) : FreeListSafe result := by
  unfold SynArena.replace at replaced
  cases equation : replaceAt id.position fact state.synFacts with
  | none => simp [equation] at replaced
  | some slots =>
      simp [equation] at replaced
      subst result
      rcases safe with ⟨visited, chain⟩
      rcases replaceAt_target equation with ⟨old, oldLookup, newLookup⟩
      have targetFresh : id.position ∉ visited := by
        intro member
        rcases chain.position_free member with ⟨free, freeLookup⟩
        rw [oldLookup] at freeLookup
        cases freeLookup
      unfold FreeListSafe
      refine ⟨visited, ?_⟩
      cases state
      apply chain.transport
      intro position member
      apply replaceAt_other equation
      intro equal
      subst position
      exact targetFresh member

set_option linter.flexible false in
theorem Sound.remove {resolve : Resolver} {state result : SynArena}
    {id : SynFactId} (sound : Sound resolve state)
    (removed : remove state id = some result) : Sound resolve result := by
  unfold SynArena.remove at removed
  cases equation : removeAt id.position state.synFree state.synFacts with
  | none => simp [equation] at removed
  | some slots =>
      simp [equation] at removed
      subst result
      unfold Sound
      intro candidate member
      apply (valid_withSyn_iff state slots (some id)).2
      have member' : SynSlot.fact candidate ∈ slots := by
        cases state
        exact member
      exact valid_of_removeAt equation sound candidate member'

set_option linter.flexible false in
theorem FreeListSafe.remove {state result : SynArena} {id : SynFactId}
    (safe : FreeListSafe state) (removed : remove state id = some result) :
    FreeListSafe result := by
  unfold SynArena.remove at removed
  cases equation : removeAt id.position state.synFree state.synFacts with
  | none => simp [equation] at removed
  | some slots =>
      simp [equation] at removed
      subst result
      rcases safe with ⟨visited, chain⟩
      rcases removeAt_target equation with ⟨old, oldLookup, newLookup⟩
      have targetFresh : id.position ∉ visited := by
        intro member
        rcases chain.position_free member with ⟨free, freeLookup⟩
        rw [oldLookup] at freeLookup
        cases freeLookup
      have preserved : FreeChain slots state.synFree visited := by
        apply chain.transport
        intro position member
        apply removeAt_other equation
        intro equal
        subst position
        exact targetFresh member
      unfold FreeListSafe
      cases headEq : state.synFree with
      | none =>
          simp only [headEq] at newLookup preserved
          refine ⟨[id.position], ?_⟩
          cases state
          exact FreeChain.last newLookup
      | some next =>
          simp only [headEq] at newLookup preserved
          refine ⟨id.position :: visited, ?_⟩
          cases state
          exact FreeChain.cons newLookup targetFresh preserved

theorem Sound.rebuildFree {resolve : Resolver} {state : SynArena}
    (sound : Sound resolve state) : Sound resolve (rebuildFree state) := by
  unfold Sound
  intro fact member
  unfold SynArena.rebuildFree at member ⊢
  apply (valid_withSyn_iff state _ _).2
  have member' : SynSlot.fact fact ∈ (rebuildFrom 0 state.synFacts).2 := by
    cases state
    exact member
  exact valid_rebuildFrom sound fact member'

theorem FreeListSafe.rebuildFree {state : SynArena} :
    FreeListSafe (rebuildFree state) := by
  rcases rebuildFrom_freeChain ([] : List SynSlot) state.synFacts rfl with
    ⟨visited, chain, _⟩
  unfold SynArena.rebuildFree FreeListSafe
  refine ⟨visited, ?_⟩
  cases state
  exact chain

theorem Sound.truncate {resolve : Resolver} {state : SynArena} {length : Nat}
    (sound : Sound resolve state) : Sound resolve (truncate state length) := by
  apply Sound.rebuildFree
  intro fact member
  apply (valid_withSyn_iff state (state.synFacts.take length) state.synFree).2
  have member' : SynSlot.fact fact ∈ state.synFacts.take length := by
    cases state
    exact member
  exact sound fact (List.mem_of_mem_take member')

theorem FreeListSafe.truncate {state : SynArena} {length : Nat} :
    FreeListSafe (truncate state length) :=
  FreeListSafe.rebuildFree

/-- A checked cache state.  Safe mutations preserve this wrapper and can
therefore remove or rearrange evidence without enlarging the trusted theory. -/
structure Checked (resolve : Resolver) where
  state : SynArena
  sound : state.Sound resolve

namespace Checked

def append (checked : Checked resolve) (fact : SynFact.Checked resolve checked.state) :
    Checked resolve :=
  ⟨checked.state.append fact.fact, checked.sound.append fact.valid⟩

def replace (checked : Checked resolve) (id : SynFactId)
    (fact : SynFact.Checked resolve checked.state) : Option (Checked resolve) :=
  match replaced : checked.state.replace id fact.fact with
  | none => none
  | some state => some ⟨state, checked.sound.replace fact.valid replaced⟩

def remove (checked : Checked resolve) (id : SynFactId) : Option (Checked resolve) :=
  match removed : checked.state.remove id with
  | none => none
  | some state => some ⟨state, checked.sound.remove removed⟩

def truncate (checked : Checked resolve) (length : Nat) : Checked resolve :=
  ⟨checked.state.truncate length, checked.sound.truncate⟩

end Checked

end SynArena

/-! ## Integrated checked kernel state -/

namespace Arena

/-- The invariant of the Rust kernel state once the syntactic-fact table is
present: the ordinary HOL arena is kernel-valid, every occupied fact slot has
checked meaning, and following the allocator head is safe. -/
def FullKernelValid (resolve : Resolver) (arena : Arena) : Prop :=
  arena.KernelValid resolve ∧ SynArena.Sound resolve arena ∧
    SynArena.FreeListSafe arena

end Arena

/-- The actual checked arena, including its LCF cache.  This is the semantic
counterpart of Rust `Kernel`; `Kernel` above remains the cache-free core used
by the existing row constructors. -/
structure FullKernel (resolve : Resolver) where
  arena : Arena
  valid : arena.FullKernelValid resolve

namespace FullKernel

/-- The empty row arena has an empty, safe semantic cache. -/
def empty (resolve : Resolver) : FullKernel resolve where
  arena := Arena.empty
  valid := by
    refine ⟨Arena.empty_kernelValid resolve, ?_, SynArena.freeListSafe_empty⟩
    intro fact member
    change SynSlot.fact fact ∈ ([] : List SynSlot) at member
    simp at member

theorem coreValid (kernel : FullKernel resolve) :
    kernel.arena.KernelValid resolve :=
  kernel.valid.1

theorem factSound (kernel : FullKernel resolve) :
    SynArena.Sound resolve kernel.arena :=
  kernel.valid.2.1

theorem allocatorSafe (kernel : FullKernel resolve) :
    SynArena.FreeListSafe kernel.arena :=
  kernel.valid.2.2

/-- Allocate or reuse one checked fact slot.  Overflow and a malformed raw
free-list head fail without changing the checked state. -/
def push (kernel : FullKernel resolve)
    (fact : SynFact.Checked resolve kernel.arena) :
    Option (SynFactId × FullKernel resolve) :=
  match pushed : SynArena.push kernel.arena fact.fact with
  | none => none
  | some (id, arena) => some (id, {
      arena
      valid := by
        refine ⟨?_, kernel.factSound.push fact.valid pushed,
          kernel.allocatorSafe.push pushed⟩
        change arena.withoutSyn.CoreKernelValid resolve
        rw [SynArena.withoutSyn_push pushed]
        exact kernel.coreValid })

/-- Overwrite an occupied checked slot with another checked fact. -/
def replace (kernel : FullKernel resolve) (id : SynFactId)
    (fact : SynFact.Checked resolve kernel.arena) :
    Option (FullKernel resolve) :=
  match replaced : SynArena.replace kernel.arena id fact.fact with
  | none => none
  | some arena => some {
      arena
      valid := by
        refine ⟨?_, kernel.factSound.replace fact.valid replaced,
          kernel.allocatorSafe.replace replaced⟩
        change arena.withoutSyn.CoreKernelValid resolve
        rw [SynArena.withoutSyn_replace replaced]
        exact kernel.coreValid }

/-- Remove an occupied fact slot and link it into the free list. -/
def remove (kernel : FullKernel resolve) (id : SynFactId) :
    Option (FullKernel resolve) :=
  match removed : SynArena.remove kernel.arena id with
  | none => none
  | some arena => some {
      arena
      valid := by
        refine ⟨?_, kernel.factSound.remove removed,
          kernel.allocatorSafe.remove removed⟩
        change arena.withoutSyn.CoreKernelValid resolve
        rw [SynArena.withoutSyn_remove removed]
        exact kernel.coreValid }

/-- Retain a prefix and rebuild its free-list links. -/
def truncate (kernel : FullKernel resolve) (length : Nat) :
    FullKernel resolve where
  arena := SynArena.truncate kernel.arena length
  valid := by
    refine ⟨?_, kernel.factSound.truncate, SynArena.FreeListSafe.truncate⟩
    change (SynArena.truncate kernel.arena length).withoutSyn.CoreKernelValid resolve
    rw [SynArena.withoutSyn_truncate]
    exact kernel.coreValid

end FullKernel

end Nucleus.Hol.Ethane.OneBased
