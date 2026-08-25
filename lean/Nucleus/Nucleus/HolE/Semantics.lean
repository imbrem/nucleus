import Nucleus.HolE.Kernel

/-! # Relational pointed semantics for unrestricted `HolE` -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

abbrev EmptySig : Signature := fun _ => Empty

instance : SigTyping EmptySig where
  HasType symbol := nomatch symbol
  rename _ rule := nomatch rule
  instantiate _ rule := nomatch rule

structure Pointed where
  carrier : Type
  point : carrier

def DenoteKind : Kind → Type 1
  | .star => Pointed
  | .arr domain codomain => DenoteKind domain → DenoteKind codomain

abbrev TypeEnv (types : List Kind) :=
  (kind : Kind) → TyVar types kind → DenoteKind kind

def extendTypeEnv (value : DenoteKind kind) (environment : TypeEnv types) :
    TypeEnv (kind :: types)
  | _, .zero => value
  | kind, .succ v => environment kind v

def emptyTypeEnv : TypeEnv ([] : List Kind) := fun _ v => nomatch v

def boolPointed : Pointed := ⟨Bool, false⟩

noncomputable def choosePointed (type : Pointed)
    (predicate : type.carrier → Bool) : type.carrier := by
  classical
  exact if witness : ∃ value, predicate value = true then
    Classical.choose witness
  else
    type.point

theorem choosePointed_spec (type : Pointed) (predicate : type.carrier → Bool)
    (witness : type.carrier) (holds : predicate witness = true) :
    predicate (choosePointed type predicate) = true := by
  classical
  simp only [choosePointed]
  split
  · exact Classical.choose_spec ‹_›
  · exfalso
    apply ‹¬ _›
    exact Exists.intro witness holds

abbrev RawBoundEnv (depth : Nat) :=
  ∀ (_index : Fin depth) (semantic : Pointed), semantic.carrier

def emptyRawBoundEnv : RawBoundEnv 0 := fun i => Fin.elim0 i

noncomputable def extendRawBoundEnv (semantic : Pointed) (value : semantic.carrier)
    (environment : RawBoundEnv depth) : RawBoundEnv (depth + 1) := by
  classical
  intro index target
  refine Fin.cases ?_ (fun i => environment i target) index
  exact if equal : target = semantic then cast (by cases equal; rfl) value else target.point

mutual
  /-- A family can have multiple semantic realizations.  This proof relevance
  is what lets unrestricted nested `model` remain structurally recursive. -/
  inductive DenotesFam : {types : List Kind} → TypeEnv types →
      {kind : Kind} → Fam EmptySig types kind → DenoteKind kind → Prop where
    | bool (typeEnv : TypeEnv types) :
        DenotesFam typeEnv (.boolTy : Fam EmptySig types .star) boolPointed
    | arr : DenotesFam typeEnv A domain → DenotesFam typeEnv B codomain →
        DenotesFam typeEnv (.arr A B)
          ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩
    | tyApp : DenotesFam typeEnv F function → DenotesFam typeEnv A argument →
        DenotesFam typeEnv (.tyApp F A) (function argument)
    | tyLam (function : DenoteKind (.arr domain codomain)) :
        (∀ argument, DenotesFam (extendTypeEnv argument typeEnv) body
          (function argument)) →
        DenotesFam typeEnv (.tyLam body) function
    | tyBv (v : TyVar types kind) :
        DenotesFam typeEnv (.tyBv v) (typeEnv kind v)
    | sub : DenotesFam typeEnv A semantic →
        DenotesFam typeEnv (.sub A predicate) semantic
    | modelDefault : DenotesFam typeEnv (.model predicate) boolPointed
    | modelWitness (candidate : Pointed) :
        Eval (extendTypeEnv (kind := .star) candidate typeEnv) emptyBound
          emptyRawBoundEnv predicate
          .boolTy boolPointed true →
        DenotesFam typeEnv (.model predicate) candidate

  /-- Evaluation at an explicitly realized object type. -/
  inductive Eval : {types : List Kind} → (typeEnv : TypeEnv types) →
      {depth : Nat} → (Γ : BoundCtx EmptySig types depth) → RawBoundEnv depth →
      (term : Tm EmptySig types depth) → (A : Ty EmptySig types) →
      (semantic : Pointed) → semantic.carrier → Prop where
    | bv (contextLookup : Γ i = A)
        (denotes : DenotesFam typeEnv A semantic) :
        Eval typeEnv Γ boundEnv (.bv i) A semantic (boundEnv i semantic)
    | fv (name : Nat) (denotes : DenotesFam typeEnv A semantic) :
        Eval typeEnv Γ boundEnv (.fv name A) A semantic semantic.point
    | app {f : domain.carrier → codomain.carrier} {x : domain.carrier}
        (functionEval : Eval typeEnv Γ boundEnv function (.arr A B)
          ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩ f)
        (argumentEval : Eval typeEnv Γ boundEnv argument A domain x) :
        Eval typeEnv Γ boundEnv (.app function argument) B codomain (f x)
    | lam (A B : Ty EmptySig types) (domain codomain : Pointed)
        (domainDenotes : DenotesFam typeEnv A domain)
        (codomainDenotes : DenotesFam typeEnv B codomain)
        (function : domain.carrier → codomain.carrier)
        (bodyEval : ∀ argument, Eval typeEnv (extendBound A Γ)
          (extendRawBoundEnv domain argument boundEnv) body B codomain (function argument)) :
        Eval typeEnv Γ boundEnv (.lam A body) (.arr A B)
          ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩ function
    | boolean (literal : Bool) :
        Eval typeEnv Γ boundEnv (.bool literal) .boolTy boolPointed literal
    | eqTrue (denotes : DenotesFam typeEnv A semantic)
        (leftEval : Eval typeEnv Γ boundEnv left A semantic x)
        (rightEval : Eval typeEnv Γ boundEnv right A semantic y)
        (equal : x = y) :
        Eval typeEnv Γ boundEnv (.eq A left right) .boolTy boolPointed true
    | eqFalse (denotes : DenotesFam typeEnv A semantic)
        (leftEval : Eval typeEnv Γ boundEnv left A semantic x)
        (rightEval : Eval typeEnv Γ boundEnv right A semantic y)
        (notEqual : x ≠ y) :
        Eval typeEnv Γ boundEnv (.eq A left right) .boolTy boolPointed false
    | eps (denotes : DenotesFam typeEnv A semantic)
        (predicateEval : Eval typeEnv Γ boundEnv predicate (.arr A .boolTy)
          ⟨semantic.carrier → Bool, fun _ => false⟩ function) :
        Eval typeEnv Γ boundEnv (.eps A predicate) A semantic
          (choosePointed semantic function)
    | abs (carrierDenotes : DenotesFam typeEnv A semantic)
        (valueEval : Eval typeEnv Γ boundEnv value A semantic x) :
        Eval typeEnv Γ boundEnv (.abs A predicate value) (.sub A predicate) semantic x
    | rep (carrierDenotes : DenotesFam typeEnv A semantic)
        (valueEval : Eval typeEnv Γ boundEnv value (.sub A predicate) semantic x) :
        Eval typeEnv Γ boundEnv (.rep A predicate value) A semantic x
    | tyExistsTrue
        (candidate : Pointed)
        (predicateEval : Eval (extendTypeEnv (kind := .star) candidate typeEnv)
          emptyBound emptyRawBoundEnv
          predicate .boolTy boolPointed true) :
        Eval typeEnv Γ boundEnv (.tyExists predicate) .boolTy boolPointed true
    | tyExistsFalse :
        Eval typeEnv Γ boundEnv (.tyExists predicate) .boolTy boolPointed false
    -- The universal's clauses are the honest duals, with a premise on each
    -- side. `tyExistsFalse` above is premise-free — it lets `semantic_total`
    -- pick a value without deciding the existential, at the cost of the
    -- relation not being functional there. Copying that shape here would
    -- relate *every* type-universal to `true`, which is the direction that
    -- makes reading `Eval … true` as truth vacuous, so the price is paid
    -- instead in `semantic_total`, which now needs a classical case split.
    | tyForallTrue
        (predicateEval : ∀ candidate : Pointed,
          Eval (extendTypeEnv (kind := .star) candidate typeEnv)
            emptyBound emptyRawBoundEnv predicate .boolTy boolPointed true) :
        Eval typeEnv Γ boundEnv (.tyForall predicate) .boolTy boolPointed true
    | tyForallFalse
        (candidate : Pointed)
        (predicateEval : Eval (extendTypeEnv (kind := .star) candidate typeEnv)
          emptyBound emptyRawBoundEnv
          predicate .boolTy boolPointed false) :
        Eval typeEnv Γ boundEnv (.tyForall predicate) .boolTy boolPointed false
end

theorem DenotesFam.bool_inv
    {types : List Kind} (typeEnv : TypeEnv types)
    {semantic : Pointed}
    (denotes : DenotesFam typeEnv (.boolTy : Ty EmptySig types) semantic) :
    semantic = boolPointed := by
  generalize familyEq : (.boolTy : Ty EmptySig types) = family at denotes
  cases denotes <;> simp_all

theorem DenotesFam.arr_inv
    {types : List Kind} (typeEnv : TypeEnv types)
    {A B : Ty EmptySig types} {semantic : Pointed}
    (denotes : DenotesFam typeEnv (.arr A B) semantic) :
    ∃ domain codomain,
      DenotesFam typeEnv A domain ∧ DenotesFam typeEnv B codomain ∧
      semantic = ⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩ := by
  cases denotes with
  | arr domainDenotes codomainDenotes =>
      exact ⟨_, _, domainDenotes, codomainDenotes, rfl⟩

theorem DenotesFam.sub_inv
    {types : List Kind} (typeEnv : TypeEnv types)
    {A : Ty EmptySig types} {predicate : Tm EmptySig types 1}
    {semantic : Pointed}
    (denotes : DenotesFam typeEnv (.sub A predicate) semantic) :
    DenotesFam typeEnv A semantic := by
  cases denotes with
  | sub carrierDenotes => exact carrierDenotes

/-- The common structural induction principle needed for both family totality
and term evaluation.  Quantifying environments in the motive is important:
the `tyLam` case evaluates its body in an extended type environment. -/
abbrev Checks.SemanticTotal {types : List Kind} {sort : HolSort} {depth : Nat}
    (Γ : BoundCtx EmptySig types depth) (expression : Expr EmptySig types sort depth)
    (classification : Classification EmptySig types sort) : Prop :=
  ∀ typeEnv : TypeEnv types,
    match sort with
    | .kind _ => ∀ hdepth : depth = 0,
        ∃ semantic, DenotesFam typeEnv (hdepth ▸ expression) semantic
    | .tm => match classification with
      | .tm A => (∃ semantic, DenotesFam typeEnv A semantic) ∧
          ∀ boundEnv : RawBoundEnv depth, ∀ semantic : Pointed,
            DenotesFam typeEnv A semantic →
              ∃ value, Eval typeEnv Γ boundEnv expression A semantic value

theorem Checks.semantic_total {types : List Kind} {sort : HolSort} {depth : Nat}
    {Γ : BoundCtx EmptySig types depth} {expression : Expr EmptySig types sort depth}
    {classification : Classification EmptySig types sort}
    (checking : Checks Γ expression classification) :
    Checks.SemanticTotal Γ expression classification := by
  classical
  induction checking with
  | boolTy => intro typeEnv _; exact ⟨boolPointed, .bool typeEnv⟩
  | arr hA hB ihA ihB =>
      intro typeEnv _
      obtain ⟨domain, domainDenotes⟩ := ihA typeEnv rfl
      obtain ⟨codomain, codomainDenotes⟩ := ihB typeEnv rfl
      exact ⟨⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩,
        .arr domainDenotes codomainDenotes⟩
  | tyApp hF hA ihF ihA =>
      intro typeEnv _
      obtain ⟨function, functionDenotes⟩ := ihF typeEnv rfl
      obtain ⟨argument, argumentDenotes⟩ := ihA typeEnv rfl
      exact ⟨function argument, .tyApp functionDenotes argumentDenotes⟩
  | tyLam hbody ih =>
      intro typeEnv _
      let function := fun argument => Classical.choose (ih (extendTypeEnv argument typeEnv) rfl)
      refine ⟨function, .tyLam function ?_⟩
      intro argument
      exact Classical.choose_spec (ih (extendTypeEnv argument typeEnv) rfl)
  | tyBv v => intro typeEnv _; exact ⟨typeEnv _ v, .tyBv v⟩
  | sub hA hp ihA ihp =>
      intro typeEnv _
      obtain ⟨semantic, denotes⟩ := ihA typeEnv rfl
      exact ⟨semantic, .sub denotes⟩
  | model hp ih => intro typeEnv _; exact ⟨boolPointed, .modelDefault⟩
  | primFam symbol => exact nomatch symbol
  | primTm rule => exact nomatch rule
  | bv hA lookup ihA =>
      intro typeEnv
      refine ⟨ihA typeEnv rfl, ?_⟩
      intro boundEnv semantic denotes
      exact ⟨boundEnv _ semantic, .bv lookup denotes⟩
  | fv name hA ihA =>
      intro typeEnv
      refine ⟨ihA typeEnv rfl, ?_⟩
      intro boundEnv semantic denotes
      exact ⟨semantic.point, .fv name denotes⟩
  | app hf hx ihf ihx =>
      intro typeEnv
      obtain ⟨functionSemantic, functionDenotes⟩ := (ihf typeEnv).1
      obtain ⟨_, codomain, _, codomainDenotes, rfl⟩ :=
        DenotesFam.arr_inv typeEnv functionDenotes
      refine ⟨⟨codomain, codomainDenotes⟩, ?_⟩
      intro boundEnv semantic denotes
      obtain ⟨domain, domainDenotes⟩ := (ihx typeEnv).1
      obtain ⟨function, functionEval⟩ := (ihf typeEnv).2 boundEnv _
        (.arr domainDenotes denotes)
      obtain ⟨argument, argumentEval⟩ := (ihx typeEnv).2 boundEnv _ domainDenotes
      exact ⟨function argument, .app functionEval argumentEval⟩
  | lam body hA hb ihA ihb =>
      intro typeEnv
      obtain ⟨domain, domainDenotes⟩ := ihA typeEnv rfl
      obtain ⟨codomain, codomainDenotes⟩ := (ihb typeEnv).1
      refine ⟨⟨⟨domain.carrier → codomain.carrier, fun _ => codomain.point⟩,
        .arr domainDenotes codomainDenotes⟩, ?_⟩
      intro boundEnv semantic denotes
      obtain ⟨domain, codomain, domainDenotes, codomainDenotes, rfl⟩ :=
        DenotesFam.arr_inv typeEnv denotes
      let function := fun argument => Classical.choose
        ((ihb typeEnv).2 (extendRawBoundEnv domain argument boundEnv) codomain codomainDenotes)
      refine ⟨function, .lam _ _ _ _ domainDenotes codomainDenotes function ?_⟩
      intro argument
      exact Classical.choose_spec
        ((ihb typeEnv).2 (extendRawBoundEnv domain argument boundEnv) codomain codomainDenotes)
  | bool literal =>
      intro typeEnv
      refine ⟨⟨boolPointed, .bool typeEnv⟩, ?_⟩
      intro boundEnv semantic denotes
      have equal := DenotesFam.bool_inv typeEnv denotes
      subst semantic
      exact ⟨literal, .boolean literal⟩
  | eq hA hx hy ihA ihx ihy =>
      intro typeEnv
      refine ⟨⟨boolPointed, .bool typeEnv⟩, ?_⟩
      intro boundEnv semantic denotes
      have equalSemantic := DenotesFam.bool_inv typeEnv denotes
      subst semantic
      obtain ⟨carrier, carrierDenotes⟩ := ihA typeEnv rfl
      obtain ⟨left, leftEval⟩ := (ihx typeEnv).2 boundEnv carrier carrierDenotes
      obtain ⟨right, rightEval⟩ := (ihy typeEnv).2 boundEnv carrier carrierDenotes
      by_cases equal : left = right
      · exact ⟨true, .eqTrue carrierDenotes leftEval rightEval equal⟩
      · exact ⟨false, .eqFalse carrierDenotes leftEval rightEval equal⟩
  | eps hA hp ihA ihp =>
      intro typeEnv
      refine ⟨ihA typeEnv rfl, ?_⟩
      intro boundEnv semantic denotes
      obtain ⟨function, functionEval⟩ := (ihp typeEnv).2 boundEnv _
        (.arr denotes (.bool typeEnv))
      exact ⟨choosePointed semantic function, .eps denotes functionEval⟩
  | abs hA hp hx ihA ihp ihx =>
      intro typeEnv
      obtain ⟨carrier, carrierDenotes⟩ := ihA typeEnv rfl
      refine ⟨⟨carrier, .sub carrierDenotes⟩, ?_⟩
      intro boundEnv semantic denotes
      have carrierDenotes := DenotesFam.sub_inv typeEnv denotes
      obtain ⟨value, valueEval⟩ := (ihx typeEnv).2 boundEnv semantic carrierDenotes
      exact ⟨value, .abs carrierDenotes valueEval⟩
  | rep hA hp hx ihA ihp ihx =>
      intro typeEnv
      refine ⟨ihA typeEnv rfl, ?_⟩
      intro boundEnv semantic denotes
      obtain ⟨value, valueEval⟩ := (ihx typeEnv).2 boundEnv semantic (.sub denotes)
      exact ⟨value, .rep denotes valueEval⟩
  | tyExists hp ih =>
      intro typeEnv
      refine ⟨⟨boolPointed, .bool typeEnv⟩, ?_⟩
      intro boundEnv semantic denotes
      have equal := DenotesFam.bool_inv typeEnv denotes
      subst semantic
      exact ⟨false, .tyExistsFalse⟩

  | @tyForall _ predicate _ _ hp ih =>
      intro typeEnv
      refine ⟨⟨boolPointed, .bool typeEnv⟩, ?_⟩
      intro boundEnv semantic denotes
      have equal := DenotesFam.bool_inv typeEnv denotes
      subst semantic
      -- Unlike the existential, neither value is free here: the universal has
      -- to be decided. Every candidate gives the predicate *some* value by the
      -- induction hypothesis, and one of them being `false` is exactly what
      -- refutes the universal.
      by_cases every : ∀ candidate : Pointed,
          Eval (extendTypeEnv (kind := .star) candidate typeEnv)
            emptyBound emptyRawBoundEnv predicate .boolTy boolPointed true
      · exact ⟨true, .tyForallTrue every⟩
      · obtain ⟨candidate, notTrue⟩ : ∃ candidate : Pointed,
            ¬ Eval (extendTypeEnv (kind := .star) candidate typeEnv)
                emptyBound emptyRawBoundEnv predicate .boolTy boolPointed true :=
          Classical.byContradiction fun none =>
            every fun candidate =>
              Classical.byContradiction fun missing => none ⟨candidate, missing⟩
        obtain ⟨value, valueEval⟩ :=
          (ih (extendTypeEnv (kind := .star) candidate typeEnv)).2
            emptyRawBoundEnv boolPointed
            (.bool (extendTypeEnv (kind := .star) candidate typeEnv))
        cases value with
        | true => exact absurd valueEval notTrue
        | false => exact ⟨false, .tyForallFalse candidate valueEval⟩

theorem Kinded.denotes_exists {types : List Kind} (typeEnv : TypeEnv types)
    {family : Fam EmptySig types kind} (checking : Kinded family) :
    ∃ semantic, DenotesFam typeEnv family semantic :=
  checking.semantic_total typeEnv rfl

/-- Evaluate a typed term at a chosen realization of its result type. -/
theorem HasType.eval_at {types : List Kind} (typeEnv : TypeEnv types)
    {depth : Nat} {Γ : BoundCtx EmptySig types depth} (boundEnv : RawBoundEnv depth)
    {term : Tm EmptySig types depth} {A : Ty EmptySig types}
    (typing : HasType Γ term A) {semantic : Pointed}
    (denotes : DenotesFam typeEnv A semantic) :
    ∃ value, Eval typeEnv Γ boundEnv term A semantic value :=
  (typing.semantic_total typeEnv).2 boundEnv semantic denotes

theorem HasType.eval_exists {types : List Kind} (typeEnv : TypeEnv types)
    {depth : Nat} {Γ : BoundCtx EmptySig types depth} (boundEnv : RawBoundEnv depth)
    {term : Tm EmptySig types depth} {A : Ty EmptySig types}
    (typing : HasType Γ term A) :
    ∃ semantic value, Eval typeEnv Γ boundEnv term A semantic value := by
  obtain ⟨semantic, denotes⟩ := Kinded.denotes_exists typeEnv typing.typeKinded
  obtain ⟨value, evaluation⟩ := HasType.eval_at typeEnv boundEnv typing denotes
  exact ⟨semantic, value, evaluation⟩

end Nucleus.HolE
