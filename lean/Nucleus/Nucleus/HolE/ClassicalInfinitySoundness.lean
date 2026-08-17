import Nucleus.HolE.ClassicalSoundness
import Nucleus.HolE.ClassicalEquations
import Nucleus.HolE.ClassicalTermTransport
import Nucleus.HolE.Infinity

/-! # Classical realization of the HolE infinity sentence -/

namespace Nucleus.HolE

set_option relaxedAutoImplicit true

namespace Infinity

private def IEval {types depth} {Γ : BoundCtx ClassicalSig types depth}
    {A : Ty ClassicalSig types} (term : InfinityTm ClassicalSig Γ A)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (expected : CPointed) (value : expected.carrier) : Prop :=
  ∀ checking : CHasType Γ term.tm A,
    cSem checking env bound expected = ⟨value⟩

private noncomputable def iValue {types depth}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    (term : InfinityTm ClassicalSig Γ A) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (expected : CPointed) : expected.carrier :=
  (cSem term.typing.certificate env bound expected).down

private theorem IEval.canonical {types depth}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    (term : InfinityTm ClassicalSig Γ A) (env : CTypeEnv types)
    (bound : CBoundEnv depth) (expected : CPointed) :
    IEval term env bound expected (iValue term env bound expected) := by
  intro checking
  rw [cSem_certificate_coherent checking term.typing.certificate env]
  unfold iValue
  rfl

private theorem IEval.value_unique {types depth}
    {Γ : BoundCtx ClassicalSig types depth} {A : Ty ClassicalSig types}
    {term : InfinityTm ClassicalSig Γ A} {env : CTypeEnv types}
    {bound : CBoundEnv depth} {expected : CPointed} {x y : expected.carrier}
    (hx : IEval term env bound expected x) (hy : IEval term env bound expected y) :
    x = y := by
  have equal := (hx term.typing.certificate).symm.trans
    (hy term.typing.certificate)
  exact congrArg ULift.down equal

private theorem IEval.boolean (literal : Bool) (env : CTypeEnv types)
    (bound : CBoundEnv depth) :
    IEval (Γ := Γ) (InfinityTm.boolean literal) env bound cBool literal := by
  intro checking
  rw [cSem_certificate_coherent checking (.bool literal) env]
  change ULift.up (alignCValue cBool cBool literal) = ULift.up literal
  exact congrArg ULift.up (alignCValue_self cBool literal)

private theorem IEval.bv {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {X : Ty ClassicalSig types}
    (hA : Kinded X) (index : Fin depth)
    (lookup : Γ index = X) (env : CTypeEnv types) (bound : CBoundEnv depth)
    (expected : CPointed) (value : expected.carrier)
    (atIndex : bound index expected = value) :
    IEval (InfinityTm.bv hA index lookup) env bound expected value := by
  intro checking
  let cA : CKinded X := hA.certificate
  let explicit : CHasType Γ (.bv index) X := .bv cA lookup
  rw [cSem_certificate_coherent checking explicit env]
  exact congrArg ULift.up atIndex

private theorem IEval.app {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {X Y : Ty ClassicalSig types}
    (function : InfinityTm ClassicalSig Γ (.arr X Y))
    (argument : InfinityTm ClassicalSig Γ X)
    (hA : CKinded X) (hB : CKinded Y)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (functionValue : (cSem hA env).carrier → (cSem hB env).carrier)
    (argumentValue : (cSem hA env).carrier)
    (hf : IEval function env bound
      ⟨(cSem hA env).carrier → (cSem hB env).carrier,
        fun _ => (cSem hB env).point⟩ functionValue)
    (hx : IEval argument env bound (cSem hA env) argumentValue) :
    IEval (function.app argument) env bound (cSem hB env)
      (functionValue argumentValue) := by
  intro checking
  let cf := function.typing.certificate
  let cx := argument.typing.certificate
  let functionType : CPointed :=
    ⟨(cSem hA env).carrier → (cSem hB env).carrier,
      fun _ => (cSem hB env).point⟩
  let explicit : CHasType Γ (.app function.tm argument.tm) Y := .app hA hB cf cx
  rw [cSem_certificate_coherent checking explicit env]
  change ULift.up (alignCValue (cSem hB env) (cSem hB env)
    ((cSem cf env bound functionType).down
      (cSem cx env bound (cSem hA env)).down)) = _
  rw [hf cf, hx cx]
  exact congrArg ULift.up (alignCValue_self _ _)

private noncomputable def classicalEqBool {T : Type} (x y : T) : Bool := by
  classical
  exact decide (x = y)

private theorem IEval.eq {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {X : Ty ClassicalSig types}
    (hA : Kinded X) (left right : InfinityTm ClassicalSig Γ X)
    (cA : CKinded X) (env : CTypeEnv types) (bound : CBoundEnv depth)
    (x y : (cSem cA env).carrier)
    (hx : IEval left env bound (cSem cA env) x)
    (hy : IEval right env bound (cSem cA env) y) :
    IEval (InfinityTm.eq hA left right) env bound cBool
      (classicalEqBool x y) := by
  classical
  intro checking
  let cl := left.typing.certificate
  let cr := right.typing.certificate
  let explicit : CHasType Γ (.eq X left.tm right.tm) .boolTy := .eq cA cl cr
  rw [cSem_certificate_coherent checking explicit env]
  change ULift.up (alignCValue cBool cBool
    (decide ((cSem cl env bound _).down = (cSem cr env bound _).down))) = _
  rw [hx cl, hy cr]
  by_cases equal : x = y <;>
    simp [classicalEqBool, equal, alignCValue_bool]

private theorem IEval.lam {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {X Y : Ty ClassicalSig types}
    (hX : Kinded X)
    (body : InfinityTm ClassicalSig (extendBound X Γ) Y)
    (cX : CKinded X) (cY : CKinded Y)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (function : (cSem cX env).carrier → (cSem cY env).carrier)
    (bodyEval : ∀ argument,
      IEval body env (extendCBoundEnv (cSem cX env) argument bound)
        (cSem cY env) (function argument)) :
    IEval (InfinityTm.lam hX body) env bound
      ⟨(cSem cX env).carrier → (cSem cY env).carrier,
        fun _ => (cSem cY env).point⟩ function := by
  intro checking
  let cb := body.typing.certificate
  let explicit : CHasType Γ (.lam X body.tm) (.arr X Y) :=
    .lam body.tm cX cY cb
  rw [cSem_certificate_coherent checking explicit env]
  change ULift.up (alignCValue
    ⟨(cSem cX env).carrier → (cSem cY env).carrier,
      fun _ => (cSem cY env).point⟩
    ⟨(cSem cX env).carrier → (cSem cY env).carrier,
      fun _ => (cSem cY env).point⟩
    (fun argument =>
      (cSem cb env (extendCBoundEnv (cSem cX env) argument bound)
        (cSem cY env)).down)) = ULift.up function
  rw [alignCValue_self]
  congr 1
  funext argument
  exact congrArg ULift.down (bodyEval argument cb)

private noncomputable def epsilonValue (carrier : CPointed)
    (predicate : carrier.carrier → Bool) : carrier.carrier := by
  classical
  exact if witness : ∃ value, predicate value = true then
    Classical.choose witness else carrier.point

private theorem IEval.eps {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {X : Ty ClassicalSig types}
    (hX : Kinded X)
    (predicate : InfinityTm ClassicalSig Γ (.arr X .boolTy))
    (cX : CKinded X) (env : CTypeEnv types) (bound : CBoundEnv depth)
    (meaning : (cSem cX env).carrier → Bool)
    (hp : IEval predicate env bound
      ⟨(cSem cX env).carrier → Bool, fun _ => false⟩ meaning) :
    IEval (InfinityTm.eps hX predicate) env bound (cSem cX env)
      (epsilonValue (cSem cX env) meaning) := by
  classical
  intro checking
  let cp := predicate.typing.certificate
  let functionType : CPointed :=
    ⟨(cSem cX env).carrier → Bool, fun _ => false⟩
  let explicit : CHasType Γ (.eps X predicate.tm) X := .eps cX cp
  rw [cSem_certificate_coherent checking explicit env]
  change ULift.up (alignCValue (cSem cX env) (cSem cX env)
    (if witness : ∃ value, (cSem cp env bound functionType).down value = true then
      Classical.choose witness else (cSem cX env).point)) = _
  rw [hp cp]
  congr 1
  let carrier : CPointed := cSem cX env
  change alignCValue carrier carrier
    (if witness : ∃ value, meaning value = true then
      Classical.choose witness else carrier.point) =
    epsilonValue carrier meaning
  exact (alignCValue_self carrier _).trans (by rfl)

private theorem epsilonValue_spec (carrier : CPointed)
    (predicate : carrier.carrier → Bool) (witness : carrier.carrier)
    (holds : predicate witness = true) :
    predicate (epsilonValue carrier predicate) = true := by
  classical
  have existsWitness : ∃ value : carrier.carrier, predicate value = true :=
    ⟨witness, holds⟩
  simp only [epsilonValue, dif_pos existsWitness]
  exact Classical.choose_spec existsWitness

private theorem IEval.forallTm {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {X : Ty ClassicalSig types}
    (hX : Kinded X)
    (body : InfinityTm ClassicalSig (extendBound X Γ) .boolTy)
    (cX : CKinded X) (env : CTypeEnv types) (bound : CBoundEnv depth)
    (bodyTrue : ∀ argument : (cSem cX env).carrier,
      IEval body env (extendCBoundEnv (cSem cX env) argument bound)
        cBool true) :
    IEval (InfinityTm.forallTm hX body) env bound cBool true := by
  let constant : (cSem cX env).carrier → Bool := fun _ => true
  have lhs : IEval (InfinityTm.lam hX body) env bound
      ⟨(cSem cX env).carrier → Bool, fun _ => false⟩ constant := by
    exact IEval.lam hX body cX .boolTy env bound constant bodyTrue
  have rhs : IEval (InfinityTm.lam hX (InfinityTm.truth (Γ := extendBound X Γ)))
      env bound ⟨(cSem cX env).carrier → Bool, fun _ => false⟩ constant := by
    apply IEval.lam hX _ cX .boolTy env bound constant
    intro argument
    exact IEval.boolean true env _
  have equality := IEval.eq (.arr hX .boolTy)
    (InfinityTm.lam hX body)
    (InfinityTm.lam hX (InfinityTm.truth (Γ := extendBound X Γ)))
    (.arr cX .boolTy) env bound constant constant lhs rhs
  have same : classicalEqBool constant constant = true := by
    simp [classicalEqBool]
  have equality' : IEval (InfinityTm.eq (.arr hX .boolTy)
      (InfinityTm.lam hX body)
      (InfinityTm.lam hX (InfinityTm.truth (Γ := extendBound X Γ))))
      env bound cBool true := same ▸ equality
  simpa only [InfinityTm.forallTm] using equality'

private theorem IEval.existsTm {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth} {X : Ty ClassicalSig types}
    (hX : Kinded X)
    (body : InfinityTm ClassicalSig (extendBound X Γ) .boolTy)
    (cX : CKinded X) (env : CTypeEnv types) (bound : CBoundEnv depth)
    (meaning : (cSem cX env).carrier → Bool)
    (bodyEval : ∀ argument,
      IEval body env (extendCBoundEnv (cSem cX env) argument bound)
        cBool (meaning argument))
    (witness : (cSem cX env).carrier) (holds : meaning witness = true) :
    IEval (InfinityTm.existsTm hX body) env bound cBool true := by
  let predicate := InfinityTm.lam hX body
  have predicateEval : IEval predicate env bound
      ⟨(cSem cX env).carrier → Bool, fun _ => false⟩ meaning :=
    IEval.lam hX body cX .boolTy env bound meaning bodyEval
  have epsilonEval := IEval.eps hX predicate cX env bound meaning predicateEval
  have applied := IEval.app predicate (InfinityTm.eps hX predicate)
    cX .boolTy env bound meaning (epsilonValue (cSem cX env) meaning)
    predicateEval epsilonEval
  have selectedHolds := epsilonValue_spec (cSem cX env) meaning witness holds
  change IEval (predicate.app (InfinityTm.eps hX predicate)) env bound cBool
    (meaning (epsilonValue (cSem cX env) meaning)) at applied
  simpa only [InfinityTm.existsTm, selectedHolds] using applied

private theorem IEval.not_of_false {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    (proposition : InfinityTm ClassicalSig Γ .boolTy)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (evaluates : IEval proposition env bound cBool false) :
    IEval (InfinityTm.not proposition) env bound cBool true := by
  have falseEval : IEval (InfinityTm.falsehood (Γ := Γ)) env bound cBool false :=
    IEval.boolean false env bound
  have equality := IEval.eq (.boolTy) proposition InfinityTm.falsehood .boolTy
    env bound false false evaluates falseEval
  have same : classicalEqBool false false = true := by simp [classicalEqBool]
  have equality' : IEval (InfinityTm.eq (.boolTy) proposition
      InfinityTm.falsehood) env bound cBool true := same ▸ equality
  simpa only [InfinityTm.not] using equality'

private theorem IEval.and_of_true {types : List Kind} {depth : Nat}
    {Γ : BoundCtx ClassicalSig types depth}
    (left right : InfinityTm ClassicalSig Γ .boolTy)
    (env : CTypeEnv types) (bound : CBoundEnv depth)
    (leftWeakenedTrue : ∀ f : (cSem
      (CChecks.arr (types := types) CChecks.boolTy
        (CChecks.arr CChecks.boolTy CChecks.boolTy)) env).carrier,
      IEval (left.weaken (C := .arr .boolTy (.arr .boolTy .boolTy))) env
        (extendCBoundEnv (cSem
          (CChecks.arr CChecks.boolTy (CChecks.arr CChecks.boolTy CChecks.boolTy)) env)
          f bound) cBool true)
    (rightWeakenedTrue : ∀ f : (cSem
      (CChecks.arr (types := types) CChecks.boolTy
        (CChecks.arr CChecks.boolTy CChecks.boolTy)) env).carrier,
      IEval (right.weaken (C := .arr .boolTy (.arr .boolTy .boolTy))) env
        (extendCBoundEnv (cSem
          (CChecks.arr CChecks.boolTy (CChecks.arr CChecks.boolTy CChecks.boolTy)) env)
          f bound) cBool true) :
    IEval (InfinityTm.and left right) env bound cBool true := by
  let functionTy : Ty ClassicalSig types :=
    .arr .boolTy (.arr .boolTy .boolTy)
  let cFunction : CKinded functionTy :=
    .arr .boolTy (.arr .boolTy .boolTy)
  let functionSemantic : CPointed := cSem cFunction env
  let resultFunction : functionSemantic.carrier → Bool := fun f => f true true
  have lhs : IEval
      (InfinityTm.lam (.arr (.boolTy) (.arr .boolTy .boolTy)) (by
        let f : InfinityTm ClassicalSig (extendBound functionTy Γ) functionTy :=
          InfinityTm.bv (.arr .boolTy (.arr .boolTy .boolTy)) 0 rfl
        exact (f.app left.weaken).app right.weaken))
      env bound ⟨functionSemantic.carrier → Bool, fun _ => false⟩
      resultFunction := by
    apply IEval.lam (.arr .boolTy (.arr .boolTy .boolTy)) _ cFunction .boolTy
      env bound resultFunction
    intro f
    let extended := extendCBoundEnv functionSemantic f bound
    let fTm : InfinityTm ClassicalSig (extendBound functionTy Γ) functionTy :=
      InfinityTm.bv (.arr .boolTy (.arr .boolTy .boolTy)) 0 rfl
    have fEval : IEval fTm env extended functionSemantic f := by
      apply IEval.bv _ 0 rfl env extended functionSemantic f
      exact extendCBoundEnv_zero functionSemantic f bound functionSemantic
        |>.trans (alignCValue_self functionSemantic f)
    have leftEval : IEval (left.weaken (C := functionTy)) env extended cBool true :=
      leftWeakenedTrue f
    have rightEval : IEval (right.weaken (C := functionTy)) env extended cBool true :=
      rightWeakenedTrue f
    have first := IEval.app fTm left.weaken .boolTy
      (.arr .boolTy .boolTy) env extended f true fEval leftEval
    have second := IEval.app (fTm.app left.weaken) right.weaken .boolTy .boolTy
      env extended (f true) true first rightEval
    exact second
  have rhs : IEval
      (InfinityTm.lam (.arr (.boolTy) (.arr .boolTy .boolTy)) (by
        let f : InfinityTm ClassicalSig (extendBound functionTy Γ) functionTy :=
          InfinityTm.bv (.arr .boolTy (.arr .boolTy .boolTy)) 0 rfl
        exact (f.app InfinityTm.truth).app InfinityTm.truth))
      env bound ⟨functionSemantic.carrier → Bool, fun _ => false⟩
      resultFunction := by
    apply IEval.lam (.arr .boolTy (.arr .boolTy .boolTy)) _ cFunction .boolTy
      env bound resultFunction
    intro f
    let extended := extendCBoundEnv functionSemantic f bound
    let fTm : InfinityTm ClassicalSig (extendBound functionTy Γ) functionTy :=
      InfinityTm.bv (.arr .boolTy (.arr .boolTy .boolTy)) 0 rfl
    have fEval : IEval fTm env extended functionSemantic f := by
      apply IEval.bv _ 0 rfl env extended functionSemantic f
      exact extendCBoundEnv_zero functionSemantic f bound functionSemantic
        |>.trans (alignCValue_self functionSemantic f)
    have trueEval : IEval (InfinityTm.truth (Γ := extendBound functionTy Γ))
        env extended cBool true := IEval.boolean true env extended
    have first := IEval.app fTm InfinityTm.truth .boolTy
      (.arr .boolTy .boolTy) env extended f true fEval trueEval
    exact IEval.app (fTm.app InfinityTm.truth) InfinityTm.truth .boolTy .boolTy
      env extended (f true) true first trueEval
  have equality := IEval.eq (.arr (.arr .boolTy (.arr .boolTy .boolTy)) .boolTy)
    _ _ (.arr cFunction .boolTy) env bound resultFunction resultFunction lhs rhs
  have same : classicalEqBool resultFunction resultFunction = true := by
    simp [classicalEqBool]
  have equality' : IEval (InfinityTm.and left right) env bound cBool true := by
    exact same ▸ equality
  exact equality'

private theorem reflectsEquality_true
    (env : CTypeEnv [.star])
    (next : (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier →
      (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier)
    (missed : (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier)
    (reflects : ∀ x y, next x = next y ↔ x = y) :
    IEval (reflectsEquality (Sig := ClassicalSig)) env
      (extendCBoundEnv (cSem (@CChecks.tyBv [.star] .star .zero) env) missed
        (extendCBoundEnv
          ⟨(cSem (@CChecks.tyBv [.star] .star .zero) env).carrier →
              (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier,
            fun _ => (cSem (@CChecks.tyBv [.star] .star .zero) env).point⟩
          next emptyCBoundEnv)) cBool true := by
  let cA : CKinded (A (Sig := ClassicalSig)) := .tyBv .zero
  let carrier : CPointed := cSem cA env
  apply IEval.forallTm hA _ cA env _
  intro x
  apply IEval.forallTm hA _ cA env _
  intro y
  let boundXY := extendCBoundEnv carrier y
    (extendCBoundEnv carrier x
      (extendCBoundEnv carrier missed
        (extendCBoundEnv ⟨carrier.carrier → carrier.carrier,
          fun _ => carrier.point⟩ next emptyCBoundEnv)))
  let Γfz := extendBound (A (Sig := ClassicalSig))
    (extendBound (.arr A A) (emptyBound : BoundCtx ClassicalSig [.star] 0))
  let Γxy := extendBound (A (Sig := ClassicalSig))
    (extendBound (A (Sig := ClassicalSig)) Γfz)
  let fTm : InfinityTm ClassicalSig Γxy (.arr A A) :=
    .bv (.arr hA hA) 3 rfl
  let xTm : InfinityTm ClassicalSig Γxy A := .bv hA 1 rfl
  let yTm : InfinityTm ClassicalSig Γxy A := .bv hA 0 rfl
  have fEval : IEval fTm env boundXY
      ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩ next := by
    unfold fTm
    apply IEval.bv (Γ := Γxy) (.arr hA hA) 3 rfl env boundXY
      ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩ next
    dsimp only [boundXY]
    change (extendCBoundEnv carrier y
        (extendCBoundEnv carrier x
        (extendCBoundEnv carrier missed
          (extendCBoundEnv ⟨carrier.carrier → carrier.carrier,
            fun _ => carrier.point⟩ next emptyCBoundEnv))))
      (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))))
      ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩ = next
    rw [extendCBoundEnv_succ, extendCBoundEnv_succ,
      extendCBoundEnv_succ, extendCBoundEnv_zero, alignCValue_self]
  have xEval : IEval xTm env boundXY carrier x := by
    unfold xTm
    apply IEval.bv (Γ := Γxy) hA 1 rfl env boundXY carrier x
    dsimp only [boundXY]
    change (extendCBoundEnv carrier y
        (extendCBoundEnv carrier x
        (extendCBoundEnv carrier missed
          (extendCBoundEnv ⟨carrier.carrier → carrier.carrier,
            fun _ => carrier.point⟩ next emptyCBoundEnv))))
      (Fin.succ (0 : Fin 3)) carrier = x
    rw [extendCBoundEnv_succ, extendCBoundEnv_zero, alignCValue_self]
  have yEval : IEval yTm env boundXY carrier y := by
    unfold yTm
    apply IEval.bv (Γ := Γxy) hA 0 rfl env boundXY carrier y
    dsimp only [boundXY]
    rw [extendCBoundEnv_zero, alignCValue_self]
  have fx := IEval.app fTm xTm cA cA env boundXY next x fEval xEval
  have fy := IEval.app fTm yTm cA cA env boundXY next y fEval yEval
  have imageEq := IEval.eq hA (fTm.app xTm) (fTm.app yTm) cA env boundXY
    (next x) (next y) fx fy
  have inputEq := IEval.eq hA xTm yTm cA env boundXY x y xEval yEval
  have outer := IEval.eq (.boolTy)
    (InfinityTm.eq hA (fTm.app xTm) (fTm.app yTm))
    (InfinityTm.eq hA xTm yTm) .boolTy env boundXY
    (classicalEqBool (next x) (next y)) (classicalEqBool x y)
    imageEq inputEq
  have boolEqual : classicalEqBool (next x) (next y) = classicalEqBool x y := by
    by_cases equal : x = y
    · subst y
      simp [classicalEqBool]
    · have imageDifferent : next x ≠ next y := fun imageEqual =>
        equal ((reflects x y).mp imageEqual)
      simp [classicalEqBool, equal, imageDifferent]
  have result : classicalEqBool (classicalEqBool (next x) (next y))
      (classicalEqBool x y) = true := by
    rw [boolEqual]
    simp [classicalEqBool]
  exact result ▸ outer

private theorem missesPoint_true
    (env : CTypeEnv [.star])
    (next : (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier →
      (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier)
    (missed : (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier)
    (misses : ∀ x, next x ≠ missed) :
    IEval (missesPoint (Sig := ClassicalSig)) env
      (extendCBoundEnv (cSem (@CChecks.tyBv [.star] .star .zero) env) missed
        (extendCBoundEnv
          ⟨(cSem (@CChecks.tyBv [.star] .star .zero) env).carrier →
              (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier,
            fun _ => (cSem (@CChecks.tyBv [.star] .star .zero) env).point⟩
          next emptyCBoundEnv)) cBool true := by
  let cA : CKinded (A (Sig := ClassicalSig)) := .tyBv .zero
  let carrier : CPointed := cSem cA env
  apply IEval.forallTm hA _ cA env _
  intro x
  let boundX := extendCBoundEnv carrier x
    (extendCBoundEnv carrier missed
      (extendCBoundEnv ⟨carrier.carrier → carrier.carrier,
        fun _ => carrier.point⟩ next emptyCBoundEnv))
  let Γfz := extendBound (A (Sig := ClassicalSig))
    (extendBound (.arr A A) (emptyBound : BoundCtx ClassicalSig [.star] 0))
  let Γx := extendBound (A (Sig := ClassicalSig)) Γfz
  let fTm : InfinityTm ClassicalSig Γx (.arr A A) :=
    .bv (.arr hA hA) 2 rfl
  let zTm : InfinityTm ClassicalSig Γx A := .bv hA 1 rfl
  let xTm : InfinityTm ClassicalSig Γx A := .bv hA 0 rfl
  have fEval : IEval fTm env boundX
      ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩ next := by
    unfold fTm
    apply IEval.bv (Γ := Γx) (.arr hA hA) 2 rfl env boundX
      ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩ next
    dsimp only [boundX]
    change (extendCBoundEnv carrier x
      (extendCBoundEnv carrier missed
        (extendCBoundEnv ⟨carrier.carrier → carrier.carrier,
          fun _ => carrier.point⟩ next emptyCBoundEnv)))
      (Fin.succ (Fin.succ (0 : Fin 1)))
      ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩ = next
    rw [extendCBoundEnv_succ, extendCBoundEnv_succ,
      extendCBoundEnv_zero, alignCValue_self]
  have zEval : IEval zTm env boundX carrier missed := by
    unfold zTm
    apply IEval.bv (Γ := Γx) hA 1 rfl env boundX carrier missed
    dsimp only [boundX]
    change (extendCBoundEnv carrier x
      (extendCBoundEnv carrier missed
        (extendCBoundEnv ⟨carrier.carrier → carrier.carrier,
          fun _ => carrier.point⟩ next emptyCBoundEnv)))
      (Fin.succ (0 : Fin 2)) carrier = missed
    rw [extendCBoundEnv_succ, extendCBoundEnv_zero, alignCValue_self]
  have xEval : IEval xTm env boundX carrier x := by
    unfold xTm
    apply IEval.bv (Γ := Γx) hA 0 rfl env boundX carrier x
    dsimp only [boundX]
    rw [extendCBoundEnv_zero, alignCValue_self]
  have fx := IEval.app fTm xTm cA cA env boundX next x fEval xEval
  have equality := IEval.eq hA (fTm.app xTm) zTm cA env boundX
    (next x) missed fx zEval
  have isFalse : classicalEqBool (next x) missed = false := by
    simp [classicalEqBool, misses x]
  have equalityFalse : IEval (InfinityTm.eq hA (fTm.app xTm) zTm)
      env boundX cBool false := isFalse ▸ equality
  exact IEval.not_of_false _ env boundX equalityFalse

private def reflectsEqualityShifted :
    InfinityTm ClassicalSig
      (extendBound (.arr .boolTy (.arr .boolTy .boolTy))
        (extendBound (A (Sig := ClassicalSig))
          (extendBound (.arr A A)
            (emptyBound : BoundCtx ClassicalSig [.star] 0)))) .boolTy := by
  let outer := extendBound (.arr .boolTy (.arr .boolTy .boolTy))
    (extendBound A (extendBound (.arr A A)
      (emptyBound : BoundCtx ClassicalSig [.star] 0)))
  let xCtx := extendBound A outer
  let yCtx := extendBound A xCtx
  let f : InfinityTm ClassicalSig yCtx (.arr A A) := .bv (.arr hA hA) 4 rfl
  let x : InfinityTm ClassicalSig yCtx A := .bv hA 1 rfl
  let y : InfinityTm ClassicalSig yCtx A := .bv hA 0 rfl
  let reflected := InfinityTm.eq .boolTy
    (InfinityTm.eq hA (f.app x) (f.app y))
    (InfinityTm.eq hA x y)
  exact InfinityTm.forallTm hA (InfinityTm.forallTm hA reflected)

private def missesPointShifted :
    InfinityTm ClassicalSig
      (extendBound (.arr .boolTy (.arr .boolTy .boolTy))
        (extendBound (A (Sig := ClassicalSig))
          (extendBound (.arr A A)
            (emptyBound : BoundCtx ClassicalSig [.star] 0)))) .boolTy := by
  let outer := extendBound (.arr .boolTy (.arr .boolTy .boolTy))
    (extendBound A (extendBound (.arr A A)
      (emptyBound : BoundCtx ClassicalSig [.star] 0)))
  let bodyCtx := extendBound A outer
  let f : InfinityTm ClassicalSig bodyCtx (.arr A A) := .bv (.arr hA hA) 3 rfl
  let z : InfinityTm ClassicalSig bodyCtx A := .bv hA 2 rfl
  let x : InfinityTm ClassicalSig bodyCtx A := .bv hA 0 rfl
  exact InfinityTm.forallTm hA (InfinityTm.not (InfinityTm.eq hA (f.app x) z))

private theorem reflectsEqualityShifted_eq :
    reflectsEqualityShifted =
      (reflectsEquality (Sig := ClassicalSig)).weaken
        (C := .arr .boolTy (.arr .boolTy .boolTy)) := by
  rw [InfinityTm.mk.injEq]
  simp [reflectsEqualityShifted, reflectsEquality, InfinityTm.forallTm,
    InfinityTm.eq, InfinityTm.lam, InfinityTm.app, InfinityTm.bv,
    InfinityTm.truth, InfinityTm.boolean, InfinityTm.weaken, HolE.weaken,
    HolE.rename, liftRen] <;> decide

private theorem missesPointShifted_eq :
    missesPointShifted =
      (missesPoint (Sig := ClassicalSig)).weaken
        (C := .arr .boolTy (.arr .boolTy .boolTy)) := by
  rw [InfinityTm.mk.injEq]
  simp [missesPointShifted, missesPoint, InfinityTm.forallTm,
    InfinityTm.not, InfinityTm.eq, InfinityTm.lam, InfinityTm.app,
    InfinityTm.bv, InfinityTm.truth, InfinityTm.falsehood,
    InfinityTm.boolean, InfinityTm.weaken, HolE.weaken, HolE.rename, liftRen] <;>
    decide

private theorem reflectsEqualityShifted_true
    (env : CTypeEnv [.star])
    (next : (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier →
      (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier)
    (missed : (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier)
    (test : Bool → Bool → Bool)
    (reflects : ∀ x y, next x = next y ↔ x = y) :
    IEval reflectsEqualityShifted env
      (extendCBoundEnv
        ⟨Bool → Bool → Bool, fun _ => fun _ => false⟩ test
        (extendCBoundEnv (cSem (@CChecks.tyBv [.star] .star .zero) env) missed
          (extendCBoundEnv
            ⟨(cSem (@CChecks.tyBv [.star] .star .zero) env).carrier →
                (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier,
              fun _ => (cSem (@CChecks.tyBv [.star] .star .zero) env).point⟩
            next emptyCBoundEnv))) cBool true := by
  let cA : CKinded (A (Sig := ClassicalSig)) := .tyBv .zero
  let carrier : CPointed := cSem cA env
  apply IEval.forallTm hA _ cA env _
  intro x
  apply IEval.forallTm hA _ cA env _
  intro y
  let testSemantic : CPointed := ⟨Bool → Bool → Bool, fun _ => fun _ => false⟩
  let endomapSemantic : CPointed :=
    ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩
  let boundXY := extendCBoundEnv carrier y
    (extendCBoundEnv carrier x
      (extendCBoundEnv testSemantic test
        (extendCBoundEnv carrier missed
          (extendCBoundEnv endomapSemantic next emptyCBoundEnv))))
  let outer := extendBound (.arr .boolTy (.arr .boolTy .boolTy))
    (extendBound A (extendBound (.arr A A)
      (emptyBound : BoundCtx ClassicalSig [.star] 0)))
  let Γxy := extendBound A (extendBound A outer)
  let fTm : InfinityTm ClassicalSig Γxy (.arr A A) := .bv (.arr hA hA) 4 rfl
  let xTm : InfinityTm ClassicalSig Γxy A := .bv hA 1 rfl
  let yTm : InfinityTm ClassicalSig Γxy A := .bv hA 0 rfl
  have fEval : IEval fTm env boundXY endomapSemantic next := by
    unfold fTm
    apply IEval.bv (Γ := Γxy) (.arr hA hA) 4 rfl env boundXY
      endomapSemantic next
    dsimp only [boundXY]
    change (extendCBoundEnv carrier y
      (extendCBoundEnv carrier x
        (extendCBoundEnv testSemantic test
          (extendCBoundEnv carrier missed
            (extendCBoundEnv endomapSemantic next emptyCBoundEnv)))))
      (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))
      endomapSemantic = next
    rw [extendCBoundEnv_succ, extendCBoundEnv_succ, extendCBoundEnv_succ,
      extendCBoundEnv_succ, extendCBoundEnv_zero, alignCValue_self]
  have xEval : IEval xTm env boundXY carrier x := by
    unfold xTm
    apply IEval.bv (Γ := Γxy) hA 1 rfl env boundXY carrier x
    dsimp only [boundXY]
    change (extendCBoundEnv carrier y
      (extendCBoundEnv carrier x
        (extendCBoundEnv testSemantic test
          (extendCBoundEnv carrier missed
            (extendCBoundEnv endomapSemantic next emptyCBoundEnv)))))
      (Fin.succ (0 : Fin 4)) carrier = x
    rw [extendCBoundEnv_succ, extendCBoundEnv_zero, alignCValue_self]
  have yEval : IEval yTm env boundXY carrier y := by
    unfold yTm
    apply IEval.bv (Γ := Γxy) hA 0 rfl env boundXY carrier y
    dsimp only [boundXY]
    rw [extendCBoundEnv_zero, alignCValue_self]
  have fx := IEval.app fTm xTm cA cA env boundXY next x fEval xEval
  have fy := IEval.app fTm yTm cA cA env boundXY next y fEval yEval
  have imageEq := IEval.eq hA (fTm.app xTm) (fTm.app yTm) cA env boundXY
    (next x) (next y) fx fy
  have inputEq := IEval.eq hA xTm yTm cA env boundXY x y xEval yEval
  have outerEq := IEval.eq (.boolTy)
    (InfinityTm.eq hA (fTm.app xTm) (fTm.app yTm))
    (InfinityTm.eq hA xTm yTm) .boolTy env boundXY
    (classicalEqBool (next x) (next y)) (classicalEqBool x y)
    imageEq inputEq
  have boolEqual : classicalEqBool (next x) (next y) = classicalEqBool x y := by
    by_cases equal : x = y
    · subst y; simp [classicalEqBool]
    · have imageDifferent : next x ≠ next y := fun imageEqual =>
        equal ((reflects x y).mp imageEqual)
      simp [classicalEqBool, equal, imageDifferent]
  have result : classicalEqBool (classicalEqBool (next x) (next y))
      (classicalEqBool x y) = true := by
    rw [boolEqual]
    simp [classicalEqBool]
  exact result ▸ outerEq

private theorem missesPointShifted_true
    (env : CTypeEnv [.star])
    (next : (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier →
      (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier)
    (missed : (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier)
    (test : Bool → Bool → Bool) (misses : ∀ x, next x ≠ missed) :
    IEval missesPointShifted env
      (extendCBoundEnv
        ⟨Bool → Bool → Bool, fun _ => fun _ => false⟩ test
        (extendCBoundEnv (cSem (@CChecks.tyBv [.star] .star .zero) env) missed
          (extendCBoundEnv
            ⟨(cSem (@CChecks.tyBv [.star] .star .zero) env).carrier →
                (cSem (@CChecks.tyBv [.star] .star .zero) env).carrier,
              fun _ => (cSem (@CChecks.tyBv [.star] .star .zero) env).point⟩
            next emptyCBoundEnv))) cBool true := by
  let cA : CKinded (A (Sig := ClassicalSig)) := .tyBv .zero
  let carrier : CPointed := cSem cA env
  apply IEval.forallTm hA _ cA env _
  intro x
  let testSemantic : CPointed := ⟨Bool → Bool → Bool, fun _ => fun _ => false⟩
  let endomapSemantic : CPointed :=
    ⟨carrier.carrier → carrier.carrier, fun _ => carrier.point⟩
  let boundX := extendCBoundEnv carrier x
    (extendCBoundEnv testSemantic test
      (extendCBoundEnv carrier missed
        (extendCBoundEnv endomapSemantic next emptyCBoundEnv)))
  let outer := extendBound (.arr .boolTy (.arr .boolTy .boolTy))
    (extendBound A (extendBound (.arr A A)
      (emptyBound : BoundCtx ClassicalSig [.star] 0)))
  let Γx := extendBound A outer
  let fTm : InfinityTm ClassicalSig Γx (.arr A A) := .bv (.arr hA hA) 3 rfl
  let zTm : InfinityTm ClassicalSig Γx A := .bv hA 2 rfl
  let xTm : InfinityTm ClassicalSig Γx A := .bv hA 0 rfl
  have fEval : IEval fTm env boundX endomapSemantic next := by
    unfold fTm
    apply IEval.bv (Γ := Γx) (.arr hA hA) 3 rfl env boundX
      endomapSemantic next
    dsimp only [boundX]
    change (extendCBoundEnv carrier x
      (extendCBoundEnv testSemantic test
        (extendCBoundEnv carrier missed
          (extendCBoundEnv endomapSemantic next emptyCBoundEnv))))
      (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))) endomapSemantic = next
    rw [extendCBoundEnv_succ, extendCBoundEnv_succ, extendCBoundEnv_succ,
      extendCBoundEnv_zero, alignCValue_self]
  have zEval : IEval zTm env boundX carrier missed := by
    unfold zTm
    apply IEval.bv (Γ := Γx) hA 2 rfl env boundX carrier missed
    dsimp only [boundX]
    change (extendCBoundEnv carrier x
      (extendCBoundEnv testSemantic test
        (extendCBoundEnv carrier missed
          (extendCBoundEnv endomapSemantic next emptyCBoundEnv))))
      (Fin.succ (Fin.succ (0 : Fin 2))) carrier = missed
    rw [extendCBoundEnv_succ, extendCBoundEnv_succ,
      extendCBoundEnv_zero, alignCValue_self]
  have xEval : IEval xTm env boundX carrier x := by
    unfold xTm
    apply IEval.bv (Γ := Γx) hA 0 rfl env boundX carrier x
    dsimp only [boundX]
    rw [extendCBoundEnv_zero, alignCValue_self]
  have fx := IEval.app fTm xTm cA cA env boundX next x fEval xEval
  have equality := IEval.eq hA (fTm.app xTm) zTm cA env boundX
    (next x) missed fx zEval
  have isFalse : classicalEqBool (next x) missed = false := by
    simp [classicalEqBool, misses x]
  have equalityFalse : IEval (InfinityTm.eq hA (fTm.app xTm) zTm)
      env boundX cBool false := isFalse ▸ equality
  exact IEval.not_of_false _ env boundX equalityFalse

private theorem typePredicate_nat_true :
    IEval (typePredicate (Sig := ClassicalSig))
      (extendCTypeEnv natPointed emptyCTypeEnv) emptyCBoundEnv cBool true := by
  let env : CTypeEnv [.star] := extendCTypeEnv natPointed emptyCTypeEnv
  let cA : CKinded (A (Sig := ClassicalSig)) := .tyBv .zero
  have carrierEq : cSem cA env = natPointed := rfl
  let endomapTy : Ty ClassicalSig [.star] := .arr A A
  let cEndomap : CKinded endomapTy := .arr cA cA
  let endomapSemantic : CPointed := cSem cEndomap env
  let zeroValue : (cSem cA env).carrier := by
    change Nat
    exact 0
  let succ : endomapSemantic.carrier := by
    change Nat → Nat
    exact Nat.succ
  have succReflects : ∀ x y : (cSem cA env).carrier,
      succ x = succ y ↔ x = y := by
    change ∀ x y : Nat, Nat.succ x = Nat.succ y ↔ x = y
    simp
  have succMissesZero : ∀ x : (cSem cA env).carrier, succ x ≠ zeroValue := by
    change ∀ x : Nat, Nat.succ x ≠ 0
    exact Nat.succ_ne_zero
  let withF := extendBound endomapTy
    (emptyBound : BoundCtx ClassicalSig [.star] 0)
  let withZ := extendBound (A (Sig := ClassicalSig)) withF
  let body : InfinityTm ClassicalSig withZ .boolTy :=
    InfinityTm.and reflectsEquality missesPoint
  let chooseZ : InfinityTm ClassicalSig withF .boolTy :=
    InfinityTm.existsTm hA body
  let meaningF : endomapSemantic.carrier → Bool := fun f =>
    iValue chooseZ env (extendCBoundEnv endomapSemantic f emptyCBoundEnv) cBool
  have bodyAtNat : IEval body env
      (extendCBoundEnv (cSem cA env) zeroValue
        (extendCBoundEnv endomapSemantic succ emptyCBoundEnv)) cBool true := by
    apply IEval.and_of_true reflectsEquality missesPoint env _
    · intro test
      rw [← reflectsEqualityShifted_eq]
      change IEval reflectsEqualityShifted env _ cBool true
      exact reflectsEqualityShifted_true env succ zeroValue test succReflects
    · intro test
      rw [← missesPointShifted_eq]
      change IEval missesPointShifted env _ cBool true
      exact missesPointShifted_true env succ zeroValue test succMissesZero
  let meaningZ : (cSem cA env).carrier → Bool := fun z =>
    iValue body env
      (extendCBoundEnv (cSem cA env) z
        (extendCBoundEnv endomapSemantic succ emptyCBoundEnv)) cBool
  have meaningZZero : meaningZ zeroValue = true := by
    apply IEval.value_unique (IEval.canonical body env _ cBool) bodyAtNat
  have chooseZAtSucc : IEval chooseZ env
      (extendCBoundEnv endomapSemantic succ emptyCBoundEnv) cBool true := by
    exact IEval.existsTm hA body cA env _ meaningZ
      (fun z => IEval.canonical body env _ cBool) zeroValue meaningZZero
  have meaningFSucc : meaningF succ = true := by
    apply IEval.value_unique (IEval.canonical chooseZ env _ cBool) chooseZAtSucc
  have result : IEval (InfinityTm.existsTm (.arr hA hA) chooseZ)
      env emptyCBoundEnv cBool true := by
    exact IEval.existsTm (.arr hA hA) chooseZ cEndomap env
      emptyCBoundEnv meaningF
      (fun f => IEval.canonical chooseZ env _ cBool) succ meaningFSucc
  simpa only [typePredicate] using result

private noncomputable def predicateChecking :
    CHasType (emptyBound : BoundCtx ClassicalSig [.star] 0)
      (typePredicate (Sig := ClassicalSig)).tm .boolTy :=
  (typePredicate (Sig := ClassicalSig)).typing.certificate

theorem infinityAxiom_realized :
    CRealizes (Γ := (emptyBound : BoundCtx ClassicalSig [] 0))
      emptyCTypeEnv emptyCBoundEnv (infinityAxiom (Sig := ClassicalSig))
      .boolTy cBool true := by
  classical
  refine ⟨CDefChecks.tyExists (.tyExists predicateChecking) (.exact predicateChecking), ?_⟩
  change ULift.up (alignCValue cBool cBool
    (decide (∃ candidate : CPointed,
      cSem predicateChecking
        (extendCTypeEnv (kind := .star) candidate emptyCTypeEnv)
        emptyCBoundEnv cBool = ⟨true⟩))) = ⟨true⟩
  rw [alignCValue_bool]
  congr 1
  apply decide_eq_true
  refine ⟨natPointed, ?_⟩
  exact typePredicate_nat_true predicateChecking

end Infinity

end Nucleus.HolE
