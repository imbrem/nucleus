import Nucleus.Metamath.Compress

/-!
# The Metamath proof checker, and its soundness

This file mirrors `crates/logic/metamath/src/verify.rs`: a stack machine that
replays a proof step by step, popping an assertion's mandatory hypotheses,
rebuilding the substitution from the floating hypotheses, re-checking the
essential hypotheses and the distinct-variable conditions, and pushing the
substituted conclusion.

The point of writing it here is `verifyAssertionAt_sound`: **if the checker
accepts, the conclusion is derivable**, in the sense of
`Nucleus.Metamath.Provable`. The checker is an algorithm; `Provable` is the
specification; nothing about the checker is taken as definitional.

Two side conditions appear here that the Rust checker does not currently
enforce, and the soundness proof is what makes clear they are load-bearing:

* a cited assertion must occur **strictly earlier** in the database
  (`VerifyError.forwardReference`). Without it a theorem may cite itself, or two
  theorems may cite each other, and the accepting run corresponds to no
  well-founded derivation. `Provable`'s `usable` parameter is exactly this
  citation window, and the soundness statement could not be phrased without it.
* a cited hypothesis must be **active**, i.e. belong to the context of the
  assertion being proved (`VerifyError.inactiveHypothesis`). Without it a proof
  can push a premise belonging to an unrelated `${ … $}` block. `Provable`'s
  `float` and `essential` rules quantify over `ctx`, so a derivation simply
  cannot cite an out-of-scope hypothesis; the checker has to match.

  Note that this is a test against `Assertion.context`, the *active* data, not
  against `Assertion.frame`, the mandatory subset. The two differ on floating
  hypotheses — a proof may cite the `$f` of a dummy variable that appears
  nowhere in the statement — and testing against the frame would reject a large
  fraction of the upstream corpus. `Assertion.context` documents the split.

The final section proves that distinct-variable conditions **compose**
(`disjointsOk_comp`) and that substitution is therefore admissible on
derivations (`Provable.subst`). That is the cut rule for this calculus, and it
is the step a conservativity result — every theorem of a verified database is
derivable from its axioms alone — would be built on. See the closing remark for
what remains.
-/

namespace Nucleus.Metamath

/-- Why a proof failed to check. -/
inductive VerifyError where
  /-- The compressed letter block did not decode. -/
  | decode (e : DecodeError)
  /-- The proof cites a label that is not in the database. -/
  | unknownLabel (l : Sym)
  /-- The proof cites a hypothesis that is not active in the current frame. -/
  | inactiveHypothesis (l : Sym)
  /-- The proof cites an assertion that does not occur earlier in the database. -/
  | forwardReference (l : Sym)
  /-- Applying an assertion needed more arguments than the stack held. -/
  | stackUnderflow (l : Sym)
  /-- A popped argument did not match the applied assertion's floating hypothesis. -/
  | floatMismatch (l : Sym)
  /-- A popped argument did not match the applied assertion's essential hypothesis. -/
  | essentialMismatch (l : Sym)
  /-- A distinct-variable condition of the applied assertion was not discharged. -/
  | disjointViolation (l : Sym)
  /-- A `Z` marker with nothing on the stack to save. -/
  | emptySave
  /-- A heap backreference past the end of the heap. -/
  | heapOutOfRange (idx : Nat)
  /-- The proof did not end with exactly one expression on the stack. -/
  | stackResidue (l : Sym) (count : Nat)
  /-- The proof produced something other than the claimed statement. -/
  | resultMismatch (l : Sym)
  deriving DecidableEq, Repr, Inhabited

/-- The checker's state: an expression stack with the top at the head, and the
compressed-proof heap, indexed from the front in save order. -/
structure Machine where
  /-- The proof stack; the head is the top. -/
  stack : List Expr
  /-- Expressions saved by `Z` markers, in save order. -/
  heap : List Expr
  deriving DecidableEq, Repr, Inhabited

/-- Pop `n` arguments, returning them in **frame order** (the order the
mandatory hypotheses are declared in) together with the rest of the stack. -/
def popArgs (n : Nat) (stack : List Expr) : Option (List Expr × List Expr) :=
  if n ≤ stack.length then some ((stack.take n).reverse, stack.drop n) else none

theorem popArgs_mem {n : Nat} {stack args rest : List Expr}
    (h : popArgs n stack = some (args, rest)) :
    (∀ e ∈ args, e ∈ stack) ∧ (∀ e ∈ rest, e ∈ stack) := by
  unfold popArgs at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hargs, hrest⟩ := h
    subst hargs
    subst hrest
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · exact List.mem_of_mem_take (List.mem_reverse.mp he)
    · exact List.mem_of_mem_drop he
  · exact absurd h (by simp)

/-- Build the substitution an application induces: each floating hypothesis'
variable is bound to the body of the argument popped for it. -/
def buildSubst (floats : List FloatHyp) (args : List Expr) : Subst :=
  (floats.zip args).map fun p => (p.1.var, p.2.body)

/-- Every mandatory hypothesis, substituted, reproduces the argument popped for
it.

Checking this — rather than only checking typecodes and trusting the
substitution the floats induced — is what makes the soundness proof immediate:
the check *is* the premise `Provable.apply` needs. It is also strictly stronger
than a typecode comparison, because it rejects a malformed frame whose floating
hypotheses repeat a variable. -/
def matchesArgs (σ : Subst) (schemas args : List Expr) : Bool :=
  schemas.length == args.length && (schemas.zip args).all fun p => applySubst σ p.1 == p.2

private theorem matchesArgs_mem_aux (σ : Subst) :
    ∀ (schemas args : List Expr), schemas.length = args.length →
      (∀ p ∈ schemas.zip args, applySubst σ p.1 = p.2) →
      ∀ s ∈ schemas, ∃ a ∈ args, applySubst σ s = a := by
  intro schemas
  induction schemas with
  | nil =>
    intro _ _ _ s hs
    simp at hs
  | cons schema schemas ih =>
    intro args hlen hall s hs
    match args with
    | [] => simp at hlen
    | arg :: args =>
      rcases List.mem_cons.mp hs with rfl | hs'
      · refine ⟨arg, List.mem_cons_self, ?_⟩
        exact hall (s, arg) (by rw [List.zip_cons_cons]; exact List.mem_cons_self)
      · obtain ⟨a, ha, hsa⟩ := ih args (by simpa using hlen)
          (fun p hp => hall p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp)) s hs'
        exact ⟨a, List.mem_cons_of_mem _ ha, hsa⟩

theorem matchesArgs_mem {σ : Subst} {schemas args : List Expr}
    (h : matchesArgs σ schemas args = true) {s : Expr} (hs : s ∈ schemas) :
    ∃ a ∈ args, applySubst σ s = a := by
  simp only [matchesArgs, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact matchesArgs_mem_aux σ schemas args h.1 h.2 s hs

/-- The checks an application must pass, given the arguments already popped and
split into the floating and essential halves.

Split out from `applyAssertion` so that each check is a separate `if` on an
already-bound substitution — the shape the soundness proof case-splits on. -/
def checkAndPush (db : Database) (ctx : Frame) (target : Assertion) (σ : Subst)
    (floatArgs essArgs rest : List Expr) : Except VerifyError (List Expr) :=
  if !matchesArgs σ (target.frame.floats.map FloatHyp.expr) floatArgs then
    .error (.floatMismatch target.label)
  else if !matchesArgs σ (target.frame.essentials.map Hypothesis.expr) essArgs then
    .error (.essentialMismatch target.label)
  else if !disjointsOk db.isVariable ctx.disjoints σ target.frame.disjoints then
    .error (.disjointViolation target.label)
  else
    .ok (applySubst σ target.conclusion :: rest)

/-- Apply an assertion: pop its mandatory hypotheses, rebuild the substitution
from the floats, re-check the floats and the essentials against it, discharge
the distinct-variable conditions in `ctx`, and push the substituted
conclusion. -/
def applyAssertion (db : Database) (ctx : Frame) (target : Assertion) (stack : List Expr) :
    Except VerifyError (List Expr) :=
  match popArgs target.frame.mandatoryCount stack with
  | none => .error (.stackUnderflow target.label)
  | some (args, rest) =>
    checkAndPush db ctx target
      (buildSubst target.frame.floats (args.take target.frame.floats.length))
      (args.take target.frame.floats.length)
      (args.drop target.frame.floats.length)
      rest

/-- Execute one label step: push an active hypothesis, or apply an earlier
assertion. Both side conditions the Rust checker is missing live here. -/
def resolveLabel (db : Database) (idx : Nat) (ctx : Frame) (l : Sym) (stack : List Expr) :
    Except VerifyError (List Expr) :=
  match db.indexOfLabel l with
  | none => .error (.unknownLabel l)
  | some j =>
    match db.statementAt j with
    | some (.float f) =>
        if f ∈ ctx.floats then .ok (f.expr :: stack) else .error (.inactiveHypothesis l)
    | some (.essential h) =>
        if h ∈ ctx.essentials then .ok (h.expr :: stack) else .error (.inactiveHypothesis l)
    | some (.assert target) =>
        if j < idx then applyAssertion db ctx target stack else .error (.forwardReference l)
    | _ => .error (.unknownLabel l)

/-- Execute one decoded proof step. -/
def runStep (db : Database) (idx : Nat) (ctx : Frame) (m : Machine) :
    ProofStep → Except VerifyError Machine
  | .label l =>
    match resolveLabel db idx ctx l m.stack with
    | .error e => .error e
    | .ok stack => .ok { m with stack := stack }
  | .save =>
    match m.stack with
    | [] => .error .emptySave
    | top :: _ => .ok { m with heap := m.heap ++ [top] }
  | .heap k =>
    match m.heap[k]? with
    | none => .error (.heapOutOfRange k)
    | some e => .ok { m with stack := e :: m.stack }

/-- Replay a proof-step sequence. -/
def run (db : Database) (idx : Nat) (ctx : Frame) :
    List ProofStep → Machine → Except VerifyError Machine
  | [], m => .ok m
  | step :: rest, m =>
    match runStep db idx ctx m step with
    | .error e => .error e
    | .ok m' => run db idx ctx rest m'

/-- Check the assertion at source position `idx`. An axiom checks trivially.

`a.context` — the mandatory hypotheses with the *full* in-scope `$d` set — is
the frame the proof runs in, not `a.frame`. See `Assertion.scopeDisjoints`. -/
def verifyAssertionAt (db : Database) (idx : Nat) (a : Assertion) : Except VerifyError Unit :=
  match a.proof with
  | none => .ok ()
  | some _ =>
    match a.steps with
    | .error e => .error (.decode e)
    | .ok steps =>
      match run db idx a.context steps ⟨[], []⟩ with
      | .error e => .error e
      | .ok m =>
        match m.stack with
        | [result] => if result = a.conclusion then .ok () else .error (.resultMismatch a.label)
        | residue => .error (.stackResidue a.label residue.length)

/-- Check whatever is at source position `i`, if it is a theorem. -/
def verifyIndex (db : Database) (i : Nat) : Except VerifyError Unit :=
  match db.statementAt i with
  | some (.assert a) => verifyAssertionAt db i a
  | _ => .ok ()

/-- Check the listed source positions in order. -/
def verifyIndices (db : Database) : List Nat → Except VerifyError Unit
  | [] => .ok ()
  | i :: rest =>
    match verifyIndex db i with
    | .error e => .error e
    | .ok () => verifyIndices db rest

/-- Check every theorem in the database. -/
def verifyDatabase (db : Database) : Except VerifyError Unit :=
  verifyIndices db (List.range db.statements.length)

/-! ## Soundness -/

/-- Every expression the machine holds is derivable within the citation window
`idx`. This is the invariant the replay preserves. -/
def MachineOk (db : Database) (idx : Nat) (ctx : Frame) (m : Machine) : Prop :=
  (∀ e ∈ m.stack, Provable db (· < idx) ctx e) ∧ (∀ e ∈ m.heap, Provable db (· < idx) ctx e)

theorem applyAssertion_sound {db : Database} {idx j : Nat} {ctx : Frame} {target : Assertion}
    {stack stack' : List Expr}
    (found : db.statementAt j = some (.assert target)) (hj : j < idx)
    (hstack : ∀ e ∈ stack, Provable db (· < idx) ctx e)
    (h : applyAssertion db ctx target stack = .ok stack') :
    ∀ e ∈ stack', Provable db (· < idx) ctx e := by
  unfold applyAssertion at h
  split at h
  · exact absurd h (by simp)
  · rename_i args rest hpop
    obtain ⟨hargs, hrest⟩ := popArgs_mem hpop
    unfold checkAndPush at h
    split at h
    · exact absurd h (by simp)
    · rename_i hfloats
      split at h
      · exact absurd h (by simp)
      · rename_i hess
        split at h
        · exact absurd h (by simp)
        · rename_i hdisj
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hfloats hess hdisj
          simp only [Except.ok.injEq] at h
          subst h
          set σ := buildSubst target.frame.floats (args.take target.frame.floats.length) with hσ
          have hfloatProv : ∀ f ∈ target.frame.floats,
              Provable db (· < idx) ctx (applySubst σ f.expr) := by
            intro f hf
            obtain ⟨a, ha, hfa⟩ := matchesArgs_mem hfloats (List.mem_map_of_mem hf)
            rw [hfa]
            exact hstack a (hargs a (List.mem_of_mem_take ha))
          have hessProv : ∀ hyp ∈ target.frame.essentials,
              Provable db (· < idx) ctx (applySubst σ hyp.expr) := by
            intro hyp hh
            obtain ⟨a, ha, hha⟩ := matchesArgs_mem hess (List.mem_map_of_mem hh)
            rw [hha]
            exact hstack a (hargs a (List.mem_of_mem_drop ha))
          intro e he
          rcases List.mem_cons.mp he with rfl | he'
          · exact .apply found hj hfloatProv hessProv hdisj
          · exact hstack e (hrest e he')

theorem resolveLabel_sound {db : Database} {idx : Nat} {ctx : Frame} {l : Sym}
    {stack stack' : List Expr}
    (hstack : ∀ e ∈ stack, Provable db (· < idx) ctx e)
    (h : resolveLabel db idx ctx l stack = .ok stack') :
    ∀ e ∈ stack', Provable db (· < idx) ctx e := by
  unfold resolveLabel at h
  split at h
  · exact absurd h (by simp)
  · rename_i j _
    split at h
    · rename_i f _
      split at h
      · rename_i hmem
        simp only [Except.ok.injEq] at h
        subst h
        intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · exact .float hmem
        · exact hstack e he'
      · exact absurd h (by simp)
    · rename_i hyp _
      split at h
      · rename_i hmem
        simp only [Except.ok.injEq] at h
        subst h
        intro e he
        rcases List.mem_cons.mp he with rfl | he'
        · exact .essential hmem
        · exact hstack e he'
      · exact absurd h (by simp)
    · rename_i target hfound
      split at h
      · rename_i hj
        exact applyAssertion_sound hfound hj hstack h
      · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem runStep_sound {db : Database} {idx : Nat} {ctx : Frame} {m m' : Machine} {step : ProofStep}
    (hm : MachineOk db idx ctx m) (h : runStep db idx ctx m step = .ok m') :
    MachineOk db idx ctx m' := by
  obtain ⟨hstack, hheap⟩ := hm
  cases step with
  | label l =>
    simp only [runStep] at h
    split at h
    · exact absurd h (by simp)
    · rename_i stack hres
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨resolveLabel_sound hstack hres, hheap⟩
  | save =>
    simp only [runStep] at h
    split at h
    · exact absurd h (by simp)
    · rename_i top tail htop
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨hstack, fun e he => ?_⟩
      rcases List.mem_append.mp he with he' | he'
      · exact hheap e he'
      · rw [List.mem_singleton.mp he']
        exact hstack top (by rw [htop]; exact List.mem_cons_self)
  | heap k =>
    simp only [runStep] at h
    split at h
    · exact absurd h (by simp)
    · rename_i e hget
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨fun x hx => ?_, hheap⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hheap x (List.mem_of_getElem? hget)
      · exact hstack x hx'

theorem run_sound {db : Database} {idx : Nat} {ctx : Frame} :
    ∀ {steps : List ProofStep} {m m' : Machine},
      MachineOk db idx ctx m → run db idx ctx steps m = .ok m' → MachineOk db idx ctx m'
  | [], m, m', hm, h => by
    simp only [run, Except.ok.injEq] at h
    exact h ▸ hm
  | step :: rest, m, m', hm, h => by
    unfold run at h
    split at h
    · exact absurd h (by simp)
    · rename_i next hstep
      exact run_sound (runStep_sound hm hstep) h

/-- **Soundness of the checker.** If `verifyAssertionAt` accepts the assertion
at source position `idx`, its conclusion is derivable in its own context from
assertions occurring strictly earlier in the database. -/
theorem verifyAssertionAt_sound {db : Database} {idx : Nat} {a : Assertion}
    (hp : a.proof.isSome) (h : verifyAssertionAt db idx a = .ok ()) :
    Provable db (· < idx) a.context a.conclusion := by
  unfold verifyAssertionAt at h
  split at h
  · rename_i hnone
    rw [hnone] at hp
    exact absurd hp (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i steps _
      split at h
      · exact absurd h (by simp)
      · rename_i m hrun
        have hm : MachineOk db idx a.context m :=
          run_sound ⟨by simp, by simp⟩ hrun
        split at h
        · rename_i result hstack
          split at h
          · rename_i hEq
            rw [← hEq]
            exact hm.1 result (by rw [hstack]; exact List.mem_cons_self)
          · exact absurd h (by simp)
        · exact absurd h (by simp)

theorem verifyIndices_sound {db : Database} :
    ∀ {idxs : List Nat}, verifyIndices db idxs = .ok () →
      ∀ {i : Nat}, i ∈ idxs → ∀ {a : Assertion}, db.statementAt i = some (.assert a) →
        a.proof.isSome → Provable db (· < i) a.context a.conclusion
  | [], _, _, hmem, _, _, _ => by simp at hmem
  | j :: rest, h, i, hmem, a, hstmt, hp => by
    unfold verifyIndices at h
    split at h
    · exact absurd h (by simp)
    · rename_i hindex
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · unfold verifyIndex at hindex
        rw [hstmt] at hindex
        exact verifyAssertionAt_sound hp hindex
      · exact verifyIndices_sound h hmem' hstmt hp

/-- **Soundness of the database checker.** Every theorem a verified database
contains is derivable from the assertions preceding it. -/
theorem verifyDatabase_sound {db : Database} (h : verifyDatabase db = .ok ())
    {i : Nat} {a : Assertion} (hstmt : db.statementAt i = some (.assert a))
    (hp : a.proof.isSome) :
    Provable db (· < i) a.context a.conclusion := by
  refine verifyIndices_sound h ?_ hstmt hp
  rw [List.mem_range]
  have hget : db.statements[i]? = some (.assert a) := hstmt
  by_contra hle
  rw [List.getElem?_eq_none (Nat.le_of_not_lt hle)] at hget
  exact absurd hget (by simp)

/-! ## Distinct variables compose, and substitution is admissible -/

theorem disjointDeclared_comm (pairs : List (Sym × Sym)) (x y : Sym) :
    disjointDeclared pairs x y = disjointDeclared pairs y x := by
  simp only [disjointDeclared]
  congr 1
  funext p
  exact Bool.or_comm _ _

theorem exists_of_disjointDeclared {pairs : List (Sym × Sym)} {x y : Sym}
    (h : disjointDeclared pairs x y = true) :
    ∃ p ∈ pairs, (p.1 = x ∧ p.2 = y) ∨ (p.1 = y ∧ p.2 = x) := by
  simp only [disjointDeclared, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq] at h
  exact h

/-- **Distinct-variable conditions compose.**

If applying an assertion under `τ` is legal in the frame whose `$d` set is
`inner`, and `σ` in turn discharges every pair of `inner` in the outer context
`outer`, then applying that assertion under the composite `τ.comp σ` is legal in
`outer`.

This is the substantive part of Metamath's `$d` metatheory: it says the
obligations really do propagate outwards, so that discharging them one level at
a time is equivalent to discharging the composite all at once. The hypothesis
that `σ` binds only variables is not decoration — without it a constant could be
rewritten into a variable and manufacture an undeclared coincidence. -/
theorem disjointsOk_comp {isVar : Sym → Bool} {σ τ : Subst} {inner outer pairs : List (Sym × Sym)}
    (hσ : σ.MapsVariables isVar)
    (hτ : disjointsOk isVar inner τ pairs = true)
    (hcomp : disjointsOk isVar outer σ inner = true) :
    disjointsOk isVar outer (τ.comp σ) pairs = true := by
  rw [disjointsOk_iff]
  intro p hp
  rw [disjointOk_iff]
  intro u hu v hv
  rw [Subst.image_comp] at hu hv
  obtain ⟨x, hx, hux⟩ := mem_bodyVars_substBody hσ hu
  obtain ⟨y, hy, hvy⟩ := mem_bodyVars_substBody hσ hv
  obtain ⟨hxy, hdecl⟩ :=
    (disjointOk_iff.mp ((disjointsOk_iff.mp hτ) p hp)) x hx y hy
  obtain ⟨q, hq, hcase⟩ := exists_of_disjointDeclared hdecl
  have hqOk := disjointOk_iff.mp ((disjointsOk_iff.mp hcomp) q hq)
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hqOk
    exact hqOk u hux v hvy
  · rw [h1, h2] at hqOk
    obtain ⟨hne, hd⟩ := hqOk v hvy u hux
    exact ⟨fun hEq => hne hEq.symm, by rw [disjointDeclared_comm]; exact hd⟩

/-- **Substitution is admissible on derivations** — the cut rule for this
calculus.

`Provable.apply` lets an *assertion* be instantiated. This says the same of any
derivation: if every mandatory hypothesis of `inner`, substituted by `σ`, is
derivable in `outer`, and `σ` discharges `inner`'s distinct-variable conditions
there, then every consequence of `inner` transports to `outer` under `σ`.

It is proved by replaying the derivation with `σ` pushed through each step;
`disjointsOk_comp` is what keeps the `$d` obligations discharged as the
substitutions compose. -/
theorem Provable.subst {db : Database} {u : Nat → Prop} {inner outer : Frame} {σ : Subst}
    {e : Expr}
    (hσ : σ.MapsVariables db.isVariable)
    (hfloats : ∀ f ∈ inner.floats, Provable db u outer (applySubst σ f.expr))
    (hess : ∀ h ∈ inner.essentials, Provable db u outer (applySubst σ h.expr))
    (hd : disjointsOk db.isVariable outer.disjoints σ inner.disjoints = true)
    (d : Provable db u inner e) :
    Provable db u outer (applySubst σ e) := by
  induction d with
  | float mem => exact hfloats _ mem
  | essential mem => exact hess _ mem
  | apply found allowed _ _ disjoints ihf ihe =>
    rw [applySubst_applySubst]
    refine .apply found allowed (fun f hf => ?_) (fun h hh => ?_)
      (disjointsOk_comp hσ disjoints hd)
    · rw [← applySubst_applySubst]
      exact ihf f hf
    · rw [← applySubst_applySubst]
      exact ihe h hh

/-!
## What remains

`Provable.subst` is the tool a **conservativity** theorem needs: that a verified
database's `$p` theorems are derivable from its `$a` axioms alone, so citing a
theorem is never more than an abbreviation. Replacing an `apply` step that cites
a theorem by that theorem's own derivation is exactly a substitution.

The obstacle is not the cut rule but the `$d` gap between `Assertion.frame` and
`Assertion.scopeDisjoints`. An application discharges only `frame.disjoints`,
the mandatory subset, while the cited theorem's own derivation lives in a
context carrying `scopeDisjoints`, which may constrain dummy variables that
occur nowhere in its statement. Bridging the two requires renaming those dummies
apart from the caller's variables — a genuine argument, not bookkeeping, and the
natural next piece of this development.
-/

end Nucleus.Metamath
