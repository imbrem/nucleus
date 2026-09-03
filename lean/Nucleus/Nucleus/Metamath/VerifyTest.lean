import Nucleus.Metamath.Verify

/-!
# Worked databases

Concrete databases the checker is run on, evaluated at elaboration time. Two
kinds:

* `demo0`, the database from the Metamath book, whose theorem `th1` checks —
  the same fixture `crates/logic/metamath/tests/fixtures/demo0.mm` uses; and
* counterexample databases that both the Rust checker at
  `crates/logic/metamath` and this specification reject. Each would prove a
  statement that does not follow, so these are regression witnesses for the two
  side conditions in `Nucleus.Metamath.Verify`.

Frames are given explicitly rather than derived from `${ … $}` scoping, because
scope resolution is the parser's job and the parser is deliberately not
formalised — see `Nucleus.Metamath.Database`.
-/

namespace Nucleus.Metamath

/-! ## demo0 -/

private def demo0Floats : List FloatHyp :=
  [⟨"tt", "term", "t"⟩, ⟨"tr", "term", "r"⟩, ⟨"ts", "term", "s"⟩,
   ⟨"wp", "wff", "P"⟩, ⟨"wq", "wff", "Q"⟩]

private def frameOf (floats : List FloatHyp) (essentials : List Hypothesis) : Frame :=
  { floats := floats, essentials := essentials, disjoints := [] }

private def axiom' (label : Sym) (conclusion : Expr) (frame : Frame) : Statement :=
  .assert { label := label, conclusion := conclusion, frame := frame,
            proof := none, scopeFloats := frame.floats, scopeDisjoints := [] }

/-- The Metamath book's `demo0` database: a two-symbol term language, an
implication-shaped `wff` former, modus ponens, and the theorem `th1 : |- t = t`
with its reverse-Polish proof. -/
def demo0 : Database where
  symbols :=
    [("0", .constant), ("+", .constant), ("=", .constant), ("->", .constant),
     ("(", .constant), (")", .constant), ("term", .constant), ("wff", .constant),
     ("|-", .constant),
     ("t", .var), ("r", .var), ("s", .var), ("P", .var), ("Q", .var)]
  statements :=
    [ .constant ["0", "+", "=", "->", "(", ")", "term", "wff", "|-"]
    , .var ["t", "r", "s", "P", "Q"]
    , .float ⟨"tt", "term", "t"⟩
    , .float ⟨"tr", "term", "r"⟩
    , .float ⟨"ts", "term", "s"⟩
    , .float ⟨"wp", "wff", "P"⟩
    , .float ⟨"wq", "wff", "Q"⟩
    , axiom' "tze" ⟨"term", ["0"]⟩ (frameOf [] [])
    , axiom' "tpl" ⟨"term", ["(", "t", "+", "r", ")"]⟩
        (frameOf [demo0Floats[0]!, demo0Floats[1]!] [])
    , axiom' "weq" ⟨"wff", ["t", "=", "r"]⟩
        (frameOf [demo0Floats[0]!, demo0Floats[1]!] [])
    , axiom' "wim" ⟨"wff", ["(", "P", "->", "Q", ")"]⟩
        (frameOf [demo0Floats[3]!, demo0Floats[4]!] [])
    , axiom' "a1"
        ⟨"|-", ["(", "t", "=", "r", "->", "(", "t", "=", "s", "->", "r", "=", "s", ")", ")"]⟩
        (frameOf [demo0Floats[0]!, demo0Floats[1]!, demo0Floats[2]!] [])
    , axiom' "a2" ⟨"|-", ["(", "t", "+", "0", ")", "=", "t"]⟩
        (frameOf [demo0Floats[0]!] [])
    , .essential ⟨"min", ⟨"|-", ["P"]⟩⟩
    , .essential ⟨"maj", ⟨"|-", ["(", "P", "->", "Q", ")"]⟩⟩
    , axiom' "mp" ⟨"|-", ["Q"]⟩
        (frameOf [demo0Floats[3]!, demo0Floats[4]!]
          [⟨"min", ⟨"|-", ["P"]⟩⟩, ⟨"maj", ⟨"|-", ["(", "P", "->", "Q", ")"]⟩⟩])
    , .assert
        { label := "th1"
          conclusion := ⟨"|-", ["t", "=", "t"]⟩
          frame := frameOf [demo0Floats[0]!] []
          proof := some (.normal
            ["tt", "tze", "tpl", "tt", "weq", "tt", "tt", "weq", "tt", "a2",
             "tt", "tze", "tpl", "tt", "weq", "tt", "tze", "tpl", "tt", "weq",
             "tt", "tt", "weq", "wim", "tt", "a2", "tt", "tze", "tpl", "tt",
             "tt", "a1", "mp", "mp"])
          scopeFloats := demo0Floats
          scopeDisjoints := [] } ]

set_option maxRecDepth 100000 in
/-- `demo0` checks. -/
example : verifyDatabase demo0 = .ok () := by decide

/-! ## Rejected databases

Each is minimal: one variable, one floating hypothesis, and a "proof" of the
unrestricted `|- ph`. If any of them checked, every statement would. -/

private def wffPh : List (Sym × SymbolKind) :=
  [("wff", .constant), ("|-", .constant), ("ph", .var)]

private def wphFloat : FloatHyp := ⟨"wph", "wff", "ph"⟩

private def phFrame : Frame := frameOf [wphFloat] []

private def theorem' (label : Sym) (proof : List Sym) (frame : Frame) : Statement :=
  .assert { label := label, conclusion := ⟨"|-", ["ph"]⟩, frame := frame,
            proof := some (.normal proof), scopeFloats := frame.floats,
            scopeDisjoints := [] }

/-- A theorem citing itself.

The corresponding Rust fixture rejects the `.mm` source
```metamath
$c wff |- $.  $v ph $.  wph $f wff ph $.
a $p |- ph $= wph a $.
```
with `MmError::ForwardReference`. -/
def selfCiting : Database where
  symbols := wffPh
  statements :=
    [ .constant ["wff", "|-"], .var ["ph"], .float wphFloat
    , theorem' "a" ["wph", "a"] phFrame ]

example : verifyDatabase selfCiting = .error (.forwardReference "a") := by decide

/-- Two theorems citing each other. Neither proof is well founded. -/
def mutuallyCiting : Database where
  symbols := wffPh
  statements :=
    [ .constant ["wff", "|-"], .var ["ph"], .float wphFloat
    , theorem' "a" ["wph", "b"] phFrame
    , theorem' "b" ["wph", "a"] phFrame ]

example : verifyDatabase mutuallyCiting = .error (.forwardReference "b") := by decide

/-- A theorem helping itself to another block's premise.

The `$e` belongs to the `${ … $}` block around `mp`; `bad` is outside it, so
`h1` is not among `bad`'s mandatory hypotheses. Note the citation-order check
does not catch this — `h1` *is* earlier — so both checkers perform a separate
active-hypothesis test. -/
def outOfScopeHypothesis : Database where
  symbols := wffPh
  statements :=
    [ .constant ["wff", "|-"], .var ["ph"], .float wphFloat
    , .essential ⟨"h1", ⟨"|-", ["ph"]⟩⟩
    , axiom' "mp" ⟨"|-", ["ph"]⟩ (frameOf [wphFloat] [⟨"h1", ⟨"|-", ["ph"]⟩⟩])
    , theorem' "bad" ["h1"] phFrame ]

example : verifyDatabase outOfScopeHypothesis = .error (.inactiveHypothesis "h1") := by
  decide

/-- Citing one's *own* essential hypothesis is of course fine, and must stay
fine — the active-hypothesis check is a frame-membership test, not a ban. -/
def ownHypothesis : Database where
  symbols := wffPh
  statements :=
    [ .constant ["wff", "|-"], .var ["ph"], .float wphFloat
    , .essential ⟨"h1", ⟨"|-", ["ph"]⟩⟩
    , .assert
        { label := "good", conclusion := ⟨"|-", ["ph"]⟩
          frame := frameOf [wphFloat] [⟨"h1", ⟨"|-", ["ph"]⟩⟩]
          proof := some (.normal ["h1"]), scopeFloats := [wphFloat]
          scopeDisjoints := [] } ]

example : verifyDatabase ownHypothesis = .ok () := by decide

/-! ## Dummy variables

The active/mandatory distinction `Assertion.context` draws is not a technicality.
A proof routinely pushes the floating hypothesis of a *dummy* variable — one
active where the theorem is stated but absent from its statement, and so absent
from its mandatory frame. The upstream `set.mm` does this over two hundred
thousand times. A checker that tested citations against `Assertion.frame` would
reject all of them. -/

private def wpsFloat : FloatHyp := ⟨"wps", "wff", "ps"⟩

private def wffPhPs : List (Sym × SymbolKind) :=
  [("wff", .constant), ("|-", .constant), ("ph", .var), ("ps", .var)]

/-- `th` is stated with only `ph` in it, so its mandatory frame carries only
`wph`; but `wps` is active, and the proof cites it to instantiate `weaken`'s
second parameter. This must verify. -/
def dummyFloat : Database where
  symbols := wffPhPs
  statements :=
    [ .constant ["wff", "|-"], .var ["ph", "ps"]
    , .float wphFloat
    , .float wpsFloat
    , axiom' "weaken" ⟨"|-", ["ph"]⟩ (frameOf [wphFloat, wpsFloat] [])
    , .assert
        { label := "th", conclusion := ⟨"|-", ["ph"]⟩
          frame := frameOf [wphFloat] []
          proof := some (.normal ["wph", "wps", "weaken"])
          scopeFloats := [wphFloat, wpsFloat]
          scopeDisjoints := [] } ]

example : verifyDatabase dummyFloat = .ok () := by decide

/-!
The tempting statement that every checked theorem is derivable from `$a`
assertions in its *mandatory* frame is false.  A scope-local dummy can be
required to satisfy an axiom's `$d` condition even though that condition quite
correctly disappears from the theorem's public frame.

`dummyDisjoint` is the smallest witness.  Its theorem checks in the active
context containing `wps` and `$d ph ps`.  In the mandatory frame, however, the
only derivable `wff` is `ph`; instantiating both inputs of `apart` with it
violates the axiom's distinct-variable condition.  Fresh-name renaming cannot
fix the missing floating hypothesis: a fresh variable is not derivable in the
mandatory frame.
-/
def dummyDisjoint : Database where
  symbols := wffPhPs
  statements :=
    [ .constant ["wff", "|-"]
    , .var ["ph", "ps"]
    , .float wphFloat
    , .float wpsFloat
    , axiom' "apart" ⟨"|-", ["ph"]⟩
        { floats := [wphFloat, wpsFloat], essentials := [], disjoints := [("ph", "ps")] }
    , .assert
        { label := "th", conclusion := ⟨"|-", ["ph"]⟩
          frame := frameOf [wphFloat] []
          proof := some (.normal ["wph", "wps", "apart"])
          scopeFloats := [wphFloat, wpsFloat]
          scopeDisjoints := [("ph", "ps")] } ]

example : verifyDatabase dummyDisjoint = .ok () := by decide

/-- In the mandatory frame of `dummyDisjoint.th`, every axiom-only derivable
`wff` is the sole active floating hypothesis `wff ph`. -/
private theorem dummyDisjoint_wff {e : Expr}
    (d : Provable dummyDisjoint (fun i => i = 4) (frameOf [wphFloat] []) e)
    (ht : e.typecode = "wff") : e = wphFloat.expr := by
  induction d with
  | float mem =>
      simp only [frameOf, List.mem_singleton] at mem
      subst mem
      rfl
  | essential mem => simp [frameOf] at mem
  | apply found allowed floats essentials disjoints ihf ihe =>
      rename_i target σ
      subst allowed
      have found' : axiom' "apart" ⟨"|-", ["ph"]⟩
          { floats := [wphFloat, wpsFloat], essentials := [],
            disjoints := [("ph", "ps")] } = .assert target := by
        simpa [dummyDisjoint, Database.statementAt] using found
      cases found'
      simp [applySubst] at ht

private theorem dummyDisjoint_no_turnstile {e : Expr}
    (d : Provable dummyDisjoint (fun i => i = 4) (frameOf [wphFloat] []) e)
    (ht : e.typecode = "|-") : False := by
  induction d with
  | float mem =>
      simp only [frameOf, List.mem_singleton] at mem
      subst mem
      simp [wphFloat, FloatHyp.expr] at ht
  | essential mem => simp [frameOf] at mem
  | apply found allowed floats essentials disjoints ihf ihe =>
      rename_i target σ
      subst allowed
      have found' : axiom' "apart" ⟨"|-", ["ph"]⟩
          { floats := [wphFloat, wpsFloat], essentials := [],
            disjoints := [("ph", "ps")] } = .assert target := by
        simpa [dummyDisjoint, Database.statementAt] using found
      cases found'
      have hph := dummyDisjoint_wff (floats wphFloat (by simp)) rfl
      have hps := dummyDisjoint_wff (floats wpsFloat (by simp)) rfl
      have hph' : σ.image "ph" = ["ph"] := by
        simpa [FloatHyp.expr, applySubst, wphFloat] using hph
      have hps' : σ.image "ps" = ["ph"] := by
        simpa [FloatHyp.expr, applySubst, wpsFloat, wphFloat] using hps
      change disjointsOk dummyDisjoint.isVariable [] σ [("ph", "ps")] = true at disjoints
      simp only [disjointsOk, List.all_cons, List.all_nil, Bool.and_true] at disjoints
      unfold disjointOk at disjoints
      rw [hph', hps'] at disjoints
      have hvar : dummyDisjoint.isVariable "ph" = true := by decide
      simp [bodyVars, hvar] at disjoints

/-- Consequently the checked theorem is not derivable from the database's sole
`$a` assertion in its mandatory frame.  The conservativity statement needs a
derivability notion with locally bound dummy variables, rather than a renaming
lemma for the current fixed-context `Provable`. -/
example :
    ¬ Provable dummyDisjoint (fun i => i = 4) (frameOf [wphFloat] []) ⟨"|-", ["ph"]⟩ := by
  intro d
  exact dummyDisjoint_no_turnstile d rfl

/-- The same proof, with `wps` **not** active where `th` is stated, is
rejected. Active membership is what the checker tests, and it is a real test. -/
def inactiveFloat : Database where
  symbols := wffPhPs
  statements :=
    [ .constant ["wff", "|-"], .var ["ph", "ps"]
    , .float wphFloat
    , .float wpsFloat
    , axiom' "weaken" ⟨"|-", ["ph"]⟩ (frameOf [wphFloat, wpsFloat] [])
    , .assert
        { label := "th", conclusion := ⟨"|-", ["ph"]⟩
          frame := frameOf [wphFloat] []
          proof := some (.normal ["wph", "wps", "weaken"])
          scopeFloats := [wphFloat]
          scopeDisjoints := [] } ]

example : verifyDatabase inactiveFloat = .error (.inactiveHypothesis "wps") := by decide

/-! ## The compressed-proof codec -/

example : decodeInt "A".toList = some (1, []) := by decide
example : decodeInt "T".toList = some (20, []) := by decide
example : decodeInt "UA".toList = some (21, []) := by decide
example : decodeInt "YT".toList = some (120, []) := by decide
example : decodeInt "UUA".toList = some (121, []) := by decide

/-- The letter block the Rust decoder overflows on: eighty `U`s and a
terminal `A`. Here it is simply a very large `Nat`. -/
example : (decodeInt (List.replicate 80 'U' ++ ['A'])).isSome := by decide


end Nucleus.Metamath
