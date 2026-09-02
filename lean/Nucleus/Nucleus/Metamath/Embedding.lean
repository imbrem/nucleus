import Nucleus.Metamath.VerifyTest

/-!
# Deep-embedding result and provenance

This module packages the executable Metamath derivability theorem with the
attested coordinates an output database records. It is the first worked slice
of the design in `docs/metamath-hol-embedding.md`.

`EmbeddedTheorem` contains the impredicative `HolDerivable` formula, not a
native interpretation of the Metamath conclusion. The digest bytes are data
supplied by the signed corpus layer; no hash function or parser is trusted
here.
-/

namespace Nucleus.Metamath

set_option linter.style.nativeDecide false

/-- Closure conditions for a candidate set of derivable expressions.

This is the rule package quantified over by `HolDerivable`. Every argument is
first-order embedded Metamath data except `candidate` itself. -/
structure MetalogicClosed (db : Database) (usable : Nat → Prop) (ctx : Frame)
    (candidate : Expr → Prop) : Prop where
  float : ∀ f ∈ ctx.floats, candidate f.expr
  essential : ∀ h ∈ ctx.essentials, candidate h.expr
  application : ∀ {i : Nat} {a : Assertion} {σ : Subst},
    db.statementAt i = some (.assert a) → usable i →
    (∀ f ∈ a.frame.floats, candidate (applySubst σ f.expr)) →
    (∀ h ∈ a.frame.essentials, candidate (applySubst σ h.expr)) →
    disjointsOk db.isVariable ctx.disjoints σ a.frame.disjoints = true →
    candidate (applySubst σ a.conclusion)

/-- Impredicative HOL encoding of Metamath derivability: an expression belongs
to every set closed under the Metamath rules.

Unlike the inductive Lean specification `Provable`, this definition has the
shape emitted as a HOL-omega formula: universal quantification over a predicate
on encoded expressions followed by the three closure obligations. -/
def HolDerivable (db : Database) (usable : Nat → Prop) (ctx : Frame)
    (expression : Expr) : Prop :=
  ∀ candidate, MetalogicClosed db usable ctx candidate → candidate expression

/-- The inductive executable specification and the impredicative HOL encoding
state the same derivability relation. -/
theorem provable_iff_holDerivable {db : Database} {usable : Nat → Prop}
    {ctx : Frame} {expression : Expr} :
    Provable db usable ctx expression ↔ HolDerivable db usable ctx expression := by
  constructor
  · intro derivation candidate closed
    induction derivation with
    | float mem => exact closed.float _ mem
    | essential mem => exact closed.essential _ mem
    | apply found allowed _ _ disjoints floats essentials =>
      exact closed.application found allowed floats essentials disjoints
  · intro derivation
    exact derivation (Provable db usable ctx)
      { float := fun _ mem => .float mem
        essential := fun _ mem => .essential mem
        application := fun found allowed floats essentials disjoints =>
          .apply found allowed floats essentials disjoints }

/-- A 256-bit content address represented independently of a hash algorithm. -/
structure CorpusAddress where
  bytes : List UInt8
  size : bytes.length = 32
  deriving Repr

/-- Attested coordinates of one assertion in a signed corpus database. -/
structure Provenance where
  corpus : CorpusAddress
  statementIndex : Nat
  label : Sym
  deriving Repr

/-- A checked deep-embedding result linked to its source assertion.

The database and assertion are data. Authority is the `derivation` field: the
impredicative formula encoding the embedded Metamath metalogic. -/
structure EmbeddedTheorem (db : Database) where
  position : Nat
  assertion : Assertion
  found : db.statementAt position = some (.assert assertion)
  hasProof : assertion.proof.isSome
  derivation : HolDerivable db (· < position) assertion.context assertion.conclusion
  provenance : Provenance
  provenancePosition : provenance.statementIndex = position
  provenanceLabel : provenance.label = assertion.label

/-- The assertion at `demo0` source position 16, extracted by the same lookup
operation used by the checker. -/
def demo0Th1 : Assertion :=
  match demo0.statementAt 16 with
  | some (.assert assertion) => assertion
  | _ => default

private theorem demo0Th1_found :
    demo0.statementAt 16 = some (.assert demo0Th1) := by
  native_decide

private theorem demo0Th1_hasProof : demo0Th1.proof.isSome := by
  native_decide

private theorem demo0Th1_label : demo0Th1.label = "th1" := by
  native_decide

set_option maxRecDepth 100000 in
private theorem demo0_checked : verifyDatabase demo0 = .ok () := by
  native_decide

/-- The `demo0` theorem `th1`, checked from its strict source prefix and paired
with the caller's exact signed-corpus address.

Issue #405 owns construction of the signed corpus image, so this slice accepts
its address rather than pretending the source fixture hash is a database hash. -/
def demo0Embedded (corpus : CorpusAddress) : EmbeddedTheorem demo0 where
  position := 16
  assertion := demo0Th1
  found := demo0Th1_found
  hasProof := demo0Th1_hasProof
  derivation := provable_iff_holDerivable.mp
    (verifyDatabase_sound demo0_checked demo0Th1_found demo0Th1_hasProof)
  provenance := { corpus := corpus, statementIndex := 16, label := "th1" }
  provenancePosition := rfl
  provenanceLabel := demo0Th1_label.symm

/-- The worked slice's exported theorem has the intended Metamath label. -/
theorem demo0Embedded_label (corpus : CorpusAddress) :
    (demo0Embedded corpus).assertion.label = "th1" := by
  exact demo0Th1_label

end Nucleus.Metamath
