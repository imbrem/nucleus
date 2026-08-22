import Nucleus.Metamath.Expr

/-!
# Metamath databases, frames, and derivability

This file mirrors `crates/logic/metamath/src/database.rs`: the flat, source-order
statement list, the mandatory `Frame` of an assertion, and the distinct-variable
(`$d`) discipline.

It then adds what the Rust crate does not have — a **derivability relation**,
`Provable`. `Provable db usable ctx e` says that `e` follows, in the context
`ctx`, from the assertions of `db` at indices satisfying `usable`, by
hypothesis and by schematic rule application. It is the specification against
which `Nucleus.Metamath.Verify` is proved sound: the checker is not the
definition of "proved", it is an algorithm that only accepts derivable things.

`usable` is a predicate on statement indices rather than a fixed set because
Metamath's citation discipline is positional: a proof may only cite assertions
that occur *earlier* in the database. Threading that as a parameter makes the
side condition explicit instead of implicit in an evaluation order.
-/

namespace Nucleus.Metamath

/-- Classification of a declared symbol. -/
inductive SymbolKind where
  /-- A `$c` constant. -/
  | constant
  /-- A `$v` variable. -/
  | var
  deriving DecidableEq, Repr, Inhabited

/-- A floating hypothesis `label $f typecode var $.`: the declaration that `var`
ranges over expressions of typecode `typecode`. -/
structure FloatHyp where
  /-- The statement label. -/
  label : Sym
  /-- The typecode the variable is declared at. -/
  typecode : Sym
  /-- The variable being typed. -/
  var : Sym
  deriving DecidableEq, Repr, Inhabited

/-- The one-symbol expression a `$f` pushes onto the proof stack. -/
def FloatHyp.expr (f : FloatHyp) : Expr := ⟨f.typecode, [f.var]⟩

/-- An essential hypothesis `label $e <expr> $.`: a logical premise. -/
structure Hypothesis where
  /-- The statement label. -/
  label : Sym
  /-- The premise. -/
  expr : Expr
  deriving DecidableEq, Repr, Inhabited

/-- The mandatory frame of an assertion: the hypotheses it consumes, in
application order, and the distinct-variable conditions it imposes on its
callers. -/
structure Frame where
  /-- Mandatory `$f` hypotheses, in database order. -/
  floats : List FloatHyp
  /-- Mandatory `$e` hypotheses, in database order. -/
  essentials : List Hypothesis
  /-- Mandatory `$d` conditions, as unordered variable pairs. -/
  disjoints : List (Sym × Sym)
  deriving DecidableEq, Repr, Inhabited

/-- How many expressions an application of this frame pops.

The order is all floats (database order) then all essentials (database order),
matching the reference verifier `mmverify.py` and the Rust crate. -/
def Frame.mandatoryCount (frame : Frame) : Nat :=
  frame.floats.length + frame.essentials.length

/-- A `$p` theorem's proof, in either of Metamath's two encodings. -/
inductive Proof where
  /-- A reverse-Polish sequence of labels. -/
  | normal (labels : List Sym)
  /-- A parenthesised label block plus the `A`–`Y`/`Z` letter block. -/
  | compressed (labels : List Sym) (letters : List Char)
  deriving DecidableEq, Repr, Inhabited

/-- An assertion: a `$a` axiom (`proof = none`) or a `$p` theorem. -/
structure Assertion where
  /-- The statement label. -/
  label : Sym
  /-- The asserted conclusion. -/
  conclusion : Expr
  /-- The mandatory frame, i.e. what callers must supply and respect. -/
  frame : Frame
  /-- The proof, for a `$p` theorem. -/
  proof : Option Proof
  /-- **All** `$f` floating hypotheses active where this assertion is stated,
  including those for dummy variables that occur only inside its proof. -/
  scopeFloats : List FloatHyp
  /-- **All** `$d` pairs active in this assertion's scope, over all variables —
  including dummy variables used only inside its proof. -/
  scopeDisjoints : List (Sym × Sym)
  deriving DecidableEq, Repr, Inhabited

/-- The context an assertion's own proof runs in.

Metamath has **two** notions of what an assertion depends on, and conflating
them breaks the checker in one direction or the other:

* `frame` is the *mandatory* data — the hypotheses a caller must supply and the
  `$d` conditions a caller must discharge. It is what propagates when this
  assertion is later applied.
* `context` is the *active* data — everything in scope where the assertion is
  stated. It is what this assertion's own proof may cite.

`context` is the wider of the two, and the excess is exactly the dummy
variables: a proof may introduce a working variable that appears nowhere in the
statement, push its floating hypothesis, and constrain it with a `$d`. Neither
belongs in the mandatory frame — a caller has no business supplying them — but
both must be available while proving. Checking against `frame` instead would
spuriously reject legal proofs; the upstream corpus contains hundreds of
thousands of such citations.

Essentials are the one component where the two coincide, because an assertion's
mandatory essentials are *all* the active ones.

The Rust `Database` at `crates/logic/metamath` currently retains
`scope_disjoints` but not `scope_floats`, which is why its checker cannot fully
enforce that a cited `$f` is active: it has kept half of this distinction. -/
def Assertion.context (a : Assertion) : Frame :=
  { floats := a.scopeFloats
    essentials := a.frame.essentials
    disjoints := a.scopeDisjoints }

/-- A top-level statement, in source order. -/
inductive Statement where
  /-- `$c` constant declaration. -/
  | constant (names : List Sym)
  /-- `$v` variable declaration. -/
  | var (names : List Sym)
  /-- `$f` floating hypothesis. -/
  | float (hyp : FloatHyp)
  /-- `$e` essential hypothesis. -/
  | essential (hyp : Hypothesis)
  /-- `$d` distinct-variable restriction. -/
  | disjoint (names : List Sym)
  /-- `$a` axiom or `$p` theorem. -/
  | assert (a : Assertion)
  deriving DecidableEq, Repr, Inhabited

/-- The label a statement introduces, if it has one. -/
def Statement.label? : Statement → Option Sym
  | .float hyp => some hyp.label
  | .essential hyp => some hyp.label
  | .assert a => some a.label
  | _ => none

/-- A parsed Metamath database: a symbol table plus statements in source order.

Parsing is *not* formalised. The Rust crate deliberately keeps its reader
outside the trusted computing base; what has to be trustworthy is the checker,
so this development starts from an already-parsed database. -/
structure Database where
  /-- Symbol classification, mirroring the Rust symbol table. -/
  symbols : List (Sym × SymbolKind)
  /-- All statements, in source order. -/
  statements : List Statement
  deriving DecidableEq, Repr, Inhabited

namespace Database

/-- Whether `s` is a declared variable. -/
def isVariable (db : Database) (s : Sym) : Bool :=
  match db.symbols.find? (fun entry => entry.1 == s) with
  | some entry => entry.2 == SymbolKind.var
  | none => false

/-- The statement at a given source position. -/
def statementAt (db : Database) (i : Nat) : Option Statement := db.statements[i]?

/-- The source position of a labelled statement.

Labels are unique in a well-formed database; `findIdx?` takes the first, which
is the definition the citation-ordering check below relies on. -/
def indexOfLabel (db : Database) (label : Sym) : Option Nat :=
  db.statements.findIdx? (fun stmt => stmt.label? == some label)

/-- Every assertion of the database, with its source position. -/
def assertions (db : Database) : List (Nat × Assertion) :=
  db.statements.zipIdx.filterMap fun (stmt, i) =>
    match stmt with
    | .assert a => some (i, a)
    | _ => none

end Database

/-- Whether a `$d` list declares `x` and `y` distinct. The pair is unordered. -/
def disjointDeclared (pairs : List (Sym × Sym)) (x y : Sym) : Bool :=
  pairs.any fun p => (p.1 == x && p.2 == y) || (p.1 == y && p.2 == x)

/-- The obligation generated by applying an assertion that declares `$d a b`,
under the substitution `σ`, in a context whose active `$d` set is `ctx`.

Both halves are needed. Syntactic distinctness of the images' variables alone is
unsound; requiring the *caller's* frame to declare each resulting pair distinct
is what propagates the obligation outwards instead of discharging it by fiat. -/
def disjointOk (isVar : Sym → Bool) (ctx : List (Sym × Sym)) (σ : Subst)
    (pair : Sym × Sym) : Bool :=
  (bodyVars isVar (σ.image pair.1)).all fun x =>
    (bodyVars isVar (σ.image pair.2)).all fun y =>
      !(x == y) && disjointDeclared ctx x y

/-- Every `$d` obligation of an applied frame, discharged in `ctx`. -/
def disjointsOk (isVar : Sym → Bool) (ctx : List (Sym × Sym)) (σ : Subst)
    (pairs : List (Sym × Sym)) : Bool :=
  pairs.all (disjointOk isVar ctx σ)

theorem disjointOk_iff {isVar ctx σ} {pair : Sym × Sym} :
    disjointOk isVar ctx σ pair = true ↔
      ∀ x ∈ bodyVars isVar (σ.image pair.1), ∀ y ∈ bodyVars isVar (σ.image pair.2),
        x ≠ y ∧ disjointDeclared ctx x y = true := by
  simp [disjointOk]

theorem disjointsOk_iff {isVar ctx σ} {pairs : List (Sym × Sym)} :
    disjointsOk isVar ctx σ pairs = true ↔ ∀ p ∈ pairs, disjointOk isVar ctx σ p = true := by
  simp [disjointsOk]

/-- **Derivability.**

`Provable db usable ctx e` holds when `e` follows in context `ctx` from the
assertions of `db` at usable indices. The three rules are exactly the three
things a Metamath proof step can do: cite an active floating hypothesis, cite an
active essential hypothesis, or apply an assertion schematically.

Note what the `apply` rule demands and what it does not. It demands that every
mandatory hypothesis of the applied assertion, *substituted*, is itself
derivable, and that the assertion's `$d` conditions are discharged by the
current context. It does **not** consult the applied assertion's own proof: a
`$p` theorem is used exactly as an axiom of the same shape. Eliminating that
appeal — showing a verified database's theorems are conservative over its
axioms — is a separate result; see the module docs of `Nucleus.Metamath.Verify`. -/
inductive Provable (db : Database) (usable : Nat → Prop) (ctx : Frame) : Expr → Prop where
  /-- Cite an active floating hypothesis. -/
  | float {f : FloatHyp} (mem : f ∈ ctx.floats) : Provable db usable ctx f.expr
  /-- Cite an active essential hypothesis. -/
  | essential {h : Hypothesis} (mem : h ∈ ctx.essentials) : Provable db usable ctx h.expr
  /-- Apply an assertion under a substitution, having derived every mandatory
  hypothesis and discharged every `$d` obligation. -/
  | apply {i : Nat} {a : Assertion} {σ : Subst}
      (found : db.statementAt i = some (.assert a))
      (allowed : usable i)
      (floats : ∀ f ∈ a.frame.floats, Provable db usable ctx (applySubst σ f.expr))
      (essentials : ∀ h ∈ a.frame.essentials, Provable db usable ctx (applySubst σ h.expr))
      (disjoints : disjointsOk db.isVariable ctx.disjoints σ a.frame.disjoints = true) :
      Provable db usable ctx (applySubst σ a.conclusion)

/-- Derivability is monotone in the set of usable assertions. Widening the
citation window can only add derivations. -/
theorem Provable.mono {db : Database} {u u' : Nat → Prop} {ctx : Frame} {e : Expr}
    (h : ∀ i, u i → u' i) : Provable db u ctx e → Provable db u' ctx e := by
  intro d
  induction d with
  | float mem => exact .float mem
  | essential mem => exact .essential mem
  | apply found allowed _ _ disjoints ihf ihe =>
    exact .apply found (h _ allowed) (fun f hf => ihf f hf) (fun x hx => ihe x hx) disjoints

end Nucleus.Metamath
