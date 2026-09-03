import Nucleus.Metamath.Expr
import Nucleus.Metamath.Database
import Nucleus.Metamath.Compress
import Nucleus.Metamath.Verify
import Nucleus.Metamath.VerifyTest
import Nucleus.Metamath.Embedding
import Nucleus.Metamath.HolMM
import Nucleus.Metamath.Metatheory

/-!
# Metamath

A specification of the Metamath proof checker, and its soundness proof.

`Nucleus.Metamath.Provable` is the derivability relation — floating hypothesis,
essential hypothesis, and schematic rule application, with distinct-variable
obligations propagated outwards. `Nucleus.Metamath.verifyDatabase` is the executable
checker. `Nucleus.Metamath.verifyDatabase_sound` is the statement that connects
them: everything the checker accepts is derivable from what precedes it.

Parsing is not modelled. The Rust crate this specifies,
`crates/logic/metamath`, deliberately keeps its reader outside the trusted
computing base — a parser suggests structure, and authority comes from
re-deriving it — so the development starts from an already-parsed database.

The soundness proof forced two side conditions into the checker: cited
assertions must occur earlier in the database, and cited hypotheses must be
active in the current frame. `crates/logic/metamath` now enforces both, retaining
the full active float and disjoint contexts alongside each assertion's
mandatory frame.

`Nucleus.Metamath.VerifyTest` exhibits the accepted and rejected boundary
databases and is imported here rather than left standalone so that the
regressions are checked on every build.

`Nucleus.Metamath.Embedding` packages a checked `demo0` derivation with the
signed-corpus coordinates carried by replay output. The corresponding mapping,
runtime representation commitments, and shallow-bridge boundary are specified
in `docs/metamath-hol-embedding.md`.

`Nucleus.Metamath.HolMM` asks the next question: are the things a Metamath
database *asserts* true? It interprets `hol.mm`, Metamath's own higher-order
logic, into `Nucleus.Hol`'s pointed-set semantics, proves 29 of its 71 `$a`
statements sound, and exhibits a countermodel for `ax-hbl1`. Its module
documentation states precisely what is proved, what is assumed, and what is
left open.

`Nucleus.Metamath.Metatheory` makes axiom-set monotonicity explicit, proves
soundness of the classical propositional axiom set, and proves conservativity
for explicit nonrecursive propositional definitions.
-/
