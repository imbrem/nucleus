import Nucleus.Metamath.Expr
import Nucleus.Metamath.Database
import Nucleus.Metamath.Compress
import Nucleus.Metamath.Verify
import Nucleus.Metamath.VerifyTest
import Nucleus.Metamath.HolMM

/-!
# Metamath

A specification of the Metamath proof checker, and its soundness proof.

`Nucleus.Metamath.Provable` is the derivability relation — hypothesis,
hypothesis, and schematic rule application, with distinct-variable obligations
propagated outwards. `Nucleus.Metamath.verifyDatabase` is the executable
checker. `Nucleus.Metamath.verifyDatabase_sound` is the statement that connects
them: everything the checker accepts is derivable from what precedes it.

Parsing is not modelled. The Rust crate this specifies,
`crates/logic/metamath`, deliberately keeps its reader outside the trusted
computing base — a parser suggests structure, and authority comes from
re-deriving it — so the development starts from an already-parsed database.

The soundness proof forced two side conditions into the checker: cited
assertions must occur earlier in the database, and cited hypotheses must be
active in the current frame. `crates/logic/metamath` enforces both, having
accepted proofs of false statements without them.

One gap remains, and it is a gap in the Rust data model rather than in its
checker. `Assertion.context` here carries `scopeFloats`, the floating
hypotheses active where an assertion is stated; the Rust `Database` retains the
corresponding `scope_disjoints` but not `scope_floats`, so its activity test
covers `$e` and not `$f`. Until that field exists the two check different
predicates, and this specification is the stricter of the two.

`Nucleus.Metamath.VerifyTest` exhibits the databases that separate the
behaviours, and is imported here rather than left standalone so that the
separation is checked on every build.

`Nucleus.Metamath.HolMM` asks the next question: are the things a Metamath
database *asserts* true? It interprets `hol.mm`, Metamath's own higher-order
logic, into `Nucleus.Hol`'s pointed-set semantics, proves 29 of its 71 `$a`
statements sound, and exhibits a countermodel for `ax-hbl1`. Its module
documentation states precisely what is proved, what is assumed, and what is
left open.
-/
