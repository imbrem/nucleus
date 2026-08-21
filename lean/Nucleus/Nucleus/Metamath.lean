import Nucleus.Metamath.Expr
import Nucleus.Metamath.Database
import Nucleus.Metamath.Compress
import Nucleus.Metamath.Verify
import Nucleus.Metamath.VerifyTest

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

The soundness proof forced two side conditions into the checker that the Rust
implementation does not yet enforce: cited assertions must occur earlier in the
database, and cited hypotheses must be active in the current frame.
`Nucleus.Metamath.VerifyTest` exhibits the databases that separate the two, and
is imported here rather than left standalone so that the separation is checked
on every build.
-/
