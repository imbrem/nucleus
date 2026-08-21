import Nucleus.Hol.Ethane.Reference
import Nucleus.Hol.Ethane.Subtype
import Nucleus.Hol.Ethane.Conversion
import Nucleus.Hol.Ethane.Equivalence
import Nucleus.Hol.Ethane.FV
import Nucleus.Hol.Ethane.Arena
import Nucleus.Hol.Ethane.Arena.Cbor

/-!
# Ethane

Ethane is the named, model-only HOL dialect.  The root module currently exports
its unsorted syntax, sort-indexed syntax, typing relation, lowering, borrowed
HolE semantics, and reference proof theory.  Its native proof certificates and
derived subtype package are layered above this syntax boundary.
-/
