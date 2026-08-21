import Nucleus.Hol.Ethane.Reference
import Nucleus.Hol.Ethane.Subtype
import Nucleus.Hol.Ethane.Subtype.Semantics
import Nucleus.Hol.Ethane.Subtype.Checked
import Nucleus.Hol.Ethane.Subtype.Derivation
import Nucleus.Hol.Ethane.Subtype.Soundness
import Nucleus.Hol.Ethane.Conversion
import Nucleus.Hol.Ethane.Equivalence
import Nucleus.Hol.Ethane.FV
import Nucleus.Hol.Ethane.Arena
import Nucleus.Hol.Ethane.Arena.Cbor
import Nucleus.Hol.Ethane.Amber
import Nucleus.Hol.Ethane.Kernel.Contract
import Nucleus.Hol.Ethane.Kernel.Classification
import Nucleus.Hol.Ethane.Kernel.Row
import Nucleus.Hol.Ethane.Kernel.TypedFreeVariable

/-!
# Ethane

Ethane is the named, model-only HOL dialect.  The root module exports its
unsorted syntax, sort-indexed syntax, typing relation, lowering, borrowed HolE
semantics, reference proof theory, and the checked derivation and semantics of
its guarded subtype package.  Native proof certificates remain a separate
layer above this syntax boundary.  `Ethane.Amber` is its first named dense
forest, CAS, CBOR, and in-memory representation.
-/
