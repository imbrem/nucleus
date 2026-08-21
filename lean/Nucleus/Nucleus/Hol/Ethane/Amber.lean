import Nucleus.Hol.Ethane.Amber.Row
import Nucleus.Hol.Ethane.Amber.Forest
import Nucleus.Hol.Ethane.Amber.Syntax
import Nucleus.Hol.Ethane.Amber.Serialization
import Nucleus.Hol.Ethane.Amber.Cbor
import Nucleus.Hol.Ethane.Amber.Arena.Dense
import Nucleus.Hol.Ethane.Amber.Arena.Dense.Cbor
import Nucleus.Hol.Ethane.Amber.Segment
import Nucleus.Hol.Ethane.Amber.Examples

/-!
# Ethane Amber

Amber is the symbolic name for the first arena representations of Ethane. It
includes dense parent overlays, signed segment overlays, dense CBOR
codecs, an O256 CAS-key specialization, and a Rust-facing array model.
-/
