import Nucleus.Cbor.Bytes
import Nucleus.Cbor.Basic
import Nucleus.Cbor.General
import Nucleus.Cbor.Containers
import Nucleus.Cbor.Integers
import Nucleus.Cbor.Fractions
import Nucleus.Cbor.Profiles
import Nucleus.Cbor.Subsets
import Nucleus.Cbor.Reasonable
import Nucleus.Cbor.Dag
import Nucleus.Cbor.Json
import Nucleus.Cbor.Cas
import Nucleus.Cbor.Wire
import Nucleus.Cbor.Drisl
import Nucleus.Cbor.Atproto.Cid
import Nucleus.Cbor.Atproto.Data
import Nucleus.Cbor.Atproto.Address

/-!
# CBOR

CBOR data models are split between inexpensive JSON-shaped profiles, which
reuse `Json` definitionally, and the complete indexed grammar needed for tags
and arbitrary recursive map keys. Binary parsing and deterministic encoding
are deliberately separate layers.
-/
