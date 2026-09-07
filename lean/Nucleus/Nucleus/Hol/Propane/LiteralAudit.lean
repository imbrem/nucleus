import Nucleus.Hol.Propane.LiteralCorrespondence
import Nucleus.Hol.Propane.LiteralEncoding
import Nucleus.Hol.Ethane.LiteralArena

/-!
# Literal proof audit

The expected metatheoretic axioms are Lean's propositional extensionality,
classical choice, and quotient soundness. The actual infinity/natural model is
an explicit argument to the Ethane carrier construction; this file adds no
axioms. The full Propane proof system remains consistent after the builtin
computation rule is added.
-/

#print axioms Nucleus.Hol.Propane.ModelInt.equivInt
#print axioms Nucleus.Hol.Propane.integerEquivOfInfinity
#print axioms Nucleus.Hol.Propane.modelWordEquiv
#print axioms Nucleus.Hol.Propane.modelBytesEquiv
#print axioms Nucleus.Hol.Propane.EqTm.sound
#print axioms Nucleus.Hol.Propane.Proves.sound
#print axioms Nucleus.Hol.Propane.consistent
#print axioms Nucleus.Hol.Propane.literal_reduction_correspondence
#print axioms Nucleus.Hol.Ethane.Literals.builtin_sound
#print axioms Nucleus.Hol.Ethane.Literals.Dag.check_sound
#print axioms Nucleus.Hol.Propane.LiteralEncoding.decode_encodeNat
#print axioms Nucleus.Hol.Propane.LiteralEncoding.decode_encodeInt
