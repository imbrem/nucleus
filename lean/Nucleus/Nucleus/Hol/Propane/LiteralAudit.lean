import Nucleus.Hol.Propane.LiteralCorrespondence
import Nucleus.Hol.Propane.LiteralEncoding
import Nucleus.Hol.Ethane.LiteralArena
import Nucleus.Hol.Ethane.LiteralRoots
import Nucleus.Hol.Ethane.LiteralTheoremBoundary
import Nucleus.Hol.Propane.LiteralCanonical

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
#print axioms Nucleus.Hol.Propane.BoolOp.definition_sound
#print axioms Nucleus.Hol.Propane.LiteralRegistry.canonical_eval
#print axioms Nucleus.Hol.Propane.LiteralRegistry.canonical_code_injective
#print axioms Nucleus.Hol.Propane.LiteralRegistry.signatureCode_injective
#print axioms Nucleus.Hol.Propane.LiteralRegistry.decodeGlobal_canonical
#print axioms Nucleus.Hol.Propane.LiteralRegistry.decodeGlobal_injective
#print axioms Nucleus.Hol.Propane.LiteralRegistry.lookup_injective
#print axioms Nucleus.Hol.Propane.LiteralRegistry.decodeGlobal_boolean_only
#print axioms Nucleus.Hol.Ethane.LiteralRoots.union_preserves_sound
#print axioms Nucleus.Hol.Ethane.LiteralRoots.union_preserves_immutable
#print axioms Nucleus.Hol.Ethane.LiteralRoots.semantic_union_preserves_sound
#print axioms Nucleus.Hol.Ethane.LiteralRoots.semantic_union_preserves_immutable
#print axioms Nucleus.Hol.Ethane.LiteralTheoremBoundary.constantCnf_holds
#print axioms Nucleus.Hol.Ethane.LiteralTheoremBoundary.constantDnf_holds
