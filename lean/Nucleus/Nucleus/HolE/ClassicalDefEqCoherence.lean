import Nucleus.HolE.ClassicalSoundness

/-! # Coherence of typing modulo family equality

The raw-root view and semantic certificate-coherence theorem live beside the
definitionally typed evaluator in `ClassicalSoundness`, so every downstream
soundness module can use them without an import cycle.  This compatibility
module preserves the focused import boundary.
-/
