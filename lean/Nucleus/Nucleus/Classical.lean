import Nucleus.Classical.Alternating.Abstract
import Nucleus.Classical.Alternating.Equality
import Nucleus.Classical.Alternating.Packed
import Nucleus.Classical.Alternating.Rules
import Nucleus.Classical.ConcreteEmbedding
import Nucleus.Classical.Embedding
import Nucleus.Classical.Examples
import Nucleus.Classical.Mutation
import Nucleus.Classical.Mutation.Operations
import Nucleus.Classical.Packed.Block
import Nucleus.Classical.Packed.Encode
import Nucleus.Classical.Packed.Intrusive
import Nucleus.Classical.Packed.Layout
import Nucleus.Classical.Packed.Mutate
import Nucleus.Classical.Packed.Word
import Nucleus.Classical.Refutation
import Nucleus.Classical.Semantics
import Nucleus.Classical.Tagged.Abstract
import Nucleus.Classical.Tagged.Equality
import Nucleus.Classical.Tagged.Packed
import Nucleus.Classical.Tagged.Rules
import Nucleus.Classical.Tagged.Runtime
import Nucleus.Classical.Tagged.Runtime.Allocator
import Nucleus.Classical.Tagged.Runtime.Canonical
import Nucleus.Classical.Tagged.Runtime.Correspondence
import Nucleus.Classical.Tagged.Runtime.Encode
import Nucleus.Classical.Tagged.Runtime.EncodeCorrect
import Nucleus.Classical.Tagged.Runtime.Equality
import Nucleus.Classical.Tagged.Runtime.MachineWord
import Nucleus.Classical.Tagged.Runtime.Mutate
import Nucleus.Classical.Tagged.Runtime.Refutation

/-!
# Classical prover designs

The shared semantics is indexed by a partial Boolean assignment.  Syllogisms
are the null-assignment case.  The alternating and explicitly tagged designs
share a fixed-width packed substrate; refutation remains a separate layer.
`Eval` and `Holds` are total-assignment workers beneath the public `EvalAt`
and `EntailsAt` judgments, rather than assignment-free interpretations.
-/
