import Nucleus.HolOmega.Env
import Nucleus.HolOmega.PowerTower
import Nucleus.HolOmega.Beth
import Nucleus.HolOmega.TotalSubtype
import Nucleus.HolOmega.Syntax
import Nucleus.HolOmega.Typing
import Nucleus.HolOmega.Substitution
import Nucleus.HolOmega.Kernel
import Nucleus.HolOmega.Model
import Nucleus.HolOmega.Examples

-- `Semantics.lean`, `Soundness.lean` and `Spec.lean` are not imported yet.
-- They are written against a constant-domain `SoundModel` whose carrier
-- ignores the kind environment, which a real `TY_ALL` rules out: `tmTyApp`
-- would force one domain for every instantiation, collapsing the model to a
-- singleton. They are being rewritten to denote into `Kernel.Universe`.
