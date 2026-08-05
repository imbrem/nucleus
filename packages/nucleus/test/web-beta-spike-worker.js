import initHost, { WebHolProofPlan } from "../generated/nucleus.js";
import initGuest, { build } from "../generated/web-beta/guest.js";

// SECURITY: this disposable realm isolates the live kernel key and can be
// terminated for availability. It is not an ambient-capability sandbox: guest
// glue still has this Worker's network, storage, timer, and Worker APIs.
try {
  await initHost();
  await initGuest();
  const plan = new WebHolProofPlan();
  const namespace = build(plan);
  const recipe = plan.finish(namespace);
  self.postMessage({ recipe: recipe.buffer }, [recipe.buffer]);
} catch (error) {
  self.postMessage({ error: String(error?.stack ?? error) });
}
