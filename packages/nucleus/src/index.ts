import init, { Repl, Step } from "../generated/nucleus.js";
import { runShell } from "./wasi.js";

export { init, Repl, runShell };
export type { Step };
export type { ShellOptions, ShellResult } from "./wasi.js";

/** What a driven line produced. */
export interface Line {
  /** Text to show, if any. */
  output: string;
  /** Whether the session asked to leave. */
  quit: boolean;
}

/** Everything the host must supply that a session cannot do itself. */
export interface Host {
  /** The shell wasm, for `(sqlite …)`. */
  shell: () => BufferSource | Response | Promise<Response>;
}

/**
 * Reads and evaluates one line, carrying out whatever the session asks for.
 *
 * This is the browser's half of the arrangement in `covalence_repl::session`:
 * the session decides *what* should happen and this decides *how*, because
 * fetching over the network and instantiating a wasm module are things only a
 * host can do.
 */
export async function drive(
  repl: Repl,
  host: Host,
  line: string,
): Promise<Line> {
  let step: Step;
  try {
    step = repl.eval(line);
  } catch (error) {
    return { output: `error: ${messageOf(error)}`, quit: false };
  }

  switch (step.kind) {
    case "quit":
      return { output: "", quit: true };

    case "fetch":
      try {
        const response = await fetch(step.text);
        if (!response.ok) {
          throw new Error(`kernel returned ${response.status}`);
        }
        const bytes = new Uint8Array(await response.arrayBuffer());
        // Verified against the address that was asked for, so a wrong or
        // hostile kernel is caught here rather than believed.
        return { output: repl.admitVerified(step.address, bytes), quit: false };
      } catch (error) {
        return { output: `error: ${messageOf(error)}`, quit: false };
      }

    case "shell":
      try {
        const result = await runShell(repl, host.shell(), {
          args: step.arguments,
        });
        const trailer =
          result.status === 0 ? "" : `\nshell exited with status ${result.status}`;
        return {
          output: `${result.stdout}${result.stderr}${trailer}`.replace(/\n+$/, ""),
          quit: false,
        };
      } catch (error) {
        return { output: `error: ${messageOf(error)}`, quit: false };
      }

    default:
      return { output: step.text, quit: false };
  }
}

function messageOf(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}
