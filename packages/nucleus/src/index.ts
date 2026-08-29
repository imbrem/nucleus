import init, { Repl, Step } from "../generated/nucleus.js";
import { runShell } from "./shell.js";

export { init, Repl, runShell };
export type { Step };
export type { ShellOptions, ShellResult } from "./shell.js";
export type { ReadOnlyVfs, VfsError, VfsFile } from "./vfs-host.js";

/** What a driven line produced. */
export interface Line {
  /** Text to show, if any. */
  output: string;
  /** Whether the session asked to leave. */
  quit: boolean;
}

/** Browser-specific effect adapters used while driving a session. */
export interface DriveOptions {
  /** Optional alternate store for `(sqlite …)`; the local REPL is the default. */
  vfs?: import("./vfs-host.js").ReadOnlyVfs;
}

/**
 * Reads and evaluates one line, carrying out whatever the session asks for.
 *
 * The transport-neutral session decides *what* should happen. This frontend
 * adapter decides *how* to perform browser effects such as fetch, component
 * instantiation, and the separately hosted SQLite shell.
 */
export async function drive(
  repl: Repl,
  options: DriveOptions,
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

    case "proof":
      try {
        let handle = repl.openObject(step.address);
        if (handle < 0 && step.text !== "") {
          const response = await fetch(step.text);
          if (!response.ok) {
            throw new Error(`kernel returned ${response.status}`);
          }
          const fetched = new Uint8Array(await response.arrayBuffer());
          repl.admitVerified(step.address, fetched);
          handle = repl.openObject(step.address);
        }
        if (handle < 0) {
          throw new Error(`proof component ${step.address} is not resident`);
        }
        let bytes: Uint8Array;
        try {
          const length = repl.objectLength(handle);
          bytes = repl.readObject(handle, 0, length);
        } finally {
          repl.closeObject(handle);
        }
        const { kernelAddress, loadProof } = await import("./proof.js");
        const kernel = await loadProof(bytes);
        try {
          return { output: kernelAddress(kernel), quit: false };
        } finally {
          kernel[Symbol.dispose]();
        }
      } catch (error) {
        return { output: `error: ${messageOf(error)}`, quit: false };
      }

    case "shell":
      try {
        const result = await runShell(repl, {
          args: step.arguments,
          vfs: options.vfs,
        });
        const trailer =
          result.status === 0
            ? ""
            : `\nshell exited with status ${result.status}`;
        return {
          output: `${result.stdout}${result.stderr}${trailer}`.replace(
            /\n+$/,
            "",
          ),
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
