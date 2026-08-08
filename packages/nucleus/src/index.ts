import init, { Repl, Step } from "../generated/nucleus.js";
import { canSpawn, spawnShell } from "./shell-process.js";
import { runShell } from "./wasi.js";

export { init, Repl, runShell, spawnShell, canSpawn };
export type { Step };
export type { ShellOptions, ShellResult } from "./wasi.js";
import type { ShellResult } from "./wasi.js";

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
  /**
   * Run the shell in this instance rather than a worker of its own.
   *
   * The default is a separate process, which is what the native binary does
   * and what keeps a slow shell from freezing the REPL. Inline exists for
   * hosts without cross-origin isolation, where there is no
   * `SharedArrayBuffer` and therefore no way for the guest to block.
   */
  inline?: boolean;
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
        const remote = repl.selectedKernel() !== "local";
        const result = await runTheShell(repl, host, step.arguments);
        // A whole object can be checked against its address by hashing it; a
        // single range cannot, until BLAKE3 range proofs exist (#442). So a
        // streaming read trusts the server in a way `.fetch` does not, and
        // saying so is the difference between a caveat and a surprise.
        const caveat = remote
          ? "-- reading the remote kernel directly; ranges are not verified (#442)\n"
          : "";
        const trailer =
          result.status === 0
            ? ""
            : `\nshell exited with status ${result.status}`;
        return {
          output: `${caveat}${result.stdout}${result.stderr}${trailer}`.replace(
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

/**
 * Runs the shell, in its own process where that is possible.
 *
 * A worker needs the wasm as bytes rather than a response, because it is
 * transferred rather than streamed.
 */
async function runTheShell(
  repl: Repl,
  host: Host,
  args: string[],
): Promise<ShellResult> {
  // A remote kernel is read straight from the worker with synchronous ranged
  // XHR, so nothing is copied into this page first and no shared memory is
  // involved. The local kernel's bytes live here, so that path needs the
  // channel and therefore cross-origin isolation.
  const selected = repl.selectedKernel();
  const remote = selected === "local" ? undefined : selected;

  if (host.inline || !canSpawn(remote !== undefined)) {
    return await runShell(repl, host.shell(), { args });
  }
  const source = host.shell();
  const wasm =
    source instanceof Response || source instanceof Promise
      ? await (await source).arrayBuffer()
      : toArrayBuffer(source);
  return await spawnShell(repl, wasm, { args, remote });
}

function toArrayBuffer(source: BufferSource): ArrayBuffer {
  return source instanceof ArrayBuffer
    ? source
    : (source.buffer.slice(
        source.byteOffset,
        source.byteOffset + source.byteLength,
      ) as ArrayBuffer);
}

function messageOf(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}
