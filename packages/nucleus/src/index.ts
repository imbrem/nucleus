import init, { lratToText, Repl, Step } from "../generated/nucleus.js";
import { runShell } from "./shell.js";

export { init, lratToText, Repl, runShell };
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

/** Everything the host must supply that a session cannot do itself. */
export interface Host {
  /** Optional alternate store for `(sqlite …)`; the local REPL is the default. */
  vfs?: import("./vfs-host.js").ReadOnlyVfs;
  /** Optional completely untrusted SAT oracle. */
  sat?: SatSolver;
}

/** Canonical problem and operational response bound given to a SAT oracle. */
export interface SatRequest {
  dimacs: Uint8Array;
  /** Providers should emit binary LRAT; trusted checking also accepts ASCII. */
  limits: { maxModelLiterals: number; maxProofBytes: number };
}

/** Data an untrusted SAT oracle may claim. */
export type SatResult =
  | { kind: "sat"; model: readonly bigint[] | BigInt64Array }
  | { kind: "unsat"; proof: Uint8Array }
  | { kind: "unknown"; reason?: string };

/** An injected asynchronous solver capability. */
export interface SatSolver {
  solve(request: SatRequest, signal?: AbortSignal): Promise<SatResult>;
}

/** Per-invocation host controls. */
export interface DriveOptions {
  signal?: AbortSignal;
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
  options: DriveOptions = {},
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
        const result = await runShell(repl, {
          args: step.arguments,
          vfs: host.vfs,
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

    case "solve":
      return await solve(repl, host, step, options.signal);

    default:
      return { output: step.text, quit: false };
  }
}

async function solve(
  repl: Repl,
  host: Host,
  step: Step,
  signal?: AbortSignal,
): Promise<Line> {
  let consumed = false;
  try {
    if (!host.sat) throw new Error("no SAT solver is configured");
    const request = {
      dimacs: step.dimacs,
      limits: {
        maxModelLiterals: step.maxModelLiterals,
        maxProofBytes: step.maxProofBytes,
      },
    };
    if (signal?.aborted) throw new Error("SAT solve aborted");
    const result = await abortable(host.sat.solve(request, signal), signal);
    switch (result.kind) {
      case "sat": {
        if (
          !(result.model instanceof BigInt64Array) &&
          !Array.isArray(result.model)
        ) {
          throw new Error("SAT solver returned a non-integer model");
        }
        if (result.model.length > step.maxModelLiterals) {
          throw new Error("SAT solver model exceeds its response bound");
        }
        const model =
          result.model instanceof BigInt64Array
            ? result.model
            : BigInt64Array.from(result.model);
        consumed = true;
        return { output: repl.completeSat(step.job, model), quit: false };
      }
      case "unsat": {
        if (!(result.proof instanceof Uint8Array)) {
          throw new Error("SAT solver returned a non-byte LRAT proof");
        }
        if (result.proof.byteLength > step.maxProofBytes) {
          throw new Error("SAT solver proof exceeds its response bound");
        }
        consumed = true;
        return {
          output: repl.completeUnsat(step.job, result.proof),
          quit: false,
        };
      }
      case "unknown":
        repl.completeSatUnknown(step.job, result.reason);
        consumed = true;
        return {
          output: result.reason ? `unknown: ${result.reason}` : "unknown",
          quit: false,
        };
      default:
        throw new Error("SAT solver returned an invalid result");
    }
  } catch (error) {
    if (!consumed) {
      try {
        const message = messageOf(error);
        if (signal?.aborted || message === "SAT solve aborted") {
          repl.cancelSat(step.job);
        } else {
          repl.completeSatFailure(step.job, message);
        }
      } catch {
        // Preserve the provider or checker error which caused cleanup.
      }
    }
    return { output: `error: ${messageOf(error)}`, quit: false };
  }
}

async function abortable<T>(
  promise: Promise<T>,
  signal?: AbortSignal,
): Promise<T> {
  if (!signal) return await promise;
  if (signal.aborted) throw new Error("SAT solve aborted");

  let rejectAbort: ((reason: Error) => void) | undefined;
  const aborted = new Promise<never>((_resolve, reject) => {
    rejectAbort = reject;
  });
  const onAbort = () => rejectAbort?.(new Error("SAT solve aborted"));
  signal.addEventListener("abort", onAbort, { once: true });
  try {
    const result = await Promise.race([promise, aborted]);
    if (signal.aborted) throw new Error("SAT solve aborted");
    return result;
  } finally {
    signal.removeEventListener("abort", onAbort);
  }
}

function messageOf(error: unknown): string {
  return error instanceof Error ? error.message : String(error);
}
