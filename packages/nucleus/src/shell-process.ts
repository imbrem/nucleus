/**
 * Running the SQLite shell as a separate process.
 *
 * The shell gets a Worker of its own and reaches the kernel over a shared
 * memory channel. That is the same arrangement the native binary has — a
 * subprocess over a Unix socket — with the transport swapped for what a
 * browser has.
 *
 * What this buys over instantiating the shell inline:
 *
 * - a wedged or slow shell cannot freeze the REPL;
 * - the shell holds no reference to the kernel, only a channel;
 * - "a shell in one tab while the REPL runs in another" becomes a change of
 *   transport rather than a redesign.
 */

import type { Repl } from "../generated/nucleus.js";
import { OP, SLOT, STATE, createChannel } from "./protocol.js";
import type { ShellOptions, ShellResult } from "./wasi.js";

/** Whether this host can run the shell in a worker of its own. */
export function canSpawn(): boolean {
  return (
    typeof Worker !== "undefined" &&
    typeof SharedArrayBuffer !== "undefined" &&
    // Cross-origin isolation is what makes SharedArrayBuffer usable rather
    // than merely declared. The demo server sets COOP and COEP for this.
    globalThis.crossOriginIsolated === true
  );
}

/**
 * Answers one pending CAS request, if there is one.
 *
 * Kernel calls are synchronous, so the answer is in place before this returns
 * — which is what the worker's `Atomics.wait` is waiting for.
 */
function serviceOnce(repl: Repl, control: Int32Array, data: Uint8Array): void {
  if (Atomics.load(control, SLOT.state) !== STATE.request) return;

  const op = Atomics.load(control, SLOT.op);
  const a = Atomics.load(control, SLOT.a);
  const b = Atomics.load(control, SLOT.b);
  const c = Atomics.load(control, SLOT.c);

  const answer = (result: number) => {
    Atomics.store(control, SLOT.result, result);
    Atomics.store(control, SLOT.state, STATE.response);
    Atomics.notify(control, SLOT.state);
  };

  try {
    switch (op) {
      case OP.open: {
        const hex = Array.from(data.subarray(0, a))
          .map((byte) => byte.toString(16).padStart(2, "0"))
          .join("");
        answer(repl.openObject(hex));
        break;
      }
      case OP.length:
        answer(repl.objectLength(a));
        break;
      case OP.read: {
        const bytes = repl.readObject(a, b, c);
        if (bytes.length > data.length) {
          // The channel bounds one response; a guest asking for more is a
          // protocol error rather than a reason to grow it.
          answer(-1);
          break;
        }
        data.set(bytes, 0);
        answer(bytes.length);
        break;
      }
      case OP.close:
        repl.closeObject(a);
        answer(0);
        break;
      default:
        answer(-1);
    }
  } catch {
    // A refusal the guest can see, rather than a wedged channel.
    answer(-1);
  }
}

/**
 * Runs the shell in its own worker.
 *
 * Check {@link canSpawn} first; without cross-origin isolation there is no
 * `SharedArrayBuffer` and therefore no way for the guest to block.
 */
export async function spawnShell(
  repl: Repl,
  wasm: ArrayBuffer,
  options: ShellOptions,
): Promise<ShellResult> {
  const channel = createChannel();
  const control = new Int32Array(channel.control);
  const data = new Uint8Array(channel.data);

  const worker = new Worker(new URL("./shell-worker.js", import.meta.url), {
    type: "module",
  });

  return await new Promise<ShellResult>((resolve) => {
    // The worker blocks until answered, so this only has to be prompt, not
    // instant. `Atomics.notify` cannot wake this thread — a browser main
    // thread may not wait — so polling is what is available.
    const poll = setInterval(() => serviceOnce(repl, control, data), 0);

    const finish = (result: ShellResult) => {
      clearInterval(poll);
      // Release anything the worker was still holding open.
      Atomics.store(control, SLOT.state, STATE.closed);
      Atomics.notify(control, SLOT.state);
      worker.terminate();
      resolve(result);
    };

    worker.addEventListener("message", (event: MessageEvent<ShellResult>) =>
      finish(event.data),
    );
    worker.addEventListener("error", (event) =>
      finish({
        status: -1,
        stdout: "",
        stderr: `shell worker failed: ${event.message}`,
      }),
    );

    worker.postMessage({
      wasm,
      args: options.args,
      stdin: options.stdin ?? "",
      channel,
    });
  });
}
